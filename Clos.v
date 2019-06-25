From mathcomp Require Import all_ssreflect.
Require Import Util LambdaLet.
Require Heaps.

Inductive heap :=
  | Empty
  | Cons of heap & term & heap
  | Mut of seq term & heap.

Definition clos := (heap * term)%type.

Fixpoint hget h n : option clos :=
  match h with
  | Empty => None
  | Cons h t h' => (if n is n.+1 then hget h' n else Some (h, t))
  | Mut ts h => nth (hget h (n - size ts)) (map (@Some _ \o pair (Mut ts h)) ts) n
  end.

Inductive eval_name : heap -> term -> clos -> Prop :=
  | eval_name_var H H' t x v :
      hget H x = Some (H', t) ->
      eval_name H' t v ->
      eval_name H (Var x) v
  | eval_name_app H H' t0 t1 t2 v :
      eval_name H t1 (H', Abs t0) ->
      eval_name (Cons H t2 H') t0 v ->
      eval_name H (App t1 t2) v
  | eval_name_abs H t0 :
      eval_name H (Abs t0) (H, Abs t0)
  | eval_name_let H ts t v :
      eval_name (Mut ts H) t v ->
      eval_name H (Let ts t) v.

CoInductive diverge_name : heap -> term -> Prop :=
  | diverge_name_var H H' t x :
      hget H x = Some (H', t) ->
      diverge_name H' t ->
      diverge_name H (Var x)
  | diverge_name_appL H t1 t2 :
      diverge_name H t1 ->
      diverge_name H (App t1 t2)
  | diverge_name_appabs H H' t0 t1 t2 :
      eval_name H t1 (H', Abs t0) ->
      diverge_name (Cons H t2 H') t0 ->
      diverge_name H (App t1 t2)
  | diverge_name_let H ts t :
      diverge_name (Mut ts H) t ->
      diverge_name H (Let ts t).

Inductive corr_term (R : nat -> nat -> Prop) : nat -> term -> term -> Prop :=
  | corr_term_loc n l x :
      n <= x ->
      R l (x - n) ->
      corr_term R n (Loc l) (Var x)
  | corr_term_var n x :
      x < n ->
      corr_term R n (Var x) (Var x)
  | corr_term_abs n t t' :
      corr_term R n.+1 t t' ->
      corr_term R n (Abs t) (Abs t')
  | corr_term_app n t1 t1' t2 t2' :
      corr_term R n t1 t1' ->
      corr_term R n t2 t2' ->
      corr_term R n (App t1 t2) (App t1' t2')
  | corr_term_let n ts ts' t t' :
      size ts = size ts' ->
      ( forall x, x < size ts -> forall d,
        corr_term R (size ts + n)
          (nth d ts x) (nth d ts' x) ) ->
      corr_term R (size ts + n) t t' ->
      corr_term R n (Let ts t) (Let ts' t').

CoInductive corr_heap H1 : (nat -> nat -> Prop) -> heap -> Prop :=
  | corr_heap_fold (R : nat -> nat -> Prop) H2 :
      ( forall l x, R l x ->
        exists t1, nth None H1 l = Some t1 /\
        exists H2' t2, hget H2 x = Some (H2', t2) /\
        exists R', corr_heap H1 R' H2' /\ corr_term R' 0 t1 t2 ) ->
      corr_heap H1 R H2.

Lemma corr_heap_unfold R H1 H2 :
  corr_heap H1 R H2 ->
  ( forall l x, R l x ->
    exists t1, nth None H1 l = Some t1 /\
    exists H2' t2, hget H2 x = Some (H2', t2) /\
    exists R', corr_heap H1 R' H2' /\ corr_term R' 0 t1 t2 ).
Proof. by inversion 1. Qed.

Hint Constructors eval_name diverge_name corr_term corr_heap.

Lemma corr_term_impl R n t t' :
  corr_term R n t t' ->
  forall (R' : nat -> nat -> Prop),
  (forall l x, R l x -> R' l x) ->
  corr_term R' n t t'.
Proof. induction 1 => ? Himpl; eauto. Qed.

Lemma corr_term_subst :
  forall R n t t', corr_term R n t t' ->
  forall (R' : nat -> nat -> Prop) s m,
  m <= n ->
  (forall x, x < m -> s x = Var x) ->
  (forall x, m <= x -> x < n -> exists l, s x = Loc l) ->
  (forall l x, n <= x -> R l (x - n) -> R' l (x - m)) ->
  (forall l x, s x = Loc l -> R' l (x - m)) ->
  corr_term R' m (subst s t) t'.
Proof.
  have Hs_impl : forall n s m,
    (forall x, x < m -> s x = Var x) ->
    (forall x : nat, x < n + m -> upn s n x = Var x).
  { move => n ? ? Hs x ?.
    rewrite (eq_upn _ Var) => [ | ? ].
    - exact: upn_Var.
    - apply: Hs.
      by rewrite -(ltn_add2l n) subnKC. }
  have Hs'_impl: forall ts s m n,
    (forall x, m <= x -> x < n -> exists l, s x = Loc l) ->
    (forall x, ts + m <= x -> x < ts + n -> exists l, upn s ts x = Loc l).
  { move => ts ? m ? Hs' x ? ?.
    rewrite upn_unfold.
    have Hleq := leq_trans (leq_addr m _).
    rewrite ltnNge Hleq => //=.
    case (Hs' (x - ts)) => [ | | ? -> /= ];
    [ rewrite -(leq_add2l ts) subnKC
    | rewrite -(ltn_add2l ts) subnKC | ]; eauto. }
  have HR_impl: forall ts (R R' : nat -> _) m n,
    (forall l x, n <= x -> R l (x - n) -> R' l (x - m)) ->
    (forall l x, ts + n <= x -> R l (x - (ts + n)) -> R' l (x - (ts + m))).
  { move => ts ? ? ? n HR ? ? ?.
    rewrite !subnDA. apply: HR.
    rewrite -(leq_add2l ts) subnKC => //.
    exact: (leq_trans (leq_addr n _)). }
  have Hloc_impl : forall ts (R' : nat -> _) s m,
    (forall l x, s x = Loc l -> R' l (x - m)) ->
    (forall l x, upn s ts x = Loc l -> R' l (x - (ts + m))).
  { move => ts ? s m Hloc ? x.
    rewrite upn_unfold.
    move: (leqP ts x) subnDA (Hloc^~ (x - ts)) => [ ? -> | // ].
    case: (s (x - ts)); inversion 2; subst; eauto. }
  induction 1 => ? ? m Hleq Hs Hs' ? ? /=; eauto using leq_trans.
  - case (leqP m x) => Hlt.
    + case: (Hs' _ Hlt H) => ? Heq.
      rewrite Heq. eauto.
    + rewrite Hs; eauto.
  - constructor.
    apply: IHcorr_term.
    + exact Hleq.
    + exact: (Hs_impl 1).
    + exact: (Hs'_impl 1).
    + exact: (HR_impl 1).
    + exact: (Hloc_impl 1).
  - ( constructor; rewrite size_map ) => // [ x ? d | ];
    [ rewrite (nth_map d) => //; apply: H1 => // | apply: IHcorr_term ];
    solve [ by rewrite leq_add2l | exact: Hs_impl | exact: Hs'_impl | exact: HR_impl | exact: Hloc_impl ].
Qed.

Lemma corr_heap_dom R H1 H2 :
  corr_heap H1 R H2 ->
  forall (R' : nat -> nat -> Prop),
  (forall l x, R' l x -> R l x) ->
  corr_heap H1 R' H2.
Proof.
  inversion 1 => ? Hdom. subst.
  constructor => ? ? /Hdom. eauto.
Qed.

Lemma corr_heap_ext H1 H1'
  (Hext : forall l t, nth None H1 l = Some t -> nth None H1' l = Some t) :
  forall R H2,
  corr_heap H1 R H2 ->
  corr_heap H1' R H2.
Proof.
  cofix corr_heap_ext.
  inversion 1. subst.
  constructor => ? ? /H3 [ ? [ /Hext -> [ ? [ ? [ -> [ ? [ ? ? ] ] ] ] ] ] ].
  repeat (eexists; eauto).
Qed.

Corollary corr_heap_cat R H1 H2 Hd :
  corr_heap H1 R H2 ->
  corr_heap (H1 ++ Hd) R H2.
Proof.
  move => /corr_heap_ext.
  apply => l ?.
  by move: nth_cat (leqP (size H1) l) => -> [ /(nth_default _) -> | ].
Qed.

Corollary corr_heap_rcons R H1 H2 o :
  corr_heap H1 R H2 ->
  corr_heap (rcons H1 o) R H2.
Proof. by rewrite -cats1 => /corr_heap_cat. Qed.
  
Lemma corr_heap_union R R' H1 H2 :
  corr_heap H1 R H2 ->
  corr_heap H1 R' H2 ->
  corr_heap H1 (fun l x => R l x \/ R' l x) H2.
Proof.
  inversion 1. subst.
  inversion 1. subst.
  constructor => ? ? [ /H3 | /H5 ]; eauto.
Qed.

Lemma corr_heap_cons R H1 H2 H t :
  corr_heap H1 R H2 ->
  corr_heap H1 (fun l x => 0 < x /\ R l x.-1) (Cons H t H2).
Proof.
  inversion 1. subst.
  constructor => ? [ | ? ] [ ] //= ?.
  exact: H4.
Qed.

Lemma corr_heap_mut R H1 H2 cs :
  corr_heap H1 R H2 ->
  corr_heap H1 (fun l x => size cs <= x /\ R l (x - size cs)) (Mut cs H2).
Proof.
  inversion 1. subst.
  constructor => ? ? [ ? ] /= /H3 [ ? [ -> [ ? [ ? [ -> [ ? [ ? ? ] ] ] ] ] ] ].
  rewrite nth_default ?size_map => //.
  repeat (eexists; eauto).
Qed.

Theorem eval_name_sound H1 H1' t1 v1 :
  Heaps.eval_name H1 t1 H1' v1 ->
  forall R H2 t2,
  corr_heap H1 R H2 ->
  corr_term R 0 t1 t2 ->
  exists R' H2' v2,
  eval_name H2 t2 (H2', v2) /\
  corr_heap H1' R' H2' /\
  corr_term R' 0 v1 v2.
Proof.
  induction 1; inversion 1; inversion 1; subst.
  - move: subn0 H12 => -> /H5 [ ? [ ] ].
    rewrite H0. inversion 1.
    subst => [ [ ? [ ? [ ? [ ? [ Hheap Hterm ] ] ] ] ] ].
    move: (IHeval_name _ _ _ Hheap Hterm) =>
      [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ].
    repeat (eexists; eauto).
  - move: (IHeval_name1 _ _ _ H3 H12) =>
      [ R' [ H2' [ ? [ ? [ ] ] ] ] ].
    inversion 2. subst.
    have Hterm' : corr_term
      (fun l x => 0 < x /\ R' l x.-1 \/ l = size H' /\ x = 0) 0
      (subst (scons (Loc (size H')) Var) t0) t'.
    { (apply: corr_term_subst; eauto) => [ | | ? | ? ];
      move => [ | ? ] //=; eauto.
      - rewrite subn1 subn0. eauto.
      - inversion 1. eauto. }
    have Hheap' : corr_heap (rcons H' (Some t2))
      (fun l x => 0 < x /\ R' l x.-1 \/ l = size H' /\ x = 0)
      (Cons H2 t2' H2').
    { apply: corr_heap_union.
      - apply: corr_heap_cons.
        exact: corr_heap_rcons.
      - constructor => ? ? [ -> -> ] /=.
        rewrite nth_rcons ltnn eqxx.
        do 7 eexists; eauto.
        apply: corr_heap_rcons.
        refine (corr_heap_ext _ _ (Heaps.eval_name_heap _ _ _ _ _) _ _ _); eauto. }
    move: (IHeval_name2 _ _ _ Hheap' Hterm') =>
      [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ].
    repeat (eexists; eauto).
  - repeat (eexists; eauto).
  - have Hterm' : corr_term (fun l x =>
      size ts <= x /\ R l (x - size ts) \/
      x < size ts /\ l = size H + x) 0
      (subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var) t) t'.
    { (apply: corr_term_subst; eauto) => [ // | ? ? | ? ? | ? x ];
      rewrite ?nth_scat ?addn0 ?subn0; eauto.
      - move => /(nth_mkseq _) => -> /=. eauto.
      - case (leqP (size ts) x) => ?.
        + by rewrite nth_default ?size_mkseq.
        + rewrite nth_mkseq => //=.
          inversion 1. eauto. }
    have Hheap' : corr_heap
      (H ++ map (@Some _ \o
        subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var)) ts)
      (fun l x =>
        size ts <= x /\ R l (x - size ts) \/
        x < size ts /\ l = size H + x)
      (Mut ts' H2).
    { cofix Hheap'.
      constructor => ? x [ [ ? ? ] | [ ? -> ] /= ].
      - apply: corr_heap_unfold.
        + apply: corr_heap_mut.
          apply: corr_heap_cat. eauto.
        + move: H10 => /= <-. eauto.
      - rewrite nth_cat ltnNge leq_addr addKn !(nth_map (Var 0)) => /=; try congruence.
        do 7 eexists => /=; eauto.
        (apply: corr_term_subst; eauto) => [ // | ? ? | ? ? | ? y ];
        rewrite ?nth_scat ?addn0 ?subn0; eauto.
        - move => /(nth_mkseq _) => -> /=. eauto.
        - case (leqP (size ts) y) => ?.
          * by rewrite nth_default ?size_mkseq.
          * rewrite nth_mkseq => //=.
            inversion 1. eauto. }
    move: (IHeval_name _ _ _ Hheap' Hterm') =>
      [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ].
    repeat (eexists; eauto).
Qed.

Theorem diverge_name_sound :
  forall H1 t1,
  Heaps.diverge_name H1 t1 ->
  forall R H2 t2,
  corr_heap H1 R H2 ->
  corr_term R 0 t1 t2 ->
  diverge_name H2 t2.
Proof.
  cofix diverge_name_sound.
  inversion 1; inversion 1; subst; inversion 1; subst.
  - move: subn0 H10 => -> /H9 [ ? [ ] ].
    rewrite H2. inversion 1. subst => [ [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ].
    apply: diverge_name_var; eauto.
  - apply: diverge_name_appL. eauto.
  - move: (eval_name_sound _ _ _ _ H2 _ _ _ H7 H10) =>
      [ R' [ H2' [ ? [ ? [ ] ] ] ] ].
    inversion 2. subst.
    have Hterm' : corr_term
      (fun l x => 0 < x /\ R' l x.-1 \/ l = size H' /\ x = 0) 0
      (subst (scons (Loc (size H')) Var) t0) t'.
    { (apply: corr_term_subst; eauto) => [ | | ? | ? ];
      move => [ | ? ] //=; eauto.
      - rewrite subn1 subn0. eauto.
      - inversion 1. eauto. }
    have Hheap' : corr_heap (rcons H' (Some t3))
      (fun l x => 0 < x /\ R' l x.-1 \/ l = size H' /\ x = 0)
      (Cons H6 t2' H2').
    { apply: corr_heap_union.
      - apply: corr_heap_cons.
        exact: corr_heap_rcons.
      - constructor => ? ? [ -> -> ] /=.
        rewrite nth_rcons ltnn eqxx.
        do 7 eexists; eauto.
        apply: corr_heap_rcons.
        refine (corr_heap_ext _ _ (Heaps.eval_name_heap _ _ _ _ _) _ _ _); eauto. }
    apply: diverge_name_appabs; eauto.
  - have Hterm' : corr_term (fun l x =>
      size ts <= x /\ R l (x - size ts) \/
      x < size ts /\ l = size H1 + x) 0
      (subst (scat (mkseq (Loc \o addn (size H1)) (size ts)) Var) t) t'.
    { (apply: corr_term_subst; eauto) => [ // | ? ? | ? ? | ? x ];
      rewrite ?nth_scat ?addn0 ?subn0; eauto.
      - move => /(nth_mkseq _) => -> /=. eauto.
      - case (leqP (size ts) x) => ?.
        + by rewrite nth_default ?size_mkseq.
        + rewrite nth_mkseq => //=.
          inversion 1. eauto. }
    have Hheap' : corr_heap
      (H1 ++ map (@Some _ \o
        subst (scat (mkseq (Loc \o addn (size H1)) (size ts)) Var)) ts)
      (fun l x =>
        size ts <= x /\ R l (x - size ts) \/
        x < size ts /\ l = size H1 + x)
      (Mut ts' H5).
    { cofix Hheap'.
      constructor => ? x [ [ ? ? ] | [ ? -> ] /= ].
      - apply: corr_heap_unfold.
        + apply: corr_heap_mut.
          apply: corr_heap_cat. eauto.
        + move: H7 => /= <-. eauto.
      - rewrite nth_cat ltnNge leq_addr addKn !(nth_map (Var 0)) => /=; try congruence.
        do 7 eexists => /=; eauto.
        (apply: corr_term_subst; eauto) => [ // | ? ? | ? ? | ? y ];
        rewrite ?nth_scat ?addn0 ?subn0; eauto.
        + move => /(nth_mkseq _) => -> /=. eauto.
        + case (leqP (size ts) y) => ?.
          * by rewrite nth_default ?size_mkseq.
          * rewrite nth_mkseq => //=.
            inversion 1. eauto. }
    apply: diverge_name_let. eauto.
Qed.

Theorem eval_name_complete H2 t2 c :
  eval_name H2 t2 c ->
  forall R H1 t1,
  corr_heap H1 R H2 ->
  corr_term R 0 t1 t2 ->
  exists R' H1' v1,
  Heaps.eval_name H1 t1 H1' v1 /\
  corr_heap H1' R' c.1 /\
  corr_term R' 0 v1 c.2.
Proof.
  induction 1; inversion 1; inversion 1; subst.
  - move: subn0 H13 => -> /H5 [ ? [ ? [ ? [ ? [ ] ] ] ] ].
    rewrite H0. inversion 1.
    subst => [ [ ? [ Hheap Hterm ] ] ].
    move: (IHeval_name _ _ _ Hheap Hterm) =>
      [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ].
    repeat (eexists; eauto).
  - inversion H12.
  - move: (IHeval_name1 _ _ _ H3 H13) =>
      [ R' [ H2' [ ? [ ? [ ] ] ] ] ].
    inversion 2. subst.
    have Hterm' : corr_term
      (fun l x => 0 < x /\ R' l x.-1 \/ l = size H2' /\ x = 0) 0
      (subst (scons (Loc (size H2')) Var) t) t0.
    { (apply: corr_term_subst; eauto) => [ | | ? | ? ];
      move => [ | ? ] //=; eauto.
      - rewrite subn1 subn0. eauto.
      - inversion 1. eauto. }
    have Hheap' : corr_heap (rcons H2' (Some t5))
      (fun l x => 0 < x /\ R' l x.-1 \/ l = size H2' /\ x = 0)
      (Cons H t2 H').
    { apply: corr_heap_union.
      - apply: corr_heap_cons.
        exact: corr_heap_rcons.
      - constructor => ? ? [ -> -> ] /=.
        rewrite nth_rcons ltnn eqxx.
        do 7 eexists; eauto.
        apply: corr_heap_rcons.
        refine (corr_heap_ext _ _ (Heaps.eval_name_heap _ _ _ _ _) _ _ _); eauto. }
    move: (IHeval_name2 _ _ _ Hheap' Hterm') =>
      [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ].
    repeat (eexists; eauto).
  - repeat (eexists; eauto).
  - have Hterm' : corr_term (fun l x =>
      size ts0 <= x /\ R l (x - size ts0) \/
      x < size ts0 /\ l = size H1 + x) 0
      (subst (scat (mkseq (Loc \o addn (size H1)) (size ts0)) Var) t0) t.
    { (apply: corr_term_subst; eauto) => [ // | ? ? | ? ? | ? x ];
      rewrite ?nth_scat ?addn0 ?subn0; eauto.
      - move => /(nth_mkseq _) => -> /=. eauto.
      - case (leqP (size ts0) x) => ?.
        + by rewrite nth_default ?size_mkseq.
        + rewrite nth_mkseq => //=.
          inversion 1. eauto. }
    have Hheap' : corr_heap
      (H1 ++ map (@Some _ \o
        subst (scat (mkseq (Loc \o addn (size H1)) (size ts0)) Var)) ts0)
      (fun l x =>
        size ts0 <= x /\ R l (x - size ts0) \/
        x < size ts0 /\ l = size H1 + x)
      (Mut ts H).
    { cofix Hheap'.
      constructor => ? x [ [ ? ? ] | [ ? -> ] /= ].
      - apply: corr_heap_unfold.
        + apply: corr_heap_mut.
          apply: corr_heap_cat. eauto.
        + move: H10 => /= <-. eauto.
      - rewrite nth_cat ltnNge leq_addr addKn !(nth_map (Var 0)) => /=; try congruence.
        do 7 eexists => /=; eauto.
        (apply: corr_term_subst; eauto) => [ // | ? ? | ? ? | ? y ];
        rewrite ?nth_scat ?addn0 ?subn0; eauto.
        + move => /(nth_mkseq _) => -> /=. eauto.
        + case (leqP (size ts0) y) => ?.
          * by rewrite nth_default ?size_mkseq.
          * rewrite nth_mkseq => //=.
            inversion 1. eauto. }
    move: (IHeval_name _ _ _ Hheap' Hterm') =>
      [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ].
    repeat (eexists; eauto).
Qed.

Theorem diverge_name_complete :
  forall H2 t2,
  diverge_name H2 t2 ->
  forall R H1 t1,
  corr_heap H1 R H2 ->
  corr_term R 0 t1 t2 ->
  Heaps.diverge_name H1 t1.
Proof.
  cofix diverge_name_complete.
  inversion 1; inversion 1; subst; inversion 1; subst.
  - move: subn0 H11 => -> /H9 [ ? [ ? [ ? [ ? [ ] ] ] ] ].
    rewrite H1. inversion 1. subst => [ [ ? [ ? ? ] ] ].
    apply: Heaps.diverge_name_loc; eauto.
  - inversion H10.
  - apply: Heaps.diverge_name_appL; eauto.
  - move: (eval_name_complete _ _ _ H1 _ _ _ H7 H11) =>
      [ R' [ H2' [ ? [ ? [ ] ] ] ] ].
    inversion 2. subst.
    have Hterm' : corr_term
      (fun l x => 0 < x /\ R' l x.-1 \/ l = size H2' /\ x = 0) 0
      (subst (scons (Loc (size H2')) Var) t) t0.
    { (apply: corr_term_subst; eauto) => [ | | ? | ? ];
      move => [ | ? ] //=; eauto.
      - rewrite subn1 subn0. eauto.
      - inversion 1. eauto. }
    have Hheap' : corr_heap (rcons H2' (Some t5))
      (fun l x => 0 < x /\ R' l x.-1 \/ l = size H2' /\ x = 0)
      (Cons H2 t3 H').
    { apply: corr_heap_union.
      - apply: corr_heap_cons.
        exact: corr_heap_rcons.
      - constructor => ? ? [ -> -> ] /=.
        rewrite nth_rcons ltnn eqxx.
        do 7 eexists; eauto.
        apply: corr_heap_rcons.
        refine (corr_heap_ext _ _ (Heaps.eval_name_heap _ _ _ _ _) _ _ _); eauto. }
    apply: Heaps.diverge_name_appabs; eauto.
  - have Hterm' : corr_term (fun l x =>
      size ts0 <= x /\ R l (x - size ts0) \/
      x < size ts0 /\ l = size H5 + x) 0
      (subst (scat (mkseq (Loc \o addn (size H5)) (size ts0)) Var) t0) t.
    { (apply: corr_term_subst; eauto) => [ // | ? ? | ? ? | ? x ];
      rewrite ?nth_scat ?addn0 ?subn0; eauto.
      - move => /(nth_mkseq _) => -> /=. eauto.
      - case (leqP (size ts0) x) => ?.
        + by rewrite nth_default ?size_mkseq.
        + rewrite nth_mkseq => //=.
          inversion 1. eauto. }
    have Hheap' : corr_heap
      (H5 ++ map (@Some _ \o
        subst (scat (mkseq (Loc \o addn (size H5)) (size ts0)) Var)) ts0)
      (fun l x =>
        size ts0 <= x /\ R l (x - size ts0) \/
        x < size ts0 /\ l = size H5 + x)
      (Mut ts H2).
    { cofix Hheap'.
      constructor => ? x [ [ ? ? ] | [ ? -> ] /= ].
      - apply: corr_heap_unfold.
        + apply: corr_heap_mut.
          apply: corr_heap_cat. eauto.
        + move: H7 => /= <-. eauto.
      - rewrite nth_cat ltnNge leq_addr addKn !(nth_map (Var 0)) => /=; try congruence.
        do 7 eexists => /=; eauto.
        (apply: corr_term_subst; eauto) => [ // | ? ? | ? ? | ? y ];
        rewrite ?nth_scat ?addn0 ?subn0; eauto.
        + move => /(nth_mkseq _) => -> /=. eauto.
        + case (leqP (size ts0) y) => ?.
          * by rewrite nth_default ?size_mkseq.
          * rewrite nth_mkseq => //=.
            inversion 1. eauto. }
    apply: Heaps.diverge_name_let. eauto.
Qed.
