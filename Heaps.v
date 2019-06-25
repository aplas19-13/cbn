Require Import Relations Classical.
From mathcomp Require Import all_ssreflect.
Require Import Util LambdaLet.

Inductive eval_name : seq (option term) -> term -> seq (option term) -> term -> Prop :=
  | eval_name_loc H H' l t v :
      nth None H l = Some t ->
      eval_name H t H' v ->
      eval_name H (Loc l) H' v
  | eval_name_app H H' H'' t0 t1 t2 v :
      eval_name H t1 H' (Abs t0) ->
      eval_name (rcons H' (Some t2)) (subst (scons (Loc (size H')) Var) t0) H'' v ->
      eval_name H (App t1 t2) H'' v
  | eval_name_abs H t0 :
      eval_name H (Abs t0) H (Abs t0)
  | eval_name_let H H' ts t v :
      let s := scat (mkseq (Loc \o addn (size H)) (size ts)) Var in
      eval_name (H ++ map (@Some _ \o subst s) ts) (subst s t) H' v ->
      eval_name H (Let ts t) H' v.

CoInductive diverge_name : seq (option term) -> term -> Prop :=
  | diverge_name_loc H l t :
      nth None H l = Some t ->
      diverge_name H t ->
      diverge_name H (Loc l)
  | diverge_name_appL H t1 t2 :
      diverge_name H t1 ->
      diverge_name H (App t1 t2)
  | diverge_name_appabs H H' t0 t1 t2 :
      eval_name H t1 H' (Abs t0) ->
      diverge_name (rcons H' (Some t2)) (subst (scons (Loc (size H')) Var) t0) ->
      diverge_name H (App t1 t2)
  | diverge_name_let H ts t :
      let s := scat (mkseq (Loc \o addn (size H)) (size ts)) Var in
      diverge_name (H ++ map (@Some _ \o subst s) ts) (subst s t) ->
      diverge_name H (Let ts t).

Inductive red_name : seq (option term) -> term -> seq (option term) -> term -> Prop :=
  | red_name_loc H l t :
      nth None H l = Some t ->
      red_name H (Loc l) H t
  | red_name_appL H H' t1 t1' t2 :
      red_name H t1 H' t1' ->
     red_name H (App t1 t2) H' (App t1' t2)
  | red_name_beta H t11 t2 :
      red_name H (App (Abs t11) t2) (rcons H (Some t2)) (subst (scons (Loc (size H)) Var) t11)
  | red_name_let H ts t :
      let s := scat (mkseq (Loc \o addn (size H)) (size ts)) Var in
      red_name H (Let ts t) (H ++ map (@Some _ \o subst s) ts) (subst s t).

Inductive wf_term (p : nat -> Prop) : term -> Prop :=
  | wf_term_loc l :
      p l ->
      wf_term p (Loc l)
  | wf_term_var x :
      wf_term p (Var x)
  | wf_term_abs t :
      wf_term p t ->
      wf_term p (Abs t)
  | wf_term_app t1 t2 :
      wf_term p t1 ->
      wf_term p t2 ->
      wf_term p (App t1 t2)
  | wf_term_let ts t :
      ( forall x, x < size ts -> forall d,
        wf_term p (nth d ts x) ) ->
      wf_term p t ->
      wf_term p (Let ts t).

Inductive corr_term (f : nat -> nat -> Prop) : term -> term -> Prop :=
  | corr_term_loc l l' :
      f l l' ->
      corr_term f (Loc l) (Loc l')
  | corr_term_var x :
      corr_term f (Var x) (Var x)
  | corr_term_abs t t' :
      corr_term f t t' ->
      corr_term f (Abs t) (Abs t')
  | corr_term_app t1 t1' t2 t2' :
      corr_term f t1 t1' ->
      corr_term f t2 t2' ->
      corr_term f (App t1 t2) (App t1' t2')
  | corr_term_let ts ts' t t' :
      size ts = size ts' ->
      ( forall x, x < size ts -> forall d,
        corr_term f (nth d ts x) (nth d ts' x) ) ->
      corr_term f t t' ->
      corr_term f (Let ts t) (Let ts' t').

Hint Constructors eval_name diverge_name red_name clos_refl_trans eval_name diverge_name wf_term corr_term wf_term corr_term.

Definition wf_heap_segment (p p' : nat -> Prop) H :=
  forall l, p l ->
  exists t, nth None H l = Some t /\ wf_term p' t.

Definition wf_heap p := wf_heap_segment p p.

Definition iso_heap_segment (f f' : nat -> nat -> Prop) H1 H2 :=
  forall l1 l2, f l1 l2 ->
  exists t1, nth None H1 l1 = Some t1 /\
  exists t2, nth None H2 l2 = Some t2 /\
  corr_term f' t1 t2.

Definition iso_heap f := iso_heap_segment f f.


Lemma value_eval_name H v :
  value v -> eval_name H v H v.
Proof. by inversion 1. Qed.

Lemma eval_name_value H H' t v :
  eval_name H t H' v -> value v.
Proof. by induction 1. Qed.

Lemma eval_name_det H H' t v :
  eval_name H t H' v ->
  forall H'' v',
  eval_name H t H'' v' ->
  H' = H'' /\ v = v'.
Proof.
  induction 1; inversion 1; subst; eauto.
  - move: H0 H5 => ->. inversion 1. subst. eauto.
  - case: (IHeval_name1 _ _ H5) => ?. inversion 1. subst. eauto.
Qed.

Lemma eval_name_diverge_name_disjoint H H' t v :
  eval_name H t H' v ->
  diverge_name H t ->
  False.
Proof.
  induction 1; inversion 1; subst; eauto.
  - move: H0 H5 => ->. inversion 1. subst. eauto.
  - case: (eval_name_det _ _ _ _ H0_ _ _ H5).
    inversion 2. subst. eauto.
Qed.

Corollary value_diverge_name_disjoint H v :
  value v ->
  diverge_name H v ->
  False.
Proof.
  move => /(value_eval_name H).
  exact: eval_name_diverge_name_disjoint.
Qed.

Lemma eval_name_heap H H' t v :
  eval_name H t H' v ->
  forall l t,
  nth None H l = Some t ->
  nth None H' l = Some t.
Proof.
  (induction 1; eauto) => l ? Hnth; eauto.
  - apply: IHeval_name2.
    by move: nth_rcons (leqP (size H') l) (IHeval_name1 _ _ Hnth) =>
      -> [ /(nth_default _) -> | ].
  - apply: IHeval_name.
    by move: nth_cat (leqP (size H) l) Hnth =>
      -> [ /(@nth_default _ _) -> | ].
Qed.

Hint Resolve eval_name_heap.

Lemma red_name_appL_multi_aux p p' t2 :
  clos_refl_trans _ (fun p p' => red_name p.1 p.2 p'.1 p'.2) p p' ->
  forall H H' t1 t1',
  p = (H, t1) ->
  p' = (H', t1') ->
  clos_refl_trans _ (fun p p' => red_name p.1 p.2 p'.1 p'.2) (H, App t1 t2) (H', App t1' t2).
Proof.
  elim =>
    [ [ ? ? ] [ ? ? ] /= ? |
    | [ ? ? ] [ ? ? ] [ ? ? ] /= ? ? ? ? ];
  inversion 1; inversion 1; subst; eauto.
  apply: rt_step.
  by apply: red_name_appL => /=.
Qed.

Corollary red_name_appL_multi H H' t1 t1' t2 :
  clos_refl_trans _ (fun p p' => red_name p.1 p.2 p'.1 p'.2) (H, t1) (H', t1') ->
  clos_refl_trans _ (fun p p' => red_name p.1 p.2 p'.1 p'.2) (H, App t1 t2) (H', App t1' t2).
Proof. move => /red_name_appL_multi_aux. by apply. Qed.

Lemma value_normal t :
  value t ->
  forall H H' t',
  red_name H t H' t' ->
  False.
Proof. inversion 1; inversion 1. Qed.

Lemma red_name_det H t H' t' :
  red_name H t H' t' ->
  forall H'' t'',
  red_name H t H'' t'' ->
  H' = H'' /\ t' = t''.
Proof.
  induction 1; inversion 1; subst;
  try match goal with
  | H : red_name _ (Abs _) _ _ |- _ => inversion H
  end; eauto.
  - by move: H0 H5 => ->; inversion 1.
  - by case (IHred_name _ _ H8) => ? ?; subst.
Qed.

Lemma red_name_heap H t H' t' :
  red_name H t H' t' ->
  forall l t,
  nth None H l = Some t ->
  nth None H' l = Some t.
Proof.
  induction 1 => l0 ?; eauto;
  [ rewrite nth_rcons
  | rewrite nth_cat ];
  by case (leqP (size H) l0) => [ /(nth_default _) -> | ].
Qed.

Theorem eval_name_red_name_multi H t H' v :
  eval_name H t H' v ->
  clos_refl_trans _ (fun p p' => red_name p.1 p.2 p'.1 p'.2) (H, t) (H', v).
Proof.
  induction 1 => //.
  - refine (rt_trans _ _ _ (_, _) _ (rt_step _ _ _ _ _) _) => /=; eauto.
  - refine (rt_trans _ _ _ (_, _) _
      (red_name_appL_multi _ _ _ _ _ IHeval_name1)
      (rt_trans _ _ _ (_, _) _ (rt_step _ _ _ _ _) _)) => /=; eauto.
  - refine (rt_trans _ _ _ (_, _) _ (rt_step _ _ _ _ _) _) => /=; eauto.
Qed.

Lemma red_name_eval_name H t H' t' :
  red_name H t H' t' ->
  forall H'' v,
  eval_name H' t' H'' v ->
  eval_name H t H'' v.
Proof.
  induction 1; eauto.
  inversion 1. subst. eauto.
Qed.

Theorem red_name_multi_eval_name_aux p p' :
  clos_refl_trans _ (fun p p' => red_name p.1 p.2 p'.1 p'.2) p p' ->
  forall H H' t v,
  p = (H, t) ->
  p' = (H', v) ->
  value v ->
  eval_name H t H' v.
Proof.
  move => /clos_rt_rt1n_iff.
  induction 1; inversion 1; inversion 1; subst.
  - exact: value_eval_name.
  - destruct y => [ ? ].
    apply: red_name_eval_name; eauto.
Qed.

Corollary red_name_multi_eval_name H t H' v :
  clos_refl_trans _ (fun p p' => red_name p.1 p.2 p'.1 p'.2) (H, t) (H', v) ->
  value v ->
  eval_name H t H' v.
Proof. move => /red_name_multi_eval_name_aux. by apply. Qed.

Lemma diverge_reducible H t :
  diverge_name H t ->
  exists H' t', red_name H t H' t' /\ diverge_name H' t'.
Proof.
  induction t; inversion 1; subst; eauto.
  - case (IHt1 H4) => ? [ ? [ ] ]; eauto 6.
  - move: (eval_name_red_name_multi _ _ _ _ H5) => /clos_rt_rt1n_iff.
    inversion 1; subst; eauto.
    destruct y.
    move: H2 => /clos_rt_rt1n_iff /red_name_multi_eval_name. eauto 7.
Qed.
  
Lemma diverge_name_red_name_aux p p' :
  clos_refl_trans _ (fun p p' => red_name p.1 p.2 p'.1 p'.2) p p' ->
  forall H H' t t',
  p = (H, t) ->
  p' = (H', t') ->
  diverge_name H t ->
  exists H'' t'', red_name H' t' H'' t''.
Proof.
  move => /clos_rt_rt1n_iff Hrt.
  induction Hrt; inversion 1; inversion 1; subst =>
    [ /diverge_reducible [ ? [ ? [ ] ] ] ]; eauto.
  destruct y => [ /(red_name_det _ _ _ _ H) /= [ ? ? ] ].
  subst. eauto.
Qed.

Theorem diverge_name_red_name H t :
  diverge_name H t ->
  forall H' t',
  clos_refl_trans _ (fun p p' => red_name p.1 p.2 p'.1 p'.2) (H, t) (H', t') ->
  exists H'' t'', red_name H' t' H'' t''.
Proof. move => ? ? ? /diverge_name_red_name_aux. by apply. Qed.

Theorem red_name_multi_diverge_name :
  forall H t,
  ( forall H' t',
    clos_refl_trans _ (fun p p' => red_name p.1 p.2 p'.1 p'.2) (H, t) (H', t') ->
    exists H'' t'', red_name H' t' H'' t'' ) ->
  diverge_name H t.
Proof.
  cofix red_name_multi_diverge_name.
  move => H [ ? | ? | ? | t1 ? | ? ? ] Hdiv.
  - move: (Hdiv _ _ (rt_refl _ _ _)) => [ ? [ ] ]; inversion 1.
  - move: (Hdiv _ _ (rt_refl _ _ _)) => [ ? [ ] ]; inversion 1. subst.
    apply: diverge_name_loc; eauto.
    apply: red_name_multi_diverge_name => ? ? ?.
    apply: Hdiv.
    refine (rt_trans _ _ _ (_, _) _ (rt_step _ _ _ _ _) _) => /=; eauto.
  - move: (Hdiv _ _ (rt_refl _ _ _)) => [ ? [ ] ]; inversion 1.
  - case (classic (exists H' t1',
      clos_refl_trans _ (fun p p' => red_name p.1 p.2 p'.1 p'.2) (H, t1) (H', t1') /\
      forall H'' t1'', red_name H' t1' H'' t1'' -> False)) =>
      [ [ ? [ ? [ Hrt Hnf ] ] ] | Hdiv1 ].
    { case: (Hdiv _ _ (red_name_appL_multi _ _ _ _ _ Hrt)) => ? [ ];
      inversion 1; subst.
      - by move: (Hnf _ _ H6).
      - apply: diverge_name_appabs.
        + apply: red_name_multi_eval_name; eauto.
        + apply: red_name_multi_diverge_name => ? ? ?.
          apply: Hdiv.
          refine (rt_trans _ _ _ (_, _) _
            (red_name_appL_multi _ _ _ _ _ _)
            (rt_trans _ _ _ (_, _) _ (rt_step _ _ _ _ _) _)) => /=; eauto. }
    { apply: diverge_name_appL.
      apply: red_name_multi_diverge_name => ? t1' Hrt.
      move: (Hdiv _ _ (red_name_appL_multi _ _ _ _ _ Hrt)) => [ ? [ ] ];
      inversion 1; subst; eauto.
      case Hdiv1. repeat (eexists; eauto). inversion 1. }
  - apply: diverge_name_let.
    apply: red_name_multi_diverge_name => ? ? ?.
    apply: Hdiv.
    refine (rt_trans _ _ _ (_, _) _ (rt_step _ _ _ _ _) _) => /=; eauto.
Qed.

Lemma wf_term_impl (p p' : nat -> Prop) t :
  wf_term p t ->
  (forall l, p l -> p' l) ->
  wf_term p' t.
Proof. induction 1; constructor; eauto. Qed.

Lemma corr_term_value R v v' :
  corr_term R v v' ->
  value v <-> value v'.
Proof. by inversion 1; split; inversion 1; eauto. Qed.

Lemma corr_term_valueL R v v' :
  corr_term R v v' ->
  value v ->
  value v'.
Proof. by move => Hcorr /(corr_term_value _ _ _ Hcorr). Qed.

Lemma corr_term_valueR R v v' :
  corr_term R v v' ->
  value v' ->
  value v.
Proof. by move => Hcorr /(corr_term_value _ _ _ Hcorr). Qed.

Hint Resolve corr_term_valueL corr_term_valueR.

Lemma corr_term_refl (p : nat -> Prop) t :
  wf_term p t ->
  corr_term (fun l l' => l = l' /\ p l) t t.
Proof. induction 1; constructor; eauto. Qed.

Lemma corr_term_sym R t t' :
  corr_term R t t' ->
  corr_term (fun l l' => R l' l) t' t.
Proof. by induction 1; eauto 6. Qed.

Lemma corr_term_comp R R' t t' :
  corr_term R t t' ->
  forall t'', corr_term R' t' t'' ->
  corr_term (fun l l'' => exists l', R l l' /\ R' l' l'') t t''.
Proof. induction 1; inversion 1; constructor; (eauto 6 || congruence). Qed.

Lemma corr_term_impl (R R' : nat -> nat -> Prop) t t' :
  corr_term R t t' ->
  (forall l l', R l l' -> R' l l') ->
  corr_term R' t t'.
Proof. induction 1; eauto. Qed.

Lemma corr_term_wf_termL f t t' :
  corr_term f t t' ->
  wf_term (fun l => exists l', f l l') t.
Proof. induction 1; constructor; eauto. Qed.

Corollary corr_term_wf_termR f t t' :
  corr_term f t t' ->
  wf_term (fun l' => exists l, f l l') t'.
Proof. by move => /corr_term_sym /corr_term_wf_termL. Qed.

Lemma corr_term_rename R t t' :
  corr_term R t t' ->
  forall r,
  corr_term R (rename r t) (rename r t').
Proof.
  induction 1 => /=; constructor; eauto.
  - by rewrite !size_map.
  - rewrite size_map => ? ? d.
    rewrite !(nth_map d) -?H; eauto.
  - by rewrite H.
Qed.

Lemma corr_term_subst R t t' :
  corr_term R t t' ->
  forall s s',
  (forall x, corr_term R (s x) (s' x)) ->
  corr_term R (subst s t) (subst s' t').
Proof.
  induction 1 => ? ? Hs /=; (constructor || apply: Hs); eauto.
  - apply IHcorr_term => [ [ | ? ] ].
    + exact: corr_term_var.
    + exact: corr_term_rename.
  - by rewrite !size_map.
  - rewrite size_map => x ? d.
    rewrite !(nth_map d) -?H => //.
    apply: H1 => // y.
    rewrite !upn_unfold.
    case: (leqP (size ts) y) => ? //.
    exact: corr_term_rename.
  - apply: IHcorr_term => x.
    rewrite !upn_unfold -?H.
    case: (leqP (size ts) x) => ? //.
    exact: corr_term_rename.
Qed.

Lemma wf_heap_segment_weaken (p p' q q' : nat -> Prop) H H' :
  wf_heap_segment p q H ->
  ( forall l, p' l -> p l ) ->
  ( forall l, q l -> q' l ) ->
  ( forall l, p' l ->
    forall t, 
    nth None H l = Some t -> 
    nth None H' l = Some t ) ->
  wf_heap_segment p' q' H'.
Proof.
  move => Hwf Hdom ? Hext ? Hp.
  move: (Hp) => /Hdom /Hwf [ ? [ /(Hext _ Hp) -> ] ].
  eauto using wf_term_impl.
Qed.

Definition wf_heap_segment_dom p p' q H Hwf Hdom :=
  wf_heap_segment_weaken p p' q _ H _ Hwf Hdom (fun _ H => H) (fun _ _ _ H => H).
Definition wf_heap_segment_cod p q q' H Hwf Hcod :=
  wf_heap_segment_weaken p _ q q' H _ Hwf (fun _ H => H) Hcod (fun _ _ _ H => H).
Definition wf_heap_segment_ext p q H H' Hwf :=
  wf_heap_segment_weaken p _ q _ H H' Hwf (fun _ H => H) (fun _ H => H).

Lemma wf_heap_segment_union p p' q H :
  wf_heap_segment p q H ->
  wf_heap_segment p' q H ->
  wf_heap_segment (fun l => p l \/ p' l) q H.
Proof. move => Hwf Hwf' ? [ /Hwf | /Hwf' ] [ ? [ -> ] ]; eauto. Qed.

Lemma wf_heap_segment_bound p q H :
  wf_heap_segment p q H ->
  forall l, p l ->
  l < size H.
Proof.
  move => Hwf l /Hwf [ ? [ ] ].
  by case: (leqP (size H) l) => [ /(nth_default _) -> | ].
Qed.

Corollary wf_heap_segment_cat p q H Hd :
  wf_heap_segment p q H ->
  wf_heap_segment p q (H ++ Hd).
Proof.
  move => /wf_heap_segment_ext.
  apply => l ? ?.
  by move: nth_cat (leqP (size H) l) => -> [ /(nth_default _) -> | ].
Qed.

Corollary wf_heap_segment_rcons p q H o :
  wf_heap_segment p q H ->
  wf_heap_segment p q (rcons H o).
Proof. rewrite -cats1. exact: wf_heap_segment_cat. Qed.

Lemma iso_heap_segment_weaken (fdom fdom' fcod fcod' : nat -> nat -> Prop) H1 H1' H2 H2' :
  iso_heap_segment fdom fcod H1 H2 ->
  ( forall l l', fdom' l l' -> fdom l l' ) ->
  ( forall l l', fcod l l' -> fcod' l l' ) ->
  ( forall l l', fdom' l l' ->
    forall t,
    nth None H1 l = Some t ->
    nth None H1' l = Some t ) ->
  ( forall l l', fdom' l l' ->
    forall t,
    nth None H2 l' = Some t ->
    nth None H2' l' = Some t ) ->
  iso_heap_segment fdom' fcod' H1' H2'.
Proof.
  move => Hiso Hdom Hcod HL HR ? ? Hf.
  move: (Hf) => /Hdom /Hiso [ ? [ /(HL _ _ Hf) -> [ ? [ /(HR _ _ Hf) -> ] ] ] ].
  eauto 6 using corr_term_impl.
Qed.

Definition iso_heap_segment_dom (fdom fdom' fcod : nat -> nat -> Prop) H1 H2 Hiso Hdom :=
  iso_heap_segment_weaken fdom fdom' fcod _ H1 _ H2 _ Hiso Hdom (fun _ _ H => H) (fun _ _ _ _ H => H) (fun _ _ _ _ H => H).
Definition iso_heap_segment_cod (fdom fcod fcod' : nat -> nat -> Prop) H1 H2 Hiso Hcod :=
  iso_heap_segment_weaken fdom _ fcod fcod' H1 _ H2 _ Hiso (fun _ _ H => H) Hcod (fun _ _ _ _ H => H) (fun _ _ _ _ H => H).
Definition iso_heap_segment_extL (fdom fcod : nat -> nat -> Prop) H1 H1' H2 Hiso HextL :=
  iso_heap_segment_weaken fdom _ fcod _ H1 H1' H2 _ Hiso (fun _ _ H => H) (fun _ _ H => H) HextL (fun _ _ _ _ H => H).
Definition iso_heap_segment_extR (fdom fcod : nat -> nat -> Prop) H1 H2 H2' Hiso :=
  iso_heap_segment_weaken fdom _ fcod _ H1 _ H2 H2' Hiso (fun _ _ H => H) (fun _ _ H => H) (fun _ _ _ _ H => H).

Lemma iso_heap_segment_union fdom fdom' fcod H1 H2 :
  iso_heap_segment fdom fcod H1 H2 ->
  iso_heap_segment fdom' fcod H1 H2 ->
  iso_heap_segment (fun l l' => fdom l l' \/ fdom' l l') fcod H1 H2.
Proof. by move => Hiso Hiso' ? ? [ /Hiso | /Hiso' ]. Qed.

Lemma iso_heap_segment_refl p p' H :
  wf_heap_segment p p' H ->
  iso_heap_segment
    (fun l l' => l = l' /\ p l)
    (fun l l' => l = l' /\ p' l) H H.
Proof.
  move => Hwf ? ? [ -> /Hwf [ ? [ -> ] ] ].
  eauto 6 using corr_term_refl.
Qed.

Lemma iso_heap_segment_sym f f' H H' :
  iso_heap_segment f f' H H' ->
  iso_heap_segment (fun l l' => f l' l) (fun l l' => f' l' l) H' H.
Proof.
  move => Hiso ? ? /Hiso [ ? [ -> [ ? [ -> ] ] ] ].
  eauto 6 using corr_term_sym.
Qed.

Lemma iso_heap_segment_comp fdom fdom' fcod fcod' H H' H'' :
  iso_heap_segment fdom fcod H H' ->
  iso_heap_segment fdom' fcod' H' H'' ->
  iso_heap_segment
    (fun l l'' => exists l', fdom l l' /\ fdom' l' l'')
    (fun l l'' => exists l', fcod l l' /\ fcod' l' l'') H H''.
Proof.
  move => Hiso Hiso' ? ? [ ? [ ] ]
    /Hiso [ ? [ -> [ ? [ Hnth ? ] ] ] ]
    /Hiso' [ ? [ Hnth' [ ? [ -> ? ] ] ] ].
  move: Hnth Hnth' => ->. inversion 1. subst.
  eauto 6 using corr_term_comp.
Qed.

Lemma iso_heap_segment_boundL f f' H H' :
  iso_heap_segment f f' H H' ->
  forall l l', f l l' ->
  l < size H.
Proof.
  move => Hiso l ? /Hiso [ ? [ ] ].
  by case: (leqP (size H) l) => [ /(nth_default _) -> | ].
Qed.

Lemma iso_heap_segment_boundR f f' H H' :
  iso_heap_segment f f' H H' ->
  forall l l', f l l' ->
  l' < size H'.
Proof.
  move => Hiso ? l' /Hiso [ ? [ ? [ ? [ ] ] ] ].
  by case: (leqP (size H') l') => [ /(nth_default _) -> | ].
Qed.

Lemma iso_heap_segment_wf_heap_segmentL f f' H H' :
  iso_heap_segment f f' H H' ->
  wf_heap_segment (fun l => exists l', f l l') (fun l => exists l', f' l l') H.
Proof.
  move => Hiso ? [ ? ] /Hiso [ ? [ -> [ ? [ ] ] ] ].
  eauto using corr_term_wf_termL.
Qed.

Corollary iso_heap_segment_wf_heap_segmentR f f' H H' :
  iso_heap_segment f f' H H' ->
  wf_heap_segment (fun l' => exists l, f l l') (fun l' => exists l, f' l l') H'.
Proof. by move => /iso_heap_segment_sym /iso_heap_segment_wf_heap_segmentL. Qed.

Corollary iso_heap_segment_catL fdom fcod H1 H2 Hd :
  iso_heap_segment fdom fcod H1 H2 ->
  iso_heap_segment fdom fcod (H1 ++ Hd) H2.
Proof.
  move => /iso_heap_segment_extL.
  apply => l ? ? ?.
  by move: nth_cat (leqP (size H1) l) => -> [ /(nth_default _) -> | ].
Qed.

Corollary iso_heap_segment_rconsL fdom fcod H1 H2 o :
  iso_heap_segment fdom fcod H1 H2 ->
  iso_heap_segment fdom fcod (rcons H1 o) H2.
Proof. by rewrite -cats1 => /iso_heap_segment_catL. Qed.

Corollary iso_heap_segment_catR fdom fcod H1 H2 Hd :
  iso_heap_segment fdom fcod H1 H2 ->
  iso_heap_segment fdom fcod H1 (H2 ++ Hd).
Proof. by move => /iso_heap_segment_sym /iso_heap_segment_catL /iso_heap_segment_sym. Qed.

Corollary iso_heap_segment_rconsR fdom fcod H1 H2 o :
  iso_heap_segment fdom fcod H1 H2 ->
  iso_heap_segment fdom fcod H1 (rcons H2 o).
Proof. by rewrite -cats1 => /iso_heap_segment_catR. Qed.

Theorem eval_name_iso_heap H1 H1' t1 v1 :
  eval_name H1 t1 H1' v1 ->
  forall R H2 t2,
  corr_term R t2 t1 ->
  iso_heap R H2 H1 ->
  exists R' H2' v2,
  corr_term R' v2 v1 /\
  iso_heap R' H2' H1' /\
  eval_name H2 t2 H2' v2 /\
  (forall l1 l2, R l1 l2 -> R' l1 l2).
Proof.
  induction 1; inversion 1; subst => Hheap.
  - move: (Hheap _ _ H6) => [ ? ].
    move: H0 => -> [ ? [ ? [ ] ] ]. inversion 1. subst => Hcorr.
    move: (IHeval_name _ _ _ Hcorr Hheap) =>
      [ ? [ ? [ ? [ ? [ ? [ ] ] ] ] ] ].
    repeat (eexists; eauto).
  - move: (IHeval_name1 _ _ _ H7 Hheap) => [ R' [ H2' [ ? [ ] ] ] ].
    inversion 1. subst => [ [ ? [ ? ? ] ] ].
    have Hcorr' : corr_term
      (fun l l' => R' l l' \/ l = size H2' /\ l' = size H')
      (subst (scons (Loc (size H2')) Var) t)
      (subst (scons (Loc (size H')) Var) t0).
    { apply: corr_term_subst => [ | [ | ? ] ] /=;
      eauto using corr_term_impl. }
    have Hheap' : iso_heap
      (fun l l' => R' l l' \/ l = size H2' /\ l' = size H')
      (rcons H2' (Some t5)) (rcons H' (Some t2)).
    { apply: iso_heap_segment_union => [ | ? ? [ -> -> ] ].
      - apply: iso_heap_segment_rconsL.
        apply: iso_heap_segment_rconsR.
        apply: iso_heap_segment_cod; eauto.
      - rewrite !nth_rcons !ltnn !eqxx.
        repeat eexists. eauto using corr_term_impl. }
      move: (IHeval_name2 _ _ _ Hcorr' Hheap') =>
        [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ].
    repeat (eexists; eauto).
  - repeat (eexists; eauto).
  - have Hcorr' : corr_term
      (fun l l' => R l l' \/
        exists n, n < size ts0 /\ l = size H2 + n /\ l' = size H + n)
      (subst (scat (mkseq (Loc \o addn (size H2)) (size ts0)) Var) t0)
      (subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var) t).
    { apply: corr_term_subst => [ | x ];
      eauto using corr_term_impl.
      rewrite !nth_scat H5.
      case (leqP (size ts) x) => ?.
      - by rewrite !nth_default ?size_mkseq.
      - rewrite !nth_mkseq => /=; eauto 6. }
    have Hheap' : iso_heap
      (fun l l' => R l l' \/
        exists n, n < size ts0 /\ l = size H2 + n /\ l' = size H + n)
      (H2 ++ map (@Some _ \o
         subst (scat (mkseq (Loc \o addn (size H2)) (size ts0)) Var)) ts0)
      (H ++ map (@Some _ \o
         subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var)) ts).
    { apply: iso_heap_segment_union =>
        [ | ? ? [ x [ ? [ -> -> ] ] ] ].
      - apply: iso_heap_segment_catL.
        apply: iso_heap_segment_catR.
        apply: iso_heap_segment_cod; eauto.
      - rewrite !nth_cat !ltnNge !leq_addr !addKn !(nth_map (Var 0)); try congruence.
        repeat eexists.
        apply: corr_term_subst => [ | y ];
        eauto using corr_term_impl.
        rewrite !nth_scat H5.
        case (leqP (size ts) y) => ?.
        + by rewrite !nth_default ?size_mkseq.
        + rewrite !nth_mkseq => /=; eauto 6. }
    move: (IHeval_name _ _ _ Hcorr' Hheap') =>
      [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ].
    repeat (eexists; eauto).
Qed.
