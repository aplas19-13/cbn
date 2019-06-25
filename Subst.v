Require Import Relations Classical.
From mathcomp Require Import all_ssreflect.
Require Import Util LambdaLet.
Require Heaps.

Inductive red_name : term -> term -> Prop :=
  | red_name_appL t1 t1' t2 :
      red_name t1 t1' ->
      red_name (App t1 t2) (App t1' t2)
  | red_name_beta t11 t2 :
      red_name (App (Abs t11) t2) (subst (scons t2 Var) t11)
  | red_name_let ts t :
      red_name (Let ts t) (subst (scat (map (Let ts) ts) Var) t).

Inductive eval_name : term -> term -> Prop :=
  | eval_name_app t0 t1 t2 v :
      eval_name t1 (Abs t0) ->
      eval_name (subst (scons t2 Var) t0) v ->
      eval_name (App t1 t2) v
  | eval_name_abs t0 :
      eval_name (Abs t0) (Abs t0)
  | eval_name_let ts t v :
      eval_name (subst (scat (map (Let ts) ts) Var) t) v ->
      eval_name (Let ts t) v.

CoInductive diverge_name : term -> Prop :=
  | diverge_name_appL t1 t2 :
      diverge_name t1 ->
      diverge_name (App t1 t2)
  | diverge_name_appabs t0 t1 t2 :
      eval_name t1 (Abs t0) ->
      diverge_name (subst (scons t2 Var) t0) ->
      diverge_name (App t1 t2)
  | diverge_name_let ts t :
      diverge_name (subst (scat (map (Let ts) ts) Var) t) ->
      diverge_name (Let ts t).

Hint Constructors eval_name diverge_name red_name.

Inductive corr_term (P : nat -> Prop) :
      seq (option term) -> (nat -> term) -> term -> term -> Prop :=
  | corr_term_indir H mu l t t' :
      nth None H l = Some t ->
      corr_term P H mu t t' ->
      corr_term P H mu (Loc l) t'
  | corr_term_loc H mu l t' :
      P l ->
      mu l = t' ->
      corr_term P H mu (Loc l) t'
  | corr_term_var H mu x :
      corr_term P H mu (Var x) (Var x)
  | corr_term_abs H mu t t' :
      corr_term P (map (omap (rename succn)) H) (rename succn \o mu) t t' ->
      corr_term P H mu (Abs t) (Abs t')
  | corr_term_app H mu t1 t1' t2 t2' :
      corr_term P H mu t1 t1' ->
      corr_term P H mu t2 t2' ->
      corr_term P H mu (App t1 t2) (App t1' t2')
  | corr_term_let H mu ts ts' t t' :
      size ts = size ts' ->
      ( forall x, x < size ts -> forall d,
        corr_term P
          (map (omap (rename (addn (size ts)))) H)
          (rename (addn (size ts)) \o mu)
          (nth d ts x) (nth d ts' x) ) ->
      corr_term P
        (map (omap (rename (addn (size ts)))) H)
        (rename (addn (size ts)) \o mu) t t' ->
      corr_term P H mu (Let ts t) (Let ts' t').

Hint Constructors corr_term.

Definition corr_heap_segment (P P' : nat -> Prop) H mu :=
  forall l, P l ->
  exists t, nth None H l = Some t /\
  exists ts' t', mu l = Let ts' t' /\
  corr_term P' H mu t (subst (scat (map (Let ts') ts') Var) t').
Definition corr_heap P := corr_heap_segment P P.

Lemma eq_omap A B (f g : A -> B) : forall o,
  (forall x, f x = g x) ->
  omap f o = omap g o.
Proof. by move => [ ? /= -> | ]. Qed.

Lemma omap_id A : forall (o : option A), omap id o = o.
Proof. by move => [ ]. Qed.

Lemma omap_comp A B C (f : B -> C) (g : A -> B) : forall o,
  omap f (omap g o) = omap (f \o g) o.
Proof. by move => [ ]. Qed.

Lemma nth_map_heap A B H l (f : A -> B) :
  nth None (map (omap f) H) l = omap f (nth None H l).
Proof.
  case (leqP (size H) l) => ?.
  - by rewrite !nth_default ?size_map.
  - exact: nth_map.
Qed.

Lemma neutral_dec t :
  { t0 | t = Abs t0 } + { forall t0, t = Abs t0 -> False }.
Proof. by destruct t; eauto; right. Qed.

Lemma value_normal t :
  value t -> forall t', red_name t t' -> False.
Proof. by inversion 1; inversion 1. Qed.

Lemma eval_name_value t v :
  eval_name t v ->
  value v.
Proof. induction 1; eauto. Qed.
  
Lemma red_name_det t t' :
  red_name t t' ->
  forall t'',
  red_name t t'' ->
  t' = t''.
Proof.
  induction 1; inversion 1; subst;
    try match goal with
    | H : red_name (Abs _) _ |- _ => inversion H
    end; f_equal; eauto.
Qed.

Lemma red_name_appL_multi t1 t1' t2 :
  clos_refl_trans _ red_name t1 t1' ->
  clos_refl_trans _ red_name (App t1 t2) (App t1' t2).
Proof. induction 1; eauto. Qed.

Theorem eval_name_red_name_multi t v :
  eval_name t v ->
  clos_refl_trans _ red_name t v.
Proof.
  induction 1 => //.
  - apply: rt_trans.
    + apply: red_name_appL_multi.
      exact: IHeval_name1.
    + eauto.
  - apply: rt_trans.
    + exact: rt_step.
    + eauto.
Qed.

Lemma red_name_eval_name t t' :
  red_name t t' ->
  forall v,
  eval_name t' v ->
  eval_name t v.
Proof.
  induction 1; eauto.
  inversion 1. subst. eauto.
Qed.

Lemma red_name_multi_eval_name t v :
  clos_refl_trans _ red_name t v ->
  value v ->
  eval_name t v.
Proof.
  move => /clos_rt_rt1n_iff.
  induction 1; inversion 1; subst; eauto.
  apply: red_name_eval_name; eauto.
Qed.

Lemma diverge_reducible t :
  diverge_name t ->
  exists t', red_name t t' /\ diverge_name t'.
Proof.
  induction t; inversion 1; subst; eauto.
  - case (IHt1 H1) => ? [ ]. eauto.
  - move: (eval_name_red_name_multi _ _ H2) => /clos_rt_rt1n_iff.
    inversion 1; subst; eauto.
    move: H1 => /clos_rt_rt1n_iff /red_name_multi_eval_name. eauto 6.
Qed.

Theorem diverge_name_red_name t t' :
  clos_refl_trans _ red_name t t' ->
  diverge_name t ->
  exists t'', red_name t' t''.
Proof.
  move => /clos_rt_rt1n_iff.
  induction 1.
  - move => /diverge_reducible [ ? [ ] ]. eauto.
  - by move => /diverge_reducible [ ? [ ] ] /(red_name_det _ _ H) <-.
Qed.

Theorem red_name_multi_diverge_name :
  forall t,
  ( forall t', clos_refl_trans _ red_name t t' ->
    exists t'', red_name t' t'' ) ->
  diverge_name t.
Proof.
  cofix red_name_multi_diverge_name.
  move => [ ? | ? | ? | t1 ? | ? ? ] Hdiv.
  - move: (Hdiv _ (rt_refl _ _ _)) => [ ]. inversion 1.
  - move: (Hdiv _ (rt_refl _ _ _)) => [ ]. inversion 1.
  - move: (Hdiv _ (rt_refl _ _ _)) => [ ]. inversion 1.
  - case (classic (exists t1',
      clos_refl_trans _ red_name t1 t1' /\
      forall t1'', red_name t1' t1'' -> False)) =>
    [ [ ? [ Hrt Hnf ] ] | Hdiv1 ].
    { move: (Hdiv _ (red_name_appL_multi _ _ _ Hrt)) => [ ]; inversion 1; subst.
      - by move: (Hnf _ H2).
      - apply: diverge_name_appabs.
        + apply: red_name_multi_eval_name; eauto.
        + apply: red_name_multi_diverge_name => ? ?.
          apply: Hdiv.
          apply: rt_trans.
          * apply: red_name_appL_multi. eauto.
          * eauto. }
    { apply: diverge_name_appL.
      apply: red_name_multi_diverge_name => t1' Hrt.
      case: (Hdiv _ (red_name_appL_multi _ _ _ Hrt)); inversion 1; subst; eauto.
      case Hdiv1. repeat (eexists; eauto). inversion 1. }
  - apply: diverge_name_let.
    apply: red_name_multi_diverge_name => ? ?.
    apply: Hdiv. eauto.
Qed.
  
Lemma corr_term_impl P H mu t t' :
  corr_term P H mu t t' ->
  forall (P' : nat -> Prop) H' mu',
  ( forall l, P l -> P' l ) ->
  ( forall l,
    nth None H l = None \/
    nth None H l = nth None H' l ) ->
  ( forall l, P l -> mu l = mu' l ) ->
  corr_term P' H' mu' t t'.
Proof.
  induction 1 => ? H' ? HP HQ HPmu; eauto.
  - apply: corr_term_indir; eauto.
    by move: H0 (HQ l) => -> [ ].
  - apply: corr_term_loc; eauto.
    erewrite <- HPmu; eauto.
  - constructor.
    ( apply: IHcorr_term; eauto ) => l.
    + rewrite !nth_map_heap.
      case (HQ l) => ->; eauto.
    + by move => /HPmu /= ->.
  - constructor; eauto.
    + move => ? ? ?.
      ( apply: H2; eauto ) => l.
      * rewrite !nth_map_heap.
        case (HQ l) => ->; eauto.
      * by move => /HPmu /= ->.
    + ( apply: IHcorr_term; eauto ) => l.
      * rewrite !nth_map_heap.
        case (HQ l) => ->; eauto.
      * by move => /HPmu /= ->.
Qed.

Corollary corr_term_ext P H mu t t' :
  corr_term P H mu t t' ->
  forall H',
  ( forall l t,
    nth None H l = Some t ->
    nth None H' l = Some t ) ->
  corr_term P H' mu t t'.
Proof.
  move => /corr_term_impl Hterm ? Hext.
  apply: Hterm => // l.
  move: (nth None H l) (Hext l) => [ ? /(_ _ erefl) | ]; eauto.
Qed.

Corollary corr_term_cat P H Hd mu t t' :
  corr_term P H mu t t' ->
  corr_term P (H ++ Hd) mu t t'.
Proof.
  move => /corr_term_ext.
  apply => l.
  by move: nth_cat (leqP (size H) l) => -> [ /(nth_default _) -> | ].
Qed.

Corollary corr_term_rcons P H o mu t t' :
  corr_term P H mu t t' ->
  corr_term P (rcons H o) mu t t'.
Proof. by rewrite -cats1 => /corr_term_cat. Qed.

Lemma corr_term_rename P H mu t t' :
  corr_term P H mu t t' ->
  forall H' mu' r,
  (forall l, mu' l = rename r (mu l)) ->
  (forall l, nth None H' l = omap (rename r) (nth None H l)) ->
  corr_term P H' mu' (rename r t) (rename r t').
Proof.
  induction 1 => H' ? ? Hmu Hnth /=; eauto.
  - apply: corr_term_indir; eauto.
    by rewrite Hnth H0.
  - apply: corr_term_loc; eauto.
    by rewrite Hmu H1.
  - constructor.
    apply: IHcorr_term => ?.
    + rewrite /funcomp Hmu !rename_rename_comp.
      exact: eq_rename.
    + rewrite !nth_map_heap Hnth !omap_comp.
      apply: eq_omap => ?.
      rewrite /funcomp !rename_rename_comp.
      exact: eq_rename.
  - constructor; rewrite !size_map -?H0; eauto.
    + move => ? ? d.
      rewrite !(nth_map d) -?H0 => //.
      apply: H2 => // ?.
      * rewrite /funcomp Hmu !rename_rename_comp.
        apply: eq_rename => ? /=.
        by rewrite upnren_unfold ltnNge leq_addr addKn.
      * rewrite !nth_map_heap Hnth !omap_comp.
        apply: eq_omap => ?.
        rewrite /funcomp !rename_rename_comp.
        apply: eq_rename => x /=.
        by rewrite upnren_unfold ltnNge leq_addr addKn.
    + apply: IHcorr_term => ?.
      * rewrite /funcomp Hmu !rename_rename_comp.
        apply: eq_rename => ? /=.
        by rewrite upnren_unfold ltnNge leq_addr addKn.
      * rewrite !nth_map_heap Hnth !omap_comp.
        apply: eq_omap => ?.
        rewrite /funcomp !rename_rename_comp.
        apply: eq_rename => ? /=.
        by rewrite upnren_unfold ltnNge leq_addr addKn.
Qed.

Lemma corr_term_subst P H mu t t' :
  corr_term P H mu t t' ->
  forall H' mu' s s',
  (forall x, corr_term P H' mu' (s x) (s' x)) ->
  (forall l, nth None H' l = omap (subst s) (nth None H l)) ->
  (forall l, mu' l = subst s' (mu l)) ->
  corr_term P H' mu' (subst s t) (subst s' t').
Proof.
  induction 1 => ? ? ? ? Hs Hnth Hmu /=; eauto.
  - apply: corr_term_indir; eauto.
    by rewrite Hnth H0.
  - apply: corr_term_loc; eauto.
    by rewrite Hmu H1.
  - constructor.
    apply: IHcorr_term => [ [ | ? ] //= | ? | ? ].
    + ( apply: corr_term_rename; eauto ) => ?.
      by rewrite nth_map_heap.
    + rewrite !nth_map_heap Hnth !omap_comp.
      apply: eq_omap => ?.
      rewrite /funcomp rename_subst_comp subst_rename_comp.
      exact: eq_subst.
    + rewrite /funcomp Hmu rename_subst_comp subst_rename_comp.
      exact: eq_subst.
  - constructor; rewrite !size_map -?H0; eauto.
    + move => ? ? d.
      rewrite !(nth_map d) -?H0 => //.
      apply: H2 => // x.
      * rewrite !upn_unfold.
        case (leqP (size ts) x) => ? //.
        ( apply: corr_term_rename; eauto ) => ?.
        by rewrite nth_map_heap.
      * rewrite !nth_map_heap Hnth !omap_comp.
        apply: eq_omap => ?.
        rewrite /funcomp rename_subst_comp subst_rename_comp.
        apply: eq_subst => ?.
        by rewrite /funcomp upn_unfold ltnNge leq_addr addKn.
      * rewrite /funcomp Hmu rename_subst_comp subst_rename_comp.
        apply: eq_subst => ?.
        by rewrite /funcomp upn_unfold ltnNge leq_addr addKn.
    + apply IHcorr_term => x.
      * rewrite !upn_unfold.
        case (leqP (size ts) x) => ? //.
        ( apply: corr_term_rename; eauto ) => ?.
        by rewrite nth_map_heap.
      * rewrite !nth_map_heap Hnth !omap_comp.
        apply: eq_omap => ?.
        rewrite /funcomp rename_subst_comp subst_rename_comp.
        apply: eq_subst => ?.
        by rewrite /funcomp upn_unfold ltnNge leq_addr addKn.
      * rewrite /funcomp Hmu rename_subst_comp subst_rename_comp.
        apply: eq_subst => ?.
        by rewrite /funcomp upn_unfold ltnNge leq_addr addKn.
Qed.

Lemma corr_heap_segment_impl P P' H mu :
  corr_heap_segment P P' H mu ->
  forall (Q Q' : nat -> Prop) H',
  ( forall l, Q l -> P l ) ->
  ( forall l, P' l -> Q' l ) ->
  ( forall l t, nth None H l = Some t -> nth None H' l = Some t ) ->
  corr_heap_segment Q Q' H' mu.
Proof.
  move => Hheap ? ? ? Hdom Hcod Hnth ? /Hdom /Hheap
    [ ? [ /Hnth -> [ ? [ ? [ -> ? ] ] ] ] ].
  repeat (eexists; eauto).
  ( apply: corr_term_impl; eauto ) => l.
  move: (nth None H l) (Hnth l) => [ ? /(_ _ erefl) | ]; eauto.
Qed.

Lemma corr_heap_ext P H mu :
  corr_heap P H mu ->
  forall mu',
  ( forall l, P l -> mu l = mu' l ) ->
  corr_heap P H mu'.
Proof.
  move => Hheap ? HPmu ? HP.
  move: (HPmu _ HP) (Hheap _ HP) => ->
    [ ? [ -> [ ? [ ? [ -> ? ] ] ] ] ].
  repeat (eexists; eauto).
  apply: corr_term_impl; eauto.
Qed.

Corollary corr_heap_segment_cat P P' H Hd mu :
  corr_heap_segment P P' H mu ->
  corr_heap_segment P P' (H ++ Hd) mu.
Proof.
  move => /corr_heap_segment_impl.
  apply => l //.
  by move: nth_cat (leqP (size H) l) =>
    -> [ /(nth_default _) -> | ].
Qed.

Corollary corr_heap_segment_rcons P P' H o mu :
  corr_heap_segment P P' H mu ->
  corr_heap_segment P P' (rcons H o) mu.
Proof. by rewrite -cats1 => /corr_heap_segment_cat. Qed.

Lemma corr_heap_segment_union P P' Q H mu :
  corr_heap_segment P Q H mu ->
  corr_heap_segment P' Q H mu ->
  corr_heap_segment (fun l => P l \/ P' l) Q H mu.
Proof.
  move => Hheap Hheap' ? [ /Hheap | /Hheap' ]
    [ ? [ -> [ ? [ ? [ -> ? ] ] ] ] ];
  repeat (eexists; eauto).
Qed.
  
Lemma corr_heap_segment_bound P P' H mu :
  corr_heap_segment P P' H mu ->
  forall l, P l ->
  l < size H.
Proof.
  move => Hheap l /Hheap [ ? [ ] ].
  by case (leqP (size H) l) => [ /(nth_default _) -> | ].
Qed.

Lemma unwind_indirection P H mu t1 t2 :
  corr_term P H mu t1 t2 ->
  corr_heap P H mu ->
  exists t1',
  clos_refl_trans _ (fun p p' => Heaps.red_name p.1 p.2 p'.1 p'.2) (H, t1) (H, t1') /\
  ( corr_term P H mu t1' t2 /\
    (forall H' t1'', Heaps.red_name H t1' H' t1'' -> False) /\
    (forall t2', red_name t2 t2' -> False) \/
    exists t2', red_name t2 t2' /\
    exists H' t1'', Heaps.red_name H t1' H' t1'' /\
    exists P' mu',
    corr_heap P' H' mu' /\
    corr_term P' H' mu' t1'' t2' /\
    (forall l, P l -> P' l) /\
    (forall l, P l -> mu l = mu' l) ).
Proof.
  induction 1 => Hheap.
  - move: (IHcorr_term Hheap) => [ ? [ ? ? ] ].
    do 2 eexists.
    + refine (rt_trans _ _ _ (_, _) _ (rt_step _ _ _ _ _) _) => /=; eauto.
    + assumption.
  - subst.
    move: (Hheap _ H0) => [ ? [ ? [ ? [ ? [ Hmu ? ] ] ] ] ].
    rewrite Hmu.
    repeat (eexists; eauto). right.
    repeat (eexists; eauto).
  - repeat (eexists; eauto). left.
    split; eauto. split; inversion 1.
  - repeat (eexists; eauto). left.
    split; eauto. split; inversion 1.
  - move: (IHcorr_term1 Hheap) =>
      [ t11 [ ? [ [ ] | [ ? [ ? [ ? [ ? [ Hred [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ] ] ] ] ] ] ] ].
    + case (neutral_dec t11) => [ [ t0 ? ] | Hneutral ]; subst.
      { inversion 1. subst => ?.
        do 2 eexists.
        - apply: Heaps.red_name_appL_multi. eassumption.
        - have Hterm' : corr_term P
            (rcons H (Some t2)) mu
            (subst (scons (Loc (size H)) Var) t0)
            (subst (scons t2' Var) t').
          { apply: corr_term_subst.
            - ( eapply (corr_term_impl _ _ _ _ _ H4 _
                (map (omap (rename succn)) (rcons H (Some t2)))); eauto ) => l.
              rewrite !nth_map_heap nth_rcons.
              case (leqP (size H) l) => [ /(nth_default _) -> | ]; eauto.
            - move => [ | ? ] //=.
              apply: corr_term_indir => /=.
              + by rewrite nth_rcons ltnn eqxx.
              + exact: corr_term_rcons.
            - move => ?.
              rewrite nth_map_heap omap_comp (eq_omap _ _ _ id) ?omap_id => // ?.
              by rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id.
            - move => ?.
              by rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id. }
          have Hheap' : corr_heap P (rcons H (Some t2)) mu.
          { exact: corr_heap_segment_rcons. }
          right. repeat (eexists; eauto). }
      { move => Hterm [ Hnf1 Hnf2 ].
        do 2 eexists.
        - apply: Heaps.red_name_appL_multi. eassumption.
        - left. repeat split; eauto.
          + inversion 1; subst; eauto.
          + inversion 1; subst; eauto.
            inversion Hterm; subst; eauto.
            move: (Hheap _ H2) => [ ? [ ] ]. eauto. }
    + do 2 eexists.
      * apply: Heaps.red_name_appL_multi. eassumption.
      * right. repeat (econstructor; eauto).
        refine (corr_term_ext _ _ _ _ _ _ _
          (Heaps.red_name_heap _ _ _ _ _)); eauto.
        apply: corr_term_impl; eauto.
  - repeat (eexists; eauto).
    have Hterm' : corr_term
      (fun l => P l \/ size H <= l /\ l - size H < size ts)
      (H ++ map (@Some _ \o subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var)) ts)
      (fun l => if l < size H then mu l else nth (mu l) (map (Let ts') ts') (l - size H))
      (subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var) t)
      (subst (scat (map (Let ts') ts') Var) t').
    { apply: corr_term_subst.
      - ( eapply (corr_term_impl _ _ _ _ _ H3 _
            (map (omap (rename (addn (size ts))))
              (H ++ map (@Some _ \o subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var)) ts))
            (rename (addn (size ts)) \o
              (fun l => if l < size H then mu l else nth (mu l) (map (Let ts') ts') (l - size H)))); eauto ) => l.
        + rewrite !nth_map_heap nth_cat.
          case (leqP (size H) l) => [ /(nth_default _) -> | ]; eauto.
        + by move => /(corr_heap_segment_bound _ _ _ _ Hheap) /= ->.
      - move => x.
        rewrite !nth_scat size_mkseq size_map -H0.
        case (leqP (size ts) x) => ?.
        + rewrite !nth_default ?size_mkseq ?size_map -?H0; eauto.
        + rewrite nth_mkseq => //=.
          apply: corr_term_loc.
          * rewrite leq_addr addKn. eauto.
          * rewrite ltnNge leq_addr addKn.
            apply: set_nth_default.
            by rewrite size_map -H0.
      - move => l.
        rewrite nth_map_heap omap_comp (eq_omap _ _ _ id) ?omap_id => // ?.
        rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => // ? /=.
        by rewrite nth_scat nth_default size_mkseq ?addKn ?leq_addr.
      - move => ?.
        rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
        by rewrite nth_scat nth_default size_map -H0 ?addKn ?leq_addr. }
    have Hheap' : corr_heap
      (fun l => P l \/ size H <= l /\ l - size H < size ts)
      (H ++ map (@Some _ \o subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var)) ts)
      (fun l => if l < size H then mu l else nth (mu l) (map (Let ts') ts') (l - size H)).
    { apply: corr_heap_segment_union.
      - apply: corr_heap_segment_cat.
        refine (corr_heap_segment_impl _ _ _ _
          (corr_heap_ext _ _ _ Hheap _ _) _ _ _ _ _ _); eauto.
        by move => ? /(corr_heap_segment_bound _ _ _ _ Hheap) ->.
      - move => ? [ Hge Hlt ].
        rewrite nth_cat ltnNge Hge (nth_map (Var 0)) => //=.
        repeat (eexists; eauto).
        + apply: (nth_map (Var 0)). by rewrite -H0.
        + apply: corr_term_subst.
          { ( refine (corr_term_impl _ _ _ _ _ (H1 _ _ _) _
              (map (omap (rename (addn (size ts))))
                (H ++ map (@Some _ \o subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var)) ts))
              (rename (addn (size ts)) \o
                (fun l => if l < size H then mu l else nth (mu l) (map (Let ts') ts') (l - size H))) _ _ _); eauto ) => l.
            - rewrite !nth_map_heap nth_cat.
              case (leqP (size H) l) => [ /(nth_default _) -> | ]; eauto.
            - by move => /(corr_heap_segment_bound _ _ _ _ Hheap) /= ->. }
          { move => x.
            case (leqP (size ts) x) => ?.
            - by rewrite !nth_scat !nth_default ?size_mkseq ?size_map -?H0.
            - rewrite !nth_scat nth_mkseq ?(nth_map (Var 0)) -?H0 => //.
              apply: corr_term_loc.
              + rewrite leq_addr addKn. eauto.
              + by rewrite ltnNge leq_addr (nth_map (Var 0)) addKn -?H0. }
          { move => ?.
            rewrite nth_map_heap omap_comp (eq_omap _ _ _ id) ?omap_id => // ?.
            rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
            by rewrite nth_scat nth_default size_mkseq ?leq_addr ?addKn. }
          { move => ?.
            rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
            by rewrite nth_scat nth_default size_map -H0 ?leq_addr ?addKn. } }
    right. repeat (eexists; eauto).
    by move => ? /(corr_heap_segment_bound _ _ _ _ Hheap) ->.
Qed.

Lemma eval_name_sound_aux p p' :
  clos_refl_trans_1n _ (fun p p' => Heaps.red_name p.1 p.2 p'.1 p'.2) p p' ->
  forall H H'' t1 v1,
  p = (H, t1) ->
  p' = (H'', v1) ->
  value v1 ->
  forall P H' t1' mu t2,
  corr_term P H' mu t1' t2 ->
  corr_heap P H' mu ->
  clos_refl_trans_1n _ (fun p p' => Heaps.red_name p.1 p.2 p'.1 p'.2) (H, t1) (H', t1') ->
  exists v2,
  clos_refl_trans _ red_name t2 v2 /\
  value v2 /\
  exists P' mu',
  corr_heap P' H'' mu' /\
  corr_term P' H'' mu' v1 v2.
Proof.
  induction 1; inversion 1; inversion 1; inversion 4; subst.
  - inversion H3; subst; inversion H6; subst.
    repeat (eexists; eauto).
  - by move: (Heaps.value_normal _ H3 _ _ _ H9).
  - move: (unwind_indirection _ _ _ _ _ H7 H8) => [ ? [ /clos_rt_rt1n_iff ] ];
    inversion 1; subst => [ [ [ Hterm' [ Hnf ? ] ] | [ ? [ ? [ ? [ ? [ ] ] ] ] ] ] ].
    + by move: (Hnf _ _ H).
    + destruct y => /(Heaps.red_name_det _ _ _ _ H) /= [ ? ? ] [ ? [ ? [ Hheap' [ Hterm' [ ? ? ] ] ] ] ]. subst.
      move: (IHclos_refl_trans_1n _ _ _ _ erefl erefl H6 _ _ _ _ _ Hterm' Hheap' (rt1n_refl _ _ _)) =>
        [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ].
      do 2 eexists.
      * refine (rt_trans _ _ _ _ _ (rt_step _ _ _ _ _) _); eassumption.
      * repeat (eexists; eauto).
    + destruct y, y0.
      case: (Heaps.red_name_det _ _ _ _ H _ _ H1) => /= ? ?. subst.
      apply: IHclos_refl_trans_1n; eauto.
    + destruct y, y0 => [ ? [ ? [ ? [ Hheap' [ Hterm' [ ? ? ] ] ] ] ] ].
      case: (Heaps.red_name_det _ _ _ _ H _ _ H1) => /= ? ?. subst.
      move: (IHclos_refl_trans_1n _ _ _ _ erefl erefl H6 _ _ _ _ _ Hterm' Hheap') =>
        [ | ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ].
      { apply /clos_rt_rt1n_iff.
        refine (rt_trans _ _ _ (_, _) _ _ (rt_step _ _ _ _ _)) => /=.
        - apply /clos_rt_rt1n_iff. eassumption.
        - eauto. }
      do 2 eexists.
      { apply: rt_trans.
        - apply: rt_step. eassumption.
        - eassumption. }
      repeat (eexists; eauto).
  - destruct y, y0.
    case: (Heaps.red_name_det _ _ _ _ H _ _ H10) => /= ? ?. subst.
    apply: IHclos_refl_trans_1n; eauto.
Qed.

Corollary eval_name_sound H H' t1 v1 :
  Heaps.eval_name H t1 H' v1 ->
  forall P mu t2,
  corr_term P H mu t1 t2 ->
  corr_heap P H mu ->
  exists v2, eval_name t2 v2 /\
  exists P' mu',
  corr_heap P' H' mu' /\
  corr_term P' H' mu' v1 v2.
Proof.
  move => Heval ? ? ? Hterm Hheap.
  move: (Heaps.eval_name_red_name_multi _ _ _ _ Heval) =>
    /clos_rt_rt1n_iff /eval_name_sound_aux
    /(_ _ _ _ _ erefl erefl
        (Heaps.eval_name_value _ _ _ _ Heval) _ _ _ _ _ Hterm Hheap (rt1n_refl _ _ _))
  [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ].
  repeat (eexists; eauto).
  exact: red_name_multi_eval_name.
Qed.

Lemma diverge_name_sound_aux t2 t2' :
  clos_refl_trans_1n _ red_name t2 t2' ->
  forall H t1,
  ( forall H' t1',
    clos_refl_trans _ (fun p p' => Heaps.red_name p.1 p.2 p'.1 p'.2) (H, t1) (H', t1') ->
    exists H'' t1'', Heaps.red_name H' t1' H'' t1'' ) ->
  forall P mu,
  corr_term P H mu t1 t2 ->
  corr_heap P H mu ->
  exists t2'', red_name t2' t2''.
Proof.
  induction 1 => ? ? Hdiv ? ? Hterm Hheap.
  - move: (unwind_indirection _ _ _ _ _ Hterm Hheap) =>
      [ ? [ Hrt [ [ ? [ Hnf ? ] ] | [ ? [ ] ] ] ] ]; eauto.
    by move: (Hdiv _ _ Hrt) => [ ? [ ? /Hnf ] ].
  - move: (unwind_indirection _ _ _ _ _ Hterm Hheap) =>
      [ ? [ Hrt [ [ ? [ ? Hnf ] ] |
                  [ ? [ /(red_name_det _ _ H) <-
                         [ ? [ ? [ ? [ ? [ ? [ Hheap' [ Hterm' [ ? ? ] ] ] ] ] ] ] ] ] ] ] ] ].
    + edestruct Hnf. eauto.
    + refine (IHclos_refl_trans_1n _ _ _ _ _ Hterm' Hheap') => ? ? ?.
      apply: Hdiv.
      refine (rt_trans _ _ _ (_, _) _ _ (rt_trans _ _ _ (_, _) _ (rt_step _ _ _ _ _) _)) => /=; eauto. 
Qed.

Corollary diverge_name_sound H t1 :
  Heaps.diverge_name H t1 ->
  forall P mu t2,
  corr_term P H mu t1 t2 ->
  corr_heap P H mu ->
  diverge_name t2.
Proof.
  move => /Heaps.diverge_name_red_name ? ? ? ? ? ?.
  apply: red_name_multi_diverge_name => ? ?.
  apply: diverge_name_sound_aux; eauto.
  by apply /clos_rt_rt1n_iff.
Qed.

Lemma eval_name_complete_aux t2 v2 :
  clos_refl_trans_1n _ red_name t2 v2 ->
  value v2 ->
  forall P mu H t1,
  corr_term P H mu t1 t2 ->
  corr_heap P H mu ->
  exists H' v1,
  clos_refl_trans _ (fun p p' => Heaps.red_name p.1 p.2 p'.1 p'.2) (H, t1) (H', v1) /\
  value v1 /\
  exists P' mu',
  corr_heap P' H' mu' /\
  corr_term P' H' mu' v1 v2.
Proof.
  induction 1 => Hv ? ? ? ? Hterm Hheap.
  - move: (unwind_indirection _ _ _ _ _ Hterm Hheap) =>
      [ ? [ ? [ [ Hterm' [ Hnf ? ] ] | [ ? [ /(value_normal _ Hv) ] ] // ] ] ].
    repeat (eexists; eauto).
    inversion Hv; subst; inversion Hterm'; subst; eauto.
    + edestruct Hnf. eauto.
    + move: (Hheap _ H0) => [ ? [ ? ] ].
      edestruct Hnf. eauto.
  - move: (unwind_indirection _ _ _ _ _ Hterm Hheap) =>
    [ ? [ ? [ [ ? [ ? Hnf ] ] |
              [ ? [ /(red_name_det _ _ H) <-
                     [ ? [ ? [ ? [ ? [ ? [ Hheap' [ Hterm' [ ? ? ] ] ] ] ] ] ] ] ] ] ] ] ].
    + edestruct Hnf. eauto.
    + move: (IHclos_refl_trans_1n Hv _ _ _ _ Hterm' Hheap') =>
        [ ? [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ] ].
      do 3 eexists.
      { refine (rt_trans _ _ _ (_, _) _ _ _).
        - eassumption.
        - refine (rt_trans _ _ _ (_, _) _ (rt_step _ _ _ _ _) _) => /=; eauto. }
      repeat (eexists; eauto).
Qed.

Corollary eval_name_complete t2 v2 :
  eval_name t2 v2 ->
  forall P mu H t1,
  corr_term P H mu t1 t2 ->
  corr_heap P H mu ->
  exists H' v1,
  Heaps.eval_name H t1 H' v1 /\
  exists P' mu',
  corr_heap P' H' mu' /\
  corr_term P' H' mu' v1 v2.
Proof.
  move => Heval.
  move: (eval_name_red_name_multi _ _ Heval) => /clos_rt_rt1n_iff Hrt ? ? ? ? Hterm Hheap.
  have Hv := eval_name_value _ _ Heval.
  move: (eval_name_complete_aux _ _ Hrt Hv _ _ _ _ Hterm Hheap) =>
    [ ? [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ] ].
  repeat (eexists; eauto).
  exact: Heaps.red_name_multi_eval_name.
Qed.

Lemma diverge_name_complete_aux p p' :
  clos_refl_trans_1n _ (fun p p' => Heaps.red_name p.1 p.2 p'.1 p'.2) p p' ->
  forall H H'' t1 t1'',
  p = (H, t1) ->
  p' = (H'', t1'') ->
  forall P H' mu t1' t2,
  corr_term P H' mu t1' t2 ->
  corr_heap P H' mu ->
  clos_refl_trans_1n _ (fun p p' => Heaps.red_name p.1 p.2 p'.1 p'.2) (H, t1) (H', t1') ->
  ( forall t2',
    clos_refl_trans _ red_name t2 t2' ->
    exists t2'', red_name t2' t2'' ) ->
  exists H''' t1''', Heaps.red_name H'' t1'' H''' t1'''.
Proof.
  induction 1; inversion 1; inversion 1;
  inversion 3; subst => [ Hdiv ]; eauto.
  - move: (unwind_indirection _ _ _ _ _ H3 H6) => [ ? [ /clos_rt_rt1n_iff ] ]; inversion 1; subst; eauto.
    move => [ [ ? [ ? Hnf ] ] | [ ? [ ? [ ? [ ? [ ] ] ] ] ] ]; eauto.
    by case: (Hdiv _ (rt_refl _ _ _)) => ? /Hnf.
  - move: (unwind_indirection _ _ _ _ _ H6 H7) => [ ? [ /clos_rt_rt1n_iff ] ];
    inversion 1; subst => [ [ [ Hterm' [ Hnf ? ] ] | [ ? [ ? [ ? [ ? [ ] ] ] ] ] ] ].
    + case: (Hnf _ _ H).
    + destruct y => /(Heaps.red_name_det _ _ _ _ H) /= [ ? ? ].
      subst => [ [ ? [ ? [ Hheap' [ Hterm' [ ? ? ] ] ] ] ] ].
      apply: (IHclos_refl_trans_1n _ _ _ _ erefl erefl _ _ _ _ _ Hterm' Hheap' (rt1n_refl _ _ _)); eauto.
    + destruct y, y0.
      case (Heaps.red_name_det _ _ _ _ H _ _ H1) => /= ? ?. subst.
      apply: (IHclos_refl_trans_1n _ _ _ _ erefl erefl _ _ _ _ _ Hterm' H7); eauto.
    + destruct y, y0 => ? [ ? [ ? [ Hheap' [ Hterm' [ ? ? ] ] ] ] ].
      case (Heaps.red_name_det _ _ _ _ H _ _ H1) => /= ? ?. subst.
      apply: (IHclos_refl_trans_1n _ _ _ _ erefl erefl _ _ _ _ _ Hterm' Hheap'); eauto.
      { apply /clos_rt_rt1n_iff.
        refine (rt_trans _ _ _ (_, _) _ _ (rt_step _ _ _ _ _)) => /=.
        - apply /clos_rt_rt1n_iff. eassumption.
        - eauto. }
  - destruct y, y0.
    case: (Heaps.red_name_det _ _ _ _ H _ _ H9) => /= ? ?. subst.
    apply: IHclos_refl_trans_1n; eauto.
Qed.

Corollary diverge_name_complete t2 :
  diverge_name t2 ->
  forall P mu H t1,
  corr_term P H mu t1 t2 ->
  corr_heap P H mu ->
  Heaps.diverge_name H t1.
Proof.
  move => /diverge_name_red_name Hdiv ? ? ? ? Hterm Hheap.
  apply: Heaps.red_name_multi_diverge_name =>
    ? ? /clos_rt_rt1n_iff /diverge_name_complete_aux.
  apply; eauto using rt1n_refl.
Qed.

Theorem eval_name_sound' H1 H1' t1 v1 :
  Heaps.eval_name H1 t1 H1' v1 ->
  forall P mu t2,
  corr_heap P H1 mu ->
  corr_term P H1 mu t1 t2 ->
  exists v2,
  eval_name t2 v2 /\
  exists P' mu',
  corr_heap P' H1' mu' /\
  corr_term P' H1' mu' v1 v2 /\
  ( forall l, P l -> P' l ) /\
  ( forall l, P l -> mu l = mu' l ) /\
  ( forall l t, nth None H1 l = Some t -> mu l = mu' l ).
Proof.
  induction 1; inversion 2; subst.
  - move: (H0) H6 => ->. inversion 1. subst.
    exact: IHeval_name.
  - move: (H0) (H2 _ H6) => -> [ ? [ ] ].
    inversion 1. subst => [ [ ? [ ? [ -> ] ] ]
      /(IHeval_name _ _ _ H2) [ ? [ ? ? ] ] ].
    repeat (eexists; eauto).
  - move: (IHeval_name1 _ _ _ H2 H9) =>
      [ ? [ ? [ P' [ mu' [ Hheap [ ] ] ] ] ] ].
    inversion 1. subst => [ [ HP' [ ? HQmu' ] ] ].
    have Hterm' : corr_term P'
      (rcons H' (Some t2))
      [eta mu' with size H' |-> t2']
      (subst (scons (Loc (size H')) Var) t0)
      (subst (scons t2' Var) t').
    { apply: corr_term_subst.
      - ( eapply (corr_term_impl _ _ _ _ _ H8 _
            (map (omap (rename succn)) (rcons H' (Some t2)))
            (rename succn \o [eta mu' with size H' |-> t2'])); eauto ) => l.
        + rewrite !nth_map_heap nth_rcons.
          case (leqP (size H') l) => [ /(nth_default _) -> | ]; eauto.
        + by move => /= /(corr_heap_segment_bound _ _ _ _ Hheap) /ltn_eqF ->.
      - move => [ | ? ] //=.
        apply: corr_term_indir => /=.
        + by rewrite nth_rcons ltnn eqxx.
        + ( apply: corr_term_impl; eauto ) => l /=.
          * move: nth_rcons  (nth None H l)
              (Heaps.eval_name_heap _ _ _ _ H0 l) =>
              -> [ ? /(_ _ erefl) | ]; eauto.
            case (leqP (size H') l) => [ /(nth_default _) -> | ? -> ]; eauto.
          * move => HP.
            rewrite (ltn_eqF
              (corr_heap_segment_bound _ _ _ _ Hheap _ (HP' _ HP))). eauto.
      - move => ?.
        rewrite nth_map_heap omap_comp (eq_omap _ _ _ id) ?omap_id => // ?.
        by rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id.
      - move => ?.
        by rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id. }
    have Hheap' : corr_heap P'
      (rcons H' (Some t2))
      [eta mu' with size H' |-> t2'].
    { refine (corr_heap_segment_impl _ _ _ _
        (corr_heap_ext _ _ _ Hheap _ _) _ _ _ _ _ _); eauto.
      - by move => ? /(corr_heap_segment_bound _ _ _ _ Hheap) /ltn_eqF /= ->.
      - move => l.
        by move: nth_rcons (leqP (size H') l) => -> [ /(nth_default _) -> | ]. }
    move: (IHeval_name2 _ _ _ Hheap' Hterm') =>
      [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ HPmu'' HQmu'' ] ] ] ] ] ] ] ].
    repeat (eexists; eauto).
    + move => ? HP.
      rewrite -HPmu'' => /=; eauto.
      rewrite (ltn_eqF (corr_heap_segment_bound _ _ _ _ Hheap _ (HP' _ HP))). eauto.
    + move => l t HQ.
      move: nth_rcons (leqP (size H') l)
        (Heaps.eval_name_heap _ _ _ _ H0 _ _ HQ) (HQmu'' l t) =>
        -> [ /(nth_default _) -> // | Hlt ? <- //= ].
      rewrite (ltn_eqF Hlt). eauto.
  - repeat (eexists; eauto).
  - have Hterm' : corr_term
      (fun l => P l \/ size H <= l /\ l - size H < size ts)
      (H ++ map (@Some _ \o subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var)) ts)
      (fun l => if l < size H then mu l else nth (mu l) (map (Let ts') ts') (l - size H))
      (subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var) t)
      (subst (scat (map (Let ts') ts') Var) t').
    { apply: corr_term_subst.
      - ( eapply (corr_term_impl _ _ _ _ _ H11 _
            (map (omap (rename (addn (size ts))))
              (H ++ map (@Some _ \o subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var)) ts))
            (rename (addn (size ts)) \o
              (fun l => if l < size H then mu l else nth (mu l) (map (Let ts') ts') (l - size H)))); eauto ) => l.
        + rewrite !nth_map_heap nth_cat.
          case (leqP (size H) l) => [ /(nth_default _) -> | ]; eauto.
        + by move => /(corr_heap_segment_bound _ _ _ _ H1) /= ->.
      - move => x.
        rewrite !nth_scat size_mkseq size_map -H6.
        case (leqP (size ts) x) => ?.
        + rewrite !nth_default ?size_mkseq ?size_map -?H6; eauto.
        + rewrite nth_mkseq => //=.
          apply: corr_term_loc.
          * rewrite leq_addr addKn. eauto.
          * rewrite ltnNge leq_addr addKn.
            apply: set_nth_default.
            by rewrite size_map -H6.
      - move => l.
        rewrite nth_map_heap omap_comp (eq_omap _ _ _ id) ?omap_id => // ?.
        rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => // ? /=.
        by rewrite nth_scat nth_default size_mkseq ?addKn ?leq_addr.
      - move => ?.
        rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
        by rewrite nth_scat nth_default size_map -H6 ?addKn ?leq_addr. }
    have Hheap' : corr_heap
      (fun l => P l \/ size H <= l /\ l - size H < size ts)
      (H ++ map (@Some _ \o subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var)) ts)
      (fun l => if l < size H then mu l else nth (mu l) (map (Let ts') ts') (l - size H)).
    { apply: corr_heap_segment_union.
      - ( refine (corr_heap_segment_impl _ _ _ _
          (corr_heap_ext _ _ _ H1 _ _) _ _ _ _ _ _); eauto ) => l.
        + by move => /(corr_heap_segment_bound _ _ _ _ H1) ->.
        + by move: nth_cat (leqP (size H) l) => -> [ /(nth_default _) -> | ].
      - move => ? [ Hge Hlt ].
        rewrite nth_cat ltnNge Hge (nth_map (Var 0)) => //=.
        repeat (eexists; eauto).
        + apply: (nth_map (Var 0)).
          by rewrite -H6.
        + apply: corr_term_subst.
          { ( refine (corr_term_impl _ _ _ _ _ (H9 _ _ _) _
              (map (omap (rename (addn (size ts))))
                (H ++ map (@Some _ \o subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var)) ts))
              (rename (addn (size ts)) \o
                (fun l => if l < size H then mu l else nth (mu l) (map (Let ts') ts') (l - size H))) _ _ _); eauto ) => l.
            - rewrite !nth_map_heap nth_cat.
              case (leqP (size H) l) => [ /(nth_default _) -> | ]; eauto.
            - by move => /(corr_heap_segment_bound _ _ _ _ H1) /= ->. }
          { move => x.
            case (leqP (size ts) x) => ?.
            - by rewrite !nth_scat !nth_default ?size_mkseq ?size_map -?H6.
            - rewrite !nth_scat nth_mkseq ?(nth_map (Var 0)) -?H6 => //.
              apply: corr_term_loc.
              + rewrite leq_addr addKn. eauto.
              + by rewrite ltnNge leq_addr (nth_map (Var 0)) addKn -?H6. }
          { move => l.
            rewrite nth_map_heap omap_comp (eq_omap _ _ _ id) ?omap_id => // ?.
            rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
            by rewrite nth_scat nth_default size_mkseq ?leq_addr ?addKn. }
          { move => l.
            rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
            by rewrite nth_scat nth_default size_map -H6 ?leq_addr ?addKn. } }
    move: (IHeval_name _ _ _ Hheap' Hterm') =>
      [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ HPmu' HQmu' ] ] ] ] ] ] ] ].
    repeat (eexists; eauto).
    + move => ? HP.
      rewrite -HPmu'; eauto.
      erewrite corr_heap_segment_bound; eauto.
    + move => l t_.
      by move: nth_cat (leqP (size H) l) (HQmu' l t_) =>
        -> [ /(nth_default _) -> | ].
Qed.

Theorem eval_name_complete' t2 v2 :
  eval_name t2 v2 ->
  forall P mu H1 t1 t2',
  corr_term P H1 mu t1 t2' ->
  corr_heap P H1 mu ->
  t2 = t2' ->
  exists H1' v1,
  Heaps.eval_name H1 t1 H1' v1 /\
  exists P' mu',
  corr_heap P' H1' mu' /\
  corr_term P' H1' mu' v1 v2 /\
  ( forall l, P l -> P' l ) /\
  ( forall l, P l -> mu l = mu' l ) /\
  ( forall l t, nth None H1 l = Some t -> mu l = mu' l ).
Proof.
  induction 1; induction 1; inversion 2; subst.
  - move: (IHcorr_term H4 erefl) => [ ? [ ? [ ? ? ] ] ].
    repeat (eexists; eauto).
  - by move: H6 (H4 _ H2) => <- [ ? [ ? [ ? [ ? [ ] ] ] ] ].
  - move: (IHeval_name1 _ _ _ _ _ H2_ H2 erefl) =>
      [ H1' [ ? [ Hcbn [ P' [ mu' [ Hheap [ ] ] ] ] ] ] ].
    move: (Heaps.eval_name_value _ _ _ _ Hcbn).
    inversion 1. inversion 1. subst => [ [ HP' [ ? HQmu' ] ] ].
    have Hterm' : corr_term P'
      (rcons H1' (Some t4))
      [eta mu' with size H1' |-> t2']
      (subst (scons (Loc (size H1')) Var) t)
      (subst (scons t2' Var) t0).
    { apply: corr_term_subst.
      - ( eapply (corr_term_impl _ _ _ _ _ H10 _
            (map (omap (rename succn)) (rcons H1' (Some t4)))
            (rename succn \o [eta mu' with size H1' |-> t2'])); eauto ) => l.
        + rewrite !nth_map_heap nth_rcons.
          case (leqP (size H1') l) => [ /(nth_default _) -> | ]; eauto.
        + by move => /= /(corr_heap_segment_bound _ _ _ _ Hheap) /ltn_eqF ->.
      - move => [ | ? ] //=.
        apply: corr_term_indir => /=.
        + by rewrite nth_rcons ltnn eqxx.
        + ( apply: corr_term_impl; eauto ) => l /=.
          * move: nth_rcons  (nth None H1 l)
              (Heaps.eval_name_heap _ _ _ _ Hcbn l) =>
              -> [ ? /(_ _ erefl) | ]; eauto.
            case (leqP (size H1') l) => [ /(nth_default _) -> | ? -> ]; eauto.
          * move => HP.
            rewrite (ltn_eqF
              (corr_heap_segment_bound _ _ _ _ Hheap _ (HP' _ HP))). eauto.
      - move => ?.
        rewrite nth_map_heap omap_comp (eq_omap _ _ _ id) ?omap_id => // ?.
        by rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id.
      - move => ?.
        by rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id. }
    have Hheap' : corr_heap P'
      (rcons H1' (Some t4))
      [eta mu' with size H1' |-> t2'].
    { refine (corr_heap_segment_impl _ _ _ _
        (corr_heap_ext _ _ _ Hheap _ _) _ _ _ _ _ _); eauto.
      - by move => ? /(corr_heap_segment_bound _ _ _ _ Hheap) /ltn_eqF /= ->.
      - move => l.
        by move: nth_rcons (leqP (size H1') l) => -> [ /(nth_default _) -> | ]. }
    move: (IHeval_name2 _ _ _ _ _ Hterm' Hheap' erefl) =>
      [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ HPmu'' HQmu'' ] ] ] ] ] ] ] ] ].
    repeat (eexists; eauto).
    + move => ? HP.
      rewrite -HPmu'' => /=; eauto.
      rewrite (ltn_eqF (corr_heap_segment_bound _ _ _ _ Hheap _ (HP' _ HP))). eauto.
    + move => l t_ HQ.
      move: nth_rcons (leqP (size H1') l)
        (Heaps.eval_name_heap _ _ _ _ Hcbn _ _ HQ) (HQmu'' l t_) =>
        -> [ /(nth_default _) -> // | Hlt ? <- //= ].
      rewrite (ltn_eqF Hlt). eauto.
  - move: (IHcorr_term H2 erefl) => [ ? [ ? [ ? ? ] ] ].
    repeat (eexists; eauto).
  - by move: H4 (H2 _ H0) => <- [ ? [ ? [ ? [ ? [ ] ] ] ] ].
  - repeat (eexists; eauto).
  - move: (IHcorr_term H3 erefl) => [ ? [ ? [ ? ? ] ] ].
    repeat (eexists; eauto).
  - move: H4 (H3 _ H1) => <- [ ? [ ? [ ? [ ? [ ] ] ] ] ].
    inversion 1. subst => [ Hterm ].
    move: (IHeval_name _ _ _ _ _ Hterm H3 erefl) => [ ? [ ? [ ? ? ] ] ].
    repeat (eexists; eauto).
  - have Hterm' : corr_term
      (fun l => P l \/ size H0 <= l /\ l - size H0 < size ts0)
      (H0 ++ map (@Some _ \o subst (scat (mkseq (Loc \o addn (size H0)) (size ts0)) Var)) ts0)
      (fun l => if l < size H0 then mu l else nth (mu l) (map (Let ts') ts') (l - size H0))
      (subst (scat (mkseq (Loc \o addn (size H0)) (size ts0)) Var) t0)
      (subst (scat (map (Let ts') ts') Var) t').
    { apply: corr_term_subst.
      - ( eapply (corr_term_impl _ _ _ _ _ H4 _
            (map (omap (rename (addn (size ts0))))
              (H0 ++ map (@Some _ \o subst (scat (mkseq (Loc \o addn (size H0)) (size ts0)) Var)) ts0))
            (rename (addn (size ts0)) \o
              (fun l => if l < size H0 then mu l else nth (mu l) (map (Let ts') ts') (l - size H0)))); eauto ) => l.
        + rewrite !nth_map_heap nth_cat.
          case (leqP (size H0) l) => [ /(nth_default _) -> | ]; eauto.
        + by move => /(corr_heap_segment_bound _ _ _ _ H5) /= ->.
      - move => x.
        rewrite !nth_scat size_mkseq size_map -H1.
        case (leqP (size ts0) x) => ?.
        + rewrite !nth_default ?size_mkseq ?size_map -?H1; eauto.
        + rewrite nth_mkseq => //=.
          apply: corr_term_loc.
          * rewrite leq_addr addKn. eauto.
          * rewrite ltnNge leq_addr addKn.
            apply: set_nth_default.
            by rewrite size_map -H1.
      - move => ?.
        rewrite nth_map_heap omap_comp (eq_omap _ _ _ id) ?omap_id => // ?.
        rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => // ? /=.
        by rewrite nth_scat nth_default size_mkseq ?addKn ?leq_addr.
      - move => ?.
        rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
        by rewrite nth_scat nth_default size_map -H1 ?addKn ?leq_addr. }
    have Hheap' : corr_heap
      (fun l => P l \/ size H0 <= l /\ l - size H0 < size ts0)
      (H0 ++ map (@Some _ \o subst (scat (mkseq (Loc \o addn (size H0)) (size ts0)) Var)) ts0)
      (fun l => if l < size H0 then mu l else nth (mu l) (map (Let ts') ts') (l - size H0)).
    { apply: corr_heap_segment_union.
      - ( refine (corr_heap_segment_impl _ _ _ _
          (corr_heap_ext _ _ _ H5 _ _) _ _ _ _ _ _); eauto ) => l.
        + by move => /(corr_heap_segment_bound _ _ _ _ H5) ->.
        + by move: nth_cat (leqP (size H0) l) => -> [ /(nth_default _) -> | ].
      - move => ? [ Hge Hlt ].
        rewrite nth_cat ltnNge Hge (nth_map (Var 0)) => //=.
        repeat (eexists; eauto).
        + apply: (nth_map (Var 0)).
          by rewrite -H1.
        + apply: corr_term_subst.
          { ( refine (corr_term_impl _ _ _ _ _ (H2 _ _ _) _
              (map (omap (rename (addn (size ts0))))
                (H0 ++ map (@Some _ \o subst (scat (mkseq (Loc \o addn (size H0)) (size ts0)) Var)) ts0))
              (rename (addn (size ts0)) \o
                (fun l => if l < size H0 then mu l else nth (mu l) (map (Let ts') ts') (l - size H0))) _ _ _); eauto ) => l.
            - rewrite !nth_map_heap nth_cat.
              case (leqP (size H0) l) => [ /(nth_default _) -> | ]; eauto.
            - by move => /(corr_heap_segment_bound _ _ _ _ H5) /= ->. }
          { move => x.
            case (leqP (size ts0) x) => ?.
            - by rewrite !nth_scat !nth_default ?size_mkseq ?size_map -?H1.
            - rewrite !nth_scat nth_mkseq ?(nth_map (Var 0)) -?H1 => //.
              apply: corr_term_loc.
              + rewrite leq_addr addKn. eauto.
              + by rewrite ltnNge leq_addr (nth_map (Var 0)) addKn -?H1. }
          { move => ?.
            rewrite nth_map_heap omap_comp (eq_omap _ _ _ id) ?omap_id => // ?.
            rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
            by rewrite nth_scat nth_default size_mkseq ?leq_addr ?addKn. }
          { move => l.
            rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
            by rewrite nth_scat nth_default size_map -H1 ?leq_addr ?addKn. } }
    move: (IHeval_name _ _ _ _ _ Hterm' Hheap' erefl) =>
      [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ ? [ HPmu' HQmu' ] ] ] ] ] ] ] ] ].
    repeat (eexists; eauto).
    + move => ? ?.
      rewrite -HPmu'; eauto.
      erewrite corr_heap_segment_bound; eauto.
    + move => l t.
      by move: nth_cat (leqP (size H0) l) (HQmu' l t) =>
        -> [ /(nth_default _) -> | ].
Qed.

Theorem diverge_name_complete' :
  forall t2,
  diverge_name t2 ->
  forall P mu H1 t1,
  corr_term P H1 mu t1 t2 ->
  corr_heap P H1 mu ->
  Heaps.diverge_name H1 t1.
Proof.
  cofix diverge_name_complete.
  inversion 1; inversion 1; subst => [ Hheap0 ].
  - apply: Heaps.diverge_name_loc; eauto.
  - move: (Hheap0 _ H5) => [ ? [ ? [ ? [ ? [ ] ] ] ] ].
    by rewrite H6.
  - apply: Heaps.diverge_name_appL; eauto.
  - apply: Heaps.diverge_name_loc; eauto.
  - move: (Hheap0 _ H6) => [ ? [ ? [ ? [ ? [ ] ] ] ] ].
    by rewrite H7.
  - move: (eval_name_complete' _ _ H0 _ _ _ _ _ H11 Hheap0 erefl) =>
      [ H1' [ ? [ Hcbn [ P' [ mu' [ Hheap [ ] ] ] ] ] ] ].
    move: (Heaps.eval_name_value _ _ _ _ Hcbn).
    inversion 1; inversion 1. subst => [ [ ? [ ? ? ] ] ].
    have Hterm' : corr_term P'
      (rcons H1' (Some t6)) mu'
      (subst (scons (Loc (size H1')) Var) t)
      (subst (scons t3 Var) t0).
    { apply: corr_term_subst.
      - ( eapply (corr_term_impl _ _ _ _ _ H10 _
            (map (omap (rename succn)) (rcons H1' (Some t6)))); eauto ) => l.
        rewrite !nth_map_heap nth_rcons.
        case (leqP (size H1') l) => [ /(nth_default _) -> | ]; eauto.
      - move => [ | ? ] //=.
        apply: corr_term_indir => /=.
        + by rewrite nth_rcons ltnn eqxx.
        + ( apply: corr_term_impl; eauto ) => l /=.
          move: nth_rcons (nth None H3 l)
            (Heaps.eval_name_heap _ _ _ _ Hcbn l) =>
            -> [ ? /(_ _ erefl) | ]; eauto.
          case (leqP (size H1') l) => [ /(nth_default _) -> | ? -> ]; eauto.
      - move => ?.
        rewrite nth_map_heap omap_comp (eq_omap _ _ _ id) ?omap_id => // ?.
        by rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id.
      - move => ?.
        by rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id. }
    have Hheap' : corr_heap P' (rcons H1' (Some t6)) mu'.
    { exact: corr_heap_segment_rcons. }
    apply: Heaps.diverge_name_appabs; eauto.
  - apply: Heaps.diverge_name_loc; eauto.
  - move: (Hheap0 _ H5) => [ ? [ ? [ ? [ ? [ ] ] ] ] ].
    rewrite H6. inversion 1. subst => [ ? ].
    apply: Heaps.diverge_name_loc; eauto.
  - have Hterm' : corr_term
      (fun l => P l \/ size H2 <= l /\ l - size H2 < size ts0)
      (H2 ++ map (@Some _ \o subst (scat (mkseq (Loc \o addn (size H2)) (size ts0)) Var)) ts0)
      (fun l => if l < size H2 then mu l else nth (mu l) (map (Let ts) ts) (l - size H2))
      (subst (scat (mkseq (Loc \o addn (size H2)) (size ts0)) Var) t0)
      (subst (scat (map (Let ts) ts) Var) t).
    { apply: corr_term_subst.
      - ( eapply (corr_term_impl _ _ _ _ _ H12 _
            (map (omap (rename (addn (size ts0))))
              (H2 ++ map (@Some _ \o subst (scat (mkseq (Loc \o addn (size H2)) (size ts0)) Var)) ts0))
            (rename (addn (size ts0)) \o
              (fun l => if l < size H2 then mu l else nth (mu l) (map (Let ts) ts) (l - size H2)))); eauto ) => l.
        + rewrite !nth_map_heap nth_cat.
          case (leqP (size H2) l) => [ /(nth_default _) -> | ]; eauto.
        + by move => /(corr_heap_segment_bound _ _ _ _ Hheap0) /= ->.
      - move => x.
        rewrite !nth_scat size_mkseq size_map -H7.
        case (leqP (size ts0) x) => ?.
        + rewrite !nth_default ?size_mkseq ?size_map -?H1; eauto.
        + rewrite nth_mkseq => //=.
          apply: corr_term_loc.
          * rewrite leq_addr addKn. eauto.
          * rewrite ltnNge leq_addr addKn.
            apply: set_nth_default.
            by rewrite size_map -H7.
      - move => ?.
        rewrite nth_map_heap omap_comp (eq_omap _ _ _ id) ?omap_id => // ?.
        rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => // ? /=.
        by rewrite nth_scat nth_default size_mkseq ?addKn ?leq_addr.
      - move => ?.
        rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
        by rewrite nth_scat nth_default size_map -H7 ?addKn ?leq_addr. }
    have Hheap' : corr_heap
      (fun l => P l \/ size H2 <= l /\ l - size H2 < size ts0)
      (H2 ++ map (@Some _ \o subst (scat (mkseq (Loc \o addn (size H2)) (size ts0)) Var)) ts0)
      (fun l => if l < size H2 then mu l else nth (mu l) (map (Let ts) ts) (l - size H2)).
    { apply: corr_heap_segment_union.
      - apply: corr_heap_segment_cat.
        refine (corr_heap_segment_impl _ _ _ _
          (corr_heap_ext _ _ _ Hheap0 _ _) _ _ _ _ _ _); eauto.
        by move => ? /(corr_heap_segment_bound _ _ _ _ Hheap0) ->.
      - move => ? [ Hge Hlt ].
        rewrite nth_cat ltnNge Hge (nth_map (Var 0)) => //=.
        repeat (eexists; eauto).
        + apply: (nth_map (Var 0)). by rewrite -H7.
        + apply: corr_term_subst.
          { ( refine (corr_term_impl _ _ _ _ _ (H11 _ _ _) _
              (map (omap (rename (addn (size ts0))))
                (H2 ++ map (@Some _ \o subst (scat (mkseq (Loc \o addn (size H2)) (size ts0)) Var)) ts0))
              (rename (addn (size ts0)) \o
                (fun l => if l < size H2 then mu l else nth (mu l) (map (Let ts) ts) (l - size H2))) _ _ _); eauto ) => l.
            - rewrite !nth_map_heap nth_cat.
              case (leqP (size H2) l) => [ /(nth_default _) -> | ]; eauto.
            - by move => /(corr_heap_segment_bound _ _ _ _ Hheap0) /= ->. }
          { move => x.
            case (leqP (size ts0) x) => ?.
            - by rewrite !nth_scat !nth_default ?size_mkseq ?size_map -?H7.
            - rewrite !nth_scat nth_mkseq ?(nth_map (Var 0)) -?H7 => //.
              apply: corr_term_loc.
              + rewrite leq_addr addKn. eauto.
              + by rewrite ltnNge leq_addr (nth_map (Var 0)) addKn -?H7. }
          { move => ?.
            rewrite nth_map_heap omap_comp (eq_omap _ _ _ id) ?omap_id => // ?.
            rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
            by rewrite nth_scat nth_default size_mkseq ?leq_addr ?addKn. }
          { move => ?.
            rewrite /funcomp subst_rename_comp (eq_subst _ _ Var) ?subst_id => //= ?.
            by rewrite nth_scat nth_default size_map -H7 ?leq_addr ?addKn. } }
    apply: Heaps.diverge_name_let. eauto.
Qed.
