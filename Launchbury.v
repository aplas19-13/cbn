From mathcomp Require Import all_ssreflect.
Require Import Util LambdaLet Heaps.

Inductive eval_need : seq (option term) -> term -> seq (option term) -> term -> Prop :=
  | eval_need_loc H H' l t v :
      nth None H l = Some t ->
      eval_need H t H' v ->
      eval_need H (Loc l) (set_nth None H' l (Some v)) v
  | eval_need_app H H' H'' t0 t1 t2 v :
      eval_need H t1 H' (Abs t0) ->
      eval_need (rcons H' (Some t2)) (subst (scons (Loc (size H')) Var) t0) H'' v ->
      eval_need H (App t1 t2) H'' v
  | eval_need_abs H t0 :
      eval_need H (Abs t0) H (Abs t0)
  | eval_need_let H H' ts t v :
      let s := scat (mkseq (Loc \o addn (size H)) (size ts)) Var in
      eval_need (H ++ map (@Some _ \o subst s) ts) (subst s t) H' v ->
      eval_need H (Let ts t) H' v.

CoInductive diverge_need : seq (option term) -> term -> Prop :=
  | diverge_need_loc H l t :
      nth None H l = Some t ->
      diverge_need H t ->
      diverge_need H (Loc l)
  | diverge_need_appL H t1 t2 :
      diverge_need H t1 ->
      diverge_need H (App t1 t2)
  | diverge_need_appabs H H' t0 t1 t2 :
      eval_need H t1 H' (Abs t0) ->
      diverge_need (rcons H' (Some t2)) (subst (scons (Loc (size H')) Var) t0) ->
      diverge_need H (App t1 t2)
  | diverge_need_let H ts t :
      let s := scat (mkseq (Loc \o addn (size H)) (size ts)) Var in
      diverge_need (H ++ map (@Some _ \o subst s) ts) (subst s t) ->
      diverge_need H (Let ts t).

Definition corr_heap_segment (R R' : nat -> nat -> Prop) H1 H2 :=
  forall l1 l2, R l1 l2 ->
  exists t1, nth None H1 l1 = Some t1 /\
  exists t2, nth None H2 l2 = Some t2 /\
  ( corr_term R' t1 t2 \/
    exists H2' v2,
    eval_name H2 t2 H2' v2 /\
    exists S,
    iso_heap S H2 H2' /\
    corr_term (fun l0 l2 => R' l0 l2 \/ exists l1, R' l0 l1 /\ S l1 l2) t1 v2 /\
    forall l2', R l1 l2' ->
    exists t2', nth None H2 l2' = Some t2' /\
    corr_term (fun l2 l2' => exists l1, R' l1 l2 /\ R' l1 l2') t2 t2' ).

Definition corr_heap R := corr_heap_segment R R.

Hint Constructors eval_need.

Lemma value_eval_need H v :
  value v -> eval_need H v H v.
Proof. by inversion 1. Qed.

Lemma eval_need_value H H' t v :
  eval_need H t H' v -> value v.
Proof. by induction 1. Qed.

Lemma eval_need_det H H' t v :
  eval_need H t H' v ->
  forall H'' v',
  eval_need H t H'' v' ->
  H' = H'' /\ v = v'.
Proof.
  induction 1; inversion 1; subst; eauto.
  - move: H0 H5 => ->. inversion 1. subst.
    by case: (IHeval_need _ _ H7) => -> ->.
  - case: (IHeval_need1 _ _ H5) => ?. inversion 1. subst. eauto.
Qed.

Lemma eval_need_diverge_need_disjoint H H' t v :
  eval_need H t H' v ->
  diverge_need H t ->
  False.
Proof.
  induction 1; inversion 1; subst; eauto.
  - move: H0 H5 => ->. inversion 1. subst. eauto.
  - case: (eval_need_det _ _ _ _ H0_ _ _ H5).
    inversion 2. subst. eauto.
Qed.

Corollary value_diverge_need_disjoint H v :
  value v ->
  diverge_need H v ->
  False.
Proof.
  move => /(value_eval_need H).
  exact: eval_need_diverge_need_disjoint.
Qed.

Lemma iso_heap_segment_corr_heap_segment f f' H1 H2 :
  iso_heap_segment f f' H1 H2 ->
  corr_heap_segment f f' H1 H2.
Proof.
  move => Hiso ? ? /Hiso [ ? [ -> [ ? [ -> ? ] ] ] ].
  repeat eexists. eauto.
Qed.

Lemma corr_heap_segment_boundL f f' H H' :
  corr_heap_segment f f' H H' ->
  forall l l', f l l' ->
  l < size H.
Proof.
  move => Hcorr l ? /Hcorr [ ? [ ] ].
  by case: (leqP (size H) l) => [ /(nth_default _) -> | ].
Qed.

Lemma corr_heap_segment_boundR f f' H H' :
  corr_heap_segment f f' H H' ->
  forall l l', f l l' ->
  l' < size H'.
Proof.
  move => Hcorr ? l' /Hcorr [ ? [ ? [ ? [ ] ] ] ].
  by case: (leqP (size H') l') => [ /(nth_default _) -> | ].
Qed.

Lemma corr_heap_segment_wf_heap_segmentL f f' H H' :
  corr_heap_segment f f' H H' ->
  wf_heap_segment (fun l => exists l', f l l') (fun l => exists l', f' l l') H.
Proof.
  move => Hcorr ? [ ? /Hcorr
    [ ? [ -> [ ? [ ? [ ? | [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ] ] ] ] ] ] ];
  repeat (eexists; eauto).
  - apply: corr_term_wf_termL. eauto.
  - apply: wf_term_impl.
    + apply: corr_term_wf_termL. eauto.
    + move => ? [ ? [ | [ ? [ ] ] ] ]; eauto.
Qed.

Lemma corr_heap_segment_iso_heap_segmentR R R' H1 H2 :
  corr_heap_segment R R' H1 H2 ->
  iso_heap_segment
    (fun l2 l2' => exists l1, R l1 l2 /\ R l1 l2')
    (fun l2 l2' => exists l1, R' l1 l2 /\ R' l1 l2') H2 H2.
Proof.
  move => Hcorr ? ? [ ? [ HR HR' ] ];
  move: (Hcorr _ _ HR) =>
    [ ? [ Hnth1 [ ? [ Hnth2 [ ? | [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ] ] ] ] ] ];
  rewrite Hnth2; eauto.
  move: (Hcorr _ _ HR') =>
    [ ? [ Hnth1' [ ? [ Hnth2' [ ? | [ ? [ ? [ ? [ ? [ ? [ ? Hcon' ] ] ] ] ] ] ] ] ] ] ];
  move: (Hnth2') Hnth1 Hnth1' => -> ->; inversion 1; subst;
  repeat (eexists; eauto).
  - apply: corr_term_comp; eauto.
    exact: corr_term_sym.
  - move: Hnth2 (Hcon' _ HR) => -> [ ? [ ] ].
    inversion 1. subst => [ /corr_term_sym /corr_term_impl ].
    apply => ? ? [ ? [ ] ]. eauto.
Qed.

Corollary corr_heap_segment_wf_heap_segmentR f f' H H' :
  corr_heap_segment f f' H H' ->
  wf_heap_segment (fun l' => exists l, f l l') (fun l' => exists l, f' l l') H'.
Proof.
  move => /corr_heap_segment_iso_heap_segmentR /iso_heap_segment_wf_heap_segmentL Hwf.
  apply: wf_heap_segment_dom.
  - apply: wf_heap_segment_cod; eauto.
    move => ? [ ? [ ? [ ] ] ]. eauto.
  - move => ? [ ]. eauto.
Qed.

Lemma corr_heap_segment_dom (fdom fdom' fcod : nat -> nat -> Prop) H H' :
  corr_heap_segment fdom fcod H H' ->
  (forall l l', fdom' l l' -> fdom l l') ->
  corr_heap_segment fdom' fcod H H'.
Proof.
  move => Hcorr Hdom ? ? /Hdom /Hcorr
    [ ? [ -> [ ? [ -> [ ? | [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ] ] ] ] ] ];
  repeat (repeat (eexists; eauto); right).
Qed.

Lemma corr_heap_segment_cod (fdom fcod fcod' : nat -> nat -> Prop) H H' :
  corr_heap_segment fdom fcod H H' ->
  (forall l l', fcod l l' -> fcod' l l') ->
  corr_heap_segment fdom fcod' H H'.
Proof.
  move => Hcorr Hcod ? ? /Hcorr
    [ ? [ -> [ ? [ -> [ ? | [ ? [ ? [ ? [ ? [ ? [ ? Hcon ] ] ] ] ] ] ] ] ] ] ];
  repeat (eexists; eauto).
  - eauto using corr_term_impl.
  - right. do 6 (eexists; eauto).
    { apply: corr_term_impl; eauto.
      move => ? ? [ | [ ? [ ] ] ]; eauto. }
    move => ? /Hcon [ ? [ -> ? ] ].
    repeat (eexists; eauto).
    apply: corr_term_impl; eauto.
    move => ? ? [ ? [ ] ]. eauto.
Qed.

Lemma corr_heap_segment_extL R R' H1 H1' H2 :
  corr_heap_segment R R' H1 H2 ->
  ( forall l l', R l l' ->
    forall t,
    nth None H1 l = Some t ->
    nth None H1' l = Some t ) ->
  corr_heap_segment R R' H1' H2.
Proof.
  move => Hcorr Hext ? ? HR.
  move: (Hcorr _ _ HR) =>
    [ ? [ /(Hext _ _ HR) -> ] ]; eauto.
Qed.

Corollary corr_heap_segment_catL fdom fcod H1 H2 Hd :
  corr_heap_segment fdom fcod H1 H2 ->
  corr_heap_segment fdom fcod (H1 ++ Hd) H2.
Proof.
  move => /corr_heap_segment_extL.
  apply => l ? ? ?.
  by move: nth_cat (leqP (size H1) l) => -> [ /(nth_default _) -> | ].
Qed.

Corollary corr_heap_segment_rconsL fdom fcod H1 H2 o :
  corr_heap_segment fdom fcod H1 H2 ->
  corr_heap_segment fdom fcod (rcons H1 o) H2.
Proof. by rewrite -cats1 => /corr_heap_segment_catL. Qed.

Lemma corr_heap_segment_union fdom fdom' fcod H1 H2 :
  corr_heap_segment fdom fcod H1 H2 ->
  corr_heap_segment fdom' fcod H1 H2 ->
  (forall l1 l2, fdom l1 l2 -> forall l2', fdom' l1 l2' -> False) ->
  corr_heap_segment (fun l l' => fdom l l' \/ fdom' l l') fcod H1 H2.
Proof.
  move => Hcorr Hcorr' Hdisj ? ? [ Hf | Hf' ];
  [ move: (Hcorr _ _ Hf) | move: (Hcorr' _ _ Hf') ];
  move => [ ? [ -> [ ? [ -> [ ? | [ ? [ ? [ ? [ ? [ ? [ ? Hcon ] ] ] ] ] ] ] ] ] ] ];
  repeat (eexists; eauto); right; do 6 (eexists; eauto).
  - move => ? [ /Hcon [ ? [ -> ? ] ] | /(Hdisj _ _ Hf) [ ] ].
    repeat (eexists; eauto).
  - move => ? [ /Hdisj /(_ _ Hf') [ ] | /Hcon [ ? [ -> ? ] ] ].
    repeat (eexists; eauto).
Qed.

Lemma corr_heap_iso_heap_comp R S H1 H2 H2' :
  corr_heap R H1 H2 ->
  iso_heap S H2 H2' ->
  (forall l2 t2, nth None H2 l2 = Some t2 -> nth None H2' l2 = Some t2) ->
  corr_heap (fun l1 l2' => R l1 l2' \/ exists l2, R l1 l2 /\ S l2 l2') H1 H2'.
Proof.
  move => Hcorr Hiso Hsur.
  have Hiso' : iso_heap (fun l2 l2' => S l2 l2' \/ l2 = l2' /\ exists l1, R l1 l2) H2 H2'.
  { apply: iso_heap_segment_union; apply: iso_heap_segment_cod.
    - exact: Hiso.
    - eauto.
    - apply: iso_heap_segment_extR.
      + apply: iso_heap_segment_refl.
        apply: corr_heap_segment_wf_heap_segmentR; eauto.
      + eauto.
    - move => ? ? [ -> [ ] ]. eauto. }
  apply (corr_heap_segment_dom (fun l1 l2' => exists l2, R l1 l2 /\ (S l2 l2' \/ l2 = l2' /\ exists l1, R l1 l2))).
  - apply (corr_heap_segment_cod _ (fun l1 l2' => exists l2, R l1 l2 /\ (S l2 l2' \/ l2 = l2' /\ exists l1, R l1 l2))).
    { move => ? ? [ ? [ ] ]
        /Hcorr [ ? [ -> [ ? [ Hnth
          [ Hterm | [ ? [ ? [ Hcbn [ ? [ Hiso'' [ Hterm Hcon ] ] ] ] ] ] ] ] ] ] ]
        /Hiso' [ ? [ Hnth' [ ? [ -> Hterm' ] ] ] ];
      move: Hnth Hnth' => ->; inversion 1; subst;
      repeat eexists.
      - eauto using corr_term_comp.
      - right.
        move: (eval_name_iso_heap _ _ _ _ Hcbn _ _ _ Hterm' Hiso') =>
          [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ].
        do 5 (eexists; eauto).
        { apply: iso_heap_segment_comp; eauto.
          apply: iso_heap_segment_comp.
          - apply: iso_heap_segment_sym. eauto.
          - apply: iso_heap_segment_union; apply: iso_heap_segment_cod.
            + exact: Hiso''.
            + auto.
            + apply: iso_heap_segment_extR.
              * apply: iso_heap_segment_refl.
                apply: corr_heap_segment_wf_heap_segmentR. eauto.
              * move => ? ? ?. apply: eval_name_heap. eauto.
            + eauto. }
        split.
        { apply: corr_term_impl.
          - apply: corr_term_comp; eauto.
          - move => ? ? [ ? [ [ ? | [ ? [ ? ? ] ] ] ? ] ];
            right; repeat (eexists; eauto). }
        move => ? [ ? [ ] ]
          /Hcon [ ? [ Hnth'' ? ] ]
          /Hiso' [ ? [ Hnth''' [ ? [ -> ? ] ] ] ].
        move: Hnth'' Hnth''' => ->. inversion 1. subst.
        repeat (eexists; eauto).
        { apply: corr_term_impl.
          - apply: corr_term_comp; eauto.
            apply: corr_term_comp; eauto.
            apply: corr_term_sym. eauto.
          - move => ? ? [ ? [ [ ? [ ? [ ? [ ? ? ] ] ] ] ? ] ].
            repeat (eexists; eauto). } }
    move => ? ? [ ? [ ? [ ? | [ <- [ ? ? ] ] ] ] ]; eauto.
  - move => ? ? [ ? | [ ? [ ? ? ] ] ]; repeat (eexists; eauto).
Qed.

Corollary corr_heap_extR R H1 H2 H2' :
  corr_heap R H1 H2 ->
  ( forall l2 t,
    nth None H2 l2 = Some t ->
    nth None H2' l2 = Some t ) ->
  corr_heap R H1 H2'.
Proof.
  move => Hcorr Hext.
  apply: corr_heap_segment_dom.
  - apply: corr_heap_segment_cod.
    + apply: corr_heap_iso_heap_comp; eauto.
      apply: iso_heap_segment_extR.
      * apply: iso_heap_segment_refl.
        apply: corr_heap_segment_wf_heap_segmentR; eauto.
      * move => ? ? [ -> [ ] ]. eauto.
    + move => ? ? [ ? | [ ? [ ? [ <- ] ] ] ]; eauto.
  - move => /=. eauto.
Qed.

Corollary corr_heap_catR f H1 H2 Hd :
  corr_heap f H1 H2 ->
  corr_heap f H1 (H2 ++ Hd).
Proof.
  move => /corr_heap_extR.
  apply => l' ?.
  by move: nth_cat (leqP (size H2) l') => -> [ /(nth_default _) -> | ].
Qed.

Corollary corr_heap_rconsR f H1 H2 o :
  corr_heap f H1 H2 ->
  corr_heap f H1 (rcons H2 o).
Proof. by rewrite -cats1 => /corr_heap_catR. Qed.

Theorem eval_need_sound H1 t1 H1' v1 :
  eval_need H1 t1 H1' v1 ->
  forall f H2 t2,
  corr_term f t1 t2 ->
  corr_heap f H1 H2 ->
  exists f' H2' v2,
  eval_name H2 t2 H2' v2 /\
  corr_heap f' H1' H2' /\
  corr_term f' v1 v2 /\
  (forall l1 l2, f l1 l2 -> f' l1 l2).
Proof.
  induction 1; inversion 1; subst => [ Hcorr ].
  - move: (Hcorr _ _ H5) => [ ? [ ] ].
    rewrite H0. inversion 1.
    subst => [ [ ? [ Hnth [ Hterm | [ H2' [ ? [ Hcbn [ g [ ? [ Hterm' ? ] ] ] ] ] ] ] ] ] ].
    + move: (IHeval_need _ _ _ Hterm Hcorr) =>
        [ f' [ ? [ ? [ Hcbn [ Hcorr' [ ? Himpl ] ] ] ] ] ].
      do 5 (eexists; eauto).
      apply (corr_heap_segment_dom (fun l1 l2 => l1 != l /\ f' l1 l2 \/ l1 = l /\ f' l1 l2)).
      { apply: corr_heap_segment_union.
        - apply: corr_heap_segment_extL.
          + apply: corr_heap_segment_dom; eauto.
            by move => ? ? [ ].
          + move => ? ? [ /negPf Hneq ? ] ?.
            rewrite nth_set_nth => /=.
            by rewrite Hneq.
        - move => ? ? [ ? ] Hf'. subst.
          rewrite nth_set_nth => /=.
          have Hiso := corr_heap_segment_iso_heap_segmentR _ _ _ _ Hcorr.
          have Hiso' := corr_heap_segment_iso_heap_segmentR _ _ _ _ Hcorr'.
          move: (Hiso' _ _ (ex_intro _ _ (conj Hf' (Himpl _ _ H5)))) =>
            [ ? [ Hnth' [ ? [ ] ] ] ].
          rewrite Hnth' (eval_name_heap _ _ _ _ Hcbn _ _ Hnth) eqxx.
          inversion 1. subst => [ Hterm' ].
          repeat eexists. right.
          move: (eval_name_iso_heap _ _ _ _ Hcbn _ _ _
            (corr_term_comp _ _ _ _
              (corr_term_comp _ _ _ _ (corr_term_sym _ _ _ Hterm) _ Hterm) _
              (corr_term_sym _ _ _ Hterm'))
            (iso_heap_segment_comp _ _ _ _ _ _ _ 
              (iso_heap_segment_extR _ _ _ _ _ Hiso
                (fun _ _ _ => eval_name_heap _ _ _ _ Hcbn _))
              (iso_heap_segment_sym _ _ _ _ Hiso'))) =>
          [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ].
          do 6 (eexists; eauto).
          + apply: corr_term_impl.
            * apply: corr_term_comp; eauto.
            * move => //=. eauto.
          + move => ? [ ? Hf ].
            move: (Hiso' _ _ (ex_intro _ _ (conj Hf' Hf))) => [ ? [ ] ].
            rewrite Hnth'. inversion 1. subst. eauto.
        - move => ? ? [ /eqP ? ? ] ? [ ]. eauto. }
      move => l1 l2.
      case (@eqP _ l1 l) => /= [ -> | ]; eauto.
    + case: (eval_need_det _ _ _ _ H1 _ _
        (value_eval_need _ _
          (corr_term_valueR _ _ _ Hterm' (eval_name_value _ _ _ _ Hcbn)))) => ? ?. subst.
      do 5 (eexists; eauto).
      { apply: corr_heap_iso_heap_comp; eauto.
        apply: (corr_heap_segment_extL _ _ _ _ _ Hcorr) => l1 ? ? ?.
        move: nth_set_nth (@eqP _ l1 l) => -> /= [ ? | // ].
        subst. by rewrite H0. }
      eauto.
  - move: (IHeval_need1 _ _ _ H6 Hcorr) =>
      [ f' [ H2' [ ? [ ? [ Hcorr0 [ ] ] ] ] ] ].
    inversion 1. subst => [ ? ].
    have Hterm' : corr_term
      (fun l l' => f' l l' \/ l = size H' /\ l' = size H2')
      (subst (scons (Loc (size H')) Var) t0)
      (subst (scons (Loc (size H2')) Var) t').
    { apply: corr_term_subst => [ | [ | ? ] ] /=;
      eauto using corr_term_impl. }
    have Hcorr' : corr_heap
      (fun l l' => f' l l' \/ l = size H' /\ l' = size H2')
      (rcons H' (Some t2)) (rcons H2' (Some t2')).
    { apply: corr_heap_segment_union.
      - apply: corr_heap_segment_cod; eauto.
        apply: corr_heap_segment_rconsL.
        by apply: corr_heap_rconsR.
      - apply: iso_heap_segment_corr_heap_segment => ? ? [ -> -> ].
        rewrite !nth_rcons !ltnn !eqxx.
        repeat eexists. eauto using corr_term_impl.
      - move => ? ? Hf' ? [ ? ? ]. subst.
        by move: ltnn (corr_heap_segment_boundL _ _ _ _ Hcorr0 _ _ Hf') => ->. }
    move: (IHeval_need2 _ _ _ Hterm' Hcorr') =>
      [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ].
    repeat (eexists; eauto).
  - repeat (eexists; eauto).
  - have Hterm' : corr_term
      (fun l l' => f l l' \/
        exists n, n < size ts /\ l = size H + n /\ l' = size H2 + n)
      (subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var) t)
      (subst (scat (mkseq (Loc \o addn (size H2)) (size ts')) Var) t').
    { apply: corr_term_subst => [ | x ];
      eauto using corr_term_impl.
      rewrite !nth_scat H5.
      case (leqP (size ts') x) => ?.
      - by rewrite !nth_default ?size_mkseq.
      - rewrite !nth_mkseq => /=; eauto 6. }
    have Hcorr' : corr_heap
      (fun l l' => f l l' \/
        exists n, n < size ts /\ l = size H + n /\ l' = size H2 + n)
      (H ++ map (@Some _ \o
         subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var)) ts)
      (H2 ++ map (@Some _ \o
         subst (scat (mkseq (Loc \o addn (size H2)) (size ts')) Var)) ts').
    { apply: corr_heap_segment_union.
      - apply: corr_heap_segment_cod; eauto.
        apply: corr_heap_segment_catL.
        by apply: corr_heap_catR.
      - apply: iso_heap_segment_corr_heap_segment => ? ? [ x [ ? [ -> -> ] ] ].
        rewrite !nth_cat !ltnNge !leq_addr !addKn !(nth_map (Var 0)); try congruence.
        repeat eexists.
        apply: corr_term_subst => [ | y ];
        eauto using corr_term_impl.
        rewrite !nth_scat H5.
        case (leqP (size ts') y) => ?.
        + by rewrite !nth_default ?size_mkseq.
        + rewrite !nth_mkseq => /=; eauto 6.
      - move => ? ? Hf ? [ ? [ ? [ ? ? ] ] ]. subst.
        move: (corr_heap_segment_boundL _ _ _ _ Hcorr _ _ Hf).
        by rewrite ltnNge leq_addr. }
    move: (IHeval_need _ _ _ Hterm' Hcorr') =>
      [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ].
    repeat (eexists; eauto).
Qed.

Theorem diverge_need_sound :
  forall H1 t1,
  diverge_need H1 t1 ->
  forall f H2 t2,
  corr_term f t1 t2 ->
  corr_heap f H1 H2 ->
  diverge_name H2 t2.
Proof.
  cofix diverge_need_sound.
  inversion 1; subst => [ f H2_ ? ];
  inversion 1; subst => [ Hcorr ].
  - move: (Hcorr _ _ H5) => [ ? [ ] ].
    rewrite H2. inversion 1.
    subst => [ [ ? [ ? [ Hterm | [ ? [ ? [ Hcbn [ ? [ ? [ Hterm ? ] ] ] ] ] ] ] ] ] ].
    + econstructor; eauto.
    + case: (value_diverge_need_disjoint _ _
        (corr_term_valueR _ _ _ Hterm (eval_name_value _ _ _ _ Hcbn)) H3).
  - apply: diverge_name_appL; eauto.
  - move: (eval_need_sound _ _ _ _ H2 _ _ _ H6 Hcorr) =>
      [ f' [ H2' [ ? [ ? [ Hcorr0 [ ] ] ] ] ] ].
    inversion 1. subst => [ ? ].
    have Hterm' : corr_term
      (fun l l' => f' l l' \/ l = size H' /\ l' = size H2')
      (subst (scons (Loc (size H')) Var) t0)
      (subst (scons (Loc (size H2')) Var) t').
    { apply: corr_term_subst => [ | [ | ? ] ] /=;
      eauto using corr_term_impl. }
    have Hcorr' : corr_heap
      (fun l l' => f' l l' \/ l = size H' /\ l' = size H2')
      (rcons H' (Some t3)) (rcons H2' (Some t2')).
    { apply: corr_heap_segment_union.
      - apply: corr_heap_segment_cod; eauto.
        apply: corr_heap_segment_rconsL.
        by apply: corr_heap_rconsR.
      - apply: iso_heap_segment_corr_heap_segment => ? ? [ -> -> ].
        rewrite !nth_rcons !ltnn !eqxx.
        repeat eexists. eauto using corr_term_impl.
      - move => ? ? Hf' ? [ ? ? ]. subst.
        by move: ltnn (corr_heap_segment_boundL _ _ _ _ Hcorr0 _ _ Hf') => ->. }
    apply: diverge_name_appabs; eauto.
  - have Hterm' : corr_term
      (fun l l' => f l l' \/
        exists n, n < size ts /\ l = size H1 + n /\ l' = size H2_ + n)
      (subst (scat (mkseq (Loc \o addn (size H1)) (size ts)) Var) t)
      (subst (scat (mkseq (Loc \o addn (size H2_)) (size ts')) Var) t').
    { apply: corr_term_subst => [ | x ];
      eauto using corr_term_impl.
      rewrite !nth_scat H5.
      case (leqP (size ts') x) => ?.
      - by rewrite !nth_default ?size_mkseq.
      - rewrite !nth_mkseq => /=; eauto 6. }
    have Hcorr' : corr_heap
      (fun l l' => f l l' \/
        exists n, n < size ts /\ l = size H1 + n /\ l' = size H2_ + n)
      (H1 ++ map (@Some _ \o
         subst (scat (mkseq (Loc \o addn (size H1)) (size ts)) Var)) ts)
      (H2_ ++ map (@Some _ \o
         subst (scat (mkseq (Loc \o addn (size H2_)) (size ts')) Var)) ts').
    { apply: corr_heap_segment_union.
      - apply: corr_heap_segment_cod; eauto.
        apply: corr_heap_segment_catL.
        by apply: corr_heap_catR.
      - apply: iso_heap_segment_corr_heap_segment => ? ? [ x [ ? [ -> -> ] ] ].
        rewrite !nth_cat !ltnNge !leq_addr !addKn !(nth_map (Var 0)); try congruence.
        repeat eexists. 
        apply: corr_term_subst => [ | y ];
        eauto using corr_term_impl.
        rewrite !nth_scat H5.
        case (leqP (size ts') y) => ?.
        + by rewrite !nth_default ?size_mkseq.
        + rewrite !nth_mkseq => /=; eauto 6.
      - move => ? ? Hf ? [ ? [ ? [ ? ? ] ] ]. subst.
        move: (corr_heap_segment_boundL _ _ _ _ Hcorr _ _ Hf).
        by rewrite ltnNge leq_addr. }
    apply: diverge_name_let. eauto.
Qed.

Theorem eval_need_complete H2 t2 H2' v2 :
  eval_name H2 t2 H2' v2 ->
  forall f H1 t1,
  corr_term f t1 t2 ->
  corr_heap f H1 H2 ->
  exists f' H1' v1,
  eval_need H1 t1 H1' v1 /\
  corr_heap f' H1' H2' /\
  corr_term f' v1 v2 /\
  (forall l1 l2, f l1 l2 -> f' l1 l2).
Proof.
  induction 1; inversion 1; subst => [ Hcorr ].
  - move: (Hcorr _ _ H6) => [ ? [ Hnth [ ? [ ] ] ] ].
    rewrite H0. inversion 1.
    subst => [ [ Hterm | [ H2' [ ? [ Hcbn [ g [ ? [ Hterm' ? ] ] ] ] ] ] ] ].
    + move: (IHeval_name _ _ _ Hterm Hcorr) =>
        [ f' [ ? [ ? [ Hcbn [ Hcorr' [ ? Himpl ] ] ] ] ] ].
      do 5 (eexists; eauto).
      apply (corr_heap_segment_dom (fun l1 l2 => l1 != l0 /\ f' l1 l2 \/ l1 = l0 /\ f' l1 l2)).
      { apply: corr_heap_segment_union.
        - apply: corr_heap_segment_extL.
          + apply: corr_heap_segment_dom; eauto.
            by move => ? ? [ ].
          + move => ? ? [ /negPf Hneq ? ] ?.
            rewrite nth_set_nth => /=.
            by rewrite Hneq.
        - move => ? ? [ ? ] Hf'. subst.
          rewrite nth_set_nth => /=.
          have Hiso := corr_heap_segment_iso_heap_segmentR _ _ _ _ Hcorr.
          have Hiso' := corr_heap_segment_iso_heap_segmentR _ _ _ _ Hcorr'.
          move: (Hiso' _ _ (ex_intro _ _ (conj Hf' (Himpl _ _ H6)))) =>
            [ ? [ Hnth' [ ? [ ] ] ] ].
          rewrite Hnth' (eval_name_heap _ _ _ _ H1 _ _ H0) eqxx.
          inversion 1. subst => [ Hterm' ].
          repeat eexists. right.
          move: (eval_name_iso_heap _ _ _ _ H1 _ _ _
            (corr_term_comp _ _ _ _
              (corr_term_comp _ _ _ _ (corr_term_sym _ _ _ Hterm) _ Hterm) _
              (corr_term_sym _ _ _ Hterm'))
            (iso_heap_segment_comp _ _ _ _ _ _ _ 
              (iso_heap_segment_extR _ _ _ _ _ Hiso
                (fun _ _ _ => eval_name_heap _ _ _ _ H1 _))
              (iso_heap_segment_sym _ _ _ _ Hiso'))) =>
          [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ].
          do 6 (eexists; eauto).
          + apply: corr_term_impl.
            * apply: corr_term_comp; eauto.
            * move => //=. eauto.
          + move => ? [ ? Hf ].
            move: (Hiso' _ _ (ex_intro _ _ (conj Hf' Hf))) => [ ? [ ] ].
            rewrite Hnth'. inversion 1. subst. eauto.
        - move => ? ? [ /eqP ? ? ] ? [ ]. eauto. }
      move => l1 l2.
      case (@eqP _ l1 l0) => /= [ -> | ]; eauto.
    + case: (eval_name_det _ _ _ _ H1 _ _ Hcbn) => ? ?. subst.
      do 4 (eexists; eauto).
      { econstructor; eauto.
        apply: value_eval_need.
        apply: corr_term_valueR; eauto.
        apply: eval_name_value. eauto. }
      split.
      { apply: corr_heap_iso_heap_comp; eauto.
        apply: (corr_heap_segment_extL _ _ _ _ _ Hcorr) => l1 ? ? ?.
        move: nth_set_nth (@eqP _ l1 l0) => -> /= [ ? | // ].
        subst. by rewrite Hnth. }
      eauto.
  - move: (IHeval_name1 _ _ _ H7 Hcorr) =>
      [ f' [ H1' [ ? [ ? [ Hcorr0 [ ] ] ] ] ] ].
    inversion 1. subst => [ ? ].
    have Hterm' : corr_term
      (fun l l' => f' l l' \/ l = size H1' /\ l' = size H')
      (subst (scons (Loc (size H1')) Var) t)
      (subst (scons (Loc (size H')) Var) t0).
    { apply: corr_term_subst => [ | [ | ? ] ] /=;
      eauto using corr_term_impl. }
    have Hcorr' : corr_heap
      (fun l l' => f' l l' \/ l = size H1' /\ l' = size H')
      (rcons H1' (Some t5)) (rcons H' (Some t2)).
    { apply: corr_heap_segment_union.
      - apply: corr_heap_segment_cod; eauto.
        apply: corr_heap_segment_rconsL.
        by apply: corr_heap_rconsR.
      - apply: iso_heap_segment_corr_heap_segment => ? ? [ -> -> ].
        rewrite !nth_rcons !ltnn !eqxx.
        repeat eexists. eauto using corr_term_impl.
      - move => ? ? Hf' ? [ ? ? ]. subst.
        by move: ltnn (corr_heap_segment_boundL _ _ _ _ Hcorr0 _ _ Hf') => ->. }
    move: (IHeval_name2 _ _ _ Hterm' Hcorr') =>
      [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ].
    repeat (eexists; eauto).
  - repeat (eexists; eauto).
  - have Hterm' : corr_term
      (fun l l' => f l l' \/
        exists n, n < size ts0 /\ l = size H1 + n /\ l' = size H + n)
      (subst (scat (mkseq (Loc \o addn (size H1)) (size ts0)) Var) t0)
      (subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var) t).
    { apply: corr_term_subst => [ | x ];
      eauto using corr_term_impl.
      rewrite !nth_scat H5.
      case (leqP (size ts) x) => ?.
      - by rewrite !nth_default ?size_mkseq.
      - rewrite !nth_mkseq => /=; eauto 6. }
    have Hcorr' : corr_heap
      (fun l l' => f l l' \/
        exists n, n < size ts0 /\ l = size H1 + n /\ l' = size H + n)
      (H1 ++ map (@Some _ \o
         subst (scat (mkseq (Loc \o addn (size H1)) (size ts0)) Var)) ts0)
      (H ++ map (@Some _ \o
         subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var)) ts).
    { apply: corr_heap_segment_union.
      - apply: corr_heap_segment_cod; eauto.
        apply: corr_heap_segment_catL.
        by apply: corr_heap_catR.
      - apply: iso_heap_segment_corr_heap_segment => ? ? [ x [ ? [ -> -> ] ] ].
        rewrite !nth_cat !ltnNge !leq_addr !addKn !(nth_map (Var 0)); try congruence.
        repeat eexists.
        apply: corr_term_subst => [ | y ];
        eauto using corr_term_impl.
        rewrite !nth_scat H5.
        case (leqP (size ts) y) => ?.
        + by rewrite !nth_default ?size_mkseq.
        + rewrite !nth_mkseq => /=; eauto 6.
      - move => ? ? Hf ? [ ? [ ? [ ? ? ] ] ]. subst.
        move: (corr_heap_segment_boundL _ _ _ _ Hcorr _ _ Hf).
        by rewrite ltnNge leq_addr. }
    move: (IHeval_name _ _ _ Hterm' Hcorr') =>
      [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ].
    repeat (eexists; eauto).
Qed.

Theorem diverge_need_complete :
  forall H2 t2,
  diverge_name H2 t2 ->
  forall f H1 t1,
  corr_term f t1 t2 ->
  corr_heap f H1 H2 ->
  diverge_need H1 t1.
Proof.
  cofix diverge_need_complete.
  inversion 1; subst => [ f H1_ ? ];
  inversion 1; subst => [ Hcorr ].
  - move: (Hcorr _ _ H6) => [ ? [ ? [ ? [ ] ] ] ].
    rewrite H1. inversion 1.
    subst => [ [ ? | [ ? [ ? [ Hcbn [ ? [ ? [ ? ? ] ] ] ] ] ] ] ].
    + econstructor; eauto.
    + case: (eval_name_diverge_name_disjoint _ _ _ _ Hcbn H3).
  - apply: diverge_need_appL; eauto.
  - move: (eval_need_complete _ _ _ _ H1 _ _ _ H7 Hcorr) =>
      [ f' [ H1' [ ? [ ? [ Hcorr0 [ ] ] ] ] ] ].
    inversion 1. subst => [ ? ].
    have Hterm' : corr_term
      (fun l l' => f' l l' \/ l = size H1' /\ l' = size H')
      (subst (scons (Loc (size H1')) Var) t)
      (subst (scons (Loc (size H')) Var) t0).
    { apply: corr_term_subst => [ | [ | ? ] /= ];
      eauto using corr_term_impl. }
    have Hcorr' : corr_heap
      (fun l l' => f' l l' \/ l = size H1' /\ l' = size H')
      (rcons H1' (Some t4)) (rcons H' (Some t3)).
    { apply: corr_heap_segment_union.
      - apply: corr_heap_segment_cod; eauto.
        apply: corr_heap_segment_rconsL.
        by apply: corr_heap_rconsR.
      - apply: iso_heap_segment_corr_heap_segment => ? ? [ -> -> ].
        rewrite !nth_rcons !ltnn !eqxx.
        repeat eexists. eauto using corr_term_impl.
      - move => ? ? Hf' ? [ ? ? ]. subst.
        by move: ltnn (corr_heap_segment_boundL _ _ _ _ Hcorr0 _ _ Hf') => ->. }
    apply: diverge_need_appabs; eauto.
  - have Hterm' : corr_term
      (fun l l' => f l l' \/
        exists n, n < size ts0 /\ l = size H1_ + n /\ l' = size H2 + n)
      (subst (scat (mkseq (Loc \o addn (size H1_)) (size ts0)) Var) t0)
      (subst (scat (mkseq (Loc \o addn (size H2)) (size ts)) Var) t).
    { apply: corr_term_subst => [ | x ];
      eauto using corr_term_impl.
      rewrite !nth_scat H5.
      case (leqP (size ts) x) => ?.
      - by rewrite !nth_default ?size_mkseq.
      - rewrite !nth_mkseq => /=; eauto 6. }
    have Hcorr' : corr_heap
      (fun l l' => f l l' \/
        exists n, n < size ts0 /\ l = size H1_ + n /\ l' = size H2 + n)
      (H1_ ++ map (@Some _ \o
         subst (scat (mkseq (Loc \o addn (size H1_)) (size ts0)) Var)) ts0)
      (H2 ++ map (@Some _ \o
         subst (scat (mkseq (Loc \o addn (size H2)) (size ts)) Var)) ts).
    { apply: corr_heap_segment_union.
      - apply: corr_heap_segment_cod; eauto.
        apply: corr_heap_segment_catL.
        by apply: corr_heap_catR.
      - apply: iso_heap_segment_corr_heap_segment => ? ? [ x [ ? [ -> -> ] ] ].
        rewrite !nth_cat !ltnNge !leq_addr !addKn !(nth_map (Var 0)); try congruence.
        repeat eexists.
        apply: corr_term_subst => [ | y ];
        eauto using corr_term_impl.
        rewrite !nth_scat H5.
        case (leqP (size ts) y) => ?.
        + by rewrite !nth_default ?size_mkseq.
        + rewrite !nth_mkseq => /=; eauto 6.
      - move => ? ? Hf ? [ ? [ ? [ ? ? ] ] ]. subst.
        move: (corr_heap_segment_boundL _ _ _ _ Hcorr _ _ Hf).
        by rewrite ltnNge leq_addr. }
    apply: diverge_need_let. eauto.
Qed.
