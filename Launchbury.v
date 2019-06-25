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

Definition corr_heap_segment (f f' : nat -> nat -> Prop) H1 H2 :=
  forall l1 l2, f l1 l2 ->
  exists t1, nth None H1 l1 = Some t1 /\
  exists t2, nth None H2 l2 = Some t2 /\
  ( corr_term f' t1 t2 \/
    wf_term (fun l => exists l', f' l l') t1 /\
    exists H1' v1,
    eval_name H1 t1 H1' v1 /\
    exists g,
    iso_heap g H1' H1 /\
    corr_term (fun l0 l2 => exists l1, g l0 l1 /\ f' l1 l2) v1 t2 ).

Definition corr_heap f := corr_heap_segment f f.

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

Corollary corr_heap_segemtn_refl p p' H :
  wf_heap_segment p p' H ->
  corr_heap_segment
    (fun l l' => l = l' /\ p l)
    (fun l l' => l = l' /\ p' l) H H.
Proof. by move => /iso_heap_segment_refl /iso_heap_segment_corr_heap_segment. Qed.

Lemma corr_heap_segment_union fdom fdom' fcod H1 H2 :
  corr_heap_segment fdom fcod H1 H2 ->
  corr_heap_segment fdom' fcod H1 H2 ->
  corr_heap_segment (fun l l' => fdom l l' \/ fdom' l l') fcod H1 H2.
Proof. by move => Hcorr Hcorr' ? ? [ /Hcorr | /Hcorr' ]. Qed.

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
  move => Hcorr ? [ ? /Hcorr [ ? [ -> [ ? [ ? [ | [ ] ] ] ] ] ] ];
  eauto using corr_term_wf_termL.
Qed.

Lemma corr_heap_segment_wf_heap_segmentR f f' H H' :
  corr_heap_segment f f' H H' ->
  wf_heap_segment (fun l' => exists l, f l l') (fun l' => exists l, f' l l') H'.
Proof.
  move => Hcorr ? [ ? /Hcorr [ ? [ ? [ ? [ -> [ ? | [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ] ] ] ] ] ] ];
  repeat eexists; (apply: wf_term_impl; [ apply: corr_term_wf_termR | ]); eauto.
  move => ? [ ? [ ? [ ] ] ]. eauto.
Qed.

Lemma corr_heap_segment_dom (fdom fdom' fcod : nat -> nat -> Prop) H H' :
  corr_heap_segment fdom fcod H H' ->
  (forall l l', fdom' l l' -> fdom l l') ->
  corr_heap_segment fdom' fcod H H'.
Proof. by move => Hcorr Hdom ? ? /Hdom /Hcorr. Qed.

Lemma corr_heap_segment_cod (fdom fcod fcod' : nat -> nat -> Prop) H H' :
  corr_heap_segment fdom fcod H H' ->
  (forall l l', fcod l l' -> fcod' l l') ->
  corr_heap_segment fdom fcod' H H'.
Proof.
  move => Hcorr Hcod ? ? /Hcorr [ ? [ -> [ ? [ -> [ ? | [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ] ] ] ] ] ];
  repeat eexists.
  - eauto using corr_term_impl.
  - right. split.
    + apply: wf_term_impl; eauto.
      move => ? [ ]. eauto.
    + repeat (eexists; eauto).
      apply: corr_term_impl; eauto.
      move => ? ? [ ? [ ] ]. eauto.
Qed.

Lemma corr_heap_segment_extR fdom fcod H1 H2 H2' :
  corr_heap_segment fdom fcod H1 H2 ->
  ( forall l l', fdom l l' ->
    forall t,
    nth None H2 l' = Some t ->
    nth None H2' l' = Some t ) ->
  corr_heap_segment fdom fcod H1 H2'.
Proof.
  move => Hcorr Hext ? ? Hf.
  move: (Hcorr _ _ Hf) =>
    [ ? [ -> [ ? [ /(Hext _ _ Hf) -> ] ] ] ] 
    [ ? | [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ] ];
  repeat (eexists; eauto).
  right. repeat (eexists; eauto).
Qed.

Corollary corr_heap_segment_catR fdom fcod H1 H2 Hd :
  corr_heap_segment fdom fcod H1 H2 ->
  corr_heap_segment fdom fcod H1 (H2 ++ Hd).
Proof.
  move => /corr_heap_segment_extR.
  apply => ? l' ? ?.
  by move: nth_cat (leqP (size H2) l') => -> [ /(nth_default _) -> | ].
Qed.

Corollary corr_heap_segment_rconsR fdom fcod H1 H2 o :
  corr_heap_segment fdom fcod H1 H2 ->
  corr_heap_segment fdom fcod H1 (rcons H2 o).
Proof. by rewrite -cats1 => /corr_heap_segment_catR. Qed.

Lemma iso_heap_corr_heap_segment_comp (f fdom fcod : nat -> nat -> Prop) H H' H'' :
  iso_heap f H H' ->
  (forall l' l'', fcod l' l'' -> f l' l') ->
  corr_heap_segment fdom fcod H' H'' ->
  corr_heap_segment
    (fun l l'' => exists l', f l l' /\ fdom l' l'')
    (fun l l'' => exists l', f l l' /\ fcod l' l'') H H''.
Proof.
  move => Hiso Hsur Hcorr ? ? [ ? [ ] ] /Hiso [ ? [ -> [ ? [ Hnth Hterm ] ] ] ]
    /Hcorr [ ? [ Hnth' [ ? [ -> [ Hterm' | [ ? [ ? [ ? [ Hcbn [ ? [ Hiso' Hterm' ] ] ] ] ] ] ] ] ] ] ];
  move: Hnth Hnth' => ->; inversion 1; subst;
  repeat eexists.
  - eauto using corr_term_comp.
  - right. split.
    + apply: wf_term_impl.
      { apply: corr_term_wf_termL.
        apply: corr_term_comp; eauto.
        apply: corr_term_refl. eauto. }
      move => ? [ ? [ ? [ ? [ ? [ ] ] ] ] ]. subst. eauto.
    + move: (eval_name_iso_heap _ _ _ _ Hcbn _ _ _ Hterm Hiso) =>
        [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ].
      { do 5 (eexists; eauto).
        - apply: iso_heap_segment_comp; eauto.
          apply: iso_heap_segment_comp; eauto.
          apply: iso_heap_segment_sym. eauto.
        - apply: corr_term_impl.
          + apply: corr_term_comp; eauto.
          + move => ? ? [ ? [ ? [ ? [ ? ? ] ] ] ].
            repeat (eexists; eauto). }
Qed.

Corollary corr_heap_extL f H1 H1' H2 :
  corr_heap f H1 H2 ->
  ( forall l l', f l l' ->
    forall t,
    nth None H1 l = Some t ->
    nth None H1' l = Some t ) ->
  corr_heap f H1' H2.
Proof.
  move => Hcorr Hext.
  apply: corr_heap_segment_dom.
  - apply: corr_heap_segment_cod.
    + apply: iso_heap_corr_heap_segment_comp; eauto.
      * { apply: iso_heap_segment_extL.
          - apply: iso_heap_segment_refl.
            apply: corr_heap_segment_wf_heap_segmentL; eauto.
          - move => ? ? [ -> [ ] ]. eauto. }
      * move => /=. eauto.
    + by move => ? ? [ ? [ [ -> ] ] ].
  - move => /=. eauto.
Qed.

Corollary corr_heap_catL f H1 H2 Hd :
  corr_heap f H1 H2 ->
  corr_heap f (H1 ++ Hd) H2.
Proof.
  move => /corr_heap_extL.
  apply => l ? ? ?.
  by move: nth_cat (leqP (size H1) l) => -> [ /(nth_default _) -> | ].
Qed.

Corollary corr_heap_rconsL f H1 H2 o :
  corr_heap f H1 H2 ->
  corr_heap f (rcons H1 o) H2.
Proof. by rewrite -cats1 => /corr_heap_catL. Qed.

Theorem eval_need_sound H2 t2 H2' v2 :
  eval_need H2 t2 H2' v2 ->
  forall f H1 t1,
  corr_term f t1 t2 ->
  corr_heap f H1 H2 ->
  iso_heap (fun l1 l1' => exists l2, f l1 l2 /\ f l1' l2) H1 H1 ->
  exists f' H1' v1,
  eval_name H1 t1 H1' v1 /\
  corr_heap f' H1' H2' /\
  iso_heap (fun l1 l1' => exists l2, f' l1 l2 /\ f' l1' l2) H1' H1' /\
  corr_term f' v1 v2 /\
  (forall l1 l2, f l1 l2 -> f' l1 l2).
Proof.
  induction 1; inversion 1; subst => [ Hcorr Hiso ].
  - move: (Hcorr _ _ H6) => [ ? [ Hnth [ ? [ ] ] ] ].
    rewrite H0. inversion 1.
    subst => [ [ Hterm | [ ? [ H1' [ ? [ Hcbn [ g [ ? Hterm' ] ] ] ] ] ] ] ].
    + move: (IHeval_need _ _ _ Hterm Hcorr Hiso) =>
        [ f' [ ? [ ? [ Hcbn [ Hcorr' [ Hiso' [ ? Himpl ] ] ] ] ] ] ].
      do 5 (eexists; eauto).
      apply (corr_heap_segment_dom (fun l0 l' => l' != l /\ f' l0 l' \/ l' = l /\ f' l0 l')).
      { apply: corr_heap_segment_union.
        - apply: corr_heap_segment_extR.
          + apply: corr_heap_segment_dom; eauto.
            by move => ? ? [ ].
          + move => ? ? [ /negPf Hneq ? ] ?.
            rewrite nth_set_nth => /=.
            by rewrite Hneq.
        - move => ? ? [ ? ] Hf'. subst.
          rewrite nth_set_nth => /=.
          move: (Hiso' _ _ (ex_intro _ _ (conj Hf' (Himpl _ _ H6)))) =>
            [ ? [ -> [ ? [ ] ] ] ].
          rewrite (eval_name_heap _ _ _ _ Hcbn _ _ Hnth) eqxx.
          inversion 1. subst => [ Hterm' ].
          repeat eexists. right. split.
          + apply: wf_term_impl.
            * apply: corr_term_wf_termL; eauto.
            * move => ? [ ? [ ? [ ] ] ]. eauto.
          + move: (eval_name_iso_heap _ _ _ _ Hcbn _ _ _
              (corr_term_comp _ _ _ _ Hterm' _
                (corr_term_comp _ _ _ _ Hterm _ (corr_term_sym _ _ _ Hterm)))
              (iso_heap_segment_comp _ _ _ _ _ _ _ Hiso'
                (iso_heap_segment_extL _ _ _ _ _ Hiso
                  (fun _ _ _ => eval_name_heap _ _ _ _ Hcbn _)))) =>
              [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ].
            repeat (eexists; eauto using corr_term_comp). }
      move => ? l'.
      case (@eqP _ l' l) => /= [ -> | ]; eauto.
    + case: (eval_need_det _ _ _ _ H1 _ _
        (value_eval_need _ _
          (corr_term_valueL _ _ _ Hterm' (eval_name_value _ _ _ _ Hcbn)))) => ? ?. subst.
      have Hiso' : iso_heap (fun l l' => g l l' \/ l = l' /\ exists l', f l l') H1' H2.
      { apply: iso_heap_segment_union.
        - apply: iso_heap_segment_cod; eauto.
        - apply: iso_heap_segment_extL.
          + apply: iso_heap_segment_cod.
            * apply: iso_heap_segment_refl.
              apply: corr_heap_segment_wf_heap_segmentL. eauto.
            * eauto.
          + move => ? ? ?. apply: eval_name_heap. eauto. }
      do 5 (eexists; eauto).
      { apply: (iso_heap_corr_heap_segment_comp _ f f _ _ _ Hiso'); eauto.
        apply: (corr_heap_segment_extR _ _ _ _ _ Hcorr) => ? l' ? ?.
        move: nth_set_nth (@eqP _ l' l) => -> /= [ ? | // ].
        subst. by rewrite H0. }
      split.
      { apply: iso_heap_segment_dom.
        - apply: iso_heap_segment_cod.
          + apply: iso_heap_segment_comp; eauto.
            apply: iso_heap_segment_sym.
            apply: iso_heap_segment_comp; eauto.
          + move => ? ?
              [ ? [ ] ] [ ? | [ -> [ ? ? ] ] ]
              [ ? [ ] ] [ ? | [ -> [ ? ? ] ] ] [ ? [ ? ? ] ];
            repeat (eexists; eauto).
        - move => ? ? [ ? [ ] ]
            [ ? [ ] ] [ ? | [ -> [ ? ? ] ] ] ?
            [ ? [ ] ] [ ? | [ -> [ ? ? ] ] ] ?;
          repeat (rewrite -?plus_n_O; eexists; eauto). }
      split.
      { apply: corr_term_impl; eauto.
        move => ? ? [ ? [ ] ]. eauto. }
      eauto 6.
  - move: (IHeval_need1 _ _ _ H7 Hcorr Hiso) =>
      [ f' [ H1' [ ? [ ? [ Hcorr0 [ ? [ ] ] ] ] ] ] ].
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
        apply: corr_heap_rconsL.
        by apply: corr_heap_segment_rconsR.
      - apply: iso_heap_segment_corr_heap_segment => ? ? [ -> -> ].
        rewrite !nth_rcons !ltnn !eqxx.
        repeat eexists. eauto using corr_term_impl. }
    have Hiso' : iso_heap
      (fun l l'' => exists l',
        (f' l l' \/ l = size H1' /\ l' = size H') /\
        (f' l'' l' \/ l'' = size H1' /\ l' = size H'))
      (rcons H1' (Some t5)) (rcons H1' (Some t5)).
    { apply: (iso_heap_segment_dom (fun l l'' =>
        (exists l', f' l l' /\ f' l'' l') \/
        l = size H1' /\ l'' = size H1')).
      - apply: iso_heap_segment_union => [ | ? ? [ -> -> ] ].
        + apply: iso_heap_segment_rconsL.
          apply: iso_heap_segment_rconsR.
          apply: iso_heap_segment_cod; eauto.
          move => ? ? [ ? [ ] ]. eauto.
        + rewrite !nth_rcons !ltnn !eqxx.
          repeat eexists.
          apply: corr_term_impl.
          * apply: corr_term_comp; eauto.
            apply: corr_term_sym; eauto.
          * move => ? ? [ ? [ ] ]. eauto 7.
      - move => ? ? [ ? [ [ Hf | [ ? ? ] ] [ Hf' | [ ? ? ] ] ] ]; subst; eauto.
        + move: (corr_heap_segment_boundR _ _ _ _ Hcorr0 _ _ Hf).
          by rewrite ltnn.
        + move: (corr_heap_segment_boundR _ _ _ _ Hcorr0 _ _ Hf').
          by rewrite ltnn. }
    move: (IHeval_need2 _ _ _ Hterm' Hcorr' Hiso') =>
      [ ? [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ] ].
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
        apply: corr_heap_catL.
        by apply: corr_heap_segment_catR.
      - apply: iso_heap_segment_corr_heap_segment => ? ? [ x [ ? [ -> -> ] ] ].
        rewrite !nth_cat !ltnNge !leq_addr !addKn !(nth_map (Var 0)); try congruence.
        repeat eexists.
        apply: corr_term_subst => [ | y ];
        eauto using corr_term_impl.
        rewrite !nth_scat H5.
        case (leqP (size ts) y) => ?.
        + by rewrite !nth_default ?size_mkseq.
        + rewrite !nth_mkseq => /=; eauto 6. }
    have Hiso' : iso_heap
      (fun l l'' => exists l',
        (f l l' \/ exists n, n < size ts0 /\ l = size H1 + n /\ l' = size H + n) /\
        (f l'' l' \/ exists n, n < size ts0 /\ l'' = size H1 + n /\ l' = size H + n))
      (H1 ++ map (@Some _ \o
         subst (scat (mkseq (Loc \o addn (size H1)) (size ts0)) Var)) ts0)
      (H1 ++ map (@Some _ \o
         subst (scat (mkseq (Loc \o addn (size H1)) (size ts0)) Var)) ts0).
    { apply: (iso_heap_segment_dom (fun l l'' =>
        (exists l', f l l' /\ f l'' l') \/
        (exists n, n < size ts0 /\ l = size H1 + n /\ l'' = size H1 + n))).
      - apply: iso_heap_segment_union => [ | ? ? [ x [ ? [ -> -> ] ] ] ].
        + apply: iso_heap_segment_catL.
          apply: iso_heap_segment_catR.
          apply: iso_heap_segment_cod; eauto.
          move => ? ? [ ? [ ] ]. eauto.
        + rewrite !nth_cat !ltnNge !leq_addr !addKn !(nth_map (Var 0)); try congruence.
          repeat eexists.
          apply: corr_term_subst => [ | y ].
          * apply: corr_term_comp; [ | apply: corr_term_sym ];
            eauto using corr_term_impl.
          * rewrite nth_scat.
            { case (leqP (size ts0) y) => ?.
              - by rewrite nth_default ?size_mkseq.
              - rewrite !nth_mkseq => //=;
                repeat (econstructor; eauto). }
      - move => ? ? [ ? [ ] ]
          [ Hf | [ ? [ ? [ ? ? ] ] ] ]
          [ Hf' | [ ? [ ? [ ? Heq ] ] ] ]; subst; eauto.
        + move: (corr_heap_segment_boundR _ _ _ _ Hcorr _ _ Hf).
          by rewrite ltnNge leq_addr.
        + move: (corr_heap_segment_boundR _ _ _ _ Hcorr _ _ Hf').
          by rewrite ltnNge leq_addr.
        + rewrite (addnI Heq). eauto. }
    move: (IHeval_need _ _ _ Hterm' Hcorr' Hiso') =>
      [ ? [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ] ].
    repeat (eexists; eauto).
Qed.

Theorem diverge_need_sound :
  forall H2 t2,
  diverge_need H2 t2 ->
  forall f H1 t1,
  corr_term f t1 t2 ->
  corr_heap f H1 H2 ->
  iso_heap (fun l1 l1' => exists l2, f l1 l2 /\ f l1' l2) H1 H1 ->
  diverge_name H1 t1.
Proof.
  cofix diverge_need_sound.
  inversion 1; subst => [ f H1_ ? ];
  inversion 1; subst => [ Hcorr Hiso ].
  - move: (Hcorr _ _ H6) => [ ? [ ? [ ? [ ] ] ] ].
    rewrite H1. inversion 1.
    subst => [ [ Hterm | [ ? [ ? [ ? [ Hcbn [ ? [ ? Hterm ] ] ] ] ] ] ] ].
    + econstructor; eauto.
    + case: (value_diverge_need_disjoint _ _
        (corr_term_valueL _ _ _ Hterm (eval_name_value _ _ _ _ Hcbn)) H3).
  - apply: diverge_name_appL; eauto.
  - move: (eval_need_sound _ _ _ _ H1 _ _ _ H7 Hcorr Hiso) =>
      [ f' [ H1' [ ? [ ? [ Hcorr0 [ ? [ ] ] ] ] ] ] ].
    inversion 1. subst => [ ? ].
    have Hterm' : corr_term
      (fun l l' => f' l l' \/ l = size H1' /\ l' = size H')
      (subst (scons (Loc (size H1')) Var) t)
      (subst (scons (Loc (size H')) Var) t0).
    { apply: corr_term_subst => [ | [ | ? ] ] /=;
      eauto using corr_term_impl. }
    have Hcorr' : corr_heap
      (fun l l' => f' l l' \/ l = size H1' /\ l' = size H')
      (rcons H1' (Some t4)) (rcons H' (Some t3)).
    { apply: corr_heap_segment_union.
      - apply: corr_heap_segment_cod; eauto.
        apply: corr_heap_rconsL.
        by apply: corr_heap_segment_rconsR.
      - apply: iso_heap_segment_corr_heap_segment => ? ? [ -> -> ].
        rewrite !nth_rcons !ltnn !eqxx.
        repeat eexists. eauto using corr_term_impl. }
    have Hiso' : iso_heap
      (fun l l'' => exists l',
        (f' l l' \/ l = size H1' /\ l' = size H') /\
        (f' l'' l' \/ l'' = size H1' /\ l' = size H'))
      (rcons H1' (Some t4)) (rcons H1' (Some t4)).
    { apply: (iso_heap_segment_dom (fun l l'' =>
        (exists l', f' l l' /\ f' l'' l') \/
        l = size H1' /\ l'' = size H1')).
      - apply: iso_heap_segment_union => [ | ? ? [ -> -> ] ].
        + apply: iso_heap_segment_rconsL.
          apply: iso_heap_segment_rconsR.
          apply: iso_heap_segment_cod; eauto.
          move => ? ? [ ? [ ] ]. eauto.
        + rewrite !nth_rcons !ltnn !eqxx.
          repeat eexists.
          apply: corr_term_impl.
          * apply: corr_term_comp; eauto.
            apply: corr_term_sym; eauto.
          * move => ? ? [ ? [ ] ]. eauto 7.
      - move => ? ? [ ? [ [ Hf | [ ? ? ] ] [ Hf' | [ ? ? ] ] ] ]; subst; eauto.
        + move: (corr_heap_segment_boundR _ _ _ _ Hcorr0 _ _ Hf).
          by rewrite ltnn.
        + move: (corr_heap_segment_boundR _ _ _ _ Hcorr0 _ _ Hf').
          by rewrite ltnn. }
    apply: diverge_name_appabs; eauto.
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
        apply: corr_heap_catL.
        by apply: corr_heap_segment_catR.
      - apply: iso_heap_segment_corr_heap_segment => ? ? [ x [ ? [ -> -> ] ] ].
        rewrite !nth_cat !ltnNge !leq_addr !addKn !(nth_map (Var 0)); try congruence.
        repeat eexists. 
        apply: corr_term_subst => [ | y ];
        eauto using corr_term_impl.
        rewrite !nth_scat H5.
        case (leqP (size ts) y) => ?.
        + by rewrite !nth_default ?size_mkseq.
        + rewrite !nth_mkseq => /=; eauto 6. }
    have Hiso' : iso_heap
      (fun l l'' => exists l',
        (f l l' \/ exists n, n < size ts0 /\ l = size H1_ + n /\ l' = size H2 + n) /\
        (f l'' l' \/ exists n, n < size ts0 /\ l'' = size H1_ + n /\ l' = size H2 + n))
      (H1_ ++ map (@Some _ \o
         subst (scat (mkseq (Loc \o addn (size H1_)) (size ts0)) Var)) ts0)
      (H1_ ++ map (@Some _ \o
         subst (scat (mkseq (Loc \o addn (size H1_)) (size ts0)) Var)) ts0).
    { apply: (iso_heap_segment_dom (fun l l'' =>
        (exists l', f l l' /\ f l'' l') \/
        (exists n, n < size ts0 /\ l = size H1_ + n /\ l'' = size H1_ + n))).
      - apply: iso_heap_segment_union => [ | ? ? [ x [ ? [ -> -> ] ] ] ].
        + apply: iso_heap_segment_catL.
          apply: iso_heap_segment_catR.
          apply: iso_heap_segment_cod; eauto.
          move => ? ? [ ? [ ] ]. eauto.
        + rewrite !nth_cat !ltnNge !leq_addr !addKn !(nth_map (Var 0)); try congruence.
          repeat eexists.
          apply: corr_term_subst => [ | y ].
          * apply: corr_term_comp; [ | apply: corr_term_sym ];
            eauto using corr_term_impl.
          * rewrite nth_scat.
            { case (leqP (size ts0) y) => ?.
              - by rewrite nth_default ?size_mkseq.
              - rewrite !nth_mkseq => //=;
                repeat (econstructor; eauto). }
      - move => ? ? [ ? [ ] ]
          [ Hf | [ ? [ ? [ ? ? ] ] ] ]
          [ Hf' | [ ? [ ? [ ? Heq ] ] ] ]; subst; eauto.
        + move: (corr_heap_segment_boundR _ _ _ _ Hcorr _ _ Hf).
          by rewrite ltnNge leq_addr.
        + move: (corr_heap_segment_boundR _ _ _ _ Hcorr _ _ Hf').
          by rewrite ltnNge leq_addr.
        + rewrite (addnI Heq). eauto. }
    apply: diverge_name_let. eauto.
Qed.

Theorem eval_need_complete H1 t1 H1' v1 :
  eval_name H1 t1 H1' v1 ->
  forall f H2 t2,
  corr_term f t1 t2 ->
  corr_heap f H1 H2 ->
  iso_heap (fun l1 l1' => exists l2, f l1 l2 /\ f l1' l2) H1 H1 ->
  exists f' H2' v2,
  eval_need H2 t2 H2' v2 /\
  corr_heap f' H1' H2' /\
  iso_heap (fun l1 l1' => exists l2, f' l1 l2 /\ f' l1' l2) H1' H1' /\
  corr_term f' v1 v2 /\
  (forall l1 l2, f l1 l2 -> f' l1 l2).
Proof.
  induction 1; inversion 1; subst => [ Hcorr Hiso ].
  - move: (Hcorr _ _ H5) => [ ? [ ] ].
    rewrite H0. inversion 1.
    subst => [ [ ? [ Hnth [ Hterm | [ ? [ H1' [ ? [ Hcbn [ g [ ? Hterm' ] ] ] ] ] ] ] ] ] ].
    + move: (IHeval_name _ _ _ Hterm Hcorr Hiso) =>
        [ f' [ ? [ ? [ Hcbn [ Hcorr' [ Hiso' [ ? Himpl ] ] ] ] ] ] ].
      do 5 (eexists; eauto).
      apply (corr_heap_segment_dom (fun l l0' => l0' != l' /\ f' l l0' \/ l0' = l' /\ f' l l0')).
      { apply: corr_heap_segment_union.
        - apply: corr_heap_segment_extR.
          + apply: corr_heap_segment_dom; eauto.
            by move => ? ? [ ].
          + move => ? ? [ /negPf Hneq ? ] ?.
            rewrite nth_set_nth => /=.
            by rewrite Hneq.
        - move => ? ? [ ? ] Hf'. subst.
          rewrite nth_set_nth => /=.
          move: (Hiso' _ _ (ex_intro _ _ (conj Hf' (Himpl _ _ H5)))) =>
            [ ? [ -> [ ? [ ] ] ] ].
          rewrite (eval_name_heap _ _ _ _ H1 _ _ H0) eqxx.
          inversion 1. subst => [ Hterm' ].
          repeat eexists. right. split.
          + apply: wf_term_impl.
            * apply: corr_term_wf_termL; eauto.
            * move => ? [ ? [ ? [ ] ] ]. eauto.
          + move: (eval_name_iso_heap _ _ _ _ H1 _ _ _
              (corr_term_comp _ _ _ _ Hterm' _
                (corr_term_comp _ _ _ _ Hterm _ (corr_term_sym _ _ _ Hterm)))
              (iso_heap_segment_comp _ _ _ _ _ _ _ Hiso'
                (iso_heap_segment_extL _ _ _ _ _ Hiso
                  (fun _ _ _ => eval_name_heap _ _ _ _ H1 _)))) =>
              [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ].
            repeat (eexists; eauto using corr_term_comp). }
      move => ? l'0.
      case (@eqP _ l'0 l') => /= [ -> | ]; eauto.
    + move: (eval_name_det _ _ _ _ H1 _ _ Hcbn)
        (value_eval_need H2 _
          (corr_term_valueL _ _ _ Hterm' (eval_name_value _ _ _ _ Hcbn))) => [ ? ? ] ?. subst.
      have Hiso' : iso_heap (fun l l' => g l l' \/ l = l' /\ exists l', f l l') H1' H.
      { apply: iso_heap_segment_union.
        - apply: iso_heap_segment_cod; eauto.
        - apply: iso_heap_segment_extL.
          + apply: iso_heap_segment_cod.
            * apply: iso_heap_segment_refl.
              apply: corr_heap_segment_wf_heap_segmentL. eauto.
            * eauto.
          + move => ? ? ?. apply: eval_name_heap. eauto. }
      do 5 (eexists; eauto).
      { apply: (iso_heap_corr_heap_segment_comp _ f f _ _ _ Hiso'); eauto.
        apply: (corr_heap_segment_extR _ _ _ _ _ Hcorr) => ? l'0 ? ?.
        move: nth_set_nth (@eqP _ l'0 l') => -> /= [ ? | // ].
        subst. by rewrite Hnth. }
      split.
      { apply: iso_heap_segment_dom.
        - apply: iso_heap_segment_cod.
          + apply: iso_heap_segment_comp; eauto.
            apply: iso_heap_segment_sym.
            apply: iso_heap_segment_comp; eauto.
          + move => ? ?
              [ ? [ ] ] [ ? | [ -> [ ? ? ] ] ]
              [ ? [ ] ] [ ? | [ -> [ ? ? ] ] ] [ ? [ ? ? ] ];
            repeat (eexists; eauto).
        - move => ? ? [ ? [ ] ]
            [ ? [ ] ] [ ? | [ -> [ ? ? ] ] ] ?
            [ ? [ ] ] [ ? | [ -> [ ? ? ] ] ] ?;
          repeat (rewrite -?plus_n_O; eexists; eauto). }
      split.
      { apply: corr_term_impl; eauto.
        move => ? ? [ ? [ ] ]. eauto. }
      eauto 6.
  - move: (IHeval_name1 _ _ _ H6 Hcorr Hiso) =>
      [ f' [ H2' [ ? [ ? [ Hcorr0 [ ? [ ] ] ] ] ] ] ].
    inversion 1. subst => [ ? ].
    have Hterm' : corr_term
      (fun l l' => f' l l' \/ l = size H' /\ l' = size H2')
      (subst (scons (Loc (size H')) Var) t0)
      (subst (scons (Loc (size H2')) Var) t').
    { apply: corr_term_subst => [ | [ | ? ] /= ];
      eauto using corr_term_impl. }
    have Hcorr' : corr_heap
      (fun l l' => f' l l' \/ l = size H' /\ l' = size H2')
      (rcons H' (Some t2)) (rcons H2' (Some t2')).
    { apply: corr_heap_segment_union.
      - apply: corr_heap_segment_cod; eauto.
        apply: corr_heap_rconsL.
        by apply: corr_heap_segment_rconsR.
      - apply: iso_heap_segment_corr_heap_segment => ? ? [ -> -> ].
        rewrite !nth_rcons !ltnn !eqxx.
        repeat eexists. eauto using corr_term_impl. }
    have Hiso' : iso_heap
      (fun l l'' => exists l',
        (f' l l' \/ l = size H' /\ l' = size H2') /\
        (f' l'' l' \/ l'' = size H' /\ l' = size H2'))
      (rcons H' (Some t2)) (rcons H' (Some t2)).
    { apply: (iso_heap_segment_dom (fun l l'' =>
        (exists l', f' l l' /\ f' l'' l') \/
        l = size H' /\ l'' = size H')).
      - apply: iso_heap_segment_union => [ | ? ? [ -> -> ] ].
        + apply: iso_heap_segment_rconsL.
          apply: iso_heap_segment_rconsR.
          apply: iso_heap_segment_cod; eauto.
          move => ? ? [ ? [ ] ]. eauto.
        + rewrite !nth_rcons !ltnn !eqxx.
          repeat eexists.
          apply: corr_term_impl.
          * apply: corr_term_comp; eauto.
            apply: corr_term_sym; eauto.
          * move => ? ? [ ? [ ] ]. eauto 7.
      - move => ? ? [ ? [ [ Hf | [ ? ? ] ] [ Hf' | [ ? ? ] ] ] ]; subst; eauto.
        + move: (corr_heap_segment_boundR _ _ _ _ Hcorr0 _ _ Hf).
          by rewrite ltnn.
        + move: (corr_heap_segment_boundR _ _ _ _ Hcorr0 _ _ Hf').
          by rewrite ltnn. }
    move: (IHeval_name2 _ _ _ Hterm' Hcorr' Hiso') =>
      [ ? [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ] ].
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
        apply: corr_heap_catL.
        by apply: corr_heap_segment_catR.
      - apply: iso_heap_segment_corr_heap_segment => ? ? [ x [ ? [ -> -> ] ] ].
        rewrite !nth_cat !ltnNge !leq_addr !addKn !(nth_map (Var 0)); try congruence.
        repeat eexists.
        apply: corr_term_subst => [ | y ];
        eauto using corr_term_impl.
        rewrite !nth_scat H5.
        case (leqP (size ts') y) => ?.
        + by rewrite !nth_default ?size_mkseq.
        + rewrite !nth_mkseq => /=; eauto 6. }
    have Hiso' : iso_heap
      (fun l l'' => exists l',
        (f l l' \/ exists n, n < size ts /\ l = size H + n /\ l' = size H2 + n) /\
        (f l'' l' \/ exists n, n < size ts /\ l'' = size H + n /\ l' = size H2 + n))
      (H ++ map (@Some _ \o
         subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var)) ts)
      (H ++ map (@Some _ \o
         subst (scat (mkseq (Loc \o addn (size H)) (size ts)) Var)) ts).
    { apply: (iso_heap_segment_dom (fun l l'' =>
        (exists l', f l l' /\ f l'' l') \/
        (exists n, n < size ts /\ l = size H + n /\ l'' = size H + n))).
      - apply: iso_heap_segment_union => [ | ? ? [ x [ ? [ -> -> ] ] ] ].
        + apply: iso_heap_segment_catL.
          apply: iso_heap_segment_catR.
          apply: iso_heap_segment_cod; eauto.
          move => ? ? [ ? [ ] ]. eauto.
        + rewrite !nth_cat !ltnNge !leq_addr !addKn !(nth_map (Var 0)); try congruence.
          repeat eexists.
          apply: corr_term_subst => [ | y ].
          * apply: corr_term_comp; [ | apply: corr_term_sym ];
            eauto using corr_term_impl.
          * rewrite nth_scat.
            { case (leqP (size ts) y) => ?.
              - by rewrite nth_default ?size_mkseq.
              - rewrite !nth_mkseq => //=;
                repeat (econstructor; eauto). }
      - move => ? ? [ ? [ ] ]
          [ Hf | [ ? [ ? [ ? ? ] ] ] ]
          [ Hf' | [ ? [ ? [ ? Heq ] ] ] ]; subst; eauto.
        + move: (corr_heap_segment_boundR _ _ _ _ Hcorr _ _ Hf).
          by rewrite ltnNge leq_addr.
        + move: (corr_heap_segment_boundR _ _ _ _ Hcorr _ _ Hf').
          by rewrite ltnNge leq_addr.
        + rewrite (addnI Heq). eauto. }
    move: (IHeval_name _ _ _ Hterm' Hcorr' Hiso') =>
      [ ? [ ? [ ? [ ? [ ? [ ? [ ? ? ] ] ] ] ] ] ].
    repeat (eexists; eauto).
Qed.

Theorem diverge_need_complete :
  forall H1 t1,
  diverge_name H1 t1 ->
  forall f H2 t2,
  corr_term f t1 t2 ->
  corr_heap f H1 H2 ->
  iso_heap (fun l1 l1' => exists l2, f l1 l2 /\ f l1' l2) H1 H1 ->
  diverge_need H2 t2.
Proof.
  cofix diverge_need_complete.
  inversion 1; subst => [ f H2_ ? ];
  inversion 1; subst => [ Hcorr Hiso ].
  - move: (Hcorr _ _ H5) => [ ? [ ] ].
    rewrite H2. inversion 1.
    subst => [ [ ? [ ? [ Hterm | [ ? [ ? [ ? [ Hcbn [ ? [ ? Hterm ] ] ] ] ] ] ] ] ] ].
    + econstructor; eauto.
    + case: (eval_name_diverge_name_disjoint _ _ _ _ Hcbn H3).
  - apply: diverge_need_appL; eauto.
  - move: (eval_need_complete _ _ _ _ H2 _ _ _ H6 Hcorr Hiso) =>
      [ f' [ H2' [ ? [ ? [ Hcorr0 [ ? [ ] ] ] ] ] ] ].
    inversion 1. subst => [ ? ].
    have Hterm' : corr_term
      (fun l l' => f' l l' \/ l = size H' /\ l' = size H2')
      (subst (scons (Loc (size H')) Var) t0)
      (subst (scons (Loc (size H2')) Var) t').
    { apply: corr_term_subst => [ | [ | ? ] /= ];
      eauto using corr_term_impl. }
    have Hcorr' : corr_heap
      (fun l l' => f' l l' \/ l = size H' /\ l' = size H2')
      (rcons H' (Some t3)) (rcons H2' (Some t2')).
    { apply: corr_heap_segment_union.
      - apply: corr_heap_segment_cod; eauto.
        apply: corr_heap_rconsL.
        by apply: corr_heap_segment_rconsR.
      - apply: iso_heap_segment_corr_heap_segment => ? ? [ -> -> ].
        rewrite !nth_rcons !ltnn !eqxx.
        repeat eexists. eauto using corr_term_impl. }
    have Hiso' : iso_heap
      (fun l l'' => exists l',
        (f' l l' \/ l = size H' /\ l' = size H2') /\
        (f' l'' l' \/ l'' = size H' /\ l' = size H2'))
      (rcons H' (Some t3)) (rcons H' (Some t3)).
    { apply: (iso_heap_segment_dom (fun l l'' =>
        (exists l', f' l l' /\ f' l'' l') \/
        l = size H' /\ l'' = size H')).
      - apply: iso_heap_segment_union => [ | ? ? [ -> -> ] ].
        + apply: iso_heap_segment_rconsL.
          apply: iso_heap_segment_rconsR.
          apply: iso_heap_segment_cod; eauto.
          move => ? ? [ ? [ ] ]. eauto.
        + rewrite !nth_rcons !ltnn !eqxx.
          repeat eexists.
          apply: corr_term_impl.
          * apply: corr_term_comp; eauto.
            apply: corr_term_sym; eauto.
          * move => ? ? [ ? [ ] ]. eauto 7.
      - move => ? ? [ ? [ [ Hf | [ ? ? ] ] [ Hf' | [ ? ? ] ] ] ]; subst; eauto.
        + move: (corr_heap_segment_boundR _ _ _ _ Hcorr0 _ _ Hf).
          by rewrite ltnn.
        + move: (corr_heap_segment_boundR _ _ _ _ Hcorr0 _ _ Hf').
          by rewrite ltnn. }
    apply: diverge_need_appabs; eauto.
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
        apply: corr_heap_catL.
        by apply: corr_heap_segment_catR.
      - apply: iso_heap_segment_corr_heap_segment => ? ? [ x [ ? [ -> -> ] ] ].
        rewrite !nth_cat !ltnNge !leq_addr !addKn !(nth_map (Var 0)); try congruence.
        repeat eexists.
        apply: corr_term_subst => [ | y ];
        eauto using corr_term_impl.
        rewrite !nth_scat H5.
        case (leqP (size ts') y) => ?.
        + by rewrite !nth_default ?size_mkseq.
        + rewrite !nth_mkseq => /=; eauto 6. }
    have Hiso' : iso_heap
      (fun l l'' => exists l',
        (f l l' \/ exists n, n < size ts /\ l = size H1 + n /\ l' = size H2_ + n) /\
        (f l'' l' \/ exists n, n < size ts /\ l'' = size H1 + n /\ l' = size H2_ + n))
      (H1 ++ map (@Some _ \o
         subst (scat (mkseq (Loc \o addn (size H1)) (size ts)) Var)) ts)
      (H1 ++ map (@Some _ \o
         subst (scat (mkseq (Loc \o addn (size H1)) (size ts)) Var)) ts).
    { apply: (iso_heap_segment_dom (fun l l'' =>
        (exists l', f l l' /\ f l'' l') \/
        (exists n, n < size ts /\ l = size H1 + n /\ l'' = size H1 + n))).
      - apply: iso_heap_segment_union => [ | ? ? [ x [ ? [ -> -> ] ] ] ].
        + apply: iso_heap_segment_catL.
          apply: iso_heap_segment_catR.
          apply: iso_heap_segment_cod; eauto.
          move => ? ? [ ? [ ] ]. eauto.
        + rewrite !nth_cat !ltnNge !leq_addr !addKn !(nth_map (Var 0)); try congruence.
          repeat eexists.
          apply: corr_term_subst => [ | y ].
          * apply: corr_term_comp; [ | apply: corr_term_sym ];
            eauto using corr_term_impl.
          * rewrite nth_scat.
            { case (leqP (size ts) y) => ?.
              - by rewrite nth_default ?size_mkseq.
              - rewrite !nth_mkseq => //=;
                repeat (econstructor; eauto). }
      - move => ? ? [ ? [ ] ]
          [ Hf | [ ? [ ? [ ? ? ] ] ] ]
          [ Hf' | [ ? [ ? [ ? Heq ] ] ] ]; subst; eauto.
        + move: (corr_heap_segment_boundR _ _ _ _ Hcorr _ _ Hf).
          by rewrite ltnNge leq_addr.
        + move: (corr_heap_segment_boundR _ _ _ _ Hcorr _ _ Hf').
          by rewrite ltnNge leq_addr.
        + rewrite (addnI Heq). eauto. }
    apply: diverge_need_let. eauto.
Qed.
