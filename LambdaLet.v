From mathcomp Require Import all_ssreflect.
Require Import Util.

Inductive term : Type :=
  | Var of nat
  | Loc of nat
  | Abs of term
  | App of term & term
  | Let of seq term & term.

Inductive value : term -> Prop :=
  | value_abs t : value (Abs t).

Hint Constructors value.

Definition term_rect'
  (P : term -> Type)
  (HVar : forall x, P (Var x))
  (HLoc : forall l, P (Loc l))
  (HAbs : forall t, P t -> P (Abs t))
  (HApp : forall t1, P t1 -> forall t2, P t2 -> P (App t1 t2))
  (HLet : forall ts, foldr (fun t => prod (P t)) unit ts -> forall t, P t -> P (Let ts t)) :=
  fix term_ind t :=
    match t as t0 return P t0 with
    | Var _ => HVar _
    | Loc _ => HLoc _
    | Abs t => HAbs _ (term_ind t)
    | App t1 t2 => HApp _ (term_ind t1) _ (term_ind t2)
    | Let ts t => HLet _ ((fix term_ind' ts :=
        match ts as ts0 return foldr (fun t => prod (P t)) unit ts0 with
        | nil => tt
        | t :: ts => pair (term_ind t) (term_ind' ts)
        end) ts) _ (term_ind t)
    end.

Fixpoint encode t :=
  match t with
  | Var x => GenTree.Leaf (inl x)
  | Loc l => GenTree.Leaf (inr l)
  | Abs t => GenTree.Node 0 [:: encode t]
  | App t1 t2 => GenTree.Node 1 [:: encode t1; encode t2]
  | Let ts t =>  GenTree.Node 2 (encode t :: map encode ts)
  end.

Fixpoint decode t :=
  match t with
  | GenTree.Leaf (inl x) => Some (Var x)
  | GenTree.Leaf (inr l) => Some (Loc l)
  | GenTree.Node 0 [:: t'] => omap Abs (decode t')
  | GenTree.Node 1 [:: t1'; t2'] =>
      if decode t1' is Some t1 then omap (App t1) (decode t2')
      else None
  | GenTree.Node 2 (t' :: ts') => omap (Let (pmap decode ts')) (decode t')
  | GenTree.Node _ _ => None
  end.

Lemma codeK : pcancel encode decode.
Proof.
  elim /term_rect' =>
    /= [ | | ? -> | ? -> ? -> | ts IHts t -> ] //=.
  congr (Some (Let _ t)).
  elim: ts IHts => /= [ | ? ? IHIH [ -> ? ] ] //=.
  by rewrite IHIH.
Qed.

Definition term_eqMixin := PcanEqMixin codeK.
Canonical term_eqType := Eval hnf in EqType _ term_eqMixin.

Definition term_ind'
  (P : term -> Prop)
  (HVar : forall x, P (Var x))
  (HLoc : forall x, P (Loc x))
  (HAbs : forall t, P t -> P (Abs t))
  (HApp : forall t1, P t1 -> forall t2, P t2 -> P (App t1 t2))
  (HLet : forall ts, { in ts, forall t, P t } -> forall t, P t -> P (Let ts t))
  : forall t, P t.
Proof.
  elim /term_rect' => [ | | | | ts IHts ] //=.
  apply: HLet.
  elim: ts IHts => /= [ ? ? | ? ? IHts [ ? ? ] ? ].
  - by rewrite in_nil.
  - rewrite in_cons => /orP [ /eqP -> // | ].
    exact: IHts.
Qed.

Fixpoint rename_term r t :=
  match t with
  | Loc l => Loc l
  | Var x => Var (r x)
  | Abs t => Abs (rename_term (upren r) t)
  | App t1 t2 => App (rename_term r t1) (rename_term r t2)
  | Let ts t =>
      let r' := upnren r (size ts) in
      Let (map (rename_term r') ts) (rename_term r' t)
  end.

Program Instance RenameTerm : Rename term :=
  { Var := Var; rename := rename_term }.
Next Obligation.
  elim /term_ind' : t r r' H => /=;
  intros; f_equal; eauto using eq_upren, eq_upnren.
  by apply /eq_in_map => ? /H; eauto using eq_upnren.
Qed.

Program Instance RenameLemmasTerm : RenameLemmas term.
Next Obligation.
  induction t using term_ind' => /=; f_equal;
  eauto using rename_id_upren, rename_id_upnren.
  apply map_id_in => ? /H. eauto using rename_id_upnren.
Qed.
Next Obligation.
  elim /term_ind' : t r r' => /=; intros; f_equal; rewrite ?size_map;
  eauto using rename_rename_comp_upren, rename_rename_comp_upnren.
  rewrite -map_comp.
  apply /eq_in_map => ? /H.
  eauto using rename_rename_comp_upnren.
Qed.

Fixpoint subst_term s t :=
  match t with
  | Var x => s x
  | Loc l => Loc l
  | Abs t => Abs (subst_term (up s) t)
  | App t1 t2 => App (subst_term s t1) (subst_term s t2)
  | Let ts t =>
      let s' := upn s (size ts) in
      Let (map (subst_term s') ts) (subst_term s' t)
  end.

Program Instance SubstTerm : Subst term := { subst := subst_term }.
Next Obligation.
  elim /term_ind' : t s s' H => /=; intros; f_equal;
  eauto using eq_up, eq_upn.
  apply /eq_in_map => ? /H; eauto using eq_upn.
Qed.

Program Instance SubstLemmasTerm : SubstLemmas term.
Next Obligation.
  elim /term_ind' : t => /=; intros; f_equal;
  eauto using subst_id_up, subst_id_upn.
  apply: map_id_in => ? /H. eauto using subst_id_upn.
Qed.
Next Obligation.
  elim /term_ind' : t r => /=; intros; f_equal;
  eauto using rename_subst_up, rename_subst_upn.
  apply /eq_in_map => ? /H. eauto using rename_subst_upn.
Qed.
Next Obligation.
  elim /term_ind' : t r s => /=; intros; f_equal; rewrite ?size_map;
  eauto using subst_rename_comp_up, subst_rename_comp_upn.
  rewrite -map_comp.
  apply /eq_in_map => ? /H.
  eauto using subst_rename_comp_upn.
Qed.
Next Obligation.
  elim /term_ind' : t r s => /=; intros; f_equal; rewrite ?size_map;
  eauto using rename_subst_comp_up, rename_subst_comp_upn.
  rewrite -map_comp.
  apply /eq_in_map => ? /H.
  eauto using rename_subst_comp_upn.
Qed.

Program Instance SubstLemmas'Term : SubstLemmas' term.
Next Obligation.
  elim /term_ind' : t s s' => /=; intros; f_equal; rewrite ?size_map;
  eauto using subst_subst_comp_up, subst_subst_comp_upn.
  rewrite -map_comp.
  apply /eq_in_map => ? /H.
  eauto using subst_subst_comp_upn.
Qed.
