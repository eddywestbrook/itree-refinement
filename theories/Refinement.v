(***
 *** A version of the computation monad using the option-set monad
 ***)

From Coq Require Export Morphisms Setoid Program.Equality.
From ITree Require Export ITree ITreeFacts.
From Paco Require Import paco.
From Coq Require Export Eqdep EqdepFacts.

Infix ">>=" := ITree.bind (at level 58, left associativity).
Notation "m1 >> m2" := (m1 >>= fun _ => m2) (at level 58, left associativity).


(** * `itree_spec` **)

Variant SpecEvent (E:Type -> Type) (A:Type) : Type :=
| Spec_vis : E A -> SpecEvent E A
| Spec_forall : SpecEvent E A
| Spec_exists : SpecEvent E A
.

Arguments Spec_vis {E A}.
Arguments Spec_forall {E A}.
Arguments Spec_exists {E A}.

(* An ITree that defines a set of ITrees *)
Notation itree_spec E := (itree (SpecEvent E)).

(* The body of an itree_spec, inside the observe projection *)
Notation itree_spec' E A := (itree' (SpecEvent E) A).


(***
 *** Satisfaction of itree specs
 ***)

(* An itree satisfies an itree_spec iff it is eutt to an itree that satisfies
all the quantifiers in the itree_spec *)
Inductive satisfiesF {E R} (F : itree E R -> itree_spec E R -> Prop) :
  itree' E R -> itree_spec' E R -> Prop :=
  | satisfies_Ret (r : R) : satisfiesF F (RetF r) (RetF r)
  | satisfies_TauLR phi1 (phi2 : itree_spec E R) :
      F phi1 phi2 -> satisfiesF F (TauF phi1) (TauF phi2)
  | satisfies_TauL phi ophi :
      satisfiesF F (observe phi) ophi -> satisfiesF F (TauF phi) ophi
  | satisfies_TauR ophi phi :
      satisfiesF F ophi (observe phi) -> satisfiesF F ophi (TauF phi)
  | satisfies_VisLR A e kphi1 kphi2 :
      (forall a : A, F (kphi1 a) (kphi2 a) ) ->
      satisfiesF F (VisF e kphi1) (VisF (Spec_vis e) kphi2)
  | satisfies_forallR A kphi phi :
      (forall a : A, satisfiesF F phi (observe (kphi a))) ->
      satisfiesF F phi (VisF Spec_forall kphi)
  | satisfies_existsR A kphi phi (a : A) :
      (satisfiesF F phi (observe (kphi a))) ->
      satisfiesF F phi (VisF Spec_exists kphi)
.
Hint Constructors satisfiesF.
Definition satisfies_ {E R} F t1 (t2: itree_spec E R) : Prop :=
  satisfiesF F (observe t1) (observe t2).

Lemma monotone_satisfiesF {E R} ot1 (ot2 : itree_spec' E R) sim sim' 
  (LE : sim <2= sim' )
  (IN : satisfiesF sim ot1 ot2) : 
  satisfiesF sim' ot1 ot2.
Proof.
  induction IN; eauto.
Qed.

Lemma monotone_satisfies_ {E R} : monotone2 (@satisfies_ E R).
Proof. red. intros. eapply monotone_satisfiesF; eauto. Qed.

Hint Resolve monotone_satisfies_ : paco.

Instance Proper_upaco2_satisfies_ {E R} :
  Proper ((eq ==> eq ==> impl) ==> eq ==> eq ==> impl) (upaco2 (@satisfies_ E R)).
Proof.
  intros r1 r2 prp_r t1 t2 e12 t3 t4 e34 r13.
  rewrite <- e12. rewrite <- e34.
  destruct r13.
  - left. eapply (paco2_mon _ H).
    intros x y. apply (prp_r x x eq_refl y y eq_refl).
  - right. apply (prp_r _ _ eq_refl _ _ eq_refl H).
Qed.

Definition satisfies {E R} : itree E R -> itree_spec E R -> Prop :=
  paco2 satisfies_ bot2.

Instance Proper_eutt_satisfies_impl {E R} :
  Proper (eutt eq ==> eutt eq ==> impl) (@satisfies E R).
Proof.
  admit.
Admitted.

Instance Proper_eutt_satisfies {E R} :
  Proper (eutt eq ==> eutt eq ==> iff) (@satisfies E R).
Proof.
  repeat intro.
  split; apply Proper_eutt_satisfies_impl; try assumption; symmetry; assumption.
Qed.


(***
 *** Refinement of itree specs
 ***)

(* One itree_spec refines another iff, after turning finitely many quantifier
events to actual quantifiers, they have the same constructor with continuations
such that the first continuation coinductively refines the second *)
Inductive refinesF {E R} (F : itree_spec E R -> itree_spec E R -> Prop) : 
  itree_spec' E R -> itree_spec' E R -> Prop :=
  | refines_Ret (r : R) : refinesF F (RetF r) (RetF r)
  | refines_TauLR (phi1 phi2 : itree_spec E R) :
      F phi1 phi2 -> refinesF F (TauF phi1) (TauF phi2)
(*
  | refines_TauL phi ophi :
      refinesF F (observe phi) ophi -> refinesF F (TauF phi) ophi
  | refines_TauR ophi phi :
      refinesF F ophi (observe phi) -> refinesF F ophi (TauF phi)
*)
  | refines_VisLR A e kphi1 kphi2 :
      (forall a : A, F (kphi1 a) (kphi2 a) ) ->
      refinesF F (VisF e kphi1) (VisF e kphi2)
  | refines_forallR A kphi phi :
      (forall a : A, refinesF F phi (observe (kphi a))) ->
      refinesF F phi (VisF Spec_forall kphi)
  | refines_forallL A kphi phi (a : A) :
      (refinesF F (observe (kphi a)) phi) ->
      refinesF F (VisF Spec_forall kphi) phi
  | refines_existsR A kphi phi (a : A) :
      (refinesF F phi (observe (kphi a))) ->
      refinesF F phi (VisF Spec_exists kphi)
  | refines_existsL A kphi phi :
      (forall a : A, refinesF F (observe (kphi a)) phi) ->
      refinesF F (VisF Spec_exists kphi) phi
.
Hint Constructors refinesF.
Definition refines_ {E R} F (t1 t2: itree_spec E R) : Prop :=
  refinesF F (observe t1) (observe t2).

Lemma monotone_refinesF {E R} (ot1 ot2 : itree_spec' E R) sim sim' 
  (LE : sim <2= sim' )
  (IN : refinesF sim ot1 ot2) : 
  refinesF sim' ot1 ot2.
Proof.
  induction IN; eauto.
Qed.

Lemma monotone_refines_ {E R} : monotone2 (@refines_ E R).
Proof. red. intros. eapply monotone_refinesF; eauto. Qed.

Hint Resolve monotone_refines_ : paco.

Instance Proper_upaco2_refines_ {E R} :
  Proper ((eq ==> eq ==> impl) ==> eq ==> eq ==> impl) (upaco2 (@refines_ E R)).
Proof.
  intros r1 r2 prp_r t1 t2 e12 t3 t4 e34 r13.
  rewrite <- e12. rewrite <- e34.
  destruct r13.
  - left. eapply (paco2_mon _ H).
    intros x y. apply (prp_r x x eq_refl y y eq_refl).
  - right. apply (prp_r _ _ eq_refl _ _ eq_refl H).
Qed.

Lemma bot2_least {T0 T1} (r: rel2 T0 T1) : bot2 <2= r.
Proof.
  intros _ _ [].
Qed.

(* FIXME: there must be a better way to get this result... *)
Lemma upaco2_refinesF_bot_r {E R} r t1 t2 :
  upaco2
    (fun (F : itree_spec E R -> itree_spec E R -> Prop) (t4 t5 : itree_spec E R) =>
     refinesF F (observe t4) (observe t5)) bot2 t1 t2 ->
  upaco2
    (fun (F : itree_spec E R -> itree_spec E R -> Prop) (t0 t4 : itree_spec E R) =>
     refinesF F (observe t0) (observe t4)) r t1 t2.
Proof.
  intro H.
  eapply (Proper_upaco2_refines_ _ _ _ t1 t1 eq_refl t2 t2 eq_refl H). Unshelve.
  intros _ _ _ _ _ _ [].
Qed.


Definition refines {E R} : itree_spec E R -> itree_spec E R -> Prop :=
  paco2 refines_ bot2.

Instance Proper_observing_eq_refines {E R} :
  Proper (observing eq ==> observing eq ==> impl) (@refines E R).
Proof.
  unfold Proper, respectful, impl.
  intros t1 t2 e12 t3 t4 e34 r13. destruct e12 as [e12]. destruct e34 as [e34].
  pfold. punfold r13. unfold refines_ in * |- *.
  rewrite e12 in r13. rewrite e34 in r13.
  assumption.
Qed.

(* Reflexivity of refinement *)
Instance Reflexive_refines {E R} : Reflexive (@refines E R).
Proof.
  red. pcofix CIH. intro t. pfold. red.
  destruct (observe t); constructor; eauto.
Qed.

Ltac inj_existT := repeat match goal with | H : existT _ _ _ = _ |- _ => apply inj_pair2 in H end.

Lemma refines_Vis_forallR : forall (E : Type -> Type) (R A : Type) (t : itree_spec E R) k,
         refines t (Vis Spec_forall k) ->
         forall a : A, refines t (k a).
Proof.
  intros E R A. pcofix CIH. intros t k Href a.
  pfold. revert a. red. punfold Href. red in Href.
  cbn in *. remember (observe t) as ot. clear Heqot.
  remember (VisF Spec_forall k) as x.
  hinduction Href before r; intros; inv Heqx; inj_existT; subst; pclearbot.
  - econstructor. Unshelve. 2 : apply a. specialize (H a).
    assert (paco2 refines_ r (kphi1 a) (k a)). eapply paco2_mon; intros; try contradiction; eauto.
    inv PR. punfold H0.
  - clear H0. assert (refines (go phi) (k a) ).
    { pstep. apply H. }
    enough (paco2 refines_ r (go phi) (k a) ).
    { punfold H1. }
    eapply paco2_mon; eauto. intros; contradiction.
  - econstructor. Unshelve. 2 : apply a. eapply IHHref; eauto.
  - econstructor. intros. eapply H0; eauto.
Qed.

Lemma refines_Vis_existsL : forall (E : Type -> Type) (R A : Type) (t : itree_spec E R) k,
         refines (Vis Spec_exists k) t ->
         forall a : A, refines (k a) t.
Proof.
  intros E R A. intros t k Href.
  intros. pfold. red. punfold Href. red in Href.
  remember (observe t) as ot. clear Heqot. cbn in *.
  remember (VisF Spec_exists k) as x. 
  hinduction Href before A; intros; inv Heqx; inj_existT; subst.
  - pclearbot. econstructor. specialize (H a). punfold H.
  - econstructor. intros. eapply H0; eauto.
  - econstructor. eapply IHHref; eauto.
  - eauto.
Qed.


(* A version of refinesF specialized to a forall on the left *)
Inductive forallRefinesF {E R} (F : itree_spec E R -> itree_spec E R -> Prop)
          {A} (kphi1: A -> itree_spec E R)
  : itree_spec' E R -> Prop :=
  | forallRefines_VisLR kphi2 :
      (forall a : A, F (kphi1 a) (kphi2 a)) ->
      forallRefinesF F kphi1 (VisF Spec_forall kphi2)
  | forallRefines_forallR B kphi2 :
      (forall b : B, forallRefinesF F kphi1 (observe (kphi2 b))) ->
      forallRefinesF F kphi1 (VisF Spec_forall kphi2)
  | forallRefines_forallL phi (a : A) :
      refinesF F (observe (kphi1 a)) phi ->
      forallRefinesF F kphi1 phi
  | forallRefines_existsR B kphi2 (b : B) :
      (forallRefinesF F kphi1 (observe (kphi2 b))) ->
      forallRefinesF F kphi1 (VisF Spec_exists kphi2)
.

(* FIXME: should we replace the recursive call to refinesF in the above with
just a refines? *)

Lemma refinesF_Vis_forallL : forall (E : Type -> Type) (R A : Type) F
                                   (t : itree_spec' E R) (k : A -> itree_spec E R),
    refinesF F (VisF Spec_forall k) t ->
    @forallRefinesF E R F A k t.
Proof.
  intros. remember (VisF Spec_forall k) as t1. induction H.
  - inversion Heqt1.
  - inversion Heqt1.
  - assert (A0=A); [ inversion Heqt1; reflexivity | ].
    revert e kphi1 Heqt1 kphi2 H; rewrite H0; intros.
    assert (kphi1=k); [ inversion Heqt1; inj_existT; assumption | ].
    rewrite H1 in H.
    assert (e=Spec_forall); [ inversion Heqt1; inj_existT; assumption | ].
    rewrite H2.
    apply forallRefines_VisLR. apply H.
  - apply forallRefines_forallR. intro b. apply H0. assumption.
  - assert (A0=A); [ inversion Heqt1; reflexivity | ].
    revert kphi Heqt1 a H IHrefinesF; rewrite H0; intros.
    assert (kphi=k); [ inversion Heqt1; inj_existT; assumption | ].
    rewrite H1 in H.
    eapply forallRefines_forallL; eassumption.
  - eapply forallRefines_existsR. apply IHrefinesF. assumption.
  - inversion Heqt1.
Qed.


(* A version of refinesF specialized to a Tau on the left *)
Inductive tauRefinesF {E R} (F : itree_spec E R -> itree_spec E R -> Prop)
          (phi1: itree_spec E R)
  : itree_spec' E R -> Prop :=
  | tauRefines_VisLR phi2 : F phi1 phi2 -> tauRefinesF F phi1 (TauF phi2)
  | tauRefines_forallR B kphi2 :
      (forall b : B, tauRefinesF F phi1 (observe (kphi2 b))) ->
      tauRefinesF F phi1 (VisF Spec_forall kphi2)
  | tauRefines_existsR B kphi2 (b : B) :
      tauRefinesF F phi1 (observe (kphi2 b)) ->
      tauRefinesF F phi1 (VisF Spec_exists kphi2)
.

Lemma refinesF_Tau : forall (E : Type -> Type) (R : Type) F
                            t1 (t2 : itree_spec' E R),
    refinesF F (TauF t1) t2 ->
    @tauRefinesF E R F t1 t2.
Proof.
  intros. remember (TauF t1) as t. induction H; inversion Heqt.
  - rewrite <- H1. constructor. assumption.
  - constructor. intro b. apply H0. assumption.
  - econstructor. apply IHrefinesF. assumption.
Qed.


Inductive isConcreteF {E R} (F : itree_spec E R -> Prop) :
  itree_spec' E R -> Prop :=
  | isConcrete_Ret (r : R) : isConcreteF F (RetF r)
  | isConcrete_Tau (phi : itree_spec E R) :
      F phi -> isConcreteF F (TauF phi)
  | isConcrete_Vis A e kphi :
      (forall a:A, F (kphi a)) -> isConcreteF F (VisF (Spec_vis e) kphi).

Hint Constructors isConcreteF.
Definition isConcrete_ {E R} F (t: itree_spec E R) : Prop :=
  isConcreteF F (observe t).

Lemma monotone_isConcreteF {E R} (ot : itree_spec' E R) sim sim' 
  (LE : sim <1= sim' )
  (IN : isConcreteF sim ot) : 
  isConcreteF sim' ot.
Proof.
  induction IN; eauto.
Qed.

Lemma monotone_isConcrete_ {E R} : monotone1 (@isConcrete_ E R).
Proof. red. intros. eapply monotone_isConcreteF; eauto. Qed.

Hint Resolve monotone_isConcrete_ : paco.

Definition isConcrete {E R} : itree_spec E R -> Prop := paco1 isConcrete_ bot1.

Lemma isConcreteVisInv {E R A} e (k : A -> itree_spec E R) a :
  isConcrete (Vis (Spec_vis e) k) -> isConcrete (k a).
Proof.
  intro isc; punfold isc. inversion isc.
  assert (kphi0 = k); [ inj_existT; assumption | ].
  rewrite H3 in H0. pclearbot. apply H0.
Qed.

(* Transitivity of refinement if the LHS is concrete *)
Theorem concreteRefinesTrans {E R} (t1 t2 t3: itree_spec E R)
         (isc:isConcrete t1) :
  refines t1 t2 -> refines t2 t3 -> refines t1 t3.
Proof.
  revert t1 t2 t3 isc; pcofix CIH. intros t1 t2 t3 isc Ht12 Ht23.
  pfold. red. punfold Ht12. red in Ht12.
  punfold Ht23. red in Ht23.
  remember (observe t3) as ot3. clear t3 Heqot3.
  punfold isc. red in isc. remember (observe t1) as ot1. clear t1 Heqot1.
  hinduction Ht12 before r; intros.
  - remember (RetF r0) as x.
    hinduction Ht23 before r; intros; inv Heqx; eauto.
  - pclearbot. remember (TauF phi2) as x. inversion isc.
    hinduction Ht23 before r; intros; inv Heqx; pclearbot; eauto.
  - pclearbot. destruct e.
    + remember (VisF (Spec_vis e) kphi2) as x.
      hinduction Ht23 before r; intros; inv Heqx; inj_existT; subst; eauto.
      pclearbot. econstructor. right. eapply CIH; try apply H0; try apply H.
      eapply (isConcreteVisInv e0). pfold. apply isc.
    + inversion isc.
    + inversion isc.
  - remember (refinesF_Vis_forallL _ _ _ _ _ _ Ht23) as Ht23'.
    clear HeqHt23' Ht23. induction Ht23'.
    * apply refines_forallR. intro a.
      eapply H0; [ apply CIH | assumption | ].
      eapply (paco2_unfold (gf:=refines_)); [ apply monotone_refines_ | ].
      destruct (H1 a); [ eassumption | contradiction ].
    * apply refines_forallR. intro b. apply H2.
    * eapply H0; eassumption.
    * eapply refines_existsR. eassumption.
  - inversion isc.
  - assert (refines (Vis Spec_exists kphi) (go ot3)); [ pfold; apply Ht23 | ].
    apply IHHt12; try assumption.
    remember (refines_Vis_existsL _ _ _ (go ot3) kphi H a). clear Heqr0.
    red in r0. punfold r0.
  - inversion isc.
Qed.


(* Refinement defines a subset for satisfaction *)
Theorem refinesSatisfiesSubset {E R} t1 (t2 t3: itree_spec E R) :
  satisfies t1 t2 -> refines t2 t3 -> satisfies t1 t3.
Proof.
  revert t1 t2 t3; pcofix CIH. intros t1 t2 t3 Ht12 Ht23.
  pfold. red. punfold Ht12. red in Ht12.
  punfold Ht23. red in Ht23.
  remember (observe t3) as ot3. clear t3 Heqot3.
  remember (observe t1) as ot1. clear t1 Heqot1.
  hinduction Ht12 before CIH; intros.
  - remember (RetF r0) as x.
    hinduction Ht23 before r; intros; inv Heqx; eauto.
  - pclearbot. remember (TauF phi2) as x.
    hinduction Ht23 before r; intros; inv Heqx; pclearbot; eauto.
  - constructor. apply IHHt12; assumption.
  - remember (refinesF_Tau _ _ _ _ _ Ht23) as Ht23'. clear HeqHt23' Ht23.
    induction Ht23'.
    + constructor. apply IHHt12. pclearbot. punfold H.
    + constructor. intro b. apply H0.
    + econstructor. eassumption.
  - pclearbot.
    + remember (VisF (Spec_vis e) kphi2) as x.
      hinduction Ht23 before r; intros; inv Heqx; inj_existT; subst; eauto.
      pclearbot. econstructor. right. eapply CIH; try apply H0; try apply H.
  - remember (refinesF_Vis_forallL _ _ _ _ _ _ Ht23) as Ht23'.
    clear HeqHt23' Ht23. induction Ht23'.
    * apply satisfies_forallR. intro a.
      apply (H0 a).
      eapply (paco2_unfold (gf:=refines_)); [ apply monotone_refines_ | ].
      destruct (H1 a); [ eassumption | contradiction ].
    * apply satisfies_forallR. intro b. apply H2.
    * eapply H0; eassumption.
    * eapply satisfies_existsR. eassumption.
  - assert (refines (Vis Spec_exists kphi) (go ot3)); [ pfold; apply Ht23 | ].
    apply IHHt12; try assumption.
    remember (refines_Vis_existsL _ _ _ (go ot3) kphi H a). clear Heqr0.
    red in r0. punfold r0.
Qed.
