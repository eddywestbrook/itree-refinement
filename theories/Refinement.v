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
  | refines_forallL A kphi phi :
      (exists a : A, refinesF F (observe (kphi a)) phi) ->
      refinesF F (VisF Spec_forall kphi) phi
  | refines_existsR A kphi phi :
      (exists a : A, refinesF F phi (observe (kphi a))) ->
      refinesF F phi (VisF Spec_exists kphi)
  | refines_existsL A kphi phi :
      (forall a : A, refinesF F (observe (kphi a)) phi) ->
      refinesF F (VisF Spec_exists kphi) phi
.

Definition refines_ {E R} F (t1 t2: itree_spec E R) : Prop :=
  refinesF F (observe t1) (observe t2).

FIXME: update the rest of this file to match the new definition of refinesF

Lemma monotone_refines_ {E R} : monotone2 (@refines_ E R).
Proof.
  red. unfold refines_. intros t1 t2.
  generalize (observe t1). generalize (observe t2).
  intros t1' t2' r F r12. induction r12; intros; constructor.
  - apply LE; assumption.
  - intro a; apply LE; apply H.
  - intro a; apply LE; apply H.
  - destruct H as [a H]. exists a. apply LE; apply H.
  - destruct H as [a H]. exists a. apply LE; apply H.
  - intro a; apply LE; apply H.
Qed.

Hint Resolve monotone_refines_ : paco.
Print monotone2.

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
  red. pcofix CIH. intro t. pfold. unfold refines_.
  generalize (observe t); intro t'. destruct t'.
  - constructor.
  - constructor. right. apply CIH.
  - destruct e.
    + constructor; intros; right; apply CIH.
    + apply (refines_forallR _ _ _ (go _)). intro x; left; pfold.
      apply refines_forallL. exists x. right; apply CIH.
    + apply (refines_existsL _ _ _ (go _)). intro x; left; pfold.
      apply refines_existsR. exists x. right; apply CIH.
Qed.


(* Transitivity of refinement *)
Instance Transitive_refines {E R} : Transitive (@refines E R).
Proof.
  red. pcofix CIH. intros t1 t2 t3 r12 r23.
  pfold. punfold r12. punfold r23. revert r12 r23. unfold refines_.
  generalize (observe t1). generalize (observe t2). generalize (observe t3).

  intros t1' t2' t3' r12 r23. destruct r12; inversion r23.
  - constructor.
  - constructor. intro a. pclearbot. right.
    eapply CIH. reflexivity. pclearbot. apply H0.
  - destruct H0 as [a H0]. constructor. exists a. right.
    eapply CIH. reflexivity. pclearbot. apply H0.
  - constructor. right. pclearbot. eapply CIH; [ apply H | apply H1 ].
  - apply (refines_forallR _ _ _ (go _)). intro a. right. pclearbot.
    apply (CIH _ (Tau phi2)).
    + pfold. constructor. left. apply H.
    + rewrite <- H0. rewrite (observing_intros eq (go (observe phi)) phi eq_refl).
      apply H1.
  - destruct H1 as [ a H1 ]. apply (refines_existsR _ _ _ (go _)). exists a.
    right. pclearbot. apply (CIH _ (Tau phi2)).
    + pfold. constructor. left. apply H.
    + rewrite <- H0. rewrite (observing_intros eq (go (observe phi)) phi eq_refl).
      apply H1.
  - rewrite (inj_pair2 _ _ _ _ _ H2).
    constructor. intro a. pclearbot. right. eapply CIH.
    + apply H.
    + rewrite <- (inj_pair2 _ _ _ _ _ H3). apply H4.
  - apply (refines_forallR _ _ _ (go _)). intro a. right.
    apply (CIH _ ((Vis (Spec_vis e) kphi2))).
    + pfold. constructor. intro a0. apply H.
    + rewrite <- H0. rewrite (observing_intros eq (go (observe phi)) phi eq_refl).
      pclearbot. apply H1.
  - destruct H1 as [ a H1 ]. apply (refines_existsR _ _ _ (go _)). exists a.
    right. pclearbot. apply (CIH _ (Vis (Spec_vis e) kphi2)).
    + pfold. constructor. left. apply H.
    + rewrite <- H0. rewrite (observing_intros eq (go (observe phi)) phi eq_refl).
      pclearbot. apply H1.
  - apply (refines_forallR _ _ _ (go _)). intro a0. right.


FIXME: we seem to be stuck on this case:
refines phi (Spec_forall kphi)  /\  refines (Spec_forall kphi) (Spec_forall kphi0)
proved by:
(forall a, refines phi (kphi a))  /\  (forall b, refines (Spec_forall kphi) (kphi0 b))



apply (refines_forallR _ _ _ (go _)). intro a. right.
    eapply CIH.
    + rewrite (observing_intros eq (go (observe phi)) phi eq_refl).



  intros t1' t2' t3' r12 r23. destruct r12.
  - apply (monotone_refines_ (Ret r0) (go t1') _ _ r23).
    apply upaco2_refinesF_bot_r.
  - inversion r23.
    + constructor. right. pclearbot. apply (CIH _ phi2 _ H H1).
    + apply (refines_forallR _ _ _ (go _)). intro a. right. pclearbot.
      apply (CIH _ (Tau phi2)).
      * pfold. constructor. left. apply H.
      * rewrite <- H0. rewrite (observing_intros eq (go (observe phi)) phi eq_refl).
        apply H1.
    + destruct H1 as [ a H1 ]. apply (refines_existsR _ _ _ (go _)). exists a.
      right. pclearbot. apply (CIH _ (Tau phi2)).
      * pfold. constructor. left. apply H.
      * rewrite <- H0. rewrite (observing_intros eq (go (observe phi)) phi eq_refl).
        apply H1.
  - destruct t1'.
    + inversion r23.
    + inversion r23.
    + 
