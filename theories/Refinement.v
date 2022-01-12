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
  red. pcofix CIH. intro t. pfold. red.
  destruct (observe t); constructor; eauto.
Qed.

Ltac inj_existT := repeat match goal with | H : existT _ _ _ = _ |- _ => apply inj_pair2 in H end.

Definition weird1 {E R} : itree_spec E R :=
  Vis Spec_forall (fun _ : unit => ITree.spin).

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

Variant non_empty (A : Type) : Prop := ne (a : A).

Variant empty (A : Type) : Prop := emp : (A -> void) -> empty A.

Instance proper_cong_refines {E R} : Proper (@eq_itree (SpecEvent E) R R eq ==> eq_itree eq ==> Basics.flip Basics.impl) refines.
Proof. Admitted.

Ltac use_simpobs := repeat match goal with
                    | H : TauF ?ot = observe ?t |- _ => apply simpobs in H 
                    | H : observe ?t = TauF ?ot  |- _ => symmetry in H; apply simpobs in H 
                    | H : RetF ?r = observe ?t |- _ => apply simpobs in H 
                    | H : observe ?t = RetF ?r  |- _ => symmetry in H; apply simpobs in H 
                    | H : VisF ?e ?k = observe ?t |- _ => apply simpobs in H 
                    | H : observe ?t = VisF ?e ?k  |- _ => symmetry in H; apply simpobs in H 
                           end.


CoFixpoint inf_forall_A {E R} (A : Type) : itree_spec E R := Vis (@Spec_forall E A) (fun _ => inf_forall_A A).

Lemma refines_Vis_forallL' : forall (E : Type -> Type) (R A : Type) (t : itree_spec E R) k,
    
         refines (Vis Spec_forall k) t->
         ( (exists k' : A -> itree_spec E R, t ≅ Vis Spec_forall k' /\ forall a, refines (k a) (k' a))  
           \/
           exists a : A, refines (k a) t).
Proof.
  intros E R A t k Hk.  punfold Hk. red in Hk.
  cbn in *. remember (VisF Spec_forall k) as x. remember (observe t) as ot.
  hinduction Hk before R; intros; inv Heqx; inj_existT; subst; pclearbot; use_simpobs.
  - left. exists kphi2. split; auto.
  - setoid_rewrite Heqot.
    match type of Heqot with | t ≅ ?t' => assert (observe t' = observe t') end. auto.
    cbn in H1.
    match type of H with | forall a, refinesF _ ?t1 _ => assert (t1 = t1) end. auto.
    eapply H0 in H2. 2 : reflexivity. 
    destruct H2.
    + destruct H2 as [k' [? ?] ]. right. eexists. pstep. econstructor. left. exists k'. split; auto.
      admit. (*here is a pretty serious problem, this is definitely false *)
    + destruct H2. right. exists x. pstep. constructor. intros.
      admit. (*this is also a problem, uggh*)

    (* setoid_rewrite Heqot. 
    enough (exists a0 : A0, forall a, refines (k a0) (kphi a) ).
    { right. destruct H1. exists x. pstep. red. constructor. intros. specialize (H1 a0).
      punfold H1. } (* definitely something weird going on in this case *) admit. *)
  - right. exists a. pstep. auto.
  - setoid_rewrite Heqot. 
    match type of Hk with refinesF _ ?t _ => assert (t = t) end; auto.
    eapply IHHk in H. 2: reflexivity.
    destruct H.
    + decompose record H. rename x into k'. 
      left. exists k'. rewrite <- H1. split; auto. admit.
    + destruct H. right. exists x. pstep. red. cbn. econstructor.
      punfold H.
Abort.


Lemma refines_Vis_forallL : forall (E : Type -> Type) (R A : Type) (t : itree_spec E R) k,
         non_empty A ->
         refines (Vis Spec_forall k) t->
         exists a : A, refines (k a) t.
Proof.
  intros E R A t k HA Hk. punfold Hk. red in Hk.
  enough (exists a, refinesF (upaco2 refines_ bot2) (observe (k a)) (observe t)).
  { destruct H. exists x. pfold. eauto. }
  cbn in Hk. remember (VisF Spec_forall k) as x.
  remember (observe t) as ot. clear Heqot. cbn in *.
  hinduction Hk before R; intros; inv Heqx; inj_existT; subst; pclearbot; eauto.
  - destruct HA. admit.
  - admit.
  - 
Abort. (* what if A is empty *)

Lemma refines_Vis_aux:
  forall (E : Type -> Type) (R : Type) (r : itree_spec E R -> itree_spec E R -> Prop) 
    (A : Type) (e : SpecEvent E A) (kphi1 kphi2 : A -> itree_spec E R),
    (forall x y z : itree_spec E R, refines x y -> refines y z -> r x z) ->
    ( forall a : A, paco2 refines_ bot2 (kphi1 a) (kphi2 a)) ->
      forall t3 : itree_spec E R,
        refinesF (upaco2 refines_ bot2) (VisF e kphi2) (observe t3) ->
        refinesF (upaco2 refines_ r) (VisF e kphi1) (observe t3).
Proof.
  intros E R r A e kphi1 kphi2 CIH Hk t3 Ht23.
  remember (observe t3) as ot3. clear Heqot3.
  assert (Hor : (exists kphi3, ot3 = VisF e kphi3) \/ (forall kphi3, ot3 <> VisF e kphi3)).
  { destruct ot3; try (right; repeat intro; discriminate).
    admit. } clear Hor.
  destruct e.
  - (*still more weirdness here*) admit.
  - (* what I want to do is have some inversion rule on Ht23, 
       then induct from there, and that might help
     *) 
    (* suppose A is empty, then t3 must be Vis Spec_forall, take one step and then done
       otherwise may have a useful inversion
     *)
    econstructor.
    remember (VisF Spec_forall kphi2) as x. 
    hinduction Ht23 before r; intros; inv Heqx; inj_existT; subst; pclearbot.
    + econstructor. (* right. eapply CIH; eauto. apply Hk. apply H.
    + eapply refines_forallR. intros. eapply H0; eauto.
    + specialize (Hk a). 
      (*here I am not sure what is going on,   *)

(*weirdness here due to the foralls having different types, may inspire different definition *)
      admit.
    + admit.
    + rewrite itree_eta' at 1. eapply refines_existsR. eauto. admit.
  -
 econstructor. 

  remember (VisF e kphi2) as x. hinduction Ht23 before r; intros; inv Heqx; inj_existT; subst.
  - constructor. right. eapply CIH; eauto. apply Hk. pclearbot. apply H.
  - econstructor. intros. eapply H0; eauto.
  - (* this inductive hypothesis is just not what I need *) 
    destruct (observe (kphi2 a) ) eqn :  Hkphi2.
    + admit.
    + admit.
    + destruct e.
      * (* induct on Ht23*) admit.
      * eapply IHHt23; eauto.
      eapply IHHt23; eauto.

 eapply IHHt23 in Hk. econstructor. Unshelve. 2 : apply a.
    

    (* this would be fine if it were coinductive, but I'm stuck now, might need another coind hyp?*)
    admit.
  - econstructor. eapply IHHt23; eauto.
  - econstructor. (*same I am not really sure how to make progress here *) admit. *)
Abort.


(* Transitivity of refinement *)
Instance Transitive_refines {E R} : Transitive (@refines E R).
Proof.
  red. pcofix CIH. intros t1 t2 t3 Ht12 Ht23.
  pfold. red. punfold Ht12. red in Ht12.
  punfold Ht23. red in Ht23.
  hinduction Ht12 before r; intros; eauto.
  - remember (RetF r0) as x. remember (observe t3) as ot3.
    clear Heqot3. hinduction Ht23 before r; intros; inv Heqx; eauto.
  - pclearbot. remember (TauF phi2) as x. remember (observe t3) as ot3.
    clear Heqot3. hinduction Ht23 before r; intros; inv Heqx; pclearbot; eauto.
  - pclearbot. 
    destruct e. 
    + remember (VisF (Spec_vis e) kphi2) as x. remember (observe t3) as ot3.
      clear Heqot3. hinduction Ht23 before r; intros; inv Heqx; inj_existT; subst; eauto.
      pclearbot. econstructor. right. eapply CIH. apply H0. apply H.
    + remember (VisF Spec_forall kphi2 ) as x. remember (observe t3) as ot3.
      clear Heqot3. hinduction Ht23 before r; intros; inv Heqx; inj_existT; subst; eauto.
      * constructor. right. pclearbot. eapply CIH. apply H0. apply H.
      * destruct (observe (kphi2 a)) eqn : Hkphi2.
        -- econstructor. Unshelve. 2 : apply a. specialize (H a). punfold H.
           red in H. rewrite Hkphi2 in H. 
           (*here we have reduced the problem to when the middle is Ret*) admit.
        -- clear IHHt23. econstructor. Unshelve. 2 : apply a. 
           (* this tau case seems like I have not learned anything, and that is problematic *)
           admit.
        -- destruct e.
           ++ clear IHHt23.

 eapply IHHt23; eauto. admit.

 eapply IHHt23.

      remember (VisF Spec_forall kphi2 ) as x. remember (observe t3) as ot3.
      assert ((exists (kphi3 : A-> itree_spec E R), ot3 = VisF Spec_forall kphi3) \/ 
              (forall (kphi3 : A -> itree_spec E R), ot3 <> VisF Spec_forall kphi3) ).
      { destruct ot3.
        all : try (right; repeat intro; discriminate; fail).
        destruct e.
        all : try (right; repeat intro; discriminate; fail). 
        admit. (* could solve with classical logic *) }
      (* this may be the wrong disjunction *)
      clear Heqot3.
      destruct H0.
      * decompose record H0. subst. apply refines_VisLR. right. eapply CIH. apply H.
        (* this last case should be a doable lemma *) admit.
      * hinduction Ht23 before r; intros; inv Heqx; inj_existT; subst; eauto.
        -- exfalso. eapply H1. reflexivity.
        -- assert (A <> A0).
           { intro. subst. eapply H2. reflexivity. }
           

          econstructor. intros. eapply H0; eauto. 
           (*I am not sure where this condition is coming from, but its presence indicates I did not set up this induction right*) admit.
        -- eapply IHHt23; eauto.
  econstructor.


clear Heqot3. hinduction Ht23 before r; intros; inv Heqx; inj_existT; subst; pclearbot; eauto.
      * econstructor. right. eapply CIH. apply H0. apply H.
      * econstructor.

      admit.
    + admit.
    + admit.
  - 
