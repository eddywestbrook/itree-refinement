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
  induction IN; eauto; constructor.
Qed.

Lemma monotone_satisfies_ {E R} : monotone2 (@satisfies_ E R).
Proof. red. intros. eapply monotone_satisfiesF; eauto. Qed.

Global Hint Resolve monotone_satisfies_ : paco.

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
 *** One-step refinement of itree specs
 ***)

(* One itree_spec refines another iff, after turning finitely many quantifier
events to actual quantifiers, they have the same constructor with continuations
such that the first continuation coinductively refines the second *)
Inductive refines1F {E R} (F : itree_spec E R -> itree_spec E R -> Prop) : 
  itree_spec' E R -> itree_spec' E R -> Prop :=
  | refines1_Ret (r : R) : refines1F F (RetF r) (RetF r)
  | refines1_TauLR (phi1 phi2 : itree_spec E R) :
      F phi1 phi2 -> refines1F F (TauF phi1) (TauF phi2)
(*
  | refines1_TauL phi ophi :
      refines1F F (observe phi) ophi -> refines1F F (TauF phi) ophi
  | refines1_TauR ophi phi :
      refines1F F ophi (observe phi) -> refines1F F ophi (TauF phi)
*)
  | refines1_VisLR A e kphi1 kphi2 :
      (forall a : A, F (kphi1 a) (kphi2 a) ) ->
      refines1F F (VisF e kphi1) (VisF e kphi2)
  | refines1_forallR A kphi phi :
      (forall a : A, refines1F F phi (observe (kphi a))) ->
      refines1F F phi (VisF Spec_forall kphi)
  | refines1_forallL A kphi phi (a : A) :
      (refines1F F (observe (kphi a)) phi) ->
      refines1F F (VisF Spec_forall kphi) phi
  | refines1_existsR A kphi phi (a : A) :
      (refines1F F phi (observe (kphi a))) ->
      refines1F F phi (VisF Spec_exists kphi)
  | refines1_existsL A kphi phi :
      (forall a : A, refines1F F (observe (kphi a)) phi) ->
      refines1F F (VisF Spec_exists kphi) phi
.

Global Hint Constructors refines1F : refines.

Definition refines1_ {E R} F (t1 t2: itree_spec E R) : Prop :=
  refines1F F (observe t1) (observe t2).

Lemma monotone_refines1F {E R} (ot1 ot2 : itree_spec' E R) sim sim' 
  (LE : sim <2= sim' )
  (IN : refines1F sim ot1 ot2) : 
  refines1F sim' ot1 ot2.
Proof.
  induction IN; eauto with refines.
Qed.

Lemma monotone_refines1_ {E R} : monotone2 (@refines1_ E R).
Proof. red. intros. eapply monotone_refines1F; eauto. Qed.

Global Hint Resolve monotone_refines1_ : paco.

Instance Proper_upaco2_refines1_ {E R} :
  Proper ((eq ==> eq ==> impl) ==> eq ==> eq ==> impl) (upaco2 (@refines1_ E R)).
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
Lemma upaco2_refines1F_bot_r {E R} r t1 t2 :
  upaco2
    (fun (F : itree_spec E R -> itree_spec E R -> Prop) (t4 t5 : itree_spec E R) =>
     refines1F F (observe t4) (observe t5)) bot2 t1 t2 ->
  upaco2
    (fun (F : itree_spec E R -> itree_spec E R -> Prop) (t0 t4 : itree_spec E R) =>
     refines1F F (observe t0) (observe t4)) r t1 t2.
Proof.
  intro H.
  eapply (Proper_upaco2_refines1_ _ _ _ t1 t1 eq_refl t2 t2 eq_refl H). Unshelve.
  intros _ _ _ _ _ _ [].
Qed.


Definition refines1 {E R} : itree_spec E R -> itree_spec E R -> Prop :=
  paco2 refines1_ bot2.

Instance Proper_observing_eq_refines1 {E R} :
  Proper (observing eq ==> observing eq ==> impl) (@refines1 E R).
Proof.
  unfold Proper, respectful, impl.
  intros t1 t2 e12 t3 t4 e34 r13. destruct e12 as [e12]. destruct e34 as [e34].
  pfold. punfold r13. unfold refines1_ in * |- *.
  rewrite e12 in r13. rewrite e34 in r13.
  assumption.
Qed.

(* Reflexivity of refinement *)
Instance Reflexive_refines1 {E R} : Reflexive (@refines1 E R).
Proof.
  red. pcofix CIH. intro t. pfold. red.
  destruct (observe t); constructor; eauto.
Qed.

(* Properness of bind w.r.t. refinement *)
Instance Proper_bind_refines1 {E R1 R2} :
  Proper (@refines1 E R1 ==> (eq ==> @refines1 E R2) ==> @refines1 E R2) bind.
Admitted.

Ltac inj_existT := repeat match goal with | H : existT _ _ _ = _ |- _ => apply inj_pair2 in H end.

Lemma refines1_Vis_forallR : forall (E : Type -> Type) (R A : Type) (t : itree_spec E R) k,
         refines1 t (Vis Spec_forall k) ->
         forall a : A, refines1 t (k a).
Proof.
  intros E R A. pcofix CIH. intros t k Href a.
  pfold. revert a. red. punfold Href. red in Href.
  cbn in *. remember (observe t) as ot. clear Heqot.
  remember (VisF Spec_forall k) as x.
  hinduction Href before r; intros; inv Heqx; inj_existT; subst; pclearbot.
  - econstructor. Unshelve. 2 : apply a. specialize (H a).
    assert (paco2 refines1_ r (kphi1 a) (k a)). eapply paco2_mon; intros; try contradiction; eauto.
    inv PR. punfold H0.
  - clear H0. assert (refines1 (go phi) (k a) ).
    { pstep. apply H. }
    enough (paco2 refines1_ r (go phi) (k a) ).
    { punfold H1. }
    eapply paco2_mon; eauto. intros; contradiction.
  - econstructor. Unshelve. 2 : apply a. eapply IHHref; eauto.
  - econstructor. intros. eapply H0; eauto.
Qed.

Lemma refines1_Vis_existsL : forall (E : Type -> Type) (R A : Type) (t : itree_spec E R) k,
         refines1 (Vis Spec_exists k) t ->
         forall a : A, refines1 (k a) t.
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


(* A version of refines1F specialized to a forall on the left *)
Inductive forallRefines1F {E R} (F : itree_spec E R -> itree_spec E R -> Prop)
          {A} (kphi1: A -> itree_spec E R)
  : itree_spec' E R -> Prop :=
  | forallRefines1_VisLR kphi2 :
      (forall a : A, F (kphi1 a) (kphi2 a)) ->
      forallRefines1F F kphi1 (VisF Spec_forall kphi2)
  | forallRefines1_forallR B kphi2 :
      (forall b : B, forallRefines1F F kphi1 (observe (kphi2 b))) ->
      forallRefines1F F kphi1 (VisF Spec_forall kphi2)
  | forallRefines1_forallL phi (a : A) :
      refines1F F (observe (kphi1 a)) phi ->
      forallRefines1F F kphi1 phi
  | forallRefines1_existsR B kphi2 (b : B) :
      (forallRefines1F F kphi1 (observe (kphi2 b))) ->
      forallRefines1F F kphi1 (VisF Spec_exists kphi2)
.

(* FIXME: should we replace the recursive call to refines1F in the above with
just a refines1? *)

Lemma refines1F_Vis_forallL : forall (E : Type -> Type) (R A : Type) F
                                   (t : itree_spec' E R) (k : A -> itree_spec E R),
    refines1F F (VisF Spec_forall k) t ->
    @forallRefines1F E R F A k t.
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
    apply forallRefines1_VisLR. apply H.
  - apply forallRefines1_forallR. intro b. apply H0. assumption.
  - assert (A0=A); [ inversion Heqt1; reflexivity | ].
    revert kphi Heqt1 a H IHrefines1F; rewrite H0; intros.
    assert (kphi=k); [ inversion Heqt1; inj_existT; assumption | ].
    rewrite H1 in H.
    eapply forallRefines1_forallL; eassumption.
  - eapply forallRefines1_existsR. apply IHrefines1F. assumption.
  - inversion Heqt1.
Qed.


(* A version of refines1F specialized to a Tau on the left *)
Inductive tauRefines1F {E R} (F : itree_spec E R -> itree_spec E R -> Prop)
          (phi1: itree_spec E R)
  : itree_spec' E R -> Prop :=
  | tauRefines1_VisLR phi2 : F phi1 phi2 -> tauRefines1F F phi1 (TauF phi2)
  | tauRefines1_forallR B kphi2 :
      (forall b : B, tauRefines1F F phi1 (observe (kphi2 b))) ->
      tauRefines1F F phi1 (VisF Spec_forall kphi2)
  | tauRefines1_existsR B kphi2 (b : B) :
      tauRefines1F F phi1 (observe (kphi2 b)) ->
      tauRefines1F F phi1 (VisF Spec_exists kphi2)
.

Lemma refines1F_Tau : forall (E : Type -> Type) (R : Type) F
                            t1 (t2 : itree_spec' E R),
    refines1F F (TauF t1) t2 ->
    @tauRefines1F E R F t1 t2.
Proof.
  intros. remember (TauF t1) as t. induction H; inversion Heqt.
  - rewrite <- H1. constructor. assumption.
  - constructor. intro b. apply H0. assumption.
  - econstructor. apply IHrefines1F. assumption.
Qed.


(* One-step refinement defines a subset for satisfaction *)
Theorem refines1SatisfiesSubset {E R} t1 (t2 t3: itree_spec E R) :
  satisfies t1 t2 -> refines1 t2 t3 -> satisfies t1 t3.
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
  - remember (refines1F_Tau _ _ _ _ _ Ht23) as Ht23'. clear HeqHt23' Ht23.
    induction Ht23'.
    + constructor. apply IHHt12. pclearbot. punfold H.
    + constructor. intro b. apply H0.
    + econstructor. eassumption.
  - pclearbot.
    + remember (VisF (Spec_vis e) kphi2) as x.
      hinduction Ht23 before r; intros; inv Heqx; inj_existT; subst; eauto.
      pclearbot. econstructor. right. eapply CIH; try apply H0; try apply H.
  - remember (refines1F_Vis_forallL _ _ _ _ _ _ Ht23) as Ht23'.
    clear HeqHt23' Ht23. induction Ht23'.
    * apply satisfies_forallR. intro a.
      apply (H0 a).
      eapply (paco2_unfold (gf:=refines1_)); [ apply monotone_refines1_ | ].
      destruct (H1 a); [ eassumption | contradiction ].
    * apply satisfies_forallR. intro b. apply H2.
    * eapply H0; eassumption.
    * eapply satisfies_existsR. eassumption.
  - assert (refines1 (Vis Spec_exists kphi) (go ot3)); [ pfold; apply Ht23 | ].
    apply IHHt12; try assumption.
    remember (refines1_Vis_existsL _ _ _ (go ot3) kphi H a). clear Heqr0.
    red in r0. punfold r0.
Qed.


(* NOTE: this is the straightforward rewriting of mrec for itree_spec *)
(*
Definition interp_mrec_spec {D E : Type -> Type}
           (ctx : D ~> itree_spec (D +' E)) : itree_spec (D +' E) ~> itree_spec E :=
  fun R =>
    ITree.iter (fun t : itree_spec (D +' E) R =>
      match observe t with
      | RetF r => Ret (inr r)
      | TauF t => Ret (inl t)
      | VisF Spec_forall k => Vis Spec_forall (fun x => Ret (inl (k x)))
      | VisF Spec_exists k => Vis Spec_exists (fun x => Ret (inl (k x)))
      | VisF (Spec_vis (inl1 d)) k => Ret (inl (ctx _ d >>= k))
      | VisF (Spec_vis (inr1 e)) k => Vis (Spec_vis e) (fun x => Ret (inl (k x)))
      end).
*)

(* This version essentially inlines ITree.iter *)
Definition interp_mrec_spec' {D E : Type -> Type}
           (ctx : D ~> itree_spec (D +' E)) : itree_spec (D +' E) ~> itree_spec E :=
  fun R =>
    cofix mrec_ (t : itree_spec (D +' E) R) : itree_spec E R :=
    match observe t with
      | RetF r => Ret r
      | TauF t' => Tau (mrec_ t')
      | VisF Spec_forall k => Vis Spec_forall (fun x => mrec_ (k x))
      | VisF Spec_exists k => Vis Spec_exists (fun x => mrec_ (k x))
      | VisF (Spec_vis (inl1 d)) k => Tau (mrec_ (ctx _ d >>= k))
      | VisF (Spec_vis (inr1 e)) k =>
        Vis (Spec_vis e) (fun x => mrec_ (k x))
    end.

(* This version is a top-level CoFixpoint, which seems slightly nicer *)
CoFixpoint interp_mrec_spec {D E : Type -> Type}
           (ctx : D ~> itree_spec (D +' E)) {R} (t : itree_spec (D +' E) R)
  : itree_spec E R :=
  match observe t with
  | RetF r => Ret r
  | TauF t' => Tau (interp_mrec_spec ctx t')
  | VisF Spec_forall k => Vis Spec_forall (fun x => interp_mrec_spec ctx (k x))
  | VisF Spec_exists k => Vis Spec_exists (fun x => interp_mrec_spec ctx (k x))
  | VisF (Spec_vis (inl1 d)) k => Tau (interp_mrec_spec ctx (ctx _ d >>= k))
  | VisF (Spec_vis (inr1 e)) k =>
    Vis (Spec_vis e) (fun x => interp_mrec_spec ctx (k x))
  end.

Definition mrec_spec {D E : Type -> Type}
           (ctx : D ~> itree_spec (D +' E)) : D ~> itree_spec E :=
  fun R d => interp_mrec_spec ctx (ctx _ d).

Instance Proper_observing_eq_interp_mrec_spec {D E T} ctx :
  Proper (observing eq ==> observing eq) (@interp_mrec_spec D E ctx T).
Admitted.

Theorem refines1_interp_mrec {D E R} (ctx1 ctx2 : D ~> itree_spec (D +' E))
        (t1 t2 : itree_spec (D +' E) R) :
  (forall R d, refines1 (ctx1 R d) (ctx2 R d)) -> refines1 t1 t2 ->
  refines1 (interp_mrec_spec ctx1 t1) (interp_mrec_spec ctx2 t2).
Proof.
  intros rctx. revert t1 t2. pcofix CIH. intros t1 t2 Ht12.
  pfold. red. punfold Ht12. red in Ht12.
  assert (observing eq t1 (go (observe t1))); [ constructor; reflexivity | ].
  assert (observing eq t2 (go (observe t2))); [ constructor; reflexivity | ].
  rewrite H. rewrite H0.
  remember (observe t1) as ot1. remember (observe t2) as ot2.
  clear t1 t2 H H0 Heqot1 Heqot2.
  hinduction Ht12 before CIH; intros.
  - assert (observe (interp_mrec_spec ctx1 (Ret r0)) = (RetF r0)) as eq1;
      [ reflexivity | ].
    rewrite eq1.
    assert (observe (interp_mrec_spec ctx2 (Ret r0)) = (RetF r0)) as eq2;
      [ reflexivity | ].
    rewrite eq2.
    constructor.
  - assert (observe (interp_mrec_spec ctx1 (Tau phi1)) =
            TauF (interp_mrec_spec ctx1 phi1)) as eq1; [ reflexivity | ].
    rewrite eq1.
    assert (observe (interp_mrec_spec ctx2 (Tau phi2)) =
            TauF (interp_mrec_spec ctx2 phi2)) as eq2; [ reflexivity | ].
    rewrite eq2.
    constructor. right. pclearbot.
    apply CIH. assumption.
  - destruct e as [ e | | ]; [ destruct e | | ].
    + assert (observe (interp_mrec_spec ctx1 (Vis (Spec_vis (inl1 d)) kphi1)) =
              TauF (interp_mrec_spec ctx1 (ctx1 _ d >>= kphi1))) as eq1;
        [ reflexivity | ].
      rewrite eq1.
      assert (observe (interp_mrec_spec ctx2 (Vis (Spec_vis (inl1 d)) kphi2)) =
              TauF (interp_mrec_spec ctx2 (ctx2 _ d >>= kphi2))) as eq2;
        [ reflexivity | ].
      rewrite eq2.
      constructor. right. pclearbot. apply CIH.
      eapply Proper_bind_refines1; [ apply rctx | ].
      intros x y eq_xy; rewrite eq_xy. apply H.
    + assert (observe (interp_mrec_spec ctx1 (Vis (Spec_vis (inr1 e)) kphi1)) =
              VisF (Spec_vis e) (fun x => interp_mrec_spec ctx1 (kphi1 x))) as eq1;
        [ reflexivity | ].
      rewrite eq1.
      assert (observe (interp_mrec_spec ctx2 (Vis (Spec_vis (inr1 e)) kphi2)) =
              VisF (Spec_vis e) (fun x => interp_mrec_spec ctx2 (kphi2 x))) as eq2;
        [ reflexivity | ].
      rewrite eq2.
      constructor. right. pclearbot. apply CIH. apply H.
    + assert (observe (interp_mrec_spec ctx1 (Vis Spec_forall kphi1)) =
              VisF Spec_forall (fun x => interp_mrec_spec ctx1 (kphi1 x))) as eq1;
        [ reflexivity | ].
      rewrite eq1.
      assert (observe (interp_mrec_spec ctx2 (Vis Spec_forall kphi2)) =
              VisF Spec_forall (fun x => interp_mrec_spec ctx2 (kphi2 x))) as eq2;
        [ reflexivity | ].
      rewrite eq2.
      constructor. right. pclearbot. apply CIH. apply H.
    + assert (observe (interp_mrec_spec ctx1 (Vis Spec_exists kphi1)) =
              VisF Spec_exists (fun x => interp_mrec_spec ctx1 (kphi1 x))) as eq1;
        [ reflexivity | ].
      rewrite eq1.
      assert (observe (interp_mrec_spec ctx2 (Vis Spec_exists kphi2)) =
              VisF Spec_exists (fun x => interp_mrec_spec ctx2 (kphi2 x))) as eq2;
        [ reflexivity | ].
      rewrite eq2.
      constructor. right. pclearbot. apply CIH. apply H.
  - assert (observe (interp_mrec_spec ctx2 (Vis Spec_forall kphi)) =
            VisF Spec_forall (fun x => interp_mrec_spec ctx2 (kphi x))) as eq2;
      [ reflexivity | ].
    rewrite eq2.
    constructor. intro a.
    assert (observing eq (go (observe (kphi a))) (kphi a)) as eq2';
      [ constructor; reflexivity | ].
    rewrite <- eq2'. apply H0.
  - assert (observe (interp_mrec_spec ctx1 (Vis Spec_forall kphi)) =
            VisF Spec_forall (fun x => interp_mrec_spec ctx1 (kphi x))) as eq1;
      [ reflexivity | ].
    rewrite eq1. apply (refines1_forallL _ _ _ _ a).
    apply IHHt12.
  - assert (observe (interp_mrec_spec ctx2 (Vis Spec_exists kphi)) =
            VisF Spec_exists (fun x => interp_mrec_spec ctx2 (kphi x))) as eq2;
      [ reflexivity | ].
    rewrite eq2. apply (refines1_existsR _ _ _ _ a).
    assert (observing eq (go (observe (kphi a))) (kphi a)) as eq2';
      [ constructor; reflexivity | ].
    apply IHHt12.
  - assert (observe (interp_mrec_spec ctx1 (Vis Spec_exists kphi)) =
            VisF Spec_exists (fun x => interp_mrec_spec ctx1 (kphi x))) as eq1;
      [ reflexivity | ].
    rewrite eq1.
    constructor. intro a.
    assert (observing eq (go (observe (kphi a))) (kphi a)) as eq2';
      [ constructor; reflexivity | ].
    rewrite <- eq2'. apply H0.
Qed.

(* FIXME: the more general approach requires refinement between different event
types *)
(*
Theorem refines1_interp_mrec {D1 D2 E R}
        (Drel : forall A, D1 A -> D2 A -> Prop)
        (ctx1 : D1 ~> itree_spec (D1 +' E)) (ctx2 : D2 ~> itree_spec (D2 +' E))
        (t1 : itree_spec (D1 +' E) R) (t2 : itree_spec (D2 +' E) R) :
  (forall R A d1 d2, Drel A d1 d2 -> refines1 (ctx1 _ d1) (ctx2 _ d2)) ->
  refines1 t1 t2 ->
  refines1 (interp_mrec_spec ctx1 t1) (interp_mrec_spec ctx2 t2).
Proof.
  intros rctx. revert t1 t2. pcofix CIH. intros t1 t2 Ht12.
  pfold. red. punfold Ht12. red in Ht12.
  assert (observing eq t1 (go (observe t1))); [ admit | ].
  assert (observing eq t2 (go (observe t2))); [ admit | ].
  rewrite H. rewrite H0.
  remember (observe t1) as ot1. remember (observe t2) as ot2.
  clear t1 t2 H H0 Heqot1 Heqot2.
  hinduction Ht12 before CIH; intros.
  - assert (observe (interp_mrec_spec ctx1 (Ret r0)) = (RetF r0)) as eq1;
      [ reflexivity | ].
    rewrite eq1.
    assert (observe (interp_mrec_spec ctx2 (Ret r0)) = (RetF r0)) as eq2;
      [ reflexivity | ].
    rewrite eq2.
    constructor.
  - assert (observe (interp_mrec_spec ctx1 (Tau phi1)) =
            TauF (interp_mrec_spec ctx1 phi1)) as eq1; [ reflexivity | ].
    rewrite eq1.
    assert (observe (interp_mrec_spec ctx2 (Tau phi2)) =
            TauF (interp_mrec_spec ctx2 phi2)) as eq2; [ reflexivity | ].
    rewrite eq2.
    constructor. right. pclearbot.
    apply CIH. assumption.
  - 
*)


(***
 *** Contextual refinement
 ***)

Inductive crefines {E R A} : (A -> itree_spec E R) -> (A -> itree_spec E R) -> Prop :=
| refines1_crefines f1 f2 : (forall a, refines1 (f1 a) (f2 a)) -> crefines f1 f2
| eutt_crefines f1 f2 : (forall a, eutt eq (f1 a) (f2 a)) -> crefines f1 f2
| refines_trans f1 f2 f3 : crefines f1 f2 -> crefines f2 f3 -> crefines f1 f3
.
Print mrec.

(***
 *** Equivalence-closed one-step refinement
 ***)

Variant refines1e {E R} : itree_spec E R -> itree_spec E R -> Prop :=
| refines1_refines t1 t1' t2' t2 :
    eutt eq t1 t1' -> refines1 t1' t2' -> eutt eq t2' t2 -> refines1e t1 t2.

(* This notion of refinement defines a subset for satisfaction *)
Theorem refines1eSatisfiesSubset {E R} t1 (t2 t3: itree_spec E R) :
  satisfies t1 t2 -> refines1e t2 t3 -> satisfies t1 t3.
Proof.
  intros Ht12 Ht23; destruct Ht23. rewrite H in Ht12. rewrite <- H1.
  eapply refines1SatisfiesSubset; eassumption.
Qed.

Instance Reflexive_refines1e E R : Reflexive (@refines1e E R).
Proof.
  intro t. econstructor; reflexivity.
Qed.

Instance Proper_eutt_refines_impl {E R} :
  Proper (eutt eq ==> eutt eq ==> impl) (@refines1e E R).
Proof.
  intros t1 t1' e1 t2 t2' e2 r12.
  destruct r12.
  econstructor; [ | apply H0 | ]; etransitivity; try eassumption;
    symmetry; eassumption.
Qed.

(* All the refines1 constructors lift to refines1e *)

Definition refines1e_Ret {E R} r : @refines1e E R (Ret r) (Ret r).
  reflexivity.
Defined.

Definition refines1e_TauLR {E R} phi1 phi2 :
  @refines1e E R phi1 phi2 -> refines1e (Tau phi1) (Tau phi2).
Proof.
  repeat rewrite tau_eutt. intro; assumption.
Defined.

Definition refines1e_VisLR {E R} A e kphi1 kphi2
           (f : forall a : A, refines1e (kphi1 a) (kphi2 a)) :
  @refines1e E R (Vis e kphi1) (Vis e kphi2).
Proof.
  assert (forall a, exists t1, exists t2,
                 eutt eq (kphi1 a) t1 /\ refines1 t1 t2 /\ eutt eq t2 (kphi2 a)).
  - intro a. destruct (f a).
    eexists; eexists; split; [ | split ]; try eassumption.
  - 

  | refines1_forallR A kphi phi :
      (forall a : A, refines1F F phi (observe (kphi a))) ->
      refines1F F phi (VisF Spec_forall kphi)
  | refines1_forallL A kphi phi (a : A) :
      (refines1F F (observe (kphi a)) phi) ->
      refines1F F (VisF Spec_forall kphi) phi
  | refines1_existsR A kphi phi (a : A) :
      (refines1F F phi (observe (kphi a))) ->
      refines1F F phi (VisF Spec_exists kphi)
  | refines1_existsL A kphi phi :
      (forall a : A, refines1F F (observe (kphi a)) phi) ->
      refines1F F (VisF Spec_exists kphi) phi
.


(***
 *** Multi-step Refinement
 ***)

Inductive refines {E R} : itree_spec E R -> itree_spec E R -> Prop :=
| refines1_refines t1 t2 : refines1 t1 t2 -> refines t1 t2
| eutt_refines t1 t2 : eutt eq t1 t2 -> refines t1 t2
| refines_trans t1 t2 t3 : refines t1 t2 -> refines t2 t3 -> refines t1 t3
.

(* Multi-step refinement defines a subset for satisfaction *)
Theorem refinesSatisfiesSubset {E R} t1 (t2 t3: itree_spec E R) :
  satisfies t1 t2 -> refines t2 t3 -> satisfies t1 t3.
Proof.
  intros Ht12 Ht23; revert t1 Ht12; induction Ht23; intros.
  - eapply refines1SatisfiesSubset; eassumption.
  - rewrite H in Ht12. assumption.
  - apply IHHt23_2. apply IHHt23_1. assumption.
Qed.

Instance Reflexive_refines E R : Reflexive (@refines E R).
Proof.
  intro t. apply refines1_refines. reflexivity.
Qed.

Instance Transitive_refines E R : Transitive (@refines E R).
Proof.
  intros t1 t2 t3 r12 r23. eapply refines_trans; eassumption.
Qed.

Instance Proper_eutt_refines_impl {E R} :
  Proper (eutt eq ==> eutt eq ==> impl) (@refines E R).
Proof.
  intros t1 t1' e1 t2 t2' e2 r12.
  transitivity t1; [ apply eutt_refines; symmetry; assumption | ].
  transitivity t2; [ assumption | apply eutt_refines; assumption ].
Qed.

(* All the refines1 constructors lift to refines *)

Definition refines_Ret {E R} (r : R) : @refines E R (Ret r) (Ret r).
Proof.
  reflexivity.
Defined.

Definition refines_TauLR {E R} (phi1 phi2 : itree_spec E R)
           (r:refines phi1 phi2) : refines (Tau phi1) (Tau phi2).
Proof.
  rewrite tau_eutt. rewrite tau_eutt. assumption.
Defined.

(* FIXME: the following does not hold!
Definition refines_VisLR {E R} A e kphi1 kphi2
      (f: forall a : A, @refines E R (kphi1 a) (kphi2 a)) :
  refines (Vis e kphi1) (Vis e kphi2).
Proof.
*)


(***
 *** FIXME: concrete specs are deprecated, and should maybe be deleted...
 ***)
Inductive isConcreteF {E R} (F : itree_spec E R -> Prop) :
  itree_spec' E R -> Prop :=
  | isConcrete_Ret (r : R) : isConcreteF F (RetF r)
  | isConcrete_Tau (phi : itree_spec E R) :
      F phi -> isConcreteF F (TauF phi)
  | isConcrete_Vis A e kphi :
      (forall a:A, F (kphi a)) -> isConcreteF F (VisF (Spec_vis e) kphi).

Global Hint Constructors isConcreteF : refines.
Definition isConcrete_ {E R} F (t: itree_spec E R) : Prop :=
  isConcreteF F (observe t).

Lemma monotone_isConcreteF {E R} (ot : itree_spec' E R) sim sim' 
  (LE : sim <1= sim' )
  (IN : isConcreteF sim ot) : 
  isConcreteF sim' ot.
Proof.
  induction IN; eauto with refines.
Qed.

Lemma monotone_isConcrete_ {E R} : monotone1 (@isConcrete_ E R).
Proof. red. intros. eapply monotone_isConcreteF; eauto. Qed.

Global Hint Resolve monotone_isConcrete_ : paco.

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
  refines1 t1 t2 -> refines1 t2 t3 -> refines1 t1 t3.
Proof.
  revert t1 t2 t3 isc; pcofix CIH. intros t1 t2 t3 isc Ht12 Ht23.
  pfold. red. punfold Ht12. red in Ht12.
  punfold Ht23. red in Ht23.
  remember (observe t3) as ot3. clear t3 Heqot3.
  punfold isc. red in isc. remember (observe t1) as ot1. clear t1 Heqot1.
  hinduction Ht12 before r; intros.
  - remember (RetF r0) as x.
    hinduction Ht23 before r; intros; inv Heqx; eauto with refines.
  - pclearbot. remember (TauF phi2) as x. inversion isc.
    hinduction Ht23 before r; intros; inv Heqx; pclearbot; eauto with refines.
  - pclearbot. destruct e.
    + remember (VisF (Spec_vis e) kphi2) as x.
      hinduction Ht23 before r; intros; inv Heqx; inj_existT; subst;
        eauto with refines.
      pclearbot. econstructor. right. eapply CIH; try apply H0; try apply H.
      eapply (isConcreteVisInv e0). pfold. apply isc.
    + inversion isc.
    + inversion isc.
  - remember (refines1F_Vis_forallL _ _ _ _ _ _ Ht23) as Ht23'.
    clear HeqHt23' Ht23. induction Ht23'.
    * apply refines1_forallR. intro a.
      eapply H0; [ apply CIH | assumption | ].
      eapply (paco2_unfold (gf:=refines1_)); [ apply monotone_refines1_ | ].
      destruct (H1 a); [ eassumption | contradiction ].
    * apply refines1_forallR. intro b. apply H2.
    * eapply H0; eassumption.
    * eapply refines1_existsR. eassumption.
  - inversion isc.
  - assert (refines1 (Vis Spec_exists kphi) (go ot3)); [ pfold; apply Ht23 | ].
    apply IHHt12; try assumption.
    remember (refines1_Vis_existsL _ _ _ (go ot3) kphi H a). clear Heqr0.
    red in r0. punfold r0.
  - inversion isc.
Qed.
