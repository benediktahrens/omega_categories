Require Export Unicode.Utf8_core.
Require Import Vector.
Require Export path.

Set Universes Polymorphic.
Set Implicit Arguments.

Class Contr_internal (A : Type) := BuildContr {
  center : A ;
  contr : (forall y : A, center = y)
}.

Inductive trunc_index : Type :=
| minus_two : trunc_index
| trunc_S : trunc_index -> trunc_index.

(** We will use [Notation] for [trunc_index]es, so define a scope for them here. *)
Delimit Scope trunc_scope with trunc.
Bind Scope trunc_scope with trunc_index.
Arguments trunc_S _%trunc_scope.

Fixpoint nat_to_trunc_index (n : nat) : trunc_index
  := match n with
       | 0 => trunc_S (trunc_S minus_two)
       | S n' => trunc_S (nat_to_trunc_index n')
     end.

Coercion nat_to_trunc_index : nat >-> trunc_index.

Fixpoint IsTrunc_internal (n : trunc_index) (A : Type) : Type :=
  match n with
    | minus_two => Contr_internal A
    | trunc_S n' => forall (x y : A), IsTrunc_internal n' (x = y)
  end.

Notation minus_one:=(trunc_S minus_two).
(** Include the basic numerals, so we don't need to go through the coercion from [nat], and so that we get the right binding with [trunc_scope]. *)
Notation "0" := (trunc_S minus_one) : trunc_scope.
Notation "1" := (trunc_S 0) : trunc_scope.
Notation "2" := (trunc_S 1) : trunc_scope.

Arguments IsTrunc_internal n A : simpl nomatch.

Class IsTrunc (n : trunc_index) (A : Type) : Type :=
  Trunc_is_trunc : IsTrunc_internal n A.

(** We use the priciple that we should always be doing typeclass resolution on truncation of non-equality types.  We try to change the hypotheses and goals so that they never mention something like [IsTrunc n (_ = _)] and instead say [IsTrunc (S n) _].  If you're evil enough that some of your paths [a = b] are n-truncated, but others are not, then you'll have to either reason manually or add some (local) hints with higher priority than the hint below, or generalize your equality type so that it's not a path anymore. *)

Typeclasses Opaque IsTrunc. (* don't auto-unfold [IsTrunc] in typeclass search *)

Arguments IsTrunc : simpl never. (* don't auto-unfold [IsTrunc] with [simpl] *)

Instance istrunc_paths (A : Type) n `{H : IsTrunc (trunc_S n) A} (x y : A)
: IsTrunc n (x = y)
  := H x y. (* but do fold [IsTrunc] *)

Notation Contr := (IsTrunc minus_two).

Notation IsHProp := (IsTrunc minus_one).

Notation IsHSet := (IsTrunc 0).

Hint Extern 0 => progress change Contr_internal with Contr in * : typeclass_instances.

Lemma contr_inhabited_hprop (A : Type) `{H : IsHProp A} (x : A)
  : Contr A.
Proof.
  exists x.
  intro y.
  destruct (H x y). exact center0.
Defined.

Definition path_contr (A:Type) `{Contr A} (x y : A) : x = y
  := inverse (contr x) @ (contr y).

(** Similarly, any two parallel paths in a contractible space are homotopic, which is just the principle UIP. *)
Definition path2_contr (A:Type) `{Contr A} {x y : A} (p q : x = y) : p = q.
Proof.
  assert (K : forall (r : x = y), r = path_contr x y).
    intro r; destruct r; symmetry; now apply inverse_inv_L.
  transitivity (path_contr x y);auto.
Defined.

Instance contr_paths_contr (A:Type) `{Contr A} (x y : A) : Contr (x = y) | 10000 := let c := {|
  center := inverse (contr x) @ contr y;
  contr := path2_contr (inverse (contr x) @ contr y)
|} in c.

(** If inhabitation implies contractibility, then we have an h-proposition.  We probably won't often have a hypothesis of the form [A -> Contr A], so we make sure we give priority to other instances. *)
Instance hprop_inhabited_contr (A : Type) : (A -> Contr A) -> IsHProp A | 10000.
Proof.
  intros H x y.
  pose (C := H x).
  apply contr_paths_contr. exact C.
Defined.



Theorem allpath_hprop (A : Type) `{H : IsHProp A} : forall x y : A, x = y.
Proof.
  apply H.
Defined.

Theorem hprop_allpath (A : Type) : (forall (x y : A), x = y) -> IsHProp A.
  intros H x y.
  pose (C := @BuildContr A x (H x)).
  apply contr_paths_contr.
  exact C.
Defined.

Definition axiomK A := forall (x : A) (p : x = x), p = eq_refl x.

Definition axiomK_hset {A} : IsHSet A -> axiomK A.
Proof.
  intros H x p.
  apply (H x x p (eq_refl x)).
Defined.

Definition hset_axiomK {A} `{axiomK A} : IsHSet A.
Proof.
  intros x y H.
  apply @hprop_allpath.
  intros p q. destruct q. apply axiomK0.
Defined.

Definition HSet := {S : Type & IsHSet S}.

Instance HSet_IsHSet (S : HSet) : IsHSet S.1 := S.2.

Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3, format "f '^-1'").
Notation "A <~> B" := (Equiv A B) (at level 85).
Arguments eisretr {A B} f {_} _.
Arguments eissect {A B} f {_} _.
Arguments eisadj {A B} f {_} _.


Definition moveL_equiv_M A B f  `{IsEquiv A B f} (x : A) (y : B) (p : f ^-1 y = x)
  : (y = f x)
  := inverse (eisretr f y) @ ap f p.

Definition moveR_equiv_M A B f `{IsEquiv A B f} (x : A) (y : B) (p : x = f^-1 y)
  : (f x = y)
  := ap f p @ eisretr f y.

Lemma contr_equiv A B `(f : A -> B) `{IsEquiv A B f} `{Contr A}
  : Contr B.
Proof.
  exists (f (@center A _)).
  intro y.
  eapply moveR_equiv_M.
  apply contr.
Qed.

Definition contr_equiv' A B `(f : A <~> B) `{Contr A}
  : Contr B
  := @contr_equiv _ _ (equiv_fun f) (equiv_isequiv f) _.

Definition trunc_equiv A B n `(f : A -> B)
  `{IsTrunc n A} `{IsEquiv A B f}
  : IsTrunc n B.
Proof.
  generalize dependent B; generalize dependent A.
  induction n as [| n I]; simpl; intros A ? B f ?.
  - exact (@contr_equiv  _ _ f H0 _).
  - intros x y.
    admit.
    (* exact (I (f^-1 x = f^-1 y) (H (f^-1 x) (f^-1 y)) (x = y) ((@ap _ _ (f^-1) _ _)^-1) _). *)
Qed.

Definition trunc_equiv' A B n `(f : A <~> B) {H : IsTrunc n A}
  : IsTrunc n B
  := @trunc_equiv _ _ n (equiv_fun f) H (equiv_isequiv f).

Definition equiv_path_prod {A B : Type} (z z' : A * B)
  : (fst z = fst z') * (snd z = snd z')  <~>  (z = z').
Admitted.
  (* := BuildEquiv _ _ (path_prod_uncurried z z') _. *)

Instance trunc_prod A B n `{IsTrunc n A} `{IsTrunc n B} : IsTrunc n (A * B) | 100.
Proof.
  generalize dependent B; generalize dependent A.
  induction n as [| n I]; simpl; (intros A ? B ?).
  { exists (@center A _, @center B _).
    intros z; apply path_prod; apply contr. }
  { intros x y.
    exact (trunc_equiv' n (equiv_path_prod x y)). }
Defined.


Instance trunc_forall A n `{P : A -> Type} `{forall a, IsTrunc n (P a)}
  : IsTrunc n (forall a, P a).
Admitted.

Global Instance trunc_sigma A n `{P : A -> Type}
         `{IsTrunc n A} `{forall a, IsTrunc n (P a)}
: IsTrunc n (sigT P) | 100.
Admitted.
(* Proof. *)
(*   generalize dependent A. *)
(*   induction n; simpl; intros A P ac Pc. *)
(*   { exists (center; center (P (center A))). *)
(*     intros [a ?]. *)
(*     refine (path_sigma' P (contr a) (path_contr _ _)).  *)
(* } *)
(*   { intros u v. *)
(*     apply (@trunc_equiv _ _ n (path_sigma_uncurried u v)). *)
(*     admit. admit. *)
(*  } *)
(* Defined. *)

Module Export Trunc.

Private Inductive Trunc (n : trunc_index) (A :Type) : Type :=
  tr : A -> Trunc n A.
Bind Scope trunc_scope with Trunc.
Arguments tr {n A} a.

(** Make the priority 1, so that we don't override, e.g., [Unit]. *)
Instance istrunc_truncation : forall n A, IsTrunc n (Trunc n A) | 1.
Admitted.

Definition Trunc_rect {n A}
  (P : Trunc n A -> Type) `{forall aa, IsTrunc n (P aa)}
  : (forall a, P (tr a)) -> (forall aa, P aa)
:= (fun f aa => match aa with tr a => f a end).

Definition Trunc_rect4 {n A B C D}
  (P : Trunc n A -> Trunc n B -> Trunc n C -> Trunc n D -> Type) 
  `{forall aa bb cc dd, IsTrunc n (P aa bb cc dd)}
  : (forall a b c d, P (tr a) (tr b) (tr c) (tr d)) -> 
    (forall aa bb cc dd, P aa bb cc dd).
  intros. apply Trunc_rect; try apply H.
  apply (@Trunc_rect n C (fun cc => ∀ d : D, P aa bb cc (tr d))).
  intros; apply trunc_forall. intros; apply H.
  apply (@Trunc_rect n B (fun bb => ∀ (c:C) (d : D), P aa bb (tr c) (tr d))).
  repeat (intros; apply trunc_forall). intros; apply H.
  apply (@Trunc_rect n A (fun aa => ∀ (b:B) (c:C) (d : D), P aa (tr b) (tr c) (tr d))).
  repeat (intros; apply trunc_forall). intros; apply H.
  apply X. 
Defined.

End Trunc.

(** The non-dependent version of the eliminator. *)

Definition Trunc_rect_nondep {n A X} `{IsTrunc n X}
  : (A -> X) -> (Trunc n A -> X)
:= Trunc_rect (fun _ => X).

Definition hSet (T : Type) : HSet := (Trunc 0 T; istrunc_truncation 0 T).


Definition HProp := {P : Type & IsHProp P}.

Definition squash := Trunc minus_one.

Definition hProp (T : Type) : HProp := (squash T; istrunc_truncation minus_one T).



Instance trunc_succ A n `{IsTrunc n A} : IsTrunc (trunc_S n) A.
Admitted.


Definition IsHProp_IsHSet (S : HSet) (x y : S.1) : IsHProp (x = y).
apply hprop_inhabited_contr. intro H. exists H. intro H'. apply (S.2).
Defined.  



Definition decidable_paths (A : Type) :=
  forall (x y : A), (x = y) + (~ (x = y)).

(* Usually this lemma would be proved with [discriminate], but unfortunately that tactic is hardcoded to work only with Coq's [Prop]-valued equality.
   TODO: This should be in types/Sum. *)
Definition inl_injective {A B : Type} {x y : A} (p : inl B x = inl B y) : x = y :=
  (@transport _ (fun (s : A + B) => x = (match s with inl a => a | inr b => x end)) _ _ p (eq_refl x)).

Theorem axiomK_decidable {A : Type} : @decidable_paths A -> @axiomK A.
Proof.
Admitted.

Corollary hset_decidable {A : Type} : @decidable_paths A -> IsHSet A.
Proof.
  intro.
  apply @hset_axiomK. apply @axiomK_decidable. exact X.
Defined.

(* Definition contr_contr (A : Type) *)
(*   : Contr A -> Contr (Contr A). *)
(* Admitted. *)

(* Definition hprop_trunc (n : trunc_index) (A : Type) *)
(*   : IsHProp (IsTrunc n A). *)

(* Definition isHProp_Contr A : IsHProp (Contr A). *)
(*   intros x y. assert (x = y).  *)
(*   destruct x, y. apply path_sigma'. exists (path_contr (@center _ x) (@center _ y)). *)


Class IsPointed (A : Type) := point : A.
Definition pointedType := { u : Type & IsPointed u }.
Arguments point A {_}.

Instance ispointed_contr (A:Type) {H : Contr A} : IsPointed A := @center A _.

Instance ispointed_ (A:pointedType) : IsPointed A.1 := A.2.

(** A pi type with a pointed target is pointed. *)
Global Instance ispointed_forall A B {H : forall a : A, IsPointed (B a)}
: IsPointed (forall a, B a)
  := fun a => point (B a).

(** A sigma type of pointed components is pointed. *)
Global Instance ispointed_sigma A B {H:IsPointed A} {H':IsPointed (B (point A))}
: IsPointed (sigT B)
  := (point A; point (B (point A))).

(** A cartesian product of pointed types is pointed. *)
Global Instance ispointed_prod A B {H:IsPointed A} {H': IsPointed B} : IsPointed (A * B)
  := (point A, point B).

(** The type [x = x] is pointed. *)
Global Instance ispointed_loop_space A (a : A) : IsPointed (a = a) := eq_refl.

Definition loopSpace (A : pointedType) : pointedType :=
  (A.1 = A.1:Type; eq_refl A.1).

Unset Implicit Arguments. 

Fixpoint iteratedLoopSpace (n : nat) (A : Type) {H : IsPointed A} {struct n} : pointedType
  := match n with
       | O => existT IsPointed A (point A)
       | S p => iteratedLoopSpace p (point A = point A)
     end.

Set Implicit Arguments.

Definition pi_n n (A:pointedType) : HSet := hSet (iteratedLoopSpace n A.1).1.
