Require Export Unicode.Utf8_core.
Set Universes Polymorphic.
Set Implicit Arguments.
Add LoadPath "." as OmegaCategories.

(* UIP_refl on Set is valid *)

Inductive Empty : Type := .

Definition idmap {A} := fun (x:A) => x.

Definition transport {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  eq_rect x P u y p.

Definition transportage {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P x) : P y :=
  eq_rect x P u y p.

Arguments transport {A} P {x y} p u : simpl nomatch.

Lemma transport_const : ∀ (A B : Type) (x y: A) (p:x = y) (y : B),
 transport (fun _ => B) p y = y. intros. destruct p. exact (eq_refl _). 
Defined.

Notation "p # u" := (transport _ p u) (right associativity, at level 65, only parsing).

Definition inverse {A : Type} {x y : A} (p : x = y) : y = x
  := match p with eq_refl => eq_refl end.

Arguments inverse {A x y} p : simpl nomatch.

(* Definition ap {A B:Type} (f:A -> B) {x y:A} (p:x = y) : f x = f y *)
(*   := match p with eq_refl => eq_refl end. *)

Definition ap := f_equal.

Definition apD {A:Type} {B:A->Type} (f:∀ a:A, B a) {x y:A} (p:x=y):
  p # (f x) = f y
  :=
  match p with eq_refl => eq_refl end.

Definition equal_f (A : Type) (P : A -> Type) (f g : forall x, P x) (p : f = g) :
forall x, f x = g x.
intro x. destruct p. reflexivity.
Defined.

Definition ap_map A B (f:A -> B) (a b : A) (p p' : a = b) (q : p = p') : 
  ap f p = ap f p'.
  apply ap. exact q.
Defined.

(** See above for the meaning of [simpl nomatch]. *)
Arguments apD {A B} f {x y} p : simpl nomatch.

Lemma transport_compose {A B} {x y : A} (P : B -> Type) (f : A -> B)
  (p : x = y) (z : P (f x))
  : transport (fun x => P (f x)) p z  =  transport P (ap f p) z.
Proof.
  destruct p; reflexivity.
Defined.

(* Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z := *)
(*   eq_rect _ (fun w => w = z) q _ (inverse p). *)
Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z.
  destruct p; exact q.
Defined.

Notation "p @ q" := (concat p q) (at level 20) : type_scope.

Lemma apD_const {A B} {x y : A} (f : A -> B) (p: x = y) :
  apD f p = transport_const p (f x) @ ap f p.
Proof.
  destruct p. reflexivity.
Defined.

Definition ap2 (T U V : Type) (f : T -> U -> V)
           (e e' : T) (h h' : U) (X :e = e') (X':h = h'): f e h = f e' h' :=
  equal_f  _ (ap f X) h @ ap (f e') X'.

Definition ap2_map (T U V : Type) (f : T -> U -> V)
           (e e': T) (h h' : U) (X X' : e = e') (Y Y' : h = h') (H : X = X')
           (H' : Y = Y'): 
  ap2 f X Y = ap2 f X' Y' := ap2 (ap2 f (h':=h')) H H' .


Definition transport_paths_r {A : Type} {x y1 y2 : A} (p : y1 = y2) (q : x = y1)
  : transport (fun y => x = y) p q = q @ p.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition transport_paths_l {A : Type} {y x1 x2 : A} (p : x1 = x2) (q : x1 = y)
  : transport (fun x => x = y) p q = inverse p @ q.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition concat_R {A : Type} {x y z : A} (p p': x = y) (q : y = z) (e: p = p'): p @ q = p' @ q
  := ap (fun p => p @ q) e.

Definition concat_L {A : Type} {x y z : A} (p : x = y) (q q' : y = z) (e: q = q'): p @ q = p @ q'
  := ap (concat p) e.

Definition concat_LR {A : Type} {x y z : A} (p p': x = y) (q q' : y = z) 
  (e : p = p') (e': q = q') : p @ q = p' @ q' := ap2 concat e e'. 

Definition concat_R_map {A : Type} {x y z : A} (p p': x = y) (q : y = z) (e e': p = p') (H : e = e')
  : concat_R q e = concat_R q e' := ap_map (fun p => p @ q) H.

Definition concat_L_map {A : Type} {x y z : A} (p : x = y) (q q': y = z) (e e': q = q') (H : e = e')
  : concat_L p e = concat_L p e' := ap_map (concat p) H.

Definition concat_LR_map {A : Type} {x y z : A} (p p': x = y) (q q': y = z) (e e': p = p') (f f' : q = q')
           (H : e = e') (H' : f = f')
  : concat_LR e f = concat_LR e' f' := ap2_map concat H H'. 

Definition concat_assoc {A : Type} {x y z w : A} (p : x = y) (q : y = z) (r : z = w) : 
  (p @ q) @ r = p @ (q @ r).
destruct p. reflexivity. Defined.

Lemma ap_concat A B (f:A -> B) (a b c : A) (p : a = b) (q : b = c) : 
  ap f (p @ q) = ap f p @ ap f q.
  destruct p. reflexivity.
Defined.

Lemma ap2_concat A B C (f:A -> B -> C) (a b c : A) (p : a = b) (q : b = c) 
      (a' b' c' : B) (p' : a' = b') (q' : b' = c') : 
  ap2 f (p @ q) (p' @ q') = ap2 f p p' @ ap2 f q q'.
  destruct p, p'. reflexivity.
Defined.

Definition ap2_map_concat (T U V : Type) (f : T -> U -> V)
           (e e': T) (h h' : U) (X X' X'': e = e') (Y Y' Y'': h = h') 
           (H : X = X') (H' : X' = X'')
           (G : Y = Y') (G':Y' = Y''):
  ap2_map f H G @ ap2_map f H' G' = ap2_map f (H@H') (G@G') :=
  inverse (ap2_concat (ap2 f (h':=h')) H H' G G').

Definition concat_R_concat {A : Type} {x y z : A} (p p' p'': x = y) (q : y = z) 
           (e : p = p') (e' : p' = p'') 
  : concat_R q (e @ e') = concat_R q e @ concat_R q e' := ap_concat (fun p => p @ q) e e'.

Definition concat_L_concat {A : Type} {x y z : A} (p : x = y) (q q' q'' : y = z) 
           (e : q = q') (e' : q' = q'') 
  : concat_L p (e @ e') = concat_L p e @ concat_L p e' := ap_concat (concat p) e e'.

Definition concat_LR_concat {A : Type} {x y z : A} (p p' p'': x = y) (q q' q'': y = z) 
           (e : p = p') (e' : p' = p'') (f : q = q') (f' : q' = q'')
  : concat_LR (e @ e') (f @ f') = concat_LR e f @ concat_LR e' f' := 
  ap2_concat concat e e' f f'.

Lemma ap_id A (a b : A) (p : a = b) :
  ap (fun x =>  x) p = p.
destruct p.
reflexivity.
Defined.

Lemma ap_inv A B (f:A -> B) (a b : A) (p : a = b) :
  inverse (ap f p) = ap f (inverse p).
  destruct p. reflexivity.
Defined.

Lemma inverse_inv_L A (x y : A) (p : x = y) : inverse p @ p = eq_refl _.
  destruct p. reflexivity.
Defined.

Lemma inverse_inv_R A (x y : A) (p : x = y) : p @ inverse p = eq_refl _.
  destruct p. reflexivity.
Defined.

Lemma idpath_L {A : Type} {x y: A} (p : x = y) : (eq_refl _) @ p = p.
destruct p. reflexivity. Defined.

Lemma idpath_R {A : Type} {x y: A} (p : x = y) : p @ (eq_refl _) = p.
destruct p. reflexivity. Defined.

Lemma cancelL {A} {x y z : A} (p : x = y) (q r : y = z)
  : (p @ q = p @ r) -> (q = r).
Proof.
  destruct p, r.
  intro a. exact (eq_sym (idpath_L q) @ a).
Defined.

Lemma cancelR {A} {x y z : A} (p q : x = y) (r : y = z)
  : (p @ r = q @ r) -> (p = q).
Proof.
  destruct r, p.
  intro a.
  exact (a @ idpath_R q).
Defined.

Definition transport_pp {A : Type} (P : A -> Type) {x y z : A} (p : x = y) (q : y = z) (u : P x) :
  p @ q # u = q # p # u :=
  match q with eq_refl =>
    match p with eq_refl => eq_refl end
  end.

Definition transport_arrow {A : Type} {B C : A -> Type}
  {x1 x2 : A} (p : x1 = x2) (f : B x1 -> C x1) (y : B x2)
  : (transport (fun x => B x -> C x) p f) y  =  p # (f (eq_sym p # y)).
Proof.
  destruct p; simpl; auto.
Defined.

Definition ap_sym {A B:Type} (f:A -> B) {x y:A} (p:x = y) : ap f (eq_sym p) = eq_sym (ap f p) :=
  match p with eq_refl => eq_refl end.


Definition transportD {A : Type} (B : A -> Type) (C : forall a:A, B a -> Type)
  {x1 x2 : A} (p : x1 = x2) (y : B x1) (z : C x1 y)
  : C x2 (p # y)
  :=
  match p with eq_refl => z end.

Definition transport_pV {A : Type} (P : A -> Type) {x y : A} (p : x = y) (z : P y)
  : p # eq_sym p # z = z
  := eq_sym (transport_pp P (eq_sym p) p z)
  @ ap (fun r => transport P r z) (inverse_inv_L p).

Definition pointwise_paths {A} {P:A->Type} (f g:forall x:A, P x) : Type
  := forall x:A, f x = g x.

Notation "f == g" := (pointwise_paths f g) (at level 70, no associativity) : type_scope.

Definition transport_forall
  {A : Type} {P : A -> Type} {C : forall x, P x -> Type}
  {x1 x2 : A} (p : x1 = x2) (f : forall y : P x1, C x1 y)
  : (transport (fun x => forall y : P x, C x y) p f)
    == (fun y =>
       transport (C x2) (transport_pV _ _ _) (transportD _ _ p _ (f (eq_sym p # y))))
  := match p with eq_refl => fun _ => eq_refl _ end.


Definition transport_paths_lr {A : Type} {x1 x2 : A} (p : x1 = x2) (q : x1 = x1)
  : transport (fun x => x = x) p q = eq_sym p @ q @ p.
Proof.
  destruct p; simpl. 
  apply (eq_sym (idpath_R q)). 
Defined.

Definition moveR_transport_p {A : Type} (P : A -> Type) {x y : A}
  (p : x = y) (u : P x) (v : P y)
  : u = inverse p # v -> p # u = v.
Proof.
  destruct p.
  exact idmap.
Defined.

Definition moveR_transport_V {A : Type} (P : A -> Type) {x y : A}
  (p : y = x) (u : P x) (v : P y)
  : u = p # v -> inverse p # u = v.
Proof.
  destruct p.
  exact idmap.
Defined.


Definition equal_f_eq (A : Type) (P : A -> Type) (f g : forall x, P x) (p : f = g) x y (q : y = x) : equal_f P p x = transport (fun x => f x = g x) q (equal_f P p y).
  destruct p, q. reflexivity.
Defined.

Definition transport2 {A : Type} (P : A -> Type) {x y : A} {p q : x = y}
  (r : p = q) (z : P x)
  : p # z = q # z
  := ap (fun p' => p' # z) r.



Definition eq_transport {A : Type} (B : A -> Type) (g : forall a:A, B a -> B a)
  {x1 x2 : A} (p : x1 = x2) (y : B x1) (q : y = g x1 y) : p # y = transport (λ a : A, B a → B a) p (g x1) (p # y).
  destruct p. exact q. Defined.

Definition transportD_eq {A : Type} (B : A -> Type) (g : forall a:A, B a -> B a)
  {x1 x2 : A} (p : x1 = x2) (y : B x1) (q : y = g x1 y)
  : transportD B (fun a b => b = g a b) p y q =
    (eq_transport _ _ p q) @ equal_f _ (apD g p) (p # y).
  destruct p. apply (eq_sym (idpath_R _)).
Defined.


Definition transport_paths_Fl {A B : Type} {f : A -> B} {x1 x2 : A} {y : B}
  (p : x1 = x2) (q : f x1 = y)
  : transport (fun x => f x = y) p q = inverse (ap f p) @ q.
Proof.
  destruct p, q; reflexivity.
Defined.

Definition transport_paths_FFlr {A B : Type} {f : A -> B} {g : B -> A} {x1 x2 : A}
  (p : x1 = x2) (q : g (f x1) = x1)
  : transport (fun x => g (f x) = x) p q = inverse (ap g (ap f p)) @ q @ p.
Proof.
  destruct p; simpl.
  exact (inverse (idpath_L q) @ inverse (idpath_R ((eq_refl _) @ q))).
Defined.

Notation "x .1" := (projT1 x) (at level 3).
Notation "x .2" := (projT2 x) (at level 3).
Notation " ( x ; p ) " := (existT _ x p).


Definition projT1_path {A} {P : A -> Type} {u v : sigT P} (p : u = v)
  : u.1 = v.1 := ap (@projT1 _ _) p.

Notation "p ..1" := (projT1_path p) (at level 3).

Definition projT1_path_1 {A : Type} {P : A -> Type} (u : sigT P)
: (eq_refl u) ..1 = eq_refl (u .1)
:= eq_refl _.


Definition projT2_path {A} {P : A -> Type} {u v : sigT P} (p : u = v)
  : p..1 # u.2 = v.2
  := inverse (transport_compose P (@projT1 _ _) p u.2)
     @ (@apD {x:A & P x} _ (@projT2 _ _) _ _ p).

Notation "p ..2" := (projT2_path p) (at level 3).

Definition path_sigma_uncurried {A : Type} (P : A -> Type) (u v : sigT P)
  (pq : {p : u.1 = v.1 &  p # u.2 = v.2})
  : u = v.
  destruct pq, u ,v. simpl in *. 
  destruct x. simpl in *. destruct e. reflexivity. 
Defined.


Definition pr1_path_sigma_uncurried A `{P : A -> Type} {u v : sigT P}
           (pq : { p : u.1 = v.1 & p # u.2 = v.2 })
: (path_sigma_uncurried _ _ pq)..1 = pq.1.
Proof.
  destruct u as [u1 u2]; destruct v as [v1 v2]; simpl in *.
  destruct pq as [p q].
  destruct p; simpl in q; destruct q; reflexivity.
Defined.

Definition pr2_path_sigma_uncurried A `{P : A -> Type} {u v : sigT P}
           (pq : { p : u.1 = v.1 & p # u.2 = v.2 })
: (path_sigma_uncurried _ _ pq)..2
  = ap (fun s => transport P s u.2) (pr1_path_sigma_uncurried pq) @ pq.2.
Proof.
  destruct u as [u1 u2]; destruct v as [v1 v2]; simpl in *.
  destruct pq as [p q].
  destruct p; simpl in q; destruct q; reflexivity.
Defined.

Definition eta_path_sigma_uncurried A `{P : A -> Type} {u v : sigT P}
           (p : u = v)
: path_sigma_uncurried _ _ (p..1; p..2) = p.
Proof.
  destruct p. destruct u. reflexivity.
Defined.

Definition path_sigma_id A `{P : A -> Type} (u : sigT P) :
           eq_refl u = path_sigma_uncurried u u (eq_refl _ ; eq_refl _ ).
  destruct u. reflexivity.
Defined.

Definition path_sigma' {A : Type} (P : A -> Type) {x x' : A} {y : P x} {y' : P x'}
           (p : x = x') (q : p # y = y')
: (x;y) = (x';y').
  apply path_sigma_uncurried. exists p. exact q.
Defined.

  (* := match pq with *)
  (*      | existT _ p q => *)
  (*        match u, v return (forall p0, (p0 # u.2 = v.2) -> (u=v)) with *)
  (*          | (x;y), (x';y') => fun p1 q1 => *)
  (*            match p1 in (_ = x'') return (forall y'', (p1 # y = y'') -> (x;y)=(x'';y'')) with *)
  (*              | eq_refl => fun y' q2 => *)
  (*                match q2 with *)
  (*                  | eq_refl => eq_refl (x,y) *)
  (*                end *)
  (*            end y' q1 *)
  (*        end p q *)
  (*    end. *)

Definition projT1_path_sigma_uncurried {A} {P : A -> Type} {u v : sigT P}
  (pq : { p : u.1 = v.1 & p # u.2 = v.2 })
  : (path_sigma_uncurried _ _ pq)..1 = pq.1.
Proof.
  destruct u as [u1 u2]; destruct v as [v1 v2]; simpl in *.
  destruct pq as [p q].
  destruct p; simpl in q; destruct q; reflexivity.
Defined.

(* Axiom UIP_refl : forall (U:Set) (x:U) (p:x = x), p = eq_refl x. *)

(* Lemma existT_destruct2 (A:Set) (P : A -> Type)  (a:A) (t t' : P a) : (a;t) = (a;t') ->  t = t'. *)
(*   intro e. pose (H := e..2). simpl in H. rewrite <- H.  *)
(*   rewrite (UIP_refl (e..1)). reflexivity. *)
(* Defined. *)

Definition eq_sym_sym A (a b:A) (e:a=b) : eq_sym (eq_sym e) = e.
destruct e; reflexivity. Defined.

Definition eq_sym_1 A {P : A -> Type} {u v : sigT P} (p : u = v) : (eq_sym p)..1 = eq_sym (p..1).
destruct p; reflexivity. Defined.


Definition transport_sigma {A : Type} {B : A -> Type} {C : forall a:A, B a -> Type}
  {x1 x2 : A} (p : x1 = x2) (yz : { y : B x1 & C x1 y })
  : transport (fun x => { y : B x & C x y }) p yz
    = (p # yz.1 ; transportD _ _ p yz.1 yz.2).
Proof.
  destruct p.  destruct yz as [y z]. reflexivity.
Defined.

Definition transport_sigma' {A B : Type} {C : A -> B -> Type}
  {x1 x2 : A} (p : x1 = x2) (yz : { y : B & C x1 y })
  : transport (fun x => { y : B & C x y }) p yz =
  (yz.1 ; transport (fun x => C x yz.1) p yz.2).
Proof.
  destruct p. destruct yz. reflexivity.
Defined.


Definition sum_forall_adjoint A P B (f : ∀ x : A, P x -> B) : {x : A & P x} -> B. 
  intros. destruct X. exact (f x p). Defined.

Definition forall_sum_adjoint A P B (f : {x : A & P x} -> B) : ∀ x : A, P x -> B. 
  intros. exact (f (x; X)). Defined.

Definition sum_forall_adjoint_eq' A P B (f g : ∀ x : A, P x -> B) : (forall x , f x = g x) ->
  forall x, sum_forall_adjoint _ f x = sum_forall_adjoint _ g x.
  intros e x. destruct x. exact (equal_f _ (e x) p).
Defined.


Definition transport_funR {A B B': Type} {f : A -> B} (x:A) (p:B = B'):
  transport (id (A:=Type)) p (f x) = transport (λ B, A -> B) p f x.
  destruct p. reflexivity.
Defined.

Definition transport_funL {A B A': Type} {f : A -> B} (x:A') (p:A = A'):
  f (transport (id (A:=Type)) (eq_sym p) x) = transport (λ A, A -> B) p f x.
  destruct p. reflexivity.
Defined.

Definition transport_comp A B (b b': A) (c c' : B) P (f : P b c) e e':
  transport (fun b => P b c') e (transport (fun c => P b c) e' f) =
  transport (fun c => P b' c) e' (transport (fun b => P b c) e f). 
  destruct e, e'. reflexivity. Defined.



Definition transport_Hom {Obj Obj' T: Type} {Hom : Obj -> Obj -> T}
  {Hom' : Obj' -> Obj' -> T} {x1 x2 : Obj} (p : existT (λ Obj, Obj → Obj → T) Obj Hom = (Obj';Hom')) :
Hom x1 x2 =
   transport (λ Obj0 : Type, Obj0 → Obj0 → T) p ..1 Hom
     (transport (id (A:=Type)) p ..1 x1) (transport (id (A:=Type)) p ..1 x2).
  destruct p. reflexivity.
Defined.

Definition transport_Hom2 {Obj Obj' T: Type} {Hom : Obj -> Obj -> T}
  {Hom' : Obj' -> Obj' -> T} {x1 x2 : Obj'} (p : existT (λ Obj, Obj → Obj → T) Obj Hom = (Obj';Hom')) :
Hom (transport (id (A:=Type)) (eq_sym p ..1) x1) (transport (id (A:=Type)) (eq_sym p ..1) x2) =
   transport (λ Obj0 : Type, Obj0 → Obj0 → T) p ..1 Hom
     x1 x2.
  pose (H:=transport_Hom p (x1:=transport (id (A:=Type)) (eq_sym p ..1) x1) (x2:=transport (id (A:=Type)) (eq_sym p ..1) x2)). 
  etransitivity; try exact H. repeat rewrite <- transport_pp. 
  repeat rewrite inverse_inv_L. reflexivity.
Defined.

Definition transport_Hom' {Obj Obj' T: Type} {Hom : Obj -> Obj -> T}
  {Hom' : Obj' -> Obj' -> T} {x1 x2 : Obj} (p : existT (λ Obj, Obj → Obj → T) Obj Hom = (Obj';Hom'))
: Hom x1 x2 = Hom' (transport (id (A:=Type)) (p..1) x1) (transport (id (A:=Type)) (p..1) x2). 
Proof.
  pose (foo := equal_f _ (equal_f _ p..2 (transport (id (A:=Type)) p ..1 x1)) (transport (id (A:=Type)) p ..1 x2)). simpl in foo. etransitivity; try exact foo. clear foo.
  apply transport_Hom. Defined.


(** With this version of the function, we often have to give [z] and [z'] explicitly, so we make them explicit arguments. *)
Definition path_prod_uncurried {A B : Type} (z z' : A * B)
  (pq : (fst z = fst z') * (snd z = snd z'))
  : (z = z').
Proof.
  destruct z, z'. simpl in *.
  case (fst pq). case (snd pq).
  reflexivity.
Defined.

(** This is the curried one you usually want to use in practice.  We define it in terms of the uncurried one, since it's the uncurried one that is proven below to be an equivalence. *)
Definition path_prod {A B : Type} (z z' : A * B) :
  (fst z = fst z') -> (snd z = snd z') -> (z = z')
  := fun p q => path_prod_uncurried z z' (p,q).


Definition section {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.

Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
  equiv_inv : B -> A ;
  eisretr : section equiv_inv f;
  eissect : section f equiv_inv;
  eisadj : forall x : A, eisretr (f x) = ap f (eissect x)
}.
Arguments eisretr {A B} f {_} _.
Arguments eissect {A B} f {_} _.
Arguments eisadj {A B} f {_} _.


Record Equiv A B := BuildEquiv {
  equiv_fun :> A -> B ;
  equiv_isequiv :> IsEquiv equiv_fun
}.

Notation "A <~> B" := (Equiv A B) (at level 85) : equiv_scope.
Notation "f ^-1" := (@equiv_inv _ _ f _) (at level 3, format "f '^-1'").


Definition transport_commute A B x x' y y' (P : A -> B -> Type) (e:x=y) (e':x'=y') 
           (p : P x x') : 
  transport (fun X => P X y') e  (transport (fun X => P x X) e' p) = 
  transport (fun X => P y X)  e' (transport (fun X => P X x') e p). 
  destruct e, e'. reflexivity.
Defined.

Definition path_prod_split {A B : Type} (z z' : A * B) :(z = z') ->
  (fst z = fst z') * (snd z = snd z').
  destruct 1. exact (eq_refl, eq_refl).
Defined.

Definition unpack_prod {A B} (P : A * B -> Type) (u : A * B) :
  P (fst u, snd u) -> P u.
  destruct u. exact idmap.
Defined.

Definition pack_prod {A B} (P : A * B -> Type) (u : A * B) :
 P u -> P (fst u, snd u).
  destruct u. exact idmap.
Defined.

Lemma transport_path_prod_split {A B} (P : A * B -> Type) {z z' : A * B}
      (e : z = z')
      (Pz : P z)
: pack_prod P z' (transport P e Pz)
  = transport (fun x => P (x, snd z'))
              (fst (path_prod_split e))
              (transport (fun y => P (fst z, y))
                         (snd (path_prod_split e))
                         (pack_prod P z Pz)).
Proof.
  destruct e. reflexivity. 
Defined.

Lemma transport_path_prod_uncurried {A B} (P : A * B -> Type) {x y : A * B}
      (H : (fst x = fst y) * (snd x = snd y))
      (Px : P x)
: pack_prod P y (transport P (path_prod_uncurried _ _ H) Px)
  = transport (fun x => P (x, snd y))
              (fst H)
              (transport (fun y => P (fst x, y))
                         (snd H)
                         (pack_prod P x Px)).
Proof.
  destruct x, y, H; simpl in *. destruct e, e0. 
  reflexivity.
Defined.

Definition path_prod_uncurried_split {A B : Type} (z z' : A * B) (x : (fst z = fst z') * (snd z = snd z')) : path_prod_split (path_prod_uncurried _ _ x) = x.
  destruct x, z, z'. simpl in *. destruct e, e0. reflexivity.
Defined.


Definition transport_path_prod {A B} (P : A * B -> Type) {x y : A * B}
           (HA : fst x = fst y)
           (HB : snd x = snd y)
           (Px : P x)
: pack_prod P y (transport P (path_prod _ _ HA HB) Px)
  = transport (fun x => P (x, snd y))
              HA
              (transport (fun y => P (fst x, y))
                         HB
                         (pack_prod P x Px))
  := transport_path_prod_uncurried P (HA, HB) Px.

Definition transportD_is_transport
           {A:Type} (B:A->Type) (C:sigT B -> Type)
           (x1 x2:A) (p:x1=x2) (y:B x1) (z:C (x1;y))
: transportD B (fun a b => C (a;b)) p y z
  = transport C (path_sigma' B p eq_refl) z.
Proof.
  destruct p. reflexivity.
Defined.

Definition transportD_is_transport'
           {A:Type} (B:Type) (C:A -> B -> Type)
           (x1 x2:A) (p:x1=x2) (y:B) (z:C x1 y)
: transportD (fun _ => B) C p y z =
  transport (fun X => C X _) p (transport (C x1) (inverse (transport_const _ _ )) z).
  destruct p. reflexivity.
Defined.

Definition ap01D1 {A B C} (f : forall (a:A), B a -> C a)
           {x x'} (p : x = x') {y y'} (q : p # y = y')
: transport C p (f x y) = f x' y'.
Proof.
  destruct p, q; reflexivity.
Defined.



