Add LoadPath "." as OmegaCategories.
Require Export Unicode.Utf8_core.
Require Import Omega Integers truncation. 
Require Import path GType omega_cat_examples  type_to_omega_cat omega_categories. 

Set Implicit Arguments.


CoInductive IsRigid (G : ωcat) : Type :=
mkId : IsHSet (|G|) ->
       (∀ (x y : |G|), IsRigid (G [x,y])) ->
       IsRigid G.

Definition Rigid_ωcat := {G: ωcat & IsRigid G}.


Definition Univalent_ωcat := {G : ωcat & IsUnivalent G}.

Definition Univ_embedding : Univalent_ωcat -> ωcat := fun G => G.1.

Instance ωcat_transport (G:ωcat) : transport_eq G.1 := _transport.

Definition ωFunctor (G H: ωcat) := { f:G==>H & IsωFunctor G.1 f _}.

Definition ωComp A B C (F : ωFunctor A B) (G : ωFunctor B C) : ωFunctor A C.
  exists (G.1 °° F.1).
  (* split. *)
  (* - destruct F as [F [HF HF']], G as [G [HG HG']]. simpl. clear HG' HF'. *)
  (*   apply mkPreservesCompo. intros. refine (mkCommutativeSquare _ _ _ _ _ _ ).     *)
  (*   + intros. destruct HF, HG. clear p p0. specialize (c x y z). *)
  (*     specialize (c0 (F @@ x) (F@@y) (F@@z)). destruct c, c0. clear c c0. *)
  (*     exact (comm0 ((F << x, y >>) @@ (fst x0), (F << y, z >>) @@ (snd x0)) @ ap _ (comm x0)). *)
  (*   + generalize dependent C. generalize dependent B. generalize dependent A. cofix. *)
  (*     intros. refine (mkCommutativeSquare _ _ _ _ _ _ ).  *)
  (*     intros. destruct x1. destruct HF. simpl. *)
  (*     destruct x0 as [e f], y0 as [e' f']; simpl. *)
  (*     unfold prod'. simpl. refine (ωComp _ _ _ _ _ _ _ _ _ _ _). *)
  (*     destruct i0. destruct p. simpl in *. specialize (c (x1 @@ x) (x1 @@ y) (x1 @@ z)). destruct c. *)
  (*   simpl in comm. pose (comm ((x1 << x, y >>) @@ fst x0, ((x1 << y, z >>) @@ snd x0))). *)
  (*   destruct i. destruct p1. simpl in *. specialize (c0 x y z). destruct c0. *)
  (*   pose (comm0 x0). *)
  (*   pose (comm ((x1 << x, y >>) @@ fst x0, ((x1 << y, z >>) @@ snd x0))). *)
  (*   exact (e1 @ ap _ e0). *)
  (*   + intros. destruct x0, y0. simpl.  apply ωComp. *)
  (*   simpl in e. rewrite e. *)
  (*   destruct p. simpl in *. specialize (c x y z). destruct c. *)
  (*   pose (comm x0). simpl in e. rewrite e. *)
  admit.
Defined.

Notation "g °° f" := (ωComp f g) (at level 20).

Axiom HH_fun : ωcat -> Type.

Axiom HH_η : ∀ {C}, ωFunctor C (piW (HH_fun C)).

Axiom HH : ∀ C T, IsEquiv (fun (f:ωFunctor (piW (HH_fun C)) (piW T)) => f °° HH_η).

Notation "f @@ x" := (app f.1 x) (at level 20) : type_scope.

Definition map' G H (f : ωFunctor G H) (x x' : |G|) : ωFunctor (G [x,x']) (H [f @@ x, f @@ x']).
  exists (f.1 <<x, x'>>). destruct f as [f Hf]. destruct Hf.
  split. destruct p; apply p.  destruct p0; apply p0.
Defined.

Notation "f << x , x' >>" := (map' f x x') (at level 80).


Program Definition ωFunctor_Id {G : ωcat} : ωFunctor G G := (GId G.1.1; _).
Next Obligation. (* split. apply mkPreservesCompo. intros. *)
                 (* simpl.       refine (mkCommutativeSquare _ _ _ _ _ _). *)
                 (*       intros. destruct x0. reflexivity. simpl. *)
  admit. Defined.

(* Deifnition of S1 using our homotopy hypothesis *)

Definition S1 := HH_fun ωS1.

Definition ψ S T := @equiv_inv _ _ _ (HH S T).

(* Definition ψ {S T} := @equiv_inv _ _ _ (HH S T).2. *)

Definition injS1 : ωFunctor ωS1 (piW S1) := ωFunctor_Id °° HH_η.

Definition base : S1 := injS1 @@ tt.

Definition univalent_to_path (G:Univalent_ωcat) x y (e:|G.1[x,y]|) : x = y.
  destruct G. destruct i. exact (@equiv_inv _ _ _ (i x y) e).
Defined.

Definition _univalent_hom (G:Univalent_ωcat) x y : IsUnivalent (G.1[x,y]).
  destruct G. destruct i. exact (i0 x y).
Defined.

Definition univalent_hom (G:Univalent_ωcat) x y : Univalent_ωcat :=
  (G.1[x,y]; _univalent_hom G x y).

Definition loop := (injS1 <<tt,tt>> @@ 1) : base = base.
  
(* Definition loop : base = base := univalent_to_path S1 _ _ _loop. *)

Definition piω' T := (piW T; piIsUnivalent T).

CoFixpoint ω_eq_refl T (x y :T) (e:x=y) : ω_terminal ==> piW (x=y).
refine (mkGHom _ _ _ _).
- intros _. exact e.
- intros h h'. exact (ω_eq_refl _ _ _ eq_refl). 
Defined.

Fixpoint n_loop (P : Type) (b : P) (l : b = b) (n : nat) : b = b :=
  match n with
      0 => eq_refl
    | S n => n_loop l n @ l
  end.

Fixpoint n_loop_plus (P : Type) (b : P) (l : b = b) (n n0 : nat) :
  n_loop l n @ n_loop l n0 = n_loop l (n + n0).
destruct n0; simpl.
- rewrite <- plus_n_O. apply idpath_R.
- rewrite <- plus_Snm_nSm. simpl. rewrite <- concat_assoc.
  apply ap2; try apply n_loop_plus; reflexivity.
Defined.

Definition _S1_rec_fun (P : Type) (b : P) (l : b = b) :
  ωS1 ==> (piω' P).1.
  refine (mkGHom _ _ _ _). 
- intros _. exact b.
- intros x y. refine (mkGHom _ _ _ _).
  + exact (n_loop l). 
  + destruct x, y. intros n n'. case (decpaths_nat n n'); intro e.
    * exact (transport_hom (inverse (CGS1_eq_terminal e)) eq_refl (ω_eq_refl (ap (n_loop l) e))).
    * exact (transport_hom (B := piω (n_loop l n = n_loop l n')) (inverse (CGS1_neq_empty e)) eq_refl (init_empty _)).
Defined.

Definition path_product A B A' B' (eA : A = A') (eB: B = B') : (A ** B) = (A' ** B').
  destruct eA, eB. reflexivity. 
Defined.

Definition transport_hom_CGS1 (B:ωcat) n m (e : n = m) (f : ω_terminal ==> B) :
  transport_hom (CGS1_eq_terminal e) eq_refl (transport_hom (inverse (CGS1_eq_terminal e)) eq_refl f) = f.
  rewrite transport_hom_concat. rewrite inverse_inv_L. reflexivity. 
Defined.

CoFixpoint commutativeSquare_emptyR A B C D _transport U F V G :
  commutativeSquare (A ** CGempty) B C D _transport U F V G.
refine (mkCommutativeSquare _ _ _ _ _ _);intros [a absurd]; inversion absurd.
Defined.  
    
CoFixpoint commutativeSquare_emptyL A B C D _transport U F V G :
  commutativeSquare (CGempty ** A) B C D _transport U F V G.
refine (mkCommutativeSquare _ _ _ _ _ _);intros [absurd a]; inversion absurd.
Defined.  

Definition _S1_rec (P : Type) (b : P) (l : b = b) :
  ωFunctor ωS1 (piω' P).1.
  refine (existT _ _ _). exact (_S1_rec_fun l). 
  admit. 
Defined.

Definition S1_rec (P : Type) (b : P) (l : b = b) : S1 -> P :=
  app (ψ (@_S1_rec P b l)).1.

Definition equal_GHom A B (f g : ωFunctor A B) x : f = g -> f @@ x = g @@ x.
  destruct 1. reflexivity.
Defined.

Definition HH_η_law S T (f:ωFunctor S (piW T))  (x:|S|):
  ψ f @@ (ωFunctor_Id °° HH_η @@ x) = f @@ x :=
  equal_GHom x (@eisretr _ _ _ (HH S T) f).
  
Definition transport_equal_GHom A B (f g : ωFunctor A B) x y (e : f = g) (e' : |A[x,y]|) :
  transport (fun X => |B[X, g @@ y]|) (equal_GHom x e)
            (transport (fun X => |B[f @@ x, X]|) (equal_GHom y e) (f <<x,y>> @@ e')) =
  (g <<x,y>> @@ e').
  destruct e. reflexivity.
Defined. 

Definition piW_ap_hom T U (f : ωFunctor (piW T) (piW U)) x y (e:x=y) : ap (app f.1) e = (f <<x,y>> @@ e).
  destruct e. destruct f as [f [H' H]]. 
  symmetry. apply H.  
Defined. 

Definition S1_rec_beta_base (P : Type) (b : P) (l : b = b) : S1_rec l base = b
  := @HH_η_law ωS1 P _ tt.

Definition S1_rec_beta_loop (P : Type) (b : P) (l : b = b) :
  transport (fun X => X = _) (S1_rec_beta_base l)
    (transport (fun X => _ = X) (S1_rec_beta_base l)
                 (ap (S1_rec l) loop)) = l :=
  (ap _ (ap _ (piW_ap_hom (ψ (_S1_rec l)) (((@HH_η ωS1) << tt, tt >>) @@ 1)))) @
  (@transport_equal_GHom _ _ ((ψ (_S1_rec l)) °° HH_η) (_S1_rec l) tt tt (eisretr (_S1_rec l)) 1).


(* This one is not derviable *)
  
Definition S1_ind (P : S1 -> Type) (b : P base) (l : loop # b = b)
: ∀ (x:S1), P x.
Abort.



(* CoFixpoint ω_eq_refl_compo T U V x y f : *)
(*   commutativeSquare (CGterminal**CGterminal) CGterminal *)
(*                     (hom' (piω T) x x ** hom' (piω U) y y) (hom' (piω V) (f x y) (f x y)) _ *)
(*                     compo (prod_hom' (ω_eq_refl eq_refl) (ω_eq_refl eq_refl)) *)
(*                     compo (ω_eq_refl eq_refl). *)
(* refine (mkCommutativeSquare _ _ _ _ _ _). *)
(* - reflexivity. *)
(* - intros [a a'] [b b']. destruct a, a', b ,b'.  *)
(*   match goal with | |- commutativeSquare _ _ _ _ _ _ _ ?F _ => *)
(*                         assert (F = *)
(*           (piComp_V_ *)
(*            (λ (X : x = x) (X' : y = y), *)
(*             equal_f (λ _ : U, V) (ap f X) y @ ap (f x) X') eq_refl eq_refl *)
(*            eq_refl eq_refl)) end.  *)
(*   admit. *)
(*   rewrite H. *)
(*   exact (@ω_eq_refl_compo (x = x) (y =y) (f x y = f x y) *)
(*                           eq_refl eq_refl (@ap2 _ _ _ f x x y y)). *)
(* Defined. *)

(* CoFixpoint ω_eq_refl_compo' T x : *)
(*   commutativeSquare (CGterminal**CGterminal) CGterminal *)
(*                     (hom' (piω T) x x ** hom' (piω T) x x) (hom' (piω T) x x) _ *)
(*                     compo (prod_hom' (ω_eq_refl eq_refl) (ω_eq_refl eq_refl)) *)
(*                     compo (ω_eq_refl eq_refl). *)
(* refine (mkCommutativeSquare _ _ _ _ _ _). *)
(* - reflexivity. *)
(* - intros [a a'] [b b']. destruct a, a', b ,b'.  *)
(*   pose (@ω_eq_refl_compo' (x = x) eq_refl).  *)
(*   match goal with | |- commutativeSquare _ _ _ _ _ _ _ ?F _ => *)
(*                         assert (F = compo) end. *)
(*   admit. *)
(*   rewrite H.  *)
(*   admit. *)
(* Defined. *)

(* Definition ω_eq_refl_functor T (x y :T) (e:x=y) : *)
(*   IsωFunctor CGterminal (ω_eq_refl e) _. *)
(*   split. *)
(*   - destruct e. generalize dependent T. cofix ω_eq_refl_preservesCompo. intros. *)
(*     apply mkPreservesCompo. intros a b c; destruct a, b, c. *)
(*     pose (@ω_eq_refl_compo' (x=x) eq_refl). *)
(*     simpl in *. exact c. *)
(*     intros a b. destruct a, b. apply ω_eq_refl_preservesCompo. *)
(*   - destruct e. generalize dependent T. cofix ω_eq_refl_preservesId. intros. *)
(*     apply mkPreservesId. intros a; destruct a. *)
(*     reflexivity. intros a b. destruct a, b.  apply ω_eq_refl_preservesId. *)
(* Defined. *)


  (* split. *)
  (* - apply mkPreservesCompo. intros x y z; destruct x, y, z.  *)
  (* refine (mkCommutativeSquare _ _ _ _ _ _). *)
  (* + destruct x as [m n]. exact (n_loop_plus l m n).  *)
  (* + intros [n m] [n' m']. *)
  (*   pose (decpaths_nat n n'). case d. intro e. destruct e. *)
  (*   pose (decpaths_nat m m'). case d0. intro e. destruct e. simpl. *)
  (*   refine (@path_commutativeSquare _ _ _ _ (CGterminal ** CGterminal) CGterminal _ _ *)
  (*          _ _ _ _ _ _ _ eq_refl eq_refl _).  *)
  (*   * exact (path_product (CGS1_eq_terminal (eq_refl n)) (CGS1_eq_terminal (eq_refl m))). *)
  (*   * exact (CGS1_eq_terminal (eq_refl _)). *)
  (*   * match goal with | |- commutativeSquare _ _ _ _ _ _ _ _ ?f => *)
  (*                       assert (f = ω_eq_refl eq_refl) end. *)
  (*     etransitivity; try apply (transport_hom_CGS1 ( piW (n_loop l (n + m) = n_loop l (n + m))) (eq_refl (n+m))). apply ap. Opaque CGS1_eq_terminal. simpl. *)
  (*     pose (decpaths_nat_refl (n+m)). admit. *)
  (*     rewrite H. pose (ω_eq_refl_compo (n_loop l n) (n_loop l m) concat). *)
  (*     refine (@path_commutativeSquare _ _ _ _ (CGterminal ** CGterminal) CGterminal _ _ *)
  (*                                     _ _ _ _ _ eq_refl eq_refl eq_refl _ _). *)
  (*     Focus 2. rewrite <- n_loop_plus. reflexivity. *)
  (*     admit. *)
  (*   * intro e. refine (@path_commutativeSquare _ _ _ _ (CGterminal ** CGempty) _ _ _ *)
  (*          _ _ _ _ _ _ eq_refl eq_refl eq_refl _). *)
  (*     exact (path_product (CGS1_eq_terminal (eq_refl n)) (CGS1_neq_empty e)). *)
  (*     apply commutativeSquare_emptyR. *)
  (*   * intro e. refine (@path_commutativeSquare _ _ _ _ (CGempty ** ((ωS1 [tt, tt]) [m,m']).1) *)
  (*                                              _ _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl _). *)
  (*     exact (path_product (B := ((ωS1 [tt, tt]) [m,m']).1) (CGS1_neq_empty e) eq_refl). *)
  (*     apply commutativeSquare_emptyL. *)
  (* + intros. destruct x, y. *)
  (*   apply mkPreservesCompo. intros n m p. *)
  (*   pose (decpaths_nat n m). case d. intro e. destruct e. *)
  (*   pose (decpaths_nat n p). case d0. intro e. destruct e. *)
  (*   refine (@path_commutativeSquare _ _ _ _ (CGterminal ** CGterminal) CGterminal _ _ *)
  (*          _ _ _ _ _ _ _ eq_refl eq_refl _).  *)
  (*   * exact (path_product (CGS1_eq_terminal (eq_refl n)) (CGS1_eq_terminal (eq_refl n))). *)
  (*   * exact (CGS1_eq_terminal (eq_refl _)). *)
  (*   * simpl. admit. *)
  (*   *  intro e. refine (@path_commutativeSquare _ _ _ _ (CGterminal ** CGempty) _ _ _ *)
  (*          _ _ _ _ _ _ eq_refl eq_refl eq_refl _). *)
  (*     exact (path_product (CGS1_eq_terminal (eq_refl n)) (CGS1_neq_empty e)). *)
  (*     apply commutativeSquare_emptyR. *)
  (*   * intro e. refine (@path_commutativeSquare _ _ _ _ (CGempty ** ((ωS1 [tt, tt]) [m,p]).1) *)
  (*                                              _ _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl _). *)
  (*     exact (path_product (B := ((ωS1 [tt, tt]) [m,p]).1) (CGS1_neq_empty e) eq_refl). *)
  (*     apply commutativeSquare_emptyL. *)
  (*   * intros n m. destruct (decpaths_nat n m). destruct e.  *)
  (*     apply mkPreservesCompo. intros. simpl in *. admit. admit. *)
      
  (*     rewrite decpaths_nat_refl in z. *)
  (*     set (decpaths_nat n m). case d. intro e. destruct e. *)
  (*     admit. admit. *)
