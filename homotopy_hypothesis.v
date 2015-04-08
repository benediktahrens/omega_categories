Add LoadPath "." as OmegaCategories.
Require Export Unicode.Utf8_core.
Require Import Omega Integers truncation. 
Require Import path GType omega_cat_examples type_to_omega_cat omega_categories omega_categories_transport. 

Set Implicit Arguments.

Notation "f << x , x' >>" := (map' _ _ f x x') (at level 80).

(* Strict ωcat (definition 15 of TLCA paper) *)

CoInductive IsStrict (G : wild_ωcat) : Type :=
mkId : IsHSet (|G|) ->
       (∀ (x y : |G|), IsStrict (G [x,y])) ->
       IsStrict G.

Definition Strict_wild_ωcat := {G: wild_ωcat & IsStrict G}.

(* Homotopy Hypothesis 1 of TLCA paper *)

Axiom HH_fun : wild_ωcat -> Type.

Axiom HH_η : ∀ {C}, ωFunctor C (piW (HH_fun C)).

Axiom HH : ∀ C T, IsEquiv (fun (f:ωFunctor (piW (HH_fun C)) (piW T)) => f °° HH_η).

(* Definition of S1 using our homotopy hypothesis *)

Definition S1 := HH_fun ωS1.

Definition ψ S T := @equiv_inv _ _ _ (HH S T).

Definition injS1 : ωFunctor ωS1 (piW S1) := ωFunctor_Id °° HH_η.

Definition base : S1 := injS1 @@ tt.

Definition loop := (injS1 <<tt,tt>> @@ 1) : base = base.
  
Definition piω' T := (piW T; piIsUnivalent T).

Notation " A ==> B " := (A.1 ==> B.1) (at level 90).

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

Definition S1_rec_fun (P : Type) (b : P) (l : b = b) :
  ωS1 ==> (piω' P).1.
  refine (mkGHom _ _ _ _). 
- intros _. exact b.
- intros x y. refine (mkGHom _ _ _ _).
  + exact (n_loop l). 
  + destruct x, y. intros n n'. case (decpaths_nat n n'); intro e.
    * exact (transport_hom (inverse (CGS1_eq_terminal e)) eq_refl (ω_eq_refl (ap (n_loop l) e))).
    * exact (transport_hom (G' := piω (n_loop l n = n_loop l n')) (inverse (CGS1_neq_empty e)) eq_refl (init_empty _)).
Defined.

Definition path_product A B A' B' (eA : A = A') (eB: B = B') : (A ** B) = (A' ** B').
  destruct eA, eB. reflexivity. 
Defined.

Definition transport_hom_CGS1 (B:wild_ωcat) n m (e : n = m) (f : ω_terminal ==> B) :
  transport_hom (CGS1_eq_terminal e) eq_refl (transport_hom (inverse (CGS1_eq_terminal e)) eq_refl f) = f.
  rewrite transport_hom_concat. rewrite inverse_inv_L. reflexivity. 
Defined.

CoFixpoint preservesCompo_empty_dom H (f : GHom CGempty.1 H.1):
  @preservesCompo _ _ f (canonicalSquare _).
apply mkPreservesCompo.
- intros. intros n c.  match goal with | |- ?T =>
       refine (@empty_is_false_fun _ _ n c (fun c => T))  end. 
  apply prod_empty_R. apply GId.
- intros x y. apply (preservesCompo_empty_dom).
Defined.


Definition _S1_rec (P : Type) (b : P) (l : b = b) :
  ωFunctor ωS1 (piω' P).1.
  refine (existT _ (S1_rec_fun l) _). 
  split.
  - apply mkPreservesCompo.
    + intros x y z. destruct x, y, z. intros n c. destruct n.
      * apply n_loop_plus. 
      * refine (path_sigma' _ _ _). refine (path_prod _ _ _ _); apply n_loop_plus.
        destruct c as [[[x y] [x' y']] c]. 
        case (decpaths_nat x x'); intro H.
        case (decpaths_nat y y'); intro H'. simpl.
        (* issue with dependent pattern matching *)
        admit.  
        match goal with | |- ?T =>
                          refine (@empty_is_false_fun _ _ n c (fun c => T))  end. 
        refine (prod_empty_R (ωS1[tt,tt][x,x']).1 (ωS1[tt,tt][y,y']).1 _).
        apply (transport_hom (eq_sym (CGS1_neq_empty H')) eq_refl (GId _)).
        match goal with | |- ?T =>
                          refine (@empty_is_false_fun _ _ n c (fun c => T))  end. 
        refine (prod_empty_L (ωS1[tt,tt][x,x']).1 (ωS1[tt,tt][y,y']).1 _).
        apply (transport_hom (eq_sym (CGS1_neq_empty H)) eq_refl (GId _)).
    + intros x y. destruct x, y.
      apply mkPreservesCompo.
      * intros x y z n c. 
        case (decpaths_nat x y); intro H.
        case (decpaths_nat y z); intro H'.
        (* issue with dependent pattern matching *)
        admit.
        match goal with | |- ?T =>
                          refine (@empty_is_false_fun _ _ n c (fun c => T))  end. 
        refine (prod_empty_R (ωS1[tt,tt][x,y]).1 (ωS1[tt,tt][y,z]).1 _).
        apply (transport_hom (eq_sym (CGS1_neq_empty H')) eq_refl (GId _)).
        match goal with | |- ?T =>
                          refine (@empty_is_false_fun _ _ n c (fun c => T))  end. 
        refine (prod_empty_L (ωS1[tt,tt][x,y]).1 (ωS1[tt,tt][y,z]).1 _).
        apply (transport_hom (eq_sym (CGS1_neq_empty H)) eq_refl (GId _)).
      * intros x y. case (decpaths_nat x y); intro H.
        (* issue with dependent pattern matching *)
        admit.
        refine (path_preservesCompo' (CGS1_neq_empty H) _ _).
        apply preservesCompo_empty_dom. 
  -  apply mkPreservesId.
     + intros x. reflexivity.
     + intros x y. destruct x, y. apply mkPreservesId.
       * intros. unfold identity; simpl. admit.
       * intros. admit.
Defined. 

(* Constructor L(S_1)_rec of Theorem 14*)

Definition S1_rec (T : Type) (b : T) (l : b = b) : S1 -> T :=
  app (ψ (@_S1_rec T b l)).1.

Definition HH_η_law S T (f:ωFunctor S (piW T))  (x:|S|):
  ψ f @@ (ωFunctor_Id °° HH_η @@ x) = f @@ x :=
  ap2 _ (@eisretr _ _ _ (HH S T) f)..1 eq_refl.
  
Definition transport_equal_GHom A B (f g : ωFunctor A B) x y (e : f = g) (e' : |A[x,y]|) :
  transport (fun X => |B[X, g @@ y]|) (ap2 _ e..1 eq_refl)
            (transport (fun X => |B[f @@ x, X]|) (ap2 _ e..1 eq_refl) (f <<x,y>> @@ e')) =
  (g <<x,y>> @@ e').
  destruct e. reflexivity.
Defined. 

Definition piW_ap_hom T U (f : ωFunctor (piW T) (piW U)) x y (e:x=y) : ap (app f.1) e = (f <<x,y>> @@ e).
  destruct e. destruct f as [f [H' H]]. 
  symmetry. apply H.  
Defined. 

(* Computational laws L(S_1)_beta* of Theorem 14*)

Definition S1_rec_beta_base (P : Type) (b : P) (l : b = b) : S1_rec l base = b
  := @HH_η_law ωS1 P _ tt.

Definition S1_rec_beta_loop (P : Type) (b : P) (l : b = b) :
  transport (fun X => X = _) (S1_rec_beta_base l)
    (transport (fun X => _ = X) (S1_rec_beta_base l)
                 (ap (S1_rec l) loop)) = l :=
  (ap _ (ap _ (piW_ap_hom (ψ (_S1_rec l)) (((@HH_η ωS1) << tt, tt >>) @@ 1)))) @
  (@transport_equal_GHom _ _ ((ψ (_S1_rec l)) °° HH_η) (_S1_rec l) tt tt (eisretr (_S1_rec l)) 1).


(* This one is not derivable *)
  
Definition S1_ind (P : S1 -> Type) (b : P base) (l : loop # b = b)
: ∀ (x:S1), P x.
Abort.
