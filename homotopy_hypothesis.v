Add LoadPath "." as OmegaCategories.
Require Export Unicode.Utf8_core.
Require Import Omega Integers truncation. 
Require Import path GType omega_cat_examples type_to_omega_cat omega_categories_transport omega_categories. 

Set Implicit Arguments.

CoInductive IsRigid (G : ωcat) : Type :=
mkId : IsHSet (|G|) ->
       (∀ (x y : |G|), IsRigid (G [x,y])) ->
       IsRigid G.

Definition Rigid_ωcat := {G: ωcat & IsRigid G}.


Definition ωComp A B C (F : ωFunctor A B) (G : ωFunctor B C) : ωFunctor A C.
  exists (G.1 °° F.1).
  split.
  - destruct F as [F [HF HF']], G as [G [HG HG']]. simpl. clear HG' HF'.
    generalize dependent G. generalize dependent F. generalize A B C. clear A B C.
    cofix. intros.
    apply mkPreservesCompo. Focus 2. intros. simpl.
    refine (ωComp (A[x,y]) (B[F @@ x, F @@ y]) (C [G @@ (F @@ x), G @@ (F @@ y)]) _ _ _ _ ).
    destruct HF; apply p. 
    destruct HG; apply p.  
    intros x y z n c. destruct HF, HG. clear p p0.
    pose (FF := cellGHom n (A [x, y].1 ** A [y, z].1)
                         (B [F @@ x, F @@ y].1 ** B [F @@ y, F @@ z].1)
                         (prod_hom' (F<<x,y>>) (F<<y,z>>)) c).
    specialize (c1 (F @@ x) (F @@ y) (F @@ z) n FF). simpl in *.
    specialize (c0 x y z n c).
    pose (ap (cellGHom n (B [F @@ x, F @@ z].1) (C [G @@ (F @@ x), G @@ (F @@ z)].1) (G << F @@ x, F @@ z >>)) c0).
    repeat rewrite eq_cell_comp in e.
    etransitivity. Focus 2.
    apply (eq_cell_assoc2 n (A [x, y].1 ** A [y, z].1) (A [x, z]).1 (B [F @@ x, F @@ z].1)
                          (C [G @@ (F @@ x), G @@ (F @@ z)].1) c compo (F << x, z >>) (G << F @@ x, F @@ z >>)).
    etransitivity; try apply e.
    clear e c0.
    unfold FF in c1. clear FF.
    etransitivity. Focus 2. apply eq_sym.
    apply (eq_cell_assoc2 n (A [x, y].1 ** A [y, z].1) (B [F @@ x, F @@ y].1 ** B [F @@ y, F @@z].1)
                          (B [F @@ x, F @@ z].1) (C [G @@ (F @@ x), G @@ (F @@ z)].1) c
                          (prod_hom' (F << x, y >>) (F << y, z >>)) compo (G << F @@ x, F @@ z >>)).
    repeat rewrite eq_cell_comp in c1.
    etransitivity; try apply c1.
    etransitivity. Focus 2. 
    apply (eq_cell_assoc2 n (A [x, y].1 ** A [y, z].1) (B [F @@ x, F @@ y].1 ** B [F @@ y, F @@z].1)
                          (C [G @@ (F @@ x), G @@ (F @@ y)].1 ** C [G @@ (F @@ y), G @@ (F @@ z)].1)
                          (C [G @@ (F @@ x), G @@ (F @@ z)].1) c
                          (prod_hom' (F << x, y >>) (F << y, z >>))
                          (prod_hom' (G << F @@ x, F @@ y >>) (G << F @@ y, F @@ z >>)) compo).
    repeat rewrite <- eq_cell_comp.
    rewrite <- (eq_cell_comp n (A [x, y].1 ** A [y, z].1)
                             (C [G @@ (F @@ x), G @@ (F @@ y)].1 ** C [G @@ (F @@ y), G @@ (F @@ z)].1)
                             (C [G @@ (F @@ x), G @@ (F @@ z)].1) c (prod_hom' ((G << F @@ x, F @@ y >>) °° (F << x, y >>))
                                                  ((G << F @@ y, F @@ z >>) °° (F << y, z >>))) compo).
    apply ap2; try reflexivity. apply eq_sym.
    repeat rewrite eq_cell_comp. apply prod_hom'_comp.
  - destruct F as [F [HF HF']], G as [G [HG HG']]. simpl. clear HG HF.
    generalize dependent G. generalize dependent F. generalize A B C. clear A B C.
    cofix. intros.
    apply mkPreservesId. Focus 2. intros. simpl.
    refine (ωComp (A[x,y]) (B[F @@ x, F @@ y]) (C [G @@ (F @@ x), G @@ (F @@ y)]) _ _ _ _ ).
    destruct HF'; apply p. 
    destruct HG'; apply p.  
    clear ωComp. intros. destruct HF', HG'. clear p p0.
    simpl. etransitivity. apply ap. apply e. apply e0.
Defined.

Definition commutativeSquare_Id T U V f :
  @commutativeSquareHere (piω V) (canonicalSquare _)  (piω T ** piω U) (piω V) (piω T ** piω U)
                    f (prod_hom' (GId _) (GId _)) f (GId _).
  intro n. generalize dependent V. generalize dependent U. generalize dependent T. induction n; intros. 
  - destruct cG. reflexivity. 
  - destruct cG as [[[x x'] [y y']] c]. refine (path_sigma' _ _ _). reflexivity. simpl. unfold id. 
    apply IHn.
Defined. 

Program Definition ωFunctor_Id {T} : ωFunctor (piW T) (piW T) := (GId (pi T); _).
Next Obligation. split.
- generalize dependent T. cofix. intros.
  apply mkPreservesCompo.
  + clear ωFunctor_Id_obligation_1. simpl. unfold id. 
    intros. apply commutativeSquare_Id.
  + intros. simpl. apply (ωFunctor_Id_obligation_1 (x=y)).
- generalize dependent T. cofix. intros.
  apply mkPreservesId.
  + intros; reflexivity.
  + intros. simpl. apply (ωFunctor_Id_obligation_1 (x=y)).
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

(* Definition of S1 using our homotopy hypothesis *)

Definition S1 := HH_fun ωS1.

Definition ψ S T := @equiv_inv _ _ _ (HH S T).

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

Definition transport_hom_CGS1 (B:ωcat) n m (e : n = m) (f : ω_terminal ==> B) :
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


(* This one is not derivable *)
  
Definition S1_ind (P : S1 -> Type) (b : P base) (l : loop # b = b)
: ∀ (x:S1), P x.
Abort.
