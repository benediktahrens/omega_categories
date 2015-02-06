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
                 (*       refine (mkCommutativeSquare _ _ _ _ _ _). *)
                 (*       intros. destruct x0. reflexivity.  *)
                       admit. Defined.

(* Definition of S1 as in https://github.com/HoTT *)

Private Inductive S1' : Type :=
| base' : S1'.

Axiom loop' : base' = base'.

Definition S1'_ind (P : S1' -> Type) (b : P base') (l : loop' # b = b)
  : forall (x:S1'), P x
  := fun x => match x with base' => fun _ => b end l.

Axiom S1'_ind_beta_loop
  : forall (P : S1' -> Type) (b : P base') (l : loop' # b = b),
      apD (S1'_ind P l) loop' = l.

Definition S1'_rec (P : Type) (b : P) (l : b = b)
  : S1' -> P
  := S1'_ind (fun _ => P) (transport_const _ _ @ l).

Definition S1'_rec_beta_loop (P : Type) (b : P) (l : b = b)
: ap (S1'_rec l) loop' = l.
Admitted.

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

Definition piω T := (piW T; piIsUnivalent T).

CoFixpoint ω_eq_refl T (x:T) : ω_terminal ==> piW (x=x).
refine (mkGHom _ _ _ _).
- intros _. exact eq_refl.
- intros e e'. exact (ω_eq_refl _ _). 
Defined.

Definition _S1_rec (P : Type) (b : P) (l : b = b) :
  ωFunctor ωS1 (piω P).1.
  refine (existT _ _ _). refine (mkGHom _ _ _ _). 
- intros _. exact b.
- intros x y. refine (mkGHom _ _ _ _).
  + {intro n; induction n. 
         { exact eq_refl. }
         { exact (IHn @ l). }
        }
  + intros n n'. simpl in *.
        case (decpaths_nat n n'). intros h; destruct h. 
        exact (ω_eq_refl _).
        intros _. exact (init_empty _).
- admit.
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
