Add LoadPath "." as OmegaCategories.
Require Export Unicode.Utf8_core.
Require Import OmegaCategories.path OmegaCategories.GType. 

Set Implicit Arguments.

Class Composable (A B C : GType) := { compo : (A ** B) ==> C }.

Notation "g ° f" := (app compo (f, g)) (at level 20).

(* composition on a GType (Definition 3 in TLCA paper) *)

CoInductive Compo : ∀ (G : GType), Type  :=
mkCompo : ∀ (G : GType),
   (∀ x y z : |G|, Composable (G [x,y]) (G [y,z]) (G [x,z])) ->
   (∀ x y   : |G|, Compo (G [x,y])) ->
   Compo G.

(* identities on a GType (Definition 4 in TLCA paper) *)

CoInductive Id : ∀ (G : GType), Type :=
mkId : ∀ (G : GType),
    (∀ (x : |G|), |G[x,x]|) ->
    (∀ (x y : |G|), Id (G [x,y])) ->
    Id G.

(*  ω-precategories (Definition 5 in TLCA paper) *)

Class IsωPreCat (G : GType) := mkCompoGType {_comp : Compo G; 
                                             _id : Id G}.

Definition ωPreCat := {G: GType & IsωPreCat G}.

Hint Extern 1 (IsωPreCat (?T.1)) => apply (T.2) : typeclass_instances.

(* the terminal ωPreCat *)

Instance composable_id_left (G : GType) : Composable terminal G G.
  econstructor. generalize dependent G; cofix. 
  intro; apply (mkGHom (product terminal G ) G (fun X =>  snd X)).
  simpl; intros. apply composable_id_left.
Defined.

Definition composable_id_right (G : GType) : Composable G terminal G.
  econstructor. generalize dependent G; cofix. 
  intro; apply (mkGHom (product G terminal) G (fun X => fst X)).
  simpl; intros. apply composable_id_right.
Defined.

CoFixpoint Compo_terminal : Compo terminal.
apply mkCompo; intros. apply composable_id_left.
apply Compo_terminal.
Defined.

CoFixpoint Id_terminal : Id terminal.
apply mkId; intros. exact tt.
apply Id_terminal.
Defined.

Instance terminal_CompoGType : IsωPreCat terminal :=
  {| _comp := Compo_terminal; _id := Id_terminal|}. 

Definition ωterminal : ωPreCat := (terminal; terminal_CompoGType).

(* some basic definitions to get back the structure of GType *)


Definition idHom (G : ωPreCat) (x y : |G.1|) : Id (G.1[x,y]).
destruct (@_id _ G.2) as [G' _ idup]. exact (idup x y).
Defined.

Definition compoHom (G : ωPreCat) (x y : |G.1|) : Compo (G.1 [x,y]).
  destruct (@_comp _ G.2) as [G' comp0 comp1]. exact (comp1 x y).
Defined. 

Definition compo_here  (G : ωPreCat) x y z :
  Composable (G.1 [x, y]) (G.1 [y, z]) (G.1 [x, z]).
  simpl. destruct (@_comp _ G.2). apply c.
Defined.

Definition hom' (G:ωPreCat) (x y : |G.1|) : ωPreCat := 
  (G.1[x,y]; {| _comp := compoHom G x y ; _id := idHom G x y|}).

CoFixpoint prod_hom (A B C A' B' C' : GType) (_compo : Composable A B C) 
           (_compo' : Composable A' B' C') : ((A ** A') ** (B ** B') ==> (C **C')) :=
  mkGHom ((A ** A') ** (B  ** B')) (C ** C' )
         (fun X => ((@compo _ _ _ _compo) @@ (fst (fst X), fst (snd X)),
                    (@compo _ _ _ _compo') @@ (snd (fst X), snd (snd X))))
         (fun x x' => prod_hom 
              ({|compo := (@compo _ _ _ _compo) << (fst (fst x), fst (snd x)), (fst (fst x'), fst (snd x'))>>|})
              ({| compo := (@compo _ _ _ _compo') << (snd (fst x), snd (snd x)), (snd (fst x'), snd (snd x'))>>|})).

CoFixpoint prod_hom1 (A B X C : GType) (_compo : Composable A B C) 
            : (A ** (B ** X) ==> (C ** X)) :=
  mkGHom (A ** (B  ** X)) (C ** X )
         (fun X => ((@compo _ _ _ _compo) @@ (fst X, fst (snd X)),
                    snd (snd X)))
         (fun x x' => prod_hom1 _
              ({|compo := (@compo _ _ _ _compo) << (fst x, fst (snd x)), (fst x', fst (snd x'))>>|})).

CoFixpoint delta_prod (G:GType) : G ==> (G ** G). 
  apply (mkGHom G (G ** G) (fun x => (x,x))).
  intros x y. exact (delta_prod _).
Defined.

CoFixpoint prod_hom' {G G' H H' : GType} (f: G ==> H) (g : G' ==> H') :
  (G ** G') ==> (H ** H') :=
  mkGHom (G ** G') (H ** H') (fun x => (f @@ (fst x), g @@ (snd x)))
         (fun x y => prod_hom' (f <<fst x, fst y>>) (g <<snd x, snd y>>)).

Notation "G [ A , B ]" := (hom' G A B) (at level 80).

Notation "| G |" := (objects G.1) (at level 80).

Definition identity {G : ωPreCat} (x : |G|) : |G[x,x]|.
simpl. destruct (@_id _ G.2) as [G' idhere idhom]. exact (idhere x).
Defined.

CoFixpoint compo_prod (G H : ωPreCat) : Compo (G.1 ** H.1).
  apply mkCompo. 
  - intros. exact ({| compo := prod_hom (compo_here G (fst x) (fst y) (fst z))
                                      (compo_here H (snd x) (snd y) (snd z))|}).
  - intros. exact (compo_prod (G [fst x, fst y])(H [snd x, snd y])).
Defined.

CoFixpoint id_prod (G H : ωPreCat) : Id (G.1 ** H.1).
apply mkId. 
intros. exact (identity (fst x), identity (snd x)).
intros xy x'y'. exact (id_prod (G [fst xy,fst x'y']) (H[snd xy,snd x'y'])).
Defined.

Definition prod' (G H:ωPreCat) : ωPreCat := 
  (G.1**H.1; {| _comp := compo_prod G H ; _id := id_prod G H |}).

Instance composableHere (G:ωPreCat) x y z : Composable (G [x,y].1) (G [y,z].1) (G [x,z].1)
                                        := compo_here G x y z.

Instance composableHom {G H K :ωPreCat} {compGHK : Composable G.1 H.1 K.1} (f f' : |G|) (g g' : |H|) : Composable  (G [f, f'].1) (H [g, g'].1) (K [g ° f, g' ° f'].1) :=
  ({| compo := compo << (f,g), (f',g') >> |}).

Notation "A ** B" := (prod' A B) (at level 90).

Notation " A ==> B " := (A.1 ==> B.1) (at level 90).

Notation "g °° f" := (GComp f g) (at level 20).

(** compare to TLCA paper, we first parametrize the definition by a notion of *)
(** commutative triangle ans square.*)
(** we then instantiate commutation with (cellular) equality of the composite *)
(** this modalutity will be useful to avoid duplication of definition in the *)
(** construction of the fundamental groupoid *)

(* commutative triangle *)

Definition commutativeTriangle_Type (C : ωPreCat) := ∀ (A B : ωPreCat)
          (F : A ==> B) (G : B ==> C) (H : A ==> C), Type.

CoInductive commutativeTriangle (G: ωPreCat) :=
  mkCommutativeTriangle:
    commutativeTriangle_Type G ->
    (∀ (x y : |G|), commutativeTriangle (G[x,y])) ->
    commutativeTriangle G.

Class CommutativeTriangle G := {_commutativeTriangle : commutativeTriangle G}.

Definition commutativeTriangleHere G `{CommutativeTriangle G} :
  commutativeTriangle_Type G.
  destruct H as [[c _]]. exact c.
Defined.

Instance commutativeTriangleHom G `{CommutativeTriangle G} :
  ∀ (x y : |G|), CommutativeTriangle (G[x,y]).
  intros. destruct H as [[c c0]]. apply (Build_CommutativeTriangle (c0 x y)).
Defined. 

(* commutative square *)

Definition commutativeSquare_Type (D : ωPreCat) := ∀ (A B C : ωPreCat)
          (U : A ==> B) (F : A ==> C) (V : C ==> D) (G : B ==> D), Type.

CoInductive commutativeSquare (G: ωPreCat) :=
  mkCommutativeSquare:
    commutativeSquare_Type G ->
    (∀ (x y : |G|), commutativeSquare (G[x,y])) ->
    commutativeSquare G.

Class CommutativeSquare G := {_commutativeSquare : commutativeSquare G}.

Definition commutativeSquareHere G `{CommutativeSquare G} :
  commutativeSquare_Type G.
  destruct H as [[c _]]. exact c.
Defined.

Instance commutativeSquareHom G `{CommutativeSquare G} :
  ∀ (x y : |G|), CommutativeSquare (G[x,y]).
  intros. destruct H as [[c c0]]. apply (Build_CommutativeSquare (c0 x y)).
Defined. 

(* Definition of the unitality laws *)

CoFixpoint GPoint {G : ωPreCat} (f:|G|) : ωterminal ==> G :=
  mkGHom ωterminal.1 G.1 (λ _, f) (λ e e', GPoint (identity f)).

CoFixpoint ωterminal_unitL G : (ωterminal ** G) ==> G :=
  mkGHom (ωterminal ** G).1 G.1 (λ x, snd x)
         (λ x y, ωterminal_unitL (G[snd x,snd y])).

CoFixpoint ωterminal_unitR G : (G ** ωterminal) ==> G :=
  mkGHom (G ** ωterminal).1 G.1 (λ x, fst x)
         (λ x y, ωterminal_unitR (G[fst x,fst y])).

Unset Implicit Arguments.

CoInductive unitalityL (G : ωPreCat) `{CommutativeTriangle G} : Type :=
  mkUnitalityL: (* the law *)
    (∀ (x y : |G|),
       commutativeTriangleHere (ωterminal ** G[x,y])
                               (G[x,x] ** G[x,y]) 
                               (prod_hom' (GPoint (identity x)) (GId (G[x,y]).1))
                               compo (ωterminal_unitL (G[x,y]))) ->
    (* the co-induction step *)
    (∀ (x y : |G|), @unitalityL (G[x,y]) _) ->
    unitalityL G.

CoInductive unitalityR (G : ωPreCat) `{CommutativeTriangle G} : Type :=
  mkUnitalityR: (* the law *)
    (∀ (x y : |G|),
       commutativeTriangleHere (G[x,y] ** ωterminal)
                               (G[x,y] ** G[y,y])
                               (prod_hom' (GId (G[x,y]).1) (GPoint (identity y)))
                               compo (ωterminal_unitR (G[x,y]))) ->
    (* the co-induction step *)
    (∀ (x y : |G|), @unitalityR (G[x,y]) _) ->
    unitalityR G.

(* preservation of composition (Definition 7 in TLCA paper) *)

CoInductive preservesCompo  (G H : ωPreCat) (f : G ==> H) `{CommutativeSquare H}: Type :=
  mkPreservesCompo : (∀ (x y z : |G|),
                        commutativeSquareHere (G[x,y] ** G[y,z]) (G[x,z])
                          (H[f @@ x, f @@ y] ** H[f @@ y,f @@ z])
                          (@compo _ _ _ _) (prod_hom' (f << x,y >>) (f << y,z >>))
                          (@compo _ _ _ _) (f << x,z >>))
                       ->
                       (∀ (x y : |G|),
                          @preservesCompo (G[x,y]) (H[f @@ x, f @@ y]) (f << x, y >>) _)
                       -> preservesCompo G H f.

(* preservation of identities (Definition 8 in TLCA paper) *)

CoInductive preservesId (G H : ωPreCat) (f : G ==> H) : Type :=
  mkPreservesId :
    (* the law *)
    (∀ (x : |G|), f <<x,x>> @@ (identity x) = identity (f @@ x)) ->
    (* the co-induction step *)
    (∀ (x y : |G|), preservesId (G[x,y]) (H[f@@x,f@@y]) (f <<x,y>>)) ->
    preservesId G H f.

(* ωFunctor are morphisms that preserve identities and composition (Definition 9 in TLCA paper) *)

Definition IsωFunctor G H (f : G ==> H) `{CommutativeSquare H}: Type :=
  preservesCompo G H f * preservesId G H f.

CoInductive compo_ωFunctor (G : ωPreCat) `{CommutativeSquare G} : Type :=
  mkcompo_ωFunctor :
    (∀ x y z: |G|, IsωFunctor (G [x, y] ** G [y, z]) (G [x, z])
                (@compo _ _ _ _)) ->
    (∀ (x y : |G|), @compo_ωFunctor (G[x,y]) _) ->
    compo_ωFunctor G.

(* associativity *)

CoInductive associativity (G : ωPreCat) `{CommutativeSquare G}: Type := 
mkAssociativity :
        (∀ (x y z t : |G|), 
           commutativeSquareHere (G [x,y] ** (G [y,z] ** G [z,t]))
                                 (G[x,z] ** G[z,t]) (G[x,y] ** G[y,t]) 
                                 (prod_hom1 (G[z,t]).1 (compo_here G _ _ _))
                                 (prod_hom' (GId (G[x,y]).1) (@compo _ _ _ _))
                                 (@compo _ _ _ _) (@compo _ _ _ _)) ->
        (* the co-induction step *)
        (∀ (x y :   |G|), @associativity (G [x,y]) _) ->
        associativity G.

(* wild_ωcategory parametrized with CommutativeTriangle and CommutativeSquare *)

Class IsOmegaCategory (G : ωPreCat) (CT:CommutativeTriangle G) (CS:CommutativeSquare G) :=
  mkIsOmegaCategory {
      _idR   : unitalityR G;
      _idL   : unitalityL G;
      _assoc : associativity G;
      _compo_ωFunctor : compo_ωFunctor G}.

Definition GHom_eq_Type := ∀ (A B : ωPreCat)
          (F G : A ==> B), Type.

(* definition of cells for cellular equality *)

Fixpoint cell (n:nat) (G:ωPreCat) : Type := match n with 
 0 => |G|
|S n => {xy :|G| * |G| & cell n (G [fst xy,snd xy])}
end.

Fixpoint cellGHom n (G H: ωPreCat) (f: G ==> H) (cG : cell n G) {struct n}: cell n H.
destruct n.
- exact (f @@ cG).
- exact ((f @@ (fst cG.1),f @@ (snd cG.1));
         cellGHom n (G[fst cG.1, snd cG.1]) 
                  (H[f @@ fst cG.1, f @@ snd cG.1]) (f<<fst cG.1,snd cG.1>>) cG.2).
Defined.

Notation "f `@c` c " := (cellGHom _ _ _ f c) (at level 0).

(* definition of cellular equality (Definition 6 in TLCA paper) *)

Definition GHom_eq_cell : GHom_eq_Type := fun G H f g =>
  forall n (cG:cell n G), f `@c` cG = g `@c` cG.

CoFixpoint GHom_eq_to_commutative_triangle (ghom_eq : GHom_eq_Type) C :
  commutativeTriangle C :=
  mkCommutativeTriangle 
    (fun A B f g h => ghom_eq A C (g °° f) h)
    (fun x y => GHom_eq_to_commutative_triangle ghom_eq (C [x,y])).

Definition GHom_eq_to_commutative_Triangle (ghom_eq : GHom_eq_Type) G
  : CommutativeTriangle G :=
  {| _commutativeTriangle := GHom_eq_to_commutative_triangle ghom_eq G |}.

CoFixpoint GHom_eq_to_commutative_square (ghom_eq : GHom_eq_Type) D :
  commutativeSquare D :=
  mkCommutativeSquare 
    (fun A B C U F V G => ghom_eq A D (V °° F) (G °° U))
    (fun x y => GHom_eq_to_commutative_square ghom_eq (D [x,y])).

Definition GHom_eq_to_commutative_Square (ghom_eq : GHom_eq_Type) G
  : CommutativeSquare G :=
  {| _commutativeSquare := GHom_eq_to_commutative_square ghom_eq G |}.

Definition canonicalTriangle G := GHom_eq_to_commutative_Triangle GHom_eq_cell G.
Definition canonicalSquare G := GHom_eq_to_commutative_Square GHom_eq_cell G.

(* definition of ω-categories (Definition 10 in TLCA paper) *)

Definition wild_ωcat := {G: ωPreCat & IsOmegaCategory G
                               (GHom_eq_to_commutative_Triangle GHom_eq_cell G)
                               (GHom_eq_to_commutative_Square GHom_eq_cell G)}.

Definition ωFunctor (G H: wild_ωcat) := { f:G.1 ==> H.1 & @IsωFunctor G.1 H.1 f (canonicalSquare _)}.

(* some basic definitions to lift the structure of ωPreCat *)

Notation "| G |" := (objects G.1.1) (at level 80).

Hint Extern 1 (IsOmegaCategory (?T.1) _ _) => apply (T.2) : typeclass_instances.

Definition compo_ωFunctorHom (G : wild_ωcat) (x y : |G|) : @compo_ωFunctor
  (G.1 [x,y]) (canonicalSquare _).
  destruct (@_compo_ωFunctor _ _ _ G.2) as [_ comp1].
  exact (comp1 x y).
Defined.

Definition idRHom (G : wild_ωcat) (x y : |G|) : @unitalityR (G.1[x,y]) (canonicalTriangle _).
destruct (@_idR _ _ _ G.2) as [_ idup]. exact (idup x y).
Defined.

Definition idLHom (G : wild_ωcat) (x y : |G|) : @unitalityL (G.1[x,y]) (canonicalTriangle _).
destruct (@_idL _ _ _ G.2) as [_ idup]. exact (idup x y).
Defined.

Definition assocHom (G : wild_ωcat) (x y : |G|) : @associativity
                                               (G.1 [x,y]) (canonicalSquare _).
  destruct (@_assoc _ _ _ G.2) as [_ comp1]. exact (comp1 x y).
Defined.

Definition hom'' (G:wild_ωcat) (x y : |G|) : wild_ωcat := 
  (G.1[x,y]; {| _idR := idRHom G x y ;
                _idL := idLHom G x y ; 
                _assoc := assocHom G x y;
                _compo_ωFunctor := compo_ωFunctorHom G x y|}).

Notation "G [ A , B ]" := (hom'' G A B) (at level 80).

Definition idL {G:wild_ωcat} {x y : |G| } (f : |G [x,y]|) : f ° identity x = f.
  destruct G as [G a]. destruct a as [iR iL a]. destruct iL as [comp0 comp1]. simpl in *.
  specialize (comp0 x y). exact (comp0 0 (tt,f)).
Defined.

Definition idR {G:wild_ωcat} {x y : |G| } (f : |G [x,y]|) : identity y ° f = f.
  destruct G as [G a]. destruct a as [iR iL a]. destruct iR as [comp0 comp1]. simpl in *.
  specialize (comp0 x y). exact (comp0 0 (f,tt)).
Defined.

Definition assoc {G : wild_ωcat} {x y z w : |G| }
           (f : |G [x,y]|) (g : |G [y,z]|) (h : |G [z,w]|): 
  (h ° g) ° f = h ° (g ° f).
destruct G as [G a]. destruct a. destruct _assoc0 as [comp0 comp1]. simpl in *.
specialize (comp0 x y z w). exact (comp0 0 (f,(g,h))).
Defined.

(* Definition of univalence wild_ωcat *)

Definition section {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.

Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
  equiv_inv : B -> A ;
  eisretr : section equiv_inv f;
  eissect : section f equiv_inv;
  eisadj : forall x : A, eisretr (f x) = ap f (eissect x)
}.

Definition cell_path_gen {A} (G : wild_ωcat) {x y :A} (P : A -> |G|) :
  x = y -> |G[P x, P y]| :=
  fun e => transport (fun X => |G [P x, P X]|) e (identity (P x)). 

Definition cell_path (G : wild_ωcat) (x y : |G|) (e : x = y) : |G[x,y]| :=
  cell_path_gen G id e.

(* univalent categories (Definition 16) *)

CoInductive IsUnivalent (G : wild_ωcat) :=
  mkIsUnivalent :
    (∀ (x y : |G|), IsEquiv (@cell_path G x y)) ->
    (∀ (x y : |G|), IsUnivalent (G[x,y])) ->
    IsUnivalent G.

Definition Univalent_wild_ωcat := {G : wild_ωcat & IsUnivalent G}.

Definition Univ_embedding : Univalent_wild_ωcat -> wild_ωcat := fun G => G.1.

Notation " A ==> B " := (A.1 ==> B.1) (at level 90).

Definition IsUnivalent_here G (univ : IsUnivalent G) (x y :|G|) :
  IsEquiv (@cell_path G x y).
  destruct univ. exact (i x y).
Defined.

(* CoInductive weak_equivalence : ∀ (G H: wild_ωcat) (f : G ==> H), Type :=  *)
(*   mkWeakEquivalence : ∀ (G H: wild_ωcat) (f : G ==> H),  *)
(*     (∀ y : |H|, {x:|G| & |H[f @@ x,y]| }) ->  *)
(*     (∀ x x' : |G|, weak_equivalence (G[x,x']) (H[f @@ x,f @@ x']) (f<<x,x'>>)) ->  *)
(*     weak_equivalence G H f. *)


(* Duals (Definition 17 of TLCA paper) *)

CoInductive hasDual (G : wild_ωcat) : Type :=
  mkHasDual : 
      (* the law *)
      (∀ (x y : |G|) (f:|G[x,y]|),
         {inverse_f : |G[y,x]| &
         (|G[y,y][f ° inverse_f, identity _]| *
          |G[x,x][inverse_f ° f, identity _]|)%type }) ->
      (* the co-induction step *)
      (∀ x y  : |G|, hasDual (G [x,y])) ->
      hasDual G.

(* Equivalence and reversible cells (Definition 18 of TLCA paper) *)

CoInductive equivalence (G : wild_ωcat) (x y : |G|) : Type :=
mkequivalence : 
    (* the law *)
    { f : |G[x,y]| & reversible G x y f}  ->
    equivalence G x y
with reversible (G : wild_ωcat) (x y : |G|) : ∀ (f : |G[x,y]|), Type :=
mkIsInv : 
  ∀ (f : |G[x,y]|), 
    (* the law *)
    {inverse_f : |G[y,x]| &
         (equivalence (G[y,y]) (f ° inverse_f) (identity _) *
          equivalence (G[x,x]) (inverse_f ° f) (identity _))%type }  ->
    reversible G x y f.

(* Weak inverses (Definition 19 of TLCA paper) *)

CoInductive hasInverse (G : wild_ωcat) : Type :=
  mkHasInverse : 
      (* the law *)
      (∀ (x y : |G|) (f:|G[x,y]|), reversible G x y f) ->
      (* the co-induction step *)
      (∀ x y  : |G|, hasInverse (G [x,y])) ->
      hasInverse G.

Definition hasDual_pi1 {G : wild_ωcat} (dualG : hasDual G) (x y : |G|) (f:|G[x,y]|) :
  {inverse_f : |G[y,x]| &
        (|G[y,y][f ° inverse_f, identity _]| *
         |G[x,x][inverse_f ° f, identity _]|)%type }.
  destruct dualG. exact (s _ _ _).
Defined.

Definition hasDual_pi2 {G : wild_ωcat} (dualG : hasDual G)
           (x y : |G|) : hasDual (G[x,y]).
  destruct dualG. exact (h _ _).
Defined.

Definition hasInverse_pi1 {G : wild_ωcat} (dualG : hasInverse G)
           (x y : |G|) (f:|G[x,y]|) : reversible G x y f.
  destruct dualG. exact (r _ _ _).
Defined.

Definition hasInverse_pi2 {G : wild_ωcat} (dualG : hasInverse G)
           (x y : |G|) : hasInverse (G[x,y]).
  destruct dualG. exact (h _ _).
Defined.

CoFixpoint hasDual_to_reversible {G : wild_ωcat}
  (dualG : hasDual G) (x y : |G|) (f:|G[x,y]|) : reversible G x y f.
apply mkIsInv. exists ((hasDual_pi1 dualG x y f).1). split.
  { apply mkequivalence. exists (fst ((hasDual_pi1 dualG x y f).2)).
    exact (hasDual_to_reversible _
                       (hasDual_pi2 dualG y y) _ _ _). }
  { apply mkequivalence. exists (snd ((hasDual_pi1 dualG x y f).2)).
    exact (hasDual_to_reversible _
                       (hasDual_pi2 dualG x x) _ _ _). }
Defined.

(* This is a formalization of Eugenia Cheng result, 
   [An ω-category with all duals is an ω-groupoid] *)
(* This is Proposition 3 of TLCA paper *)

CoFixpoint hasDual_to_hasInverse (G : wild_ωcat) :
  hasDual G -> hasInverse G.
intro dual. apply mkHasInverse.
- intros x y f. exact (hasDual_to_reversible dual x y f). 
- destruct dual. exact (fun x y => hasDual_to_hasInverse _ (h x y)).
Defined.


