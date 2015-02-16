Add LoadPath "." as OmegaCategories.
Require Export Unicode.Utf8_core.
Require Import BinInt Even List Heap Le Plus Minus.
Require Import Omega. 
Require Import path GType. 

Set Implicit Arguments.

Class Composable (A B C : GType) := { compo : (A ** B) ==> C }.

Notation "g ° f" := (app compo (f, g)) (at level 20).

CoInductive Id : ∀ (G : GType), Type :=
mkId : ∀ (G : GType),
    (∀ (x : |G|), |G[x,x]|) ->
    (∀ (x y : |G|), Id (G [x,y])) ->
    Id G.


CoInductive Compo : ∀ (G : GType), Type  :=
mkCompo : ∀ (G : GType),
   (∀ x y z : |G|, Composable (G [x,y]) (G [y,z]) (G [x,z])) ->
   (∀ x y   : |G|, Compo (G [x,y])) ->
Compo G.

Class IsωPreCat (G : GType) := mkCompoGType {_comp : Compo G; 
                                             _id : Id G}.

Definition ωPreCat := {G: GType & IsωPreCat G}.

(* some basic definitions to get back the structure of GType *)

Hint Extern 1 (IsωPreCat (?T.1)) => apply (T.2) : typeclass_instances.

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

(* Definition of internal transports *)

CoFixpoint append_left {G1 G2 G : ωPreCat} (f : |G1|) (g g' : |G2|)
     {compG : Composable G1.1 G2.1 G.1} :
  G2[g,g'] ==> G[g°f,g'°f] :=
  mkGHom _ _ (fun e => e ° identity f)
             (fun e e' => append_left (identity f) e e').

CoFixpoint append_right {G1 G2 G : ωPreCat} (f f' : |G1|) (g : |G2|)
     {compG : Composable G1.1 G2.1 G.1} :
  G1[f,f'] ==> G[g°f,g°f'] :=
  mkGHom _ _ (fun e => identity g ° e)
             (fun e e' => append_right e e' (identity g)).

Definition transport_GHomL {G:ωPreCat} {x y z : |G| } (f : |G[x,y]|) :
  G[y,z] ==> G[x,z] :=
  mkGHom _ _ (fun g => g ° f) (fun g g' => append_left f g g').

Definition transport_GHomR {G:ωPreCat} {z x y : |G| } (f : |G[x,y]|) :
  G[z,x] ==> G[z,y] :=
  mkGHom _ _ (fun g => f ° g) (fun g g' => append_right g g' f).

Definition transport_GHomL_eq_J {G:ωPreCat} {x y z : |G| } (f : x = y) :
  G[y,z] ==> G[x,z] :=
  transport_GHomL (transport (λ X, |G [x, X]|) f (identity x)).

Definition transport_GHomR_eq_J {G:ωPreCat} {z x y : |G| } (f :x = y) :
  G[z,x] ==> G[z,y] := 
  transport_GHomR (transport (λ X, |G [x, X]|) f (identity x)).

CoInductive transport_GHom_eq_type : ∀ (G:ωPreCat), Type := 
  mkTransport_GHom_eq_type : ∀ (G : ωPreCat), 
  (∀ {x y z : |G| } (f : x = y), G[y,z] ==> G[x,z]) ->
  (∀ {z x y : |G| } (f : x = y), G[z,x] ==> G[z,y]) ->
  (∀ {x y : |G| }, transport_GHom_eq_type (G[x,y])) ->
  transport_GHom_eq_type G.

(*** transport_eq describes the internal transport of identity in an ωPreCat ***)
(*** The need for a internal transport is explained in footnote 1 of the paper, ***)
(*** it is used in the construction of the fundamental groupoid to provide ***)
(*** a more direct transport, based on concatenation only. ***)

Class _transport_eq (G:ωPreCat) := _mkTransport_eq
{
  transport_GHom_eq : transport_GHom_eq_type G
}.

Definition canonical_transport (G:ωPreCat) : _transport_eq G.
  econstructor. generalize dependent G; cofix. intro. econstructor. 
  intros; apply transport_GHomL_eq_J; auto.
  intros; apply transport_GHomR_eq_J; auto.
  intros; apply canonical_transport.
Defined.

Definition transport_GHomL_eq_here {G:ωPreCat} {_transport : _transport_eq G}
           {x y z : |G| } (f : x = y) : G[y,z] ==> G[x,z].
  destruct _transport as [H]. destruct H.  apply (g x y z f).
Defined.

Definition transport_GHomR_eq_here {G:ωPreCat} {_transport : _transport_eq G}
           {x y z : |G| } (f : x = y) : G[z,x] ==> G[z,y].
  destruct _transport as [H]. destruct H.  apply (g0 z x y f).
Defined.

Definition transport_GHom_eq_hom (G:ωPreCat) (_transport : _transport_eq G)
           {x y : |G| } : _transport_eq  (G[x,y]).
  econstructor. destruct _transport as [H]. destruct H. apply t.
Defined.

Hint Extern 1 (_transport_eq (?G[?x,?z])) => apply (transport_GHom_eq_hom _) : typeclass_instances.

(*** State the compatibility with canonical transport ***)
(*** Because the internal transport can not be arbitrary ***)
(*** We say that it must correspond (by bisimilarity) to the ***)
(*** to the canonical transport ***)

CoInductive GHom_eq  (G G' : ωPreCat) (f g : G ==> G') : Type :=
   mkGHom_eq_J : ∀ (fgeq : ∀ x, f @@ x = g @@ x),
                   (∀ x y, GHom_eq (G [x, y])
                                 (G' [g @@ x, g @@ y])
                                 (transport_GHomL_eq_J (inverse (fgeq x)) °° 
                                  (transport_GHomR_eq_J (fgeq y) °° 
                                   (f << x , y >>))) 
                                 (g << x , y >>)) ->
                   GHom_eq _ _ f g.

Definition transport_GHomL_compat G (x y z : |G|) (e : x = y) (_transport : _transport_eq G) :=
  GHom_eq _ _ (@transport_GHomL_eq_J G x y z e) (@transport_GHomL_eq_here G _ x y z e).

Definition transport_GHomR_compat G (x y z : |G|) (e : x = y) (_transport : _transport_eq G) :=
  GHom_eq _ _ (@transport_GHomR_eq_J G z x y e) (@transport_GHomR_eq_here G _ x y z e).

CoInductive transport_is_canonical (G:ωPreCat) (_transport : _transport_eq G) : Type := 
  mkTransport_compat :
  (∀ {x y z : |G| } (e : x = y), transport_GHomL_compat z e _) ->
  (∀ {z x y : |G| } (e : x = y), transport_GHomR_compat z e _) ->
  (∀ {x y : |G| }, @transport_is_canonical (G[x,y]) _) ->
  @transport_is_canonical G _.

Class transport_eq (G:ωPreCat) := mkTransport_eq
{
  _transport :> _transport_eq G;
  _transport_is_canonical : transport_is_canonical _transport
}.

Definition transport_GHom_eq_hom' (G:ωPreCat) (_transport : transport_eq G)
           {x y : |G| } : transport_eq  (G[x,y]).
  econstructor. destruct _transport as [H H_can]. destruct H_can. apply t1.
Defined.

Hint Extern 1 (transport_eq (?G[?x,?z])) => apply (transport_GHom_eq_hom' _) : typeclass_instances.

(* Definition of the identity laws *)

Unset Implicit Arguments.

Definition higher_composable_compoIdL (G H : ωPreCat) (candidate_id : |G|) (_transport : transport_eq H)
                                { composable : Composable G.1 H.1 H.1}
                                (idL : ∀ (h : |H|), h ° candidate_id = h) h h' :
  Composable (G[candidate_id, candidate_id]).1 (H [h,h']).1 (H [h, h']).1 :=
{| compo := transport_GHomL_eq_here (inverse (idL h)) °°
               (transport_GHomR_eq_here (idL h') °°
                    (compo << (candidate_id,h), (candidate_id,h') >>)) |}.

CoInductive compoIdL_H (G H : ωPreCat) (candidate_id : |G|) {_transport : transport_eq H}
            {composable : Composable G.1 H.1 H.1} : Type :=
  mkCompoIdL_H : ∀ (idL : ∀ (h : |H|), h ° candidate_id = h),
     (∀ (h h' : |H|), @compoIdL_H (G[candidate_id, candidate_id]) (H[h,h']) (identity candidate_id)
                _ (higher_composable_compoIdL _ _ _ _ idL h h')) ->
    compoIdL_H G H candidate_id.

CoInductive compoIdL (G : ωPreCat) {_transport : transport_eq G} : Type :=
  mkCompoIdL :(* the law *)
              (∀ (x y : |G|), compoIdL_H (G[x,x]) (G[x,y]) (identity x)) ->
              (* the co-induction step *)
              (∀ (x y : |G|), @compoIdL (G[x,y]) _) ->
              compoIdL G.

Definition higher_composable_compoIdR (G H : ωPreCat) (candidate_id : |H|) (_transport : transport_eq G)
                                { composable : Composable G.1 H.1 G.1}
                                (idR : ∀ (g : |G|), candidate_id ° g = g) g g' :
  Composable (G[g,g']).1 (H[candidate_id, candidate_id]).1 (G [g, g']).1 :=
{| compo := transport_GHomL_eq_here (inverse (idR g)) °°
               (transport_GHomR_eq_here (idR g') °°
                    (compo << (g,candidate_id), (g',candidate_id) >>)) |}.


CoInductive compoIdR_H (G H : ωPreCat) (candidate_id : |H|) {_transport : transport_eq G}
                                { composable : Composable G.1 H.1 G.1} : Type :=
  mkCompoIdR_H : ∀ (idR : ∀ (g : |G|), candidate_id ° g = g), 
     (∀ (g g' : |G|), @compoIdR_H (G[g,g']) (H[candidate_id, candidate_id]) (identity candidate_id)
                _ (higher_composable_compoIdR _ _ _ _ idR g g')) ->
    compoIdR_H G H candidate_id.

CoInductive compoIdR (G : ωPreCat) {_transport : transport_eq G} : Type :=
  mkCompoIdr :(* the law *)
              (∀ (x y : |G|), compoIdR_H (G[x,y]) (G[y,y]) (identity y)) ->
              (* the co-induction step *)
              (∀ (x y : |G|), @compoIdR (G[x,y]) _) ->
              compoIdR G.

Set Implicit Arguments.

(* commutative square *)

CoInductive commutativeSquare  (A B C D : ωPreCat) {_transport : transport_eq D}
                             (U : A ==> B) (F : A ==> C) (V : C ==> D) (G : B ==> D) : Type :=
  mkCommutativeSquare : ∀ (comm : ∀ x, (V °°F) @@ x =  (G °° U) @@ x),
                (∀ x y, @commutativeSquare (A [x, y]) (B [U @@ x, U @@ y])
                                   (C [F @@ x, F @@ y]) (D[(G°°U) @@ x, (G°°U) @@ y]) _
                                   (U << x , y >>) (F << x , y >>)
                                   (transport_GHomL_eq_here (inverse (comm x)) °°
                                     (transport_GHomR_eq_here (comm y) °°
                                        (V << F @@ x , F @@ y >>)))
                                   (G << U @@ x , U @@ y >>)) ->
                 @commutativeSquare A B C D _ U F V G.

Arguments commutativeSquare : clear implicits.

Definition transport_hom (A B A' B': ωPreCat) (eA:A = A') (eB:B = B') (f : A ==> B)
           := transport (fun X => X ==> B') eA (transport (fun X => A ==> X) eB f).

Definition transport_hom_concat (A B A' B' A'' B'': ωPreCat) (eA:A = A') (eB:B = B') (eA':A' = A'') (eB':B' = B'') (f : A ==> B) :
  transport_hom eA' eB' (transport_hom eA eB f) = transport_hom (eA @ eA') (eB @ eB') f.
  destruct eA, eB. reflexivity.
Defined.
  
Definition path_commutativeSquare A B C D A' B' C' D'
           (_transport : transport_eq D)
           (U : A ==> B) (F : A ==> C) (V : C ==> D) (G : B ==> D) 
           (eA:A = A') (eB:B = B') (eC:C = C') (eD:D = D')
           (commS : commutativeSquare A' B' C' D' (eD # _transport)
                                      (transport_hom eA eB U) (transport_hom eA eC F)
                                      (transport_hom eC eD V) (transport_hom eB eD G)) :
  commutativeSquare A B C D _transport U F V G.
  destruct eA, eB, eC, eD. exact commS.
Defined.

(* morphism that preserves identity and composition *)

CoInductive preservesCompo  (G H : ωPreCat) (f : G ==> H) (_transport : transport_eq H) : Type :=
  mkPreservesCompo : (∀ (x y z : |G|), commutativeSquare (G[x,y] ** G[y,z]) (G[x,z])
                          (H[f @@ x, f @@ y] ** H[f @@ y,f @@ z]) (H[f @@ x,f @@ z]) _
                          (@compo _ _ _ _) (prod_hom' (f << x,y >>) (f << y,z >>))
                          (@compo _ _ _ _) (f << x,z >>))
                       ->
                       (∀ (x y : |G|),
                          @preservesCompo (G[x,y]) (H[f @@ x, f @@ y]) (f << x, y >>) _)
                       -> @preservesCompo G H f _.

CoInductive preservesId (G H : ωPreCat) (f : G ==> H) : Type :=
  mkPreservesId :
    (* the law *)
    (∀ (x : |G|), f <<x,x>> @@ (identity x) = identity (f @@ x)) ->
    (* the co-induction step *)
    (∀ (x y : |G|), preservesId (G[x,y]) (H[f@@x,f@@y]) (f <<x,y>>)) ->
    preservesId G H f.

Definition IsωFunctor G H (f : G ==> H) (_transport : transport_eq H) : Type :=
  @preservesCompo G H f _ * preservesId G H f.

Unset Implicit Arguments.

CoInductive compo_ωFunctor (G : ωPreCat) {_transport : transport_eq G} : Type :=
  mkcompo_ωFunctor :
    (∀ x y z: |G|, @ IsωFunctor (G [x, y] ** G [y, z]) (G [x, z])
                (@compo _ _ _ _) _) ->
    (∀ (x y : |G|), @compo_ωFunctor (G[x,y]) _) ->
    compo_ωFunctor G.

(* associativity *)

CoInductive associativity (G : ωPreCat) {_transport : transport_eq G} : Type := 
mkAssociativity :
        (∀ (x y z t : |G|), 
           commutativeSquare (G [x,y] ** (G [y,z] ** G [z,t]))
                             (G[x,z] ** G[z,t]) (G[x,y] ** G[y,t]) (G[x,t]) _
                             (prod_hom1 (G[z,t]).1 (compo_here G _ _ _))
                             (prod_hom' (GId (G[x,y]).1) (@compo _ _ _ _))
                             (@compo _ _ _ _) (@compo _ _ _ _)) ->
        (* the co-induction step *)
        (∀ (x y :   |G|), @associativity (G [x,y]) _) ->
        associativity G.

Set Implicit Arguments.

Class IsOmegaCategory (G : ωPreCat) := mkIsOmegaCategory {
  _tran  : transport_eq G;
  _idR   : compoIdR G;
  _idL   : compoIdL G;
  _assoc : associativity G;
  _compo_ωFunctor : compo_ωFunctor G}.

Definition ωcat := {G: ωPreCat & IsOmegaCategory G}.

(* some basic definitions to lift the structure of ωPreCat *)

Notation "| G |" := (objects G.1.1) (at level 80).

Hint Extern 1 (IsOmegaCategory (?T.1)) => apply (T.2) : typeclass_instances.

Definition compo_ωFunctorHom (G : ωcat) (x y : |G|) : @compo_ωFunctor (G.1 [x,y])
                                                                    (transport_GHom_eq_hom' _tran).
  destruct (@_compo_ωFunctor _ G.2) as [_ comp1]. exact (comp1 x y).
Defined.

Definition idRHom (G : ωcat) (x y : |G|) : @compoIdR (G.1[x,y]) (transport_GHom_eq_hom' _tran).
destruct (@_idR _ G.2) as [_ idup]. exact (idup x y).
Defined.

Definition idLHom (G : ωcat) (x y : |G|) : @compoIdL (G.1[x,y]) (transport_GHom_eq_hom' _tran).
destruct (@_idL _ G.2) as [_ idup]. exact (idup x y).
Defined.

Definition assocHom (G : ωcat) (x y : |G|) : @associativity (G.1 [x,y])
                                                      (transport_GHom_eq_hom' _tran).
  destruct (@_assoc _ G.2) as [_ comp1]. exact (comp1 x y).
Defined.

Definition hom'' (G:ωcat) (x y : |G|) : ωcat := 
  (G.1[x,y]; {| _idR := idRHom G x y ;
                _idL := idLHom G x y ; 
                _assoc := assocHom G x y;
                _compo_ωFunctor := compo_ωFunctorHom G x y|}).

Notation "G [ A , B ]" := (hom'' G A B) (at level 80).

Definition idL {G:ωcat} {x y : |G| } (f : |G [x,y]|) : f ° identity x = f.
  destruct G as [G a]. destruct a as [a iR iL]. destruct iL as [comp0 comp1]. simpl in *.
  specialize (comp0 x y). destruct comp0 as [comp0 _ ]. apply comp0.
Defined.

Definition idR {G:ωcat} {x y : |G| } (f : |G [x,y]|) : identity y ° f = f.
  destruct G as [G a]. destruct a as [a iR iL]. destruct iR as [comp0 comp1]. simpl in *.
  specialize (comp0 x y). destruct comp0 as [comp0 _ ]. apply comp0.
Defined.

Definition assoc {G : ωcat} {x y z w : |G| }
           (f : |G [x,y]|) (g : |G [y,z]|) (h : |G [z,w]|): 
  (h ° g) ° f = h ° (g ° f).
destruct G as [G a]. destruct a. destruct _assoc0 as [comp0 comp1]. simpl in *.
specialize (comp0 x y z w). destruct comp0. apply (comm (f,(g,h))).
Defined.

(* Definition of univalence ωcat *)

Definition section {A B : Type} (s : A -> B) (r : B -> A) :=
  forall x : A, r (s x) = x.

Class IsEquiv {A B : Type} (f : A -> B) := BuildIsEquiv {
  equiv_inv : B -> A ;
  eisretr : section equiv_inv f;
  eissect : section f equiv_inv;
  eisadj : forall x : A, eisretr (f x) = ap f (eissect x)
}.

Definition cell_path_gen A (G : ωcat) (x y :A) (P : A -> |G|) :
  x = y -> |G[P x, P y]| :=
  fun e => transport (fun X => |G [P x, P X]|) e (identity (P x)). 

Definition cell_path (G : ωcat) (x y : |G|) (e : x = y) : |G[x,y]| :=
  cell_path_gen G id e.

CoInductive IsUnivalent (G : ωcat) :=
  mkIsUnivalent :
    (∀ (x y : |G|), IsEquiv (@cell_path G x y)) ->
    (∀ (x y : |G|), IsUnivalent (G[x,y])) ->
    IsUnivalent G.


Instance IsEquiv_id A : IsEquiv (id (A:=A)) :=
  {| equiv_inv := idmap;
     eisretr := fun x => eq_refl ;
     eissect := fun x => eq_refl ;
     eisadj  := fun x => eq_refl |}.

Notation " A ==> B " := (A.1 ==> B.1) (at level 90).

Definition IsUnivalent_here G (univ : IsUnivalent G) (x y :|G|) :
  IsEquiv (@cell_path G x y).
  destruct univ. exact (i x y).
Defined.

CoInductive weak_equivalence : ∀ (G H: ωcat) (f : G ==> H), Type := 
  mkWeakEquivalence : ∀ (G H: ωcat) (f : G ==> H), 
    (∀ y : |H|, {x:|G| & |H[f @@ x,y]| }) -> 
    (∀ x x' : |G|, weak_equivalence (G[x,x']) (H[f @@ x,f @@ x']) (f<<x,x'>>)) -> 
    weak_equivalence G H f.


(* for inverse *)

CoInductive hasDual (G : ωcat) : Type :=
  mkHasDual : 
      (* the law *)
      (∀ (x y : |G|) (f:|G[x,y]|),
         {inverse_f : |G[y,x]| &
         (|G[y,y][f ° inverse_f, identity _]| *
          |G[x,x][inverse_f ° f, identity _]|)%type }) ->
      (* the co-induction step *)
      (∀ x y  : |G|, hasDual (G [x,y])) ->
      hasDual G.


CoInductive Iso (G : ωcat) (x y : |G|) : Type :=
mkIso : 
    (* the law *)
    { f : |G[x,y]| & isInv G x y f}  ->
    Iso G x y
with isInv (G : ωcat) (x y : |G|) : ∀ (f : |G[x,y]|), Type :=
mkIsInv : 
  ∀ (f : |G[x,y]|), 
    (* the law *)
    {inverse_f : |G[y,x]| &
         (Iso (G[y,y]) (f ° inverse_f) (identity _) *
          Iso (G[x,x]) (inverse_f ° f) (identity _))%type }  ->
    isInv G x y f.

CoInductive hasInverse (G : ωcat) : Type :=
  mkHasInverse : 
      (* the law *)
      (∀ (x y : |G|) (f:|G[x,y]|), isInv G x y f) ->
      (* the co-induction step *)
      (∀ x y  : |G|, hasInverse (G [x,y])) ->
      hasInverse G.

Definition hasDual_pi1 (G : ωcat) (dualG : hasDual G) (x y : |G|) (f:|G[x,y]|) :
  {inverse_f : |G[y,x]| &
        (|G[y,y][f ° inverse_f, identity _]| *
         |G[x,x][inverse_f ° f, identity _]|)%type }.
  destruct dualG. exact (s _ _ _).
Defined.

Definition hasDual_pi2 (G : ωcat) (dualG : hasDual G)
           (x y : |G|) : hasDual (G[x,y]).
  destruct dualG. exact (h _ _).
Defined.

Definition hasInverse_pi1 (G : ωcat) (dualG : hasInverse G)
           (x y : |G|) (f:|G[x,y]|) : isInv G x y f.
  destruct dualG. exact (i _ _ _).
Defined.

Definition hasInverse_pi2 (G : ωcat) (dualG : hasInverse G)
           (x y : |G|) : hasInverse (G[x,y]).
  destruct dualG. exact (h _ _).
Defined.

CoFixpoint hasDual_to_isInv (G : ωcat)
  (dualG : hasDual G) (x y : |G|) (f:|G[x,y]|) : isInv G x y f.
apply mkIsInv. exists ((hasDual_pi1 dualG x y f).1). split.
  { apply mkIso. exists (fst ((hasDual_pi1 dualG x y f).2)).
    exact (hasDual_to_isInv _
                       (hasDual_pi2 dualG y y) _ _ _). }
  { apply mkIso. exists (snd ((hasDual_pi1 dualG x y f).2)).
    exact (hasDual_to_isInv _
                       (hasDual_pi2 dualG x x) _ _ _). }
Defined.

(* This is a formalization of Eugenia Cheng result, 
   [An ω-category with all duals is an ω-groupoid] *)

CoFixpoint hasDual_to_hasInverse (G : ωcat) :
  hasDual G -> hasInverse G.
intro dual. apply mkHasInverse.
- intros x y f. exact (hasDual_to_isInv dual x y f). 
- destruct dual. exact (fun x y => hasDual_to_hasInverse _ (h x y)).
Defined.
