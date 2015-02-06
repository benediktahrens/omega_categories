Add LoadPath "." as OmegaCategories.
Require Export Unicode.Utf8_core.
Require Import BinInt Even List Heap Le Plus Minus.
Require Import Omega. 

(** * Globular sets, basic definitions  *)

(** First, a notation for [existT], the quantifier over [Type]s *)

Set Implicit Arguments.

(** Inductive type for globular sets *)
CoInductive GType : Type := mkGType : ∀ (Obj : Type), (Obj -> Obj -> GType) -> GType. 

Definition objects (G : GType) : Type.
destruct G as [Obj G]. exact Obj.
Defined.

Notation " | A |" := (objects A) (at level 80).

Definition hom (G : GType) : ∀ (a b : |G|), GType.
destruct G as [Obj G]. exact G.
Defined.

Reserved Notation " A ==> B " (at level 90).
Notation " G [ A , B ]" := (hom G A B) (at level 80).

CoInductive GHom : ∀ (G H : GType), Type := 
  mkGHom : ∀ (G H : GType) (f0 : |G| -> |H|)
             (f1 : ∀ (x x' : |G|), G [x,x'] ==> H [f0 x, f0 x']),
             G ==> H
where " A ==> B " := (GHom A B).

(* identity on GTypes *)

CoFixpoint GId (G:GType) : G ==> G := mkGHom G G id (fun x y => GId (G [x, y])).

Definition app G H (f : G ==> H) : |G| -> |H|.
intro x. destruct f. exact (f0 x).
Defined.

Notation "f @@ x" := (app f x) (at level 20) : type_scope.

Definition map G H (f : G ==> H) (x x' : |G|) : G [x,x'] ==> H [f @@ x, f @@ x'].
destruct f. exact (f1 x x').
Defined.

Notation "f << x , x' >>" := (map f x x') (at level 80).

CoFixpoint GComp  (X Y Z:GType) : X ==> Y -> Y ==> Z -> X ==> Z :=
  fun f g => mkGHom _ _ (fun x => g @@ (f @@ x)) 
                    (fun x x' => GComp (f << x , x' >>) (g << f @@ x, f @@ x'>>)).

Reserved Notation "A ** B" (at level 90).

CoFixpoint product (G H : GType) : GType :=  
  @mkGType (prod (objects G) (objects H)) 
         (fun xy xy' => G [fst xy, fst xy'] ** H [snd xy, snd xy'])
where "A ** B"  := (product A B).
