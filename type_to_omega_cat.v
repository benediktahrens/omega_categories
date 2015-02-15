Add LoadPath "." as OmegaCategories.
Require Export Unicode.Utf8_core.
Require Import BinInt Even List Heap Le Plus Minus.
Require Import Omega. 
Require Import path GType omega_categories. 

Set Implicit Arguments.

Notation "| G |" := (objects G) (at level 80).
Notation "G [ A , B ]" := (hom G A B) (at level 80).
Notation "A ** B" := (product A B) (at level 90).
Notation " A ==> B " := (GHom A B) (at level 90).

(* On attaque la def de omega-gpd *)

CoFixpoint pi (T : Type) : GType := @mkGType (T) (fun x y => pi (x = y)).

CoFixpoint piId  (T : Type) : Id (pi T) := 
  mkId (pi T) (fun x => (eq_refl x)) (fun x y => piId (x = y)).

CoFixpoint piComp_V_ (T U V : Type) (f : T -> U -> V)  
           (x y : T) (z w : U)  : 
  (pi (x = y) ** pi (z = w)) ==> pi (f x z = f y w) :=
  mkGHom (pi (x = y) ** pi (z = w))(pi (f x z = f y w)) 
         (fun X =>  ap2 f (fst X) (snd X))
         (fun X Y => piComp_V_ _ _ _ _ _). 

Instance piComp_V (T U V : Type) (f : T -> U -> V)  
         (x y :  T) (z w :  U)  : 
  Composable (pi (x = y)) (pi (z = w)) (pi (f x z = f y w)) :=
  {| compo := piComp_V_ f x y z w |}.

Instance piComp_H (T :Type) (x y z : T) :
  Composable (pi (x = y)) (pi (y = z)) (pi (x = z)) := 
{| compo := 
                         mkGHom ((pi (x = y)) ** (pi (y = z))) (pi (x = z))
                                (fun X => fst X @ snd X) 
                                (fun X Y => compo) |}.

CoFixpoint piComp (T : Type) : Compo (pi T) :=
  mkCompo (pi T) (fun x y z => piComp_H x y z) 
          (fun x y => piComp (x = y)).

Instance pi_IsωPreCat (T : Type) : IsωPreCat (pi T) :=
  {| _comp := piComp T; _id := piId T|}. 

Definition piω (T:Type) : ωPreCat := (pi T; pi_IsωPreCat T).


Notation "G [ A , B ]" := (hom' G A B) (at level 80).

Notation "| G |" := (objects G.1) (at level 80).

Notation "A ** B" := (prod' A B) (at level 90).

Notation " A ==> B " := (A.1 ==> B.1) (at level 90).

(* a more inlined version of idCompo *)

CoInductive idCompoH (G H K : ωPreCat) {composable : Composable G.1 H.1 K.1} : Type :=
  mkIdCompoH :
    (* the law *)
    (∀ (f : |G|) (g : |H|), (identity g) ° (identity f) = identity (g ° f)) ->
    (* the co-induction step *)
    (∀ (f f' : |G|) (g g' : |H|), @idCompoH (G[f,f']) (H[g,g']) (K[g°f,g'°f']) _) ->
    idCompoH G H K.

CoInductive idCompo (G : ωPreCat) : Type :=
mkIdCompo : 
    (* the law *)
    (∀ x y z : |G|, idCompoH (G[x,y]) (G[y,z]) (G[x,z])) ->
    (* the co-induction step *)
    (∀ x y   : |G|, idCompo (G [x,y])) ->
    idCompo G.

Definition  pi_idCompo_gen_eq (T U V : Type) (f : T -> U -> V)  (x y : T) (z w : U)
           (P : (x = y) -> (z = w) -> (f x z = f y w))
           (e e' : x = y) (h h' : z = w) (E : e = e') (H : h = h')  :
  (@identity (piω (h = h')) H ° @identity (piω (e = e')) E) =
  @identity (piω (P e h = P e' h')) (ap2 P E H).
  simpl. destruct E, H. reflexivity.
Defined.

Instance piωComp_V (T U V : Type) (f : T -> U -> V)  (x y : T) (z w : U) :
  Composable (piω (x = y)).1 (piω (z = w)).1 (piω (f x z = f y w)).1 :=
  {| compo := piComp_V_ f x y z w |}.

Instance composableGsetisωPreCat (T U V : Type) (compoTUV : (Composable (pi T) (pi U) (pi V))) : Composable (piω T).1 (piω U).1 (piω V).1 :=
  {| compo := compo |}.

CoFixpoint pi_idCompo_gen (T U V : Type) (f : T -> U -> V)  (x y : T) (z w : U)
           (P : (x = y) -> (z = w) -> (f x z = f y w))
           (e e' : x = y) (h h' : z = w) :
  idCompoH (piω (x = y) [e,e']) (piω (z = w) [h,h']) 
           (piω (f x z = f y w) [P e h, P e' h']) :=
  mkIdCompoH (fun E H => pi_idCompo_gen_eq f P E H) 
             (fun E E' H H' => pi_idCompo_gen P (ap2 P (h':=h')) E E' H H').

Definition pi_idCompoH (T : Type) (x y z :T) : 
  idCompoH (piω T [x, y]) (piω T [y, z]) (piω T [x, z]).
apply mkIdCompoH.
- intros f g. simpl in *. destruct f, g. reflexivity.
- intros f f' g g'. simpl in *. 
  apply mkIdCompoH.
  intros e e'. simpl in *. destruct e, e'. reflexivity.
  intros; simpl in *. apply pi_idCompo_gen.
Defined.

CoFixpoint pi_idCompo (T : Type) : idCompo (piω T) :=
  mkIdCompo (fun (x y z : |piω T|) => pi_idCompoH x y z) 
            (fun x y => pi_idCompo (x = y)).


CoFixpoint piω_transport_GHom_eq (T:Type) : transport_GHom_eq_type (piω T)
  := mkTransport_GHom_eq_type
    (@transport_GHomL (piω T)) 
    (@transport_GHomR (piω T))
    (λ x y, piω_transport_GHom_eq (x = y)).

Instance piω_transport_eq (T:Type) : transport_eq (piω T) :=
  {| transport_GHom_eq := piω_transport_GHom_eq T |}.


(* a more inlined version of the interchange law *)

Definition higher_composable {G1 G2 G H1 H2 H K1 K2 K : ωPreCat}
     { _transport : transport_eq K}
     {compG : Composable G1.1 G2.1 G.1}
     {compH : Composable H1.1 H2.1 H.1}
     {compK : Composable K1.1 K2.1 K.1} 
     {comp1 : Composable G1.1 H1.1 K1.1}
     {comp2 : Composable G2.1 H2.1 K2.1}
     {compGHK : Composable G.1 H.1 K.1} 
     (interchangeLaw : ∀ (f1 : |G1|) (f2 : |G2|) (g1 : |H1|) (g2 : |H2|),
                     (g2 ° f2) ° (g1 ° f1) = (g2 ° g1) ° (f2 ° f1)) 
     (f1 f'1 : |G1|) (f2 f'2 : |G2|) (g1 g'1 : |H1|) (g2 g'2 : |H2|) :
  Composable (K1 [g1 ° f1, g'1 ° f'1]).1 (K2 [g2 ° f2, g'2 ° f'2]).1
        (K [(g2 ° g1) ° (f2 ° f1), (g'2 ° g'1) ° (f'2 ° f'1)]).1 :=
{|
compo := transport_GHomL_eq_here (inverse (interchangeLaw f1 f2 g1 g2))
         °° (transport_GHomR_eq_here (interchangeLaw f'1 f'2 g'1 g'2)
             °° (compo << (g1 ° f1, g2 ° f2), (g'1 ° f'1, g'2 ° f'2) >>)) |}.


CoInductive interchangeV (G1 G2 G H1 H2 H K1 K2 K : ωPreCat)
            (_transport : transport_eq K)
            {compG : Composable G1.1 G2.1 G.1}
            {compH : Composable H1.1 H2.1 H.1}
            (compK : Composable K1.1 K2.1 K.1)
            {comp1 : Composable G1.1 H1.1 K1.1}
            {comp2 : Composable G2.1 H2.1 K2.1}
            {compGHK : Composable G.1 H.1 K.1} : Type :=
 mkInterchangeV :
   {
     (* the law *)
     interchangeLaw : ∀ (f1 : |G1|) (f2 : |G2|) (g1 : |H1|) (g2 : |H2|),
              (g2 ° f2) ° (g1 ° f1) = (g2 ° g1) ° (f2 ° f1) &
     (* the co-induction step *)
     ∀ (f1 f'1 : |G1|) (f2 f'2 : |G2|) (g1 g'1 : |H1|) (g2 g'2 : |H2|),
       @interchangeV
        (G1 [f1,f'1]) (G2 [f2,f'2]) (G [f2 ° f1, f'2  ° f'1])
        (H1 [g1,g'1]) (H2 [g2,g'2]) (H [g2 ° g1, g'2 ° g'1])
        (K1 [g1 ° f1, g'1 ° f'1]) (K2 [g2 ° f2, g'2 ° f'2])
        (K [(g2 ° g1) ° (f2 ° f1), (g'2 ° g'1) ° (f'2 ° f'1)]) _
        _ _ (higher_composable interchangeLaw _ _ _ _ _ _ _ _) _ _ _}   
     ->
     interchangeV G1 G2 G H1 H2 H K1 K2 _transport compK.

(* Pour avoir un test a verifier pour la loi d'echange, une fois qu'on
   a fixe x, y, z en dim d, il faut fixer f f' f'' et g g' g'' de dim
   d+p resp. dans [x,y] et [y,z].
   Le predicat suivant parcourt tout ces choix puis passe la main au predicat precedent.
   Voir la suite pour comprendre quels sont ses parametres initiaux.
*)

CoInductive interchangeH (G H K : ωPreCat) (_transport : transport_eq K) 
            {compGHK : Composable G.1 H.1 K.1}: Type :=
  mkInterchangeH : 
    (* the law *)
    (∀ (f f' f'' : |G|) (g g' g'' : |H|),
      interchangeV
        (G [f, f']) (G [f', f'']) (G [f, f'']) 
        (H [g, g']) (H [g', g'']) (H [g, g'']) 
        (K [g ° f, g' ° f']) (K [g' ° f', g'' ° f'']) 
        (transport_GHom_eq_hom _) _) -> 
    (* the co-induction step *)
    (∀ (f f' : |G|) (g g' : |H|),
      @interchangeH (G [f, f']) (H [g, g']) (K [g ° f, g' ° f']) _ _) ->
      interchangeH G H _transport.

CoInductive interchange (G : ωPreCat) (_transport : transport_eq G) : Type :=
mkInterchange : 
        (* the law *)
        (∀ (x y z : |G|), 
           @interchangeH (G [x,y]) (G [y,z]) (G [x,z]) _ _)
        ->
        (* the co-induction step *)
        (∀ (x y :   |G|), @interchange (G [x,y]) _) ->
        @interchange G _.


CoFixpoint interchangeV_interchange (G1 G2 G H1 H2 H K1 K2 K : ωPreCat)
            (_transport : transport_eq K)
            {compG : Composable G1.1 G2.1 G.1}
            {compH : Composable H1.1 H2.1 H.1}
            (compK : Composable K1.1 K2.1 K.1)
            {comp1 : Composable G1.1 H1.1 K1.1}
            {comp2 : Composable G2.1 H2.1 K2.1}
            {compGHK : Composable G.1 H.1 K.1} :
  interchangeV G1 G2 G H1 H2 H K1 K2 _ compK ->
  @commutativeSquare ((G1 ** H1)**(G2**H2)) (G**H) (K1**K2) _ _
                    (prod_hom compG compH)
                    (prod_hom' (@compo _ _ _ comp1) (@compo _ _ _ comp2))
                    compo compo.
intros [[i s]]. refine (mkCommutativeSquare _ _ _ _ _ _).
- intros [[f1 g1] [f2 g2]]. exact (i f1 f2 g1 g2).
- intros [[f1 g1] [f2 g2]] [[f1' g1'] [f2' g2']]. 
  exact (interchangeV_interchange _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                   (s f1 f1' f2 f2' g1 g1' g2 g2')).
Defined.
 

CoFixpoint interchangeH_interchange (G H K : ωPreCat) (_transport : transport_eq K) 
           {compGHK : Composable G.1 H.1 K.1}:
  interchangeH G H _transport -> preservesCompo (G**H) (@compo _ _ _ compGHK) _transport.
intros [i s]. refine (mkPreservesCompo _ _ _).
- intros [f g] [f' g'] [f'' g''].
  exact (interchangeV_interchange (i f f' f'' g g' g'')).
- intros [f g] [f' g']. 
  exact (interchangeH_interchange _ _ _ _ _ (s f f' g g')).
Defined.

CoFixpoint idCompoH_preservesId (G H K : ωPreCat) {composable : Composable G.1 H.1 K.1} :
  idCompoH G H K -> preservesId (G**H) K compo.
intro Idcompo; destruct Idcompo. apply mkPreservesId.
- intros. destruct x. apply e.
- intros. destruct x, y.
  exact (idCompoH_preservesId (G [o,o1]) (H[o0, o2]) (K [o0 ° o, o2 ° o1]) _ (i _ _ _ _)). 
Defined.


CoFixpoint interchange_idcompo_compo_ωFunctor (G : ωPreCat) (_transport : transport_eq G) :
  @interchange G _ -> idCompo G -> @compo_ωFunctor G _.
intros [i s] [id idh]. apply mkcompo_ωFunctor.
- intros x y z. exact (interchangeH_interchange (i x y z),
                       idCompoH_preservesId  (id x y z)).
- intros x y. exact (interchange_idcompo_compo_ωFunctor  _ _ (s x y) (idh x y)).
Defined.

Instance piωComp_H (T : Type) (x y z : T) :
  Composable (piω (x = y)).1 (piω (y = z)).1 (piω (x = z)).1 :=
  {| compo :=
       mkGHom ((piω (x = y)) ** (piω (y = z))).1 (piω (x = z)).1
              (fun X => concat (fst X) (snd X))
              (fun X Y => compo)|}.

Instance piωComp_V' (T : Type) (x y z : T) (e e' : |piω (x = y)|)
         (f f' : |piω (y = z)|) :
  Composable (piω (e = e')).1 (piω (f = f')).1 (piω (f ° e = f' ° e')).1 :=
  piComp_V concat e e' f f'.

Definition pi_interchangeV_law {T:Type} {x y z : T} {f f' f'' : |piω (x = y)| }
           {g g' g'' : |piω (y = z)| }
       (f1 :|piω (f = f')|) (f2 : |piω  (f' = f'')|) (g1 : |piω (g = g')|)  
       (g2 :|piω (g' = g'')|)
       (X1 := g1 ° f1) (X2 := g2 ° f2)  
       (Y1 := f2 ° f1) (Y2 := g2 ° g1) : X2 ° X1 = Y2 ° Y1 :=
  inverse (concat_LR_concat f1 f2 g1 g2).

Definition higher_composable_gen {T1 T2 T U1 U2 U V1 V2 V : Type}
           {fT : T1 -> T2 -> T}
           {fU : U1 -> U2 -> U}
           {fV : V1 -> V2 -> V}
           {fTUV1 : T1 -> U1 -> V1}
           {fTUV2 : T2 -> U2 -> V2}
           {fTUV : T -> U -> V}
           (interchangeLaw : ∀ (F1 : |piω T1|) (F2 : |piω T2|)
               (G1 : |piω U1|) (G2 : |piω U2|)
               (X1 := fTUV1 F1 G1) (X2 := fTUV2 F2 G2),
               fV X1 X2 = fTUV (fT F1 F2) (fU G1 G2)) 
           (F1 F1': |piω T1|) (F2 F2': |piω T2|)
           (G1 G1': |piω U1|) (G2 G2': |piω U2|) :
  fV (fTUV1 F1 G1) (fTUV2 F2 G2) = fV (fTUV1 F1' G1') (fTUV2 F2' G2') ->
  fTUV (fT F1 F2) (fU G1 G2) = fTUV (fT F1' F2') (fU G1' G2')
  := fun E =>
      inverse (interchangeLaw F1 F2 G1 G2) @
      (E @ interchangeLaw F1' F2' G1' G2').

Definition inversE {T : Type} {x y : |piω T| } (f: |(piω T)[x,y]|) : |(piω T)[y,x]|.
exact (inverse f).
Defined.

Definition pi_interchangeV_gen_law (T1 T2 T U1 U2 U V1 V2 V : Type)
           (F1 F1': |piω T1|) (F2 F2': |piω T2|)
           (G1 G1': |piω U1|) (G2 G2': |piω U2|)
           (fT : T1 -> T2 -> T)
           (fU : U1 -> U2 -> U)
           (fV : V1 -> V2 -> V)
           (fTUV1 : T1 -> U1 -> V1)
           (fTUV2 : T2 -> U2 -> V2)
           (fTUV : T -> U -> V)
           (PT : forall {x y z w}, (x = y) -> (z = w) -> fT x z = fT y w := ap2 fT)
           (PU : forall {x y z w}, (x = y) -> (z = w) -> fU x z = fU y w := ap2 fU) 
           (PV : forall {x1 x1' x2 x2' y1 y1' y2 y2'}, 
                   (fTUV1 x1 x2 = fTUV1 x1' x2') -> (fTUV2 y1 y2 = fTUV2 y1' y2') 
                   -> fV (fTUV1 x1 x2) (fTUV2 y1 y2) = fV (fTUV1 x1' x2') (fTUV2 y1' y2'))
           (PTUV1 : forall {x y z w}, (x = y) -> (z = w) -> fTUV1 x z = fTUV1 y w := ap2 fTUV1)
           (PTUV2 : forall {x y z w}, (x = y) -> (z = w) -> fTUV2 x z = fTUV2 y w := ap2 fTUV2)
           (PTUV : forall {x1 x1' x2 x2' y1 y1' y2 y2'}, 
                   (fT x1 x2 = fT x1' x2') -> (fU y1 y2 = fU y1' y2') 
                   -> fTUV (fT x1 x2) (fU y1 y2) = fTUV (fT x1' x2') (fU y1' y2')  :=
           fun _ _ _ _ _ _ _ _ e e' => ap2 fTUV e e')
           (PV_refl : forall {x1 x2 y1 y2}, PV (eq_refl (fTUV1 x1 x2)) (eq_refl (fTUV2 y1 y2)) = eq_refl _)
           (interchangeLaw : ∀ (F1 : |piω T1|) (F2 : |piω T2|)
               (G1 : |piω U1|) (G2 : |piω U2|)
               (X1 := fTUV1 F1 G1) (X2 := fTUV2 F2 G2),
               fV X1 X2 = fTUV (fT F1 F2) (fU G1 G2)) 
  (hComp := higher_composable_gen interchangeLaw F1 F1' F2 F2' G1 G1' G2 G2') 
  (f1 : |piω T1 [F1,F1']|) (f2 : |piω T2 [F2,F2']|)
  (g1 : |piω U1 [G1,G1']|) (g2 : |piω U2 [G2,G2']|)
  (X1 := PTUV1 _ _ _ _ f1 g1) (X2 := PTUV2 _ _ _ _ f2 g2) 
  (X1' := PT _ _ _ _ f1 f2) (X2' := PU _ _ _ _ g1 g2): 
  hComp (PV X1 X2) = PTUV _ _ _ _ _ _ _ _ X1' X2'.
  unfold hComp, higher_composable_gen.
  destruct f1, f2, g1, g2. simpl in *. 
  unfold X1, X2, X1', X2'. 
  rewrite PV_refl. unfold ap2, equal_f; simpl. 
  rewrite inverse_inv_L. reflexivity.
Defined.

Definition piCompGen2 (T U V: ωPreCat) (f : |T| -> |U| -> |V|)  
           {x y : |T| } {z w : |U| }
           (P : (|T[x,y]|) -> (|U[z,w]|) -> |V[f x z , f y w]|)
           (v1:|V|) (v2:|V|)
           (law1 : |V [v1, f x z]|)  (law2 : |V [f y w , v2]|)
           (e e' : |T[x,y]|) (h h' : |U[z, w]|) 
           (compV : (T[x,y][e,e'] ** U[z,w][h , h']) ==> V[_,_][P e h, P e' h']) : 
  (T [x, y][e, e'] ** U [z, w][h, h']) ==>
   V [v1, v2][(law2 ° P e h) ° law1, (law2 ° P e' h') ° law1]
:= append_left law1 (law2 ° P e h) (law2 ° P e' h') 
   °° (append_right (P e h) (P e' h') law2
     °° compV). 

Definition higher_composable_gen2
           {T1 T2 T U1 U2 U V1 V2 V : Type}
           {fT : T1 -> T2 -> T}
           {fU : U1 -> U2 -> U}
           {fV : V1 -> V2 -> V}
           {fTUV1 : T1 -> U1 -> V1}
           {fTUV2 : T2 -> U2 -> V2}
           {fTUV : T -> U -> V}
           (PT : forall {x y z w}, (x = y) -> (z = w) -> fT x z = fT y w := ap2 fT)
           (PU : forall {x y z w}, (x = y) -> (z = w) -> fU x z = fU y w := ap2 fU) 
           (PV : forall {x1 x1' x2 x2' y1 y1' y2 y2'}, 
                   (fTUV1 x1 x2 = fTUV1 x1' x2') -> (fTUV2 y1 y2 = fTUV2 y1' y2') 
                   -> fV (fTUV1 x1 x2) (fTUV2 y1 y2) = fV (fTUV1 x1' x2') (fTUV2 y1' y2'))
           (PTUV1 : forall {x y z w}, (x = y) -> (z = w) -> fTUV1 x z = fTUV1 y w := ap2 fTUV1)
           (PTUV2 : forall {x y z w}, (x = y) -> (z = w) -> fTUV2 x z = fTUV2 y w := ap2 fTUV2)
           (PTUV : forall {x1 x1' x2 x2' y1 y1' y2 y2'}, 
                   (fT x1 x2 = fT x1' x2') -> (fU y1 y2 = fU y1' y2') 
                   -> fTUV (fT x1 x2) (fU y1 y2) = fTUV (fT x1' x2') (fU y1' y2')  :=
           fun _ _ _ _ _ _ _ _ e e' => ap2 fTUV e e')
           (PV_refl : forall {x1 x2 y1 y2}, PV (eq_refl (fTUV1 x1 x2)) (eq_refl (fTUV2 y1 y2)) = eq_refl _)
           (interchangeLaw : ∀ (F1 : |piω T1|) (F2 : |piω T2|)
               (G1 : |piω U1|) (G2 : |piω U2|)
               (X1 := fTUV1 F1 G1) (X2 := fTUV2 F2 G2),
               fV X1 X2 = fTUV (fT F1 F2) (fU G1 G2)) 
           (F1 F1': |piω T1|) (F2 F2': |piω T2|)
           (G1 G1': |piω U1|) (G2 G2': |piω U2|)
           (hComp := higher_composable_gen interchangeLaw F1 F1' F2 F2' G1 G1' G2 G2')
           (f1 f1': |piω T1 [F1,F1']|) (f2 f2': |piω T2 [F2,F2']|)
           (g1 g1': |piω U1 [G1,G1']|) (g2 g2': |piω U2 [G2,G2']|)
           (compV : (piω (PTUV1 _ _ _ _ f1 g1 = PTUV1 _ _ _ _ f1' g1') ** piω (PTUV2 _ _ _ _ f2 g2 = PTUV2 _ _ _ _ f2' g2')) ==> piω (PV (PTUV1 _ _ _ _ f1 g1) (PTUV2 _ _ _ _ f2 g2) = PV (PTUV1 _ _ _ _ f1' g1') (PTUV2 _ _ _ _ f2' g2'))) 
           (iLaw := pi_interchangeV_gen_law F1 F1' F2 F2' G1 G1' G2 G2'
                                          fT fU fV fTUV1 fTUV2 fTUV
                                          (@PV) (@PV_refl)
                                          interchangeLaw: ∀ f1 f2 g1 g2,
 |piω (fTUV (fT F1 F2) (fU G1 G2) = fTUV (fT F1' F2') (fU G1' G2')) [hComp
    (PV (PTUV1 _ _ _ _ f1 g1) (PTUV2 _ _ _ _ f2 g2)),
  PTUV _ _ _ _ _ _ _ _ (PT _ _ _ _ f1 f2) (PU _ _ _ _ g1 g2)]|)
  (compV2 := piCompGen2 (piω V1) (piω V2) (piω V) fV (@PV F1 F1' G1 G1' F2 F2' G2 G2') _ _ (inverse (interchangeLaw F1 F2 G1 G2)) (interchangeLaw F1' F2' G1' G2')
                              (PTUV1 _ _ _ _ f1 g1) (PTUV1 _ _ _ _ f1' g1') (PTUV2 _ _ _ _ f2 g2) (PTUV2 _ _ _ _ f2' g2') compV)
           (X1 := PT _ _ _ _ f1 f2) (X2 := PU _ _ _ _ g1 g2)
           (X1' := PT _ _ _ _ f1' f2') (X2' := PU _ _ _ _ g1' g2')
: Composable (pi (PTUV1 _ _ _ _ f1 g1 = PTUV1 _ _ _ _ f1' g1'))
             (pi (PTUV2 _ _ _ _ f2 g2 = PTUV2 _ _ _ _ f2' g2'))
             (pi (PTUV _ _ _ _ _ _ _ _ X1 X2 = PTUV _ _ _ _ _ _ _ _ X1' X2'))
:= {| compo := transport_GHomL (inversE (iLaw f1 f2 g1 g2))
               °° (transport_GHomR (iLaw f1' f2' g1' g2') °° compV2) |}.




CoInductive Id_ind : ∀ (A B C A' B' C' C'': Type) (f : A -> B -> C) (f' : A' -> B' -> C')
                       (g : C -> C' -> C'')
                       (p : forall x1 x1' x2 x2' y1 y1' y2 y2',
                              (piω (f x1 x2 = f x1' x2') **
                               piω (f' y1 y2 = f' y1' y2'))
                              ==> piω (g (f x1 x2) (f' y1 y2) = g (f x1' x2') (f' y1' y2'))), Type :=
  mkId_ind :  ∀ (A B C A' B' C' C'': Type) (f : A -> B -> C) (f' : A' -> B' -> C')
                       (g : C -> C' -> C'')
                       (p : forall x1 x1' x2 x2' y1 y1' y2 y2',
                              (piω (f x1 x2 = f x1' x2') **
                               piω (f' y1 y2 = f' y1' y2'))
                              ==> piω (g (f x1 x2) (f' y1 y2) = g (f x1' x2') (f' y1' y2'))),
    (∀ x1 x2 y1 y2 , p x1 x1 x2 x2 y1 y1 y2 y2 @@ (eq_refl,eq_refl) = eq_refl) ->
    (∀ x1 x1' x2 x2' y1 y1' y2 y2',
       Id_ind _ _ (fun x y => p x1 x1' x2 x2' y1 y1' y2 y2' @@ (x,y)) (fun (f1 f1':x1=x1') (f2 f2': x2=x2') (g1 g1' : y1 =y1') (g2 g2' : y2 = y2') => (p  x1 x1' x2 x2' y1 y1' y2 y2') << (ap2 f f1 f2,ap2 f' g1 g2) , (ap2 f f1' f2',ap2 f' g1' g2')>>))
    -> Id_ind f f' g  p.

Definition Id_ind_refl (A B C A' B' C' C'': Type) (f : A -> B -> C) (f' : A' -> B' -> C')
                       (g : C -> C' -> C'')
                       (p : forall x1 x1' x2 x2' y1 y1' y2 y2',
                              (piω (f x1 x2 = f x1' x2') **
                               piω (f' y1 y2 = f' y1' y2'))
                              ==> piω (g (f x1 x2) (f' y1 y2) = g (f x1' x2') (f' y1' y2')))
                                              (e:Id_ind f f' g p) :
  ∀ x1 x2 y1 y2 , p x1 x1 x2 x2 y1 y1 y2 y2 @@ (eq_refl,eq_refl) = eq_refl.
  destruct e. exact e.
Defined.

Definition Id_ind_hom (A B C A' B' C' C'': Type) (f : A -> B -> C) (f' : A' -> B' -> C')
                       (g : C -> C' -> C'')
                       (p : forall x1 x1' x2 x2' y1 y1' y2 y2',
                              (piω (f x1 x2 = f x1' x2') **
                               piω (f' y1 y2 = f' y1' y2'))
                              ==> piω (g (f x1 x2) (f' y1 y2) = g (f x1' x2') (f' y1' y2'))) (e:Id_ind f f' g p) :
∀ x1 x1' x2 x2' y1 y1' y2 y2',
       Id_ind _ _ (fun x y => p x1 x1' x2 x2' y1 y1' y2 y2' @@ (x,y)) (fun (f1 f1':x1=x1') (f2 f2': x2=x2') (g1 g1' : y1 =y1') (g2 g2' : y2 = y2') => (p  x1 x1' x2 x2' y1 y1' y2 y2') << (ap2 f f1 f2,ap2 f' g1 g2) , (ap2 f f1' f2',ap2 f' g1' g2')>>).
  destruct e. exact i.
Defined.


CoFixpoint append_right_id_ind (A B C A' B' C' C'' D E: Type)
           (f : A -> B -> C) 
           (f' : A' -> B' -> C')
           (g : (piω C ** piω C') ==> piω C'') 
           (h : |piω D|)
           (k : C'' -> D -> E)
           (a1 a2 : A) (b1 b2 : B) 
           (a1' a2' : A') (b1' b2' : B') 
           (H : Id_ind (ap2 f (h':=b2)) (ap2 f' (h':=b2'))
        (λ (x : f a1 b1 = f a2 b2) (y : f' a1' b1' = f' a2' b2'),
         (g << (f a1 b1, f' a1' b1'), (f a2 b2, f' a2' b2') >>) @@ (x, y))
        (λ (f1 f1' : a1 = a2) (f2 f2' : b1 = b2) (g1 g1' : a1' = a2')
         (g2 g2' : b1' = b2'),
         (g << (f a1 b1, f' a1' b1'), (f a2 b2, f' a2' b2') >>) <<
         (ap2 f f1 f2, ap2 f' g1 g2), (ap2 f f1' f2', ap2 f' g1' g2') >>)) 
           (compoK := piComp_V k)
 : Id_ind (@ap2 _ _ _ f a1 a2 b1 b2) (@ap2 _ _ _ f' a1' a2' b1' b2') 
          (fun c c' => (identity h) ° 
                       (g << (f a1 b1,f' a1' b1'),(f a2 b2, f' a2' b2')>> @@ (c,c')))
         (fun (x1 x1' : |piω (a1 = a2)|) (x2 x2' : |piω (b1 = b2)|) 
            (y1 y1' : |piω (a1' = a2')|) (y2 y2' : |piω (b1' = b2')|) =>
               (@append_right 
                  (piω (g @@ (f a1 b1, f' a1' b1') = g @@ (f a2 b2, f' a2' b2')))
                  (piω (h= h))
                  (piω (_ = _))
                  ((g << (f a1 b1, f' a1' b1'), (f a2 b2, f' a2' b2') >>) 
                     @@ (ap2 f x1 x2, ap2 f' y1 y2))
                  ((g << (f a1 b1, f' a1' b1'), (f a2 b2, f' a2' b2') >>) 
                     @@ (ap2 f x1' x2', ap2 f' y1' y2'))
                    (identity h) _)
         °° ((g <<(f a1 b1, f' a1' b1'),(f a2 b2,f' a2' b2')>>) 
               <<(ap2 f x1 x2,ap2 f' y1 y2),(ap2 f x1' x2',ap2 f' y1' y2')>>)).
apply mkId_ind. 
- intros. pose (Id_ind_refl H x1 x2 y1 y2). 
  simpl in *. rewrite e. reflexivity.
- intros. simpl. 
  exact (@append_right_id_ind 
          (a1 = a2) (b1 = b2) (f a1 b1 = f a2 b2)
          (a1' = a2') (b1' = b2') (f' a1' b1' = f' a2' b2')
          (g @@ (f a1 b1, f' a1' b1')  = g @@ (f a2 b2, f' a2' b2'))
          (h = h) (k (g @@ (f a1 b1, f' a1' b1')) h = 
                    k (g @@ (f a2 b2, f' a2' b2')) h)
          (ap2 f (h':=b2)) (ap2 f' (h':=b2')) 
          (g <<(f a1 b1, f' a1' b1'),(f a2 b2,f' a2' b2')>>) 
          (identity h) (@ap2 _ _ _ k _ _ _ _)
          x1 x1' x2 x2' y1 y1' y2 y2'
          (Id_ind_hom H x1 x1' x2 x2' y1 y1' y2 y2')).
Defined.



CoFixpoint append_left_id_ind (A B C A' B' C' C'' D E: Type)
           (f : A -> B -> C) 
           (f' : A' -> B' -> C')
           (g : (piω C ** piω C') ==> piω C'') 
           (h : |piω D|)
           (k : D -> C'' -> E)
           (a1 a2 : A) (b1 b2 : B) 
           (a1' a2' : A') (b1' b2' : B') 
           (H : Id_ind (ap2 f (h':=b2)) (ap2 f' (h':=b2'))
        (λ (x : f a1 b1 = f a2 b2) (y : f' a1' b1' = f' a2' b2'),
         (g << (f a1 b1, f' a1' b1'), (f a2 b2, f' a2' b2') >>) @@ (x, y))
        (λ (f1 f1' : a1 = a2) (f2 f2' : b1 = b2) (g1 g1' : a1' = a2')
         (g2 g2' : b1' = b2'),
         (g << (f a1 b1, f' a1' b1'), (f a2 b2, f' a2' b2') >>) <<
         (ap2 f f1 f2, ap2 f' g1 g2), (ap2 f f1' f2', ap2 f' g1' g2') >>)) 
           (compoK := piComp_V k)
 : Id_ind (@ap2 _ _ _ f a1 a2 b1 b2) (@ap2 _ _ _ f' a1' a2' b1' b2') 
          (fun c c' => (g << (f a1 b1,f' a1' b1'),(f a2 b2, f' a2' b2')>> @@ (c,c')) 
                         ° (identity h))
         (fun (x1 x1' : |piω (a1 = a2)|) (x2 x2' : |piω (b1 = b2)|) 
            (y1 y1' : |piω (a1' = a2')|) (y2 y2' : |piω (b1' = b2')|) =>
               (@append_left
                  (piω (h= h))
                  (piω (g @@ (f a1 b1, f' a1' b1') = g @@ (f a2 b2, f' a2' b2')))
                  (piω (_ = _))
                  (identity h)
                  ((g << (f a1 b1, f' a1' b1'), (f a2 b2, f' a2' b2') >>) 
                     @@ (ap2 f x1 x2, ap2 f' y1 y2))
                  ((g << (f a1 b1, f' a1' b1'), (f a2 b2, f' a2' b2') >>) 
                     @@ (ap2 f x1' x2', ap2 f' y1' y2'))
                     _)
         °° ((g <<(f a1 b1, f' a1' b1'),(f a2 b2,f' a2' b2')>>) 
               <<(ap2 f x1 x2,ap2 f' y1 y2),(ap2 f x1' x2',ap2 f' y1' y2')>>)).
apply mkId_ind. 
- intros. pose (Id_ind_refl H x1 x2 y1 y2). 
  simpl in *. rewrite e. reflexivity.
- intros. simpl. 
  exact (@append_left_id_ind 
          (a1 = a2) (b1 = b2) (f a1 b1 = f a2 b2)
          (a1' = a2') (b1' = b2') (f' a1' b1' = f' a2' b2')
          (g @@ (f a1 b1, f' a1' b1')  = g @@ (f a2 b2, f' a2' b2'))
          (h = h) (k h (g @@ (f a1 b1, f' a1' b1')) = 
                    k h (g @@ (f a2 b2, f' a2' b2')))
          (ap2 f (h':=b2)) (ap2 f' (h':=b2')) 
          (g <<(f a1 b1, f' a1' b1'),(f a2 b2,f' a2' b2')>>) 
          (identity h) (@ap2 _ _ _ k _ _ _ _)
          x1 x1' x2 x2' y1 y1' y2 y2'
          (Id_ind_hom H x1 x1' x2 x2' y1 y1' y2 y2')).
Defined.

CoFixpoint pi_interchangeV_gen_Id_ind (T1 T2 U1 U2 V1 V2 V : Type)
           (F1 F1': |piω T1|) (F2 F2': |piω T2|)
           (G1 G1': |piω U1|) (G2 G2': |piω U2|)
           (f1 f1': |piω T1 [F1,F1']|) (f2 f2': |piω T2 [F2,F2']|)
           (g1 g1': |piω U1 [G1,G1']|) (g2 g2': |piω U2 [G2,G2']|)       
           {fV : V1 -> V2 -> V}
           {fTUV1 : T1 -> U1 -> V1}
           {fTUV2 : T2 -> U2 -> V2}
           (PV : forall x1 x1' x2 x2' y1 y1' y2 y2', 
                   (piω (fTUV1 x1 x2 = fTUV1 x1' x2') **
                    piω (fTUV2 y1 y2 = fTUV2 y1' y2') ) ==>
                   (piω (fV (fTUV1 x1 x2) (fTUV2 y1 y2) = 
                                         fV (fTUV1 x1' x2') (fTUV2 y1' y2'))))
           (PTUV1 : forall {x y z w}, (x = y) -> (z = w) -> fTUV1 x z = fTUV1 y w := ap2 fTUV1)
           (PTUV2 : forall {x y z w}, (x = y) -> (z = w) -> fTUV2 x z = fTUV2 y w := ap2 fTUV2)
           (PV_hom := fun f1 f1' g1 g1' f2 f2' g2 g2' => (PV F1 F1' G1 G1' F2 F2'  G2 G2' << (PTUV1 _ _ _ _ f1 g1, PTUV2 _ _ _ _ f2 g2) , (PTUV1 _ _ _ _ f1' g1', PTUV2 _ _ _ _ f2' g2') >>))
           (PV_refl : Id_ind  (ap2 (PTUV1 F1 F1' G1 G1') (h':=g1'))
                              (ap2 (PTUV2 F2 F2' G2 G2') (h':=g2'))
                              (fun x y => PV_hom f1 f1' g1 g1' f2 f2' g2 g2' @@ (x,y))
                              (fun x1 x1' y1 y1' x2 x2'  y2 y2' => 
                                 PV_hom f1 f1' g1 g1' f2 f2' g2 g2' <<
              (ap2 (PTUV1 F1 F1' G1 G1') x1 y1,
               ap2 (PTUV2 F2 F2' G2 G2') x2 y2),
              (ap2 (PTUV1 F1 F1' G1 G1') x1' y1',
               ap2 (PTUV2 F2 F2' G2 G2') x2' y2') >>))
           v v'
           (Y  : v = fV (fTUV1 F1 G1) (fTUV2 F2 G2))
           (Y' : fV (fTUV1 F1' G1') (fTUV2 F2' G2') = v')
           (apPV :=fun f1 f1' g1 g1' f2 f2' g2 g2' =>  
                     piCompGen2 (piω V1) (piω V2) (piω V) fV 
                                      (fun x y => @PV F1 F1' G1 G1' F2 F2' G2 G2' @@ (x,y)) v v' 
                                      Y Y'
                     (@PTUV1 _ _ _ _ f1 g1) (@PTUV1 _ _ _ _ f1' g1') (@PTUV2 _ _ _ _ f2 g2) 
                     (@PTUV2 _ _ _ _ f2' g2') 
                     (PV_hom f1 f1' g1 g1' f2 f2' g2 g2')) : 
  Id_ind (ap2 (PTUV1 F1 F1' G1 G1') (h':=g1'))
         (ap2 (PTUV2 F2 F2' G2 G2') (h':=g2'))
         (λ X Y, apPV f1 f1' g1 g1' f2 f2' g2 g2' @@ (X,Y))
         (fun x1 x1' y1 y1' x2 x2' y2 y2' => apPV f1 f1' g1 g1' f2 f2' g2 g2' <<
              (ap2 (PTUV1 F1 F1' G1 G1') x1 y1,
               ap2 (PTUV2 F2 F2' G2 G2') x2 y2),
              (ap2 (PTUV1 F1 F1' G1 G1') x1' y1',
               ap2 (PTUV2 F2 F2' G2 G2') x2' y2') >>).

pose (@transport_GHomR (piω V) _ (fV (fTUV1 F1' G1') (fTUV2 F2' G2')) v' Y' °° 
                      (PV F1 F1' G1 G1' F2 F2' G2 G2')).

apply  (@append_left_id_ind
          (F1 = F1') (G1 = G1') (fTUV1 F1 G1 = fTUV1 F1' G1')
          (F2 = F2') (G2 = G2') (fTUV2 F2 G2 = fTUV2 F2' G2')
          (fV (fTUV1 F1 G1) (fTUV2 F2 G2) = v')
          (v = fV (fTUV1 F1 G1) (fTUV2 F2 G2))
          (v = v')
          (PTUV1 F1 F1' G1 G1') (PTUV2 F2 F2' G2 G2')
          g Y concat
          f1 f1' g1 g1' f2 f2' g2 g2'). 
exact (@append_right_id_ind
          (F1 = F1') (G1 = G1') (fTUV1 F1 G1 = fTUV1 F1' G1')
          (F2 = F2') (G2 = G2') (fTUV2 F2 G2 = fTUV2 F2' G2')
          (fV (fTUV1 F1 G1) (fTUV2 F2 G2) = fV (fTUV1 F1' G1') (fTUV2 F2' G2'))
          (fV (fTUV1 F1' G1') (fTUV2 F2' G2') = v')
          (fV (fTUV1 F1 G1) (fTUV2 F2 G2) = v')
          (PTUV1 F1 F1' G1 G1') (PTUV2 F2 F2' G2 G2')
          (PV F1 F1' G1 G1' F2 F2' G2 G2') Y' concat
          f1 f1' g1 g1' f2 f2' g2 g2' PV_refl).

Defined.

Definition pi_interchangeV_gen_Id_ind_simple (T1 T2 T U1 U2 U V1 V2 V : Type)
           (F1 F1': |piω T1|) (F2 F2': |piω T2|)
           (G1 G1': |piω U1|) (G2 G2': |piω U2|)
           {fT : T1 -> T2 -> T}
           {fU : U1 -> U2 -> U}
           {fV : V1 -> V2 -> V}
           {fTUV1 : T1 -> U1 -> V1}
           {fTUV2 : T2 -> U2 -> V2}
           {fTUV : T -> U -> V}
           (PT : forall {x y z w}, (x = y) -> (z = w) -> fT x z = fT y w := ap2 fT)
           (PU : forall {x y z w}, (x = y) -> (z = w) -> fU x z = fU y w := ap2 fU)
           (PV : forall x1 x1' x2 x2' y1 y1' y2 y2', 
                   (piω (fTUV1 x1 x2 = fTUV1 x1' x2') **
                    piω (fTUV2 y1 y2 = fTUV2 y1' y2') ) ==>
                   (piω (fV (fTUV1 x1 x2) (fTUV2 y1 y2) = 
                                         fV (fTUV1 x1' x2') (fTUV2 y1' y2'))))
           (PTUV1 : forall {x y z w}, (x = y) -> (z = w) -> fTUV1 x z = fTUV1 y w := ap2 fTUV1)
           (PTUV2 : forall {x y z w}, (x = y) -> (z = w) -> fTUV2 x z = fTUV2 y w := ap2 fTUV2)
           (PTUV : forall {x1 x1' x2 x2' y1 y1' y2 y2'}, 
                   (fT x1 x2 = fT x1' x2') -> (fU y1 y2 = fU y1' y2') 
                   -> fTUV (fT x1 x2) (fU y1 y2) = fTUV (fT x1' x2') (fU y1' y2')  :=
           fun _ _ _ _ _ _ _ _ e e' => ap2 fTUV e e')
           (PV_refl : Id_ind fTUV1 fTUV2 fV PV)
           (interchangeLaw : ∀ (F1 : |piω T1|) (F2 : |piω T2|)
               (G1 : |piω U1|) (G2 : |piω U2|)
               (X1 := fTUV1 F1 G1) (X2 := fTUV2 F2 G2),
               fV X1 X2 = fTUV (fT F1 F2) (fU G1 G2))
 (hComp := higher_composable_gen interchangeLaw F1 F1' F2 F2' G1 G1' G2 G2') 
 (apPV := fun f1 f1' g1 g1' f2 f2' g2 g2' =>
                     piCompGen2 (piω V1) (piω V2) (piω V) fV 
                                      (fun x y => @PV F1 F1' G1 G1' F2 F2' G2 G2' @@ (x,y)) _ _ 
                     (inverse (interchangeLaw F1 F2 G1 G2)) (interchangeLaw F1' F2' G1' G2')
                     (@PTUV1 _ _ _ _ f1 g1) (@PTUV1 _ _ _ _ f1' g1') (@PTUV2 _ _ _ _ f2 g2) 
                     (@PTUV2 _ _ _ _ f2' g2') 
                     (PV F1 F1' G1 G1' F2 F2'  G2 G2' << (PTUV1 _ _ _ _ f1 g1, PTUV2 _ _ _ _ f2 g2) , (PTUV1 _ _ _ _ f1' g1', PTUV2 _ _ _ _ f2' g2') >>)) 
  (iLaw := pi_interchangeV_gen_law F1 F1' F2 F2' G1 G1' G2 G2'
                                   fT fU fV fTUV1 fTUV2 fTUV
                                   (fun x1 x1' x2 x2' y1 y1' y2 y2' x y => @PV x1 x1' x2 x2' y1 y1' y2 y2'  @@ (x,y)) (Id_ind_refl PV_refl) interchangeLaw)
:
  Id_ind (PTUV1 F1 F1' G1 G1') (PTUV2 F2 F2' G2 G2')
                    (λ (X : fTUV1 F1 G1 = fTUV1 F1' G1')
                     (Y : fTUV2 F2 G2 = fTUV2 F2' G2'),
                     hComp (PV F1 F1' G1 G1' F2 F2' G2 G2' @@ (X, Y))) apPV.
  pose (PV_hom_refl := Id_ind_hom PV_refl F1 F1' G1 G1' F2 F2' G2 G2').
  apply mkId_ind. 
- intros. unfold apPV, piCompGen2, PTUV1, PTUV2. simpl. 
   pose (Id_ind_refl PV_hom_refl x1 x2 y1 y2). simpl in e.
   rewrite e. reflexivity.
 - intros f1 f1' g1 g1' f2 f2' g2 g2'. 
   apply pi_interchangeV_gen_Id_ind.
   exact (Id_ind_hom PV_hom_refl f1 f1' g1 g1' f2 f2' g2 g2' ).
Defined.

CoFixpoint pi_interchangeV_gen : forall (T1 T2 T U1 U2 U V1 V2 V : Type)
           (F1 F1': |piω T1|) (F2 F2': |piω T2|)
           (G1 G1': |piω U1|) (G2 G2': |piω U2|)
           (f1 f1': |piω T1 [F1,F1']|) (f2 f2': |piω T2 [F2,F2']|)
           (g1 g1': |piω U1 [G1,G1']|) (g2 g2': |piω U2 [G2,G2']|)
           {fT : T1 -> T2 -> T}
           {fU : U1 -> U2 -> U}
           {fV : V1 -> V2 -> V}
           {fTUV1 : T1 -> U1 -> V1}
           {fTUV2 : T2 -> U2 -> V2}
           {fTUV : T -> U -> V}
           (PT : forall {x y z w}, (x = y) -> (z = w) -> fT x z = fT y w := ap2 fT)
           (PU : forall {x y z w}, (x = y) -> (z = w) -> fU x z = fU y w := ap2 fU)
           (PV : forall x1 x1' x2 x2' y1 y1' y2 y2', 
                   (piω (fTUV1 x1 x2 = fTUV1 x1' x2') **
                    piω (fTUV2 y1 y2 = fTUV2 y1' y2') ) ==>
                   (piω (fV (fTUV1 x1 x2) (fTUV2 y1 y2) = 
                                         fV (fTUV1 x1' x2') (fTUV2 y1' y2'))))
           (PTUV1 : forall {x y z w}, (x = y) -> (z = w) -> fTUV1 x z = fTUV1 y w := ap2 fTUV1)
           (PTUV2 : forall {x y z w}, (x = y) -> (z = w) -> fTUV2 x z = fTUV2 y w := ap2 fTUV2)
           (PTUV : forall {x1 x1' x2 x2' y1 y1' y2 y2'}, 
                   (fT x1 x2 = fT x1' x2') -> (fU y1 y2 = fU y1' y2') 
                   -> fTUV (fT x1 x2) (fU y1 y2) = fTUV (fT x1' x2') (fU y1' y2')  :=
           fun _ _ _ _ _ _ _ _ e e' => ap2 fTUV e e')
           (PV_refl : Id_ind fTUV1 fTUV2 fV PV)
           (interchangeLaw : ∀ (F1 : |piω T1|) (F2 : |piω T2|)
               (G1 : |piω U1|) (G2 : |piω U2|)
               (X1 := fTUV1 F1 G1) (X2 := fTUV2 F2 G2),
               fV X1 X2 = fTUV (fT F1 F2) (fU G1 G2))
 (compV : forall  (f1 f1': |piω T1 [F1,F1']|) 
           (g1 g1': |piω U1 [G1,G1']|)(f2 f2': |piω T2 [F2,F2']|) (g2 g2': |piω U2 [G2,G2']|), (piω (PTUV1 _ _ _ _ f1 g1 = PTUV1 _ _ _ _ f1' g1') ** piω (PTUV2 _ _ _ _ f2 g2 = PTUV2 _ _ _ _ f2' g2')) ==> piω (PV _ _ _ _ _ _ _ _ @@ (PTUV1 _ _ _ _ f1 g1, PTUV2 _ _ _ _ f2 g2) = PV _ _ _ _ _ _ _ _ @@ (PTUV1 _ _ _ _ f1' g1', PTUV2 _ _ _ _ f2' g2'))
 := fun f1 f1' g1 g1' f2 f2' g2 g2' => PV F1 F1' G1 G1' F2 F2'  G2 G2' << (PTUV1 _ _ _ _ f1 g1, PTUV2 _ _ _ _ f2 g2) , (PTUV1 _ _ _ _ f1' g1', PTUV2 _ _ _ _ f2' g2') >>) 
  (hComp := higher_composable_gen interchangeLaw F1 F1' F2 F2' G1 G1' G2 G2')
  (X1 := PTUV1 _ _ _ _ f1 g1) (X2 := PTUV2 _ _ _ _ f2 g2) 
  (X1' := PTUV1 _ _ _ _ f1' g1') (X2' := PTUV2 _ _ _ _ f2' g2')
  (Y1 := PT _ _ _ _ f1 f2) (Y2 := PU _ _ _ _ g1 g2) 
  (Y1' := PT _ _ _ _ f1' f2') (Y2' := PU _ _ _ _ g1' g2') 
  (iLaw := pi_interchangeV_gen_law F1 F1' F2 F2' G1 G1' G2 G2'
                                          fT fU fV fTUV1 fTUV2 fTUV
                                          (fun x1 x1' x2 x2' y1 y1' y2 y2' x y => @PV x1 x1' x2 x2' y1 y1' y2 y2'  @@ (x,y)) (Id_ind_refl PV_refl) interchangeLaw)

  (hComp' := fun f1 f1' g1 g1' f2 f2' g2 g2' =>
       @higher_composable_gen2 T1 T2 T U1 U2 U V1 V2 V
                                          fT fU fV fTUV1 fTUV2 fTUV
                                         (fun x1 x1' x2 x2' y1 y1' y2 y2' x y => @PV x1 x1' x2 x2' y1 y1' y2 y2'  @@ (x,y)) (Id_ind_refl PV_refl) interchangeLaw  F1 F1' F2 F2' G1 G1' G2 G2' f1 f1' f2 f2' g1 g1' g2 g2' (compV f1 f1' g1 g1' f2 f2' g2 g2')) ,
  @interchangeV
    (((piω T1) [F1, F1']) [f1,f1'])
    (((piω T2) [F2, F2']) [f2,f2'])
    (((piω T ) [fT F1 F2, fT F1' F2']) [PT _ _ _ _ f1 f2, PT _ _ _ _ f1' f2'])
    (((piω U1) [G1, G1']) [g1, g1'])
    (((piω U2) [G2, G2']) [g2, g2'])
    (((piω U ) [fU G1 G2, fU G1' G2']) [PU _ _ _ _ g1 g2, PU _ _ _ _ g1' g2'])
    (((piω V1) [fTUV1 F1 G1, fTUV1 F1' G1']) [PTUV1 _ _ _ _ f1 g1, PTUV1 _ _ _ _ f1' g1'])
    (((piω V2) [fTUV2 F2 G2, fTUV2 F2' G2']) [PTUV2 _ _ _ _ f2 g2, PTUV2 _ _ _ _ f2' g2'])
    (((piω V ) [fTUV (fT F1 F2) (fU G1 G2), fTUV (fT F1' F2') (fU G1' G2')])
                     [PTUV _ _ _ _ _ _ _ _ Y1 Y2,PTUV _ _ _ _ _ _ _ _ Y1' Y2'])
    _ (piComp_V (@PT _ _ _ _)  _ _ _ _) (piComp_V (@PU _ _ _ _) _ _ _ _) 
    (hComp' f1 f1' g1 g1' f2 f2' g2 g2')
    (piComp_V (@PTUV1 _ _ _ _) _ _ _ _) (piComp_V (@PTUV2 _ _ _ _) _ _ _ _)
    (piComp_V (@PTUV _ _ _ _ _ _ _ _) _ _ _ _).
   intros.
   apply mkInterchangeV. 
   pose (apPV := fun f1 f1' g1 g1' f2 f2' g2 g2' =>
                     piCompGen2 (piω V1) (piω V2) (piω V) fV (fun x y => 
  @PV F1 F1' G1 G1' F2 F2' G2 G2' @@ (x,y)) _ _ (inverse (interchangeLaw F1 F2 G1 G2)) (interchangeLaw F1' F2' G1' G2')
                                      (@PTUV1 _ _ _ _ f1 g1) (@PTUV1 _ _ _ _ f1' g1') (@PTUV2 _ _ _ _ f2 g2) (@PTUV2 _ _ _ _ f2' g2') (compV f1 f1' g1 g1' f2 f2' g2 g2')).
   pose (apPV_refl := pi_interchangeV_gen_Id_ind_simple 
                                            F1 F1' F2 F2' G1 G1' G2 G2' PV_refl interchangeLaw).

   exists (pi_interchangeV_gen_law f1 f1' f2 f2' g1 g1' g2 g2' (@PT _ _ _ _) (@PU _ _ _ _)
          (fun X Y => hComp (@PV _ _ _ _ _ _ _ _ @@ (X,Y))) (@PTUV1 _ _ _ _) (@PTUV2 _ _ _ _)
          (@PTUV _ _ _ _ _ _ _ _ )
          (fun x1 x1' x2 x2' y1 y1' y2 y2' x y => apPV x1 x1' x2 x2' y1 y1' y2 y2'  @@ (x,y)) 
          (Id_ind_refl apPV_refl) iLaw). 

  intros ff1 ff1' ff2 ff2' gg1 gg1' gg2 gg2'. 
  exact (pi_interchangeV_gen
          (F1 = F1') (F2 = F2') (fT F1 F2 = fT F1' F2')
          (G1 = G1') (G2 = G2') (fU G1 G2 = fU G1' G2')
           (fTUV1 F1 G1 = fTUV1 F1' G1') (fTUV2 F2 G2 = fTUV2 F2' G2')
           (fTUV (fT F1 F2) (fU G1 G2) = fTUV (fT F1' F2') (fU G1' G2'))
          f1 f1' f2 f2' g1 g1' g2 g2' ff1 ff1' ff2 ff2' gg1 gg1' gg2 gg2'
           (@PT _ _ _ _) (@PU _ _ _ _) (fun X Y => hComp (@PV _ _ _ _ _ _ _ _ @@ (X,Y))) 
           (@PTUV1 _ _ _ _) (@PTUV2 _ _ _ _) (@PTUV _ _ _ _ _ _ _ _ )
          apPV apPV_refl iLaw).
Defined.


CoFixpoint pi_interchangeV_gen_Id_ind_init
           (T1 T2 U1 U2 V1 V2 V : Type)
           {fV : V1 -> V2 -> V}
           {fTUV1 : T1 -> U1 -> V1}
           {fTUV2 : T2 -> U2 -> V2}
           (PTUV1 : forall {x y z w}, (x = y) -> (z = w) -> fTUV1 x z = fTUV1 y w := ap2 fTUV1)
           (PTUV2 : forall {x y z w}, (x = y) -> (z = w) -> fTUV2 x z = fTUV2 y w := ap2 fTUV2)
           (PV : forall x1 x1' x2 x2' y1 y1' y2 y2', 
                   (piω (fTUV1 x1 x2 = fTUV1 x1' x2') **
                    piω (fTUV2 y1 y2 = fTUV2 y1' y2') ) ==>
                   (piω (fV (fTUV1 x1 x2) (fTUV2 y1 y2) = 
                                         fV (fTUV1 x1' x2') (fTUV2 y1' y2')))
            := fun x1 x1' x2 x2' y1 y1' y2 y2' => piComp_V_ fV 
              (fTUV1 x1 x2) (fTUV1 x1' x2') (fTUV2 y1 y2) (fTUV2 y1' y2')) :
      Id_ind fTUV1 fTUV2 fV PV.
apply mkId_ind. intros. reflexivity.
intros F1 F1' G1 G1' F2 F2' G2 G2'.
exact (pi_interchangeV_gen_Id_ind_init (F1 = F1') (F2 = F2') 
          (G1 = G1') (G2 = G2') 
           (fTUV1 F1 G1 = fTUV1 F1' G1') (fTUV2 F2 G2 = fTUV2 F2' G2')
           (fV (fTUV1 F1 G1) (fTUV2 F2 G2) = fV (fTUV1 F1' G1') (fTUV2 F2' G2'))
           (fun a b => @PV F1 F1' G1 G1' F2 F2' G2 G2' @@ (a,b)) (@PTUV1 _ _ _ _) (@PTUV2 _ _ _ _)).
Defined.

Definition pi_interchangeV_gen_simple
       (T1 T2 T U1 U2 U V1 V2 V : Type) (F1 F1' : | piω T1 |)
       (F2 F2' : | piω T2 |) (G1 G1' : | piω U1 |)
       (G2 G2' : | piω U2 |) (f1 f1' : | piω T1 [F1, F1'] |)
       (f2 f2' : | piω T2 [F2, F2'] |)
       (g1 g1' : | piω U1 [G1, G1'] |)
       (g2 g2' : | piω U2 [G2, G2'] |)
       (fT : T1 → T2 → T)
       (fU : U1 → U2 → U)
       (fV : V1 → V2 → V)
       (fTUV1 : T1 → U1 → V1)
       (fTUV2 : T2 → U2 → V2)
       (fTUV : T → U → V)
       (interchangeLaw : ∀ (F3 : | piω T1 |) 
                         (F4 : | piω T2 |) (G3 : | piω U1 |)
                         (G4 : | piω U2 |) (X1:=fTUV1 F3 G3)
                         (X2:=fTUV2 F4 G4),
                         fV X1 X2 = fTUV (fT F3 F4) (fU G3 G4))
       (compV:=
        λ (f3 f1'0 : | piω T1 [F1, F1'] |)
        (g3 g1'0 : | piω U1 [G1, G1'] |)
        (f4 f2'0 : | piω T2 [F2, F2'] |)
        (g4 g2'0 : | piω U2 [G2, G2'] |),
        (λ (x1 x1' : T1) (x2 x2' : U1) 
         (y1 y1' : T2) (y2 y2' : U2),
         piComp_V_ fV (fTUV1 x1 x2) (fTUV1 x1' x2') 
           (fTUV2 y1 y2) (fTUV2 y1' y2')) F1 F1' G1 G1' F2 F2' G2 G2' <<
        (ap2 fTUV1 f3 g3, ap2 fTUV2 f4 g4),
        (ap2 fTUV1 f1'0 g1'0, ap2 fTUV2 f2'0 g2'0) >>)
       (hComp:=
        higher_composable_gen interchangeLaw F1 F1' F2 F2' G1 G1' G2 G2')
       (X1:=ap2 fTUV1 f1 g1) (X2:=ap2 fTUV2 f2 g2) 
       (X1':=ap2 fTUV1 f1' g1') (X2':=ap2 fTUV2 f2' g2') 
       (Y1:=ap2 fT f1 f2) (Y2:=ap2 fU g1 g2) (Y1':=ap2 fT f1' f2')
       (Y2':=ap2 fU g1' g2')
       (iLaw:=
        pi_interchangeV_gen_law  F1 F1' F2 F2'
          G1 G1' G2 G2' fT fU fV fTUV1 fTUV2 fTUV
          (λ (x1 x1' : T1) (x2 x2' : U1) 
           (y1 y1' : T2) (y2 y2' : U2)
           (x : fTUV1 x1 x2 = fTUV1 x1' x2')
           (y : fTUV2 y1 y2 = fTUV2 y1' y2'),
           (λ (x3 x1'0 : T1) (x4 x2'0 : U1) 
            (y3 y1'0 : T2) (y4 y2'0 : U2),
            piComp_V_ fV (fTUV1 x3 x4) (fTUV1 x1'0 x2'0) 
              (fTUV2 y3 y4) (fTUV2 y1'0 y2'0)) x1 x1' x2 x2' y1 y1' y2 y2' @@
           (x, y))
          (Id_ind_refl
             (pi_interchangeV_gen_Id_ind_init))
          interchangeLaw)
           (PV := fun x1 x1' x2 x2' y1 y1' y2 y2' => piComp_V_ fV 
              (fTUV1 x1 x2) (fTUV1 x1' x2') (fTUV2 y1 y2) (fTUV2 y1' y2'))
       (hComp':=
        λ (f3 f1'0 : | piω T1 [F1, F1'] |)
        (g3 g1'0 : | piω U1 [G1, G1'] |)
        (f4 f2'0 : | piω T2 [F2, F2'] |)
        (g4 g2'0 : | piω U2 [G2, G2'] |),
        higher_composable_gen2
          (λ (x1 x1' : T1) (x2 x2' : U1) 
           (y1 y1' : T2) (y2 y2' : U2)
           (x : fTUV1 x1 x2 = fTUV1 x1' x2')
           (y : fTUV2 y1 y2 = fTUV2 y1' y2'),
           (λ (x3 x1'0 : T1) (x4 x2'0 : U1) 
            (y3 y1'0 : T2) (y4 y2'0 : U2),
            piComp_V_ fV (fTUV1 x3 x4) (fTUV1 x1'0 x2'0) 
              (fTUV2 y3 y4) (fTUV2 y1'0 y2'0)) x1 x1' x2 x2' y1 y1' y2 y2' @@
           (x, y))
          (Id_ind_refl
             (pi_interchangeV_gen_Id_ind_init))
          interchangeLaw F1 F1' F2 F2' G1 G1' G2 G2' f3 f1'0 f4 f2'0 g3 g1'0
          g4 g2'0 (compV f3 f1'0 g3 g1'0 f4 f2'0 g4 g2'0)):
       @interchangeV ((piω T1 [F1, F1']) [f1, f1'])
         ((piω T2 [F2, F2']) [f2, f2'])
         ((piω T [fT F1 F2, fT F1' F2']) [ap2 fT f1 f2, ap2 fT f1' f2'])
         ((piω U1 [G1, G1']) [g1, g1'])
         ((piω U2 [G2, G2']) [g2, g2'])
         ((piω U [fU G1 G2, fU G1' G2']) [ap2 fU g1 g2, ap2 fU g1' g2'])
         ((piω V1 [fTUV1 F1 G1, fTUV1 F1' G1']) [
          ap2 fTUV1 f1 g1, ap2 fTUV1 f1' g1'])
         ((piω V2 [fTUV2 F2 G2, fTUV2 F2' G2']) [
          ap2 fTUV2 f2 g2, ap2 fTUV2 f2' g2']) 
         ((piω V [fTUV (fT F1 F2) (fU G1 G2),
           fTUV (fT F1' F2') (fU G1' G2')])
          [(λ (x1 x1' : T1) (x2 x2' : T2) 
            (y1 y1' : U1) (y2 y2' : U2)
            (e : fT x1 x2 = fT x1' x2') (e' : fU y1 y2 = fU y1' y2'),
            ap2 fTUV e e') F1 F1' F2 F2' G1 G1' G2 G2' Y1 Y2,
          (λ (x1 x1' : T1) (x2 x2' : T2) 
           (y1 y1' : U1) (y2 y2' : U2)
           (e : fT x1 x2 = fT x1' x2') (e' : fU y1 y2 = fU y1' y2'),
           ap2 fTUV e e') F1 F1' F2 F2' G1 G1' G2 G2' Y1' Y2']) _
         _ _ (hComp' f1 f1' g1 g1' f2 f2' g2 g2') _ _ _
:=
  pi_interchangeV_gen F1 F1' F2 F2' G1 G1' G2 G2' f1 f1' f2 f2' g1 g1' g2 g2'
                      pi_interchangeV_gen_Id_ind_init interchangeLaw.


Definition pi_interchangeV (T:Type) (x y z : T)  
           (f f' f'' : |piω (x = y)|) (g g' g'' : |piω (y = z)|) :
   @interchangeV ((piω T [x, y]) [f, f']) ((piω T [x, y]) [f', f''])
     ((piω T [x, y]) [f, f'']) ((piω T [y, z]) [g, g'])
     ((piω T [y, z]) [g', g'']) ((piω T [y, z]) [g, g''])
     ((piω T [x, z]) [g ° f, g' ° f'])
     ((piω T [x, z]) [g' ° f', g'' ° f''])
     ((piω T [x, z]) [g ° f, g'' ° f'']) _ _ _ _ _ _ _.
apply mkInterchangeV. exists (fun f1 f2 g1 g2 => pi_interchangeV_law f1 f2 g1 g2).
intros F1 F1' F2 F2' G1 G1' G2 G2'. 
apply mkInterchangeV. simpl.
exists (@pi_interchangeV_gen_law (f = f') (f' = f'') 
           (f = f'') (g = g') (g' = g'') (g = g'') 
           (f @ g = f' @ g') (f' @ g' = f'' @ g'') 
           (f @ g = f'' @ g'') F1 F1' F2 F2' G1 G1' G2 G2' _ _ _ _ _ _
           (λ (f0 f1'0 : f = f') (f3 f2'0 : g = g') 
            (g0 g1'0 : f' = f'') (g3 g2'0 : g' = g''),
            ap2 concat (h':=concat_LR g1'0 g2'0))
           (fun _ _ _ _ => eq_refl _) 
           (λ (a : f = f') (b : f' = f'') (c : g = g') 
            (d : g' = g''), inverse (concat_LR_concat a b c d))).
intros f1 f1' f2 f2' g1 g1' g2 g2'.
exact (pi_interchangeV_gen_simple 
                F1 F1' F2 F2' G1 G1' G2 G2' f1 f1' f2 f2' g1 g1' g2 g2'
                concat concat concat (@concat_LR (T) x y z f f' g g')
                (@concat_LR T x y z f' f'' g' g'')
                (@concat_LR T x y z f f'' g g'') 
               (fun a b c d => inverse (@concat_LR_concat _ _ _ _ f f' f'' g g' g'' a b c d))).
Defined.


CoFixpoint pi_interchangeH_gen (T U V : Type) (ff : T -> U -> V)  
           {f f' : T} {g g' : U}
           (P : forall x y z w, |piω T [x,y]| -> |piω U [z,w]| -> 
                                |piω V [ff x z,ff y w]| := ap2 ff) 
           (F F': |piω T [f,f']|) (G G': |piω U [g,g']|) :
  @interchangeH ((piω T [f, f']) [F, F']) ((piω U [g, g']) [G, G'])
               (((piω V) [ff f g, ff f' g']) [P _ _ _ _ F G, P _ _ _ _  F' G']) _ _.

apply mkInterchangeH. 
- intros X X' X'' Y Y' Y''. simpl in *. 
  apply mkInterchangeV. exists (fun f1 f2 g1 g2 => ap2_map_concat _ _ _ _ _).
  intros F1 F1' F2 F2' G1 G1' G2 G2'. simpl. 
  apply mkInterchangeV. simpl. 
  exists (pi_interchangeV_gen_law  F1 F1' F2 F2' G1 G1' G2 G2' 
                concat concat concat 
                (@ap2_map _ _ _ _ _ _ _ _ _ _ _ _)
                (@ap2_map _ _ _ _ _ _ _ _ _ _ _ _)
                (@ap2_map _ _ _ _ _ _ _ _ _ _ _ _)
                (fun f1 f1' f2 f2' g1 g1' g2 g2' => 
                             @ap2 _ _ _ _ _ _ _ _) (fun _ _ _ _ => eq_refl _)
                (@ap2_map_concat _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
  intros f1 f1' f2 f2' g1 g1' g2 g2'. 
  exact (pi_interchangeV_gen_simple F1 F1' F2 F2' G1 G1' G2 G2' f1 f1' f2 f2' g1 g1' g2 g2'
                concat concat concat 
                (@ap2_map _ _ _ _ _ _ _ _ _ _ _ _)
                (@ap2_map _ _ _ _ _ _ _ _ _ _ _ _)
                (@ap2_map _ _ _ _ _ _ _ _ _ _ _ _)
                (@ap2_map_concat _ _ _ _ _ _ _ _ _ _ _ _ _ _)).
- intros. apply pi_interchangeH_gen.
Defined.

Definition pi_interchangeH (T:Type) (x y z : T) : 
  @interchangeH (piω T [x,y]) (piω T [y,z]) (piω T [x,z]) _ _. 
apply mkInterchangeH. 
- intros f f' f'' g g' g''. exact (pi_interchangeV x y z f f' f'' g g' g'').
- intros f f' g g'. apply mkInterchangeH. 
  intros X X' X'' Y Y' Y''. apply mkInterchangeV. simpl. 
  exists (fun f1 f2 g1 g2 => inverse (ap2_concat _ _ _ _ _)). 
  intros F1 F1' F2 F2' G1 G1' G2 G2'. 
  apply mkInterchangeV. 
  exists (pi_interchangeV_gen_law 
                F1 F1' F2 F2' G1 G1' G2 G2' 
                concat concat concat 
                (@concat_LR_map _ _ _ _ _ _ _ _ _ _ _ _)
                (@concat_LR_map _ _ _ _ _ _ _ _ _ _ _ _)
                (@concat_LR_map _ _ _ _ _ _ _ _ _ _ _ _)
                (fun f1 f1' f2 f2' g1 g1' g2 g2' => 
                             @ap2 _ _ _ _ _ _ _ _) (fun _ _ _ _ => eq_refl _)
       (fun _ _ _ _ => inverse (ap2_concat _ _ _ _ _))).
  intros f1 f1' f2 f2' g1 g1' g2 g2'. 
  exact (pi_interchangeV_gen_simple F1 F1' F2 F2' G1 G1' G2 G2' f1 f1' f2 f2' g1 g1' g2 g2'
                concat concat concat 
                (@concat_LR_map _ _ _ _ _ _ _ _ _ _ _ _)
                (@concat_LR_map _ _ _ _ _ _ _ _ _ _ _ _)
                (@concat_LR_map _ _ _ _ _ _ _ _ _ _ _ _)
       (fun _ _ _ _ => inverse (ap2_concat _ _ _ _ _))).
  intros F F' G G'. simpl in *. 
  exact (pi_interchangeH_gen concat F F' G G').
Defined.

CoFixpoint pi_interchange (T:Type) : @interchange (piω T) _ :=
  mkInterchange (fun (x y z : |piω T|) => pi_interchangeH x y z) 
                (fun x y => pi_interchange (x = y)).

Definition pi_compo_ωFunctor (T:Type) : @compo_ωFunctor (piω T) _ :=
  interchange_idcompo_compo_ωFunctor (pi_interchange T) (pi_idCompo T).


(*** associativity law ***)

Definition higher_composable_assoc {G1 G2 G3 G12 G23 G : ωPreCat}
           {_transport : transport_eq G}
           {comp12 : Composable G1.1 G2.1 G12.1}
           {comp23 : Composable G2.1 G3.1 G23.1}
           {comp12_3 : Composable G12.1 G3.1 G.1}
           {comp1_23 : Composable G1.1 G23.1 G.1}
     (associate : ∀ (f : |G1|) (g : |G2|) (h : |G3|),
                   (h ° g) ° f = h ° (g ° f)) 
     (f f' : |G1|) (g g' : |G2|) (h h' : |G3|)  :
  Composable (G1[f,f']).1 (G23[h ° g, h' ° g']).1
        (G[h ° (g ° f), h' ° (g' ° f')]).1 :=
{| compo := transport_GHomL_eq_here (inverse (associate f g h))
            °° (transport_GHomR_eq_here (associate f' g' h')
               °° (compo << (f,h °g),(f',h'°g')>>)) |}.


CoInductive associativityH (G1 G2 G3 G12 G23 G : ωPreCat)
            (_transport : transport_eq G)
            {comp12 : Composable G1.1 G2.1 G12.1}
            {comp23 : Composable G2.1 G3.1 G23.1}
            {comp12_3 : Composable G12.1 G3.1 G.1}
            {comp1_23 : Composable G1.1 G23.1 G.1} : Type :=
  mkAssociativityH :
  {
    (* The associativity law *)
    associate : ∀ (f : |G1|) (g : |G2|) (h : |G3|),
                  (h ° g) ° f = h ° (g ° f) &
    (* The inductive step *)
    ∀ (f f' : |G1|) (g g' : |G2|) (h h' : |G3|),
    @associativityH (G1[f,f']) (G2[g,g']) (G3[h,h'])
                    (G12[g ° f, g' ° f']) (G23[h ° g, h' ° g'])
                    (G[h ° (g ° f), h' ° (g' ° f')])
                    _ _ _ _  
                    (higher_composable_assoc associate f f' g g' h h')
  } ->
  @associativityH G1 G2 G3 G12 G23 G _ comp12 comp23 comp12_3 comp1_23.


CoInductive associativity' (G : ωPreCat) (_transport : transport_eq G) : Type := 
mkAssociativity' :
        (∀ (x y z t : |G|), 
           @associativityH (G [x,y]) (G [y,z]) (G [z,t]) (G[x,z]) (G[y,t]) (G[x,t])
                           _ _ _ _ _) ->
        (* the co-induction step *)
        (∀ (x y :   |G|), @associativity' (G [x,y]) _) ->
        @associativity' G _.


CoFixpoint assocH_assoc (G1 G2 G3 G12 G23 G : ωPreCat)
            (_transport : transport_eq G)
            {comp12 : Composable G1.1 G2.1 G12.1}
            {comp23 : Composable G2.1 G3.1 G23.1}
            {comp12_3 : Composable G12.1 G3.1 G.1}
            {comp1_23 : Composable G1.1 G23.1 G.1} :
  @associativityH G1 G2 G3 G12 G23 G _ _ _ _ _ ->
  @commutativeSquare (G1 ** (G2 ** G3))
                     (G12 ** G3) (G1 ** G23) G _ 
                     (prod_hom1 G3.1 _)
                     (prod_hom' (GId G1.1) (@compo _ _ _ _))
                     (@compo _ _ _ _) (@compo _ _ _ _).
intro H. refine (mkCommutativeSquare _ _ _ _ _ _).
- intros. destruct H as [[a H]]. destruct x as [x [y z]]. apply a.
- intros. destruct H as [[a H]]. destruct x as [f [g h]], y as [f' [g' h']]. 
  apply (assocH_assoc _ _ _ _ _ _ _ _ _ _ _ (H f f' g g' h h')).
Defined.
 
CoFixpoint assoc'_assoc (G : ωPreCat) (_transport : transport_eq G) :
  @associativity' G _ -> @associativity G _.
intro H. apply mkAssociativity.
- intros. destruct H. apply assocH_assoc; auto.
- intros. destruct H. apply assoc'_assoc; auto.
Defined.

Definition higher_composable_assoc_gen {G1 G2 G3 G12 G23 G123 : Type}
           {f12 : G1 → G2 → G12}
           {f23 : G2 → G3 → G23}
           {f12_3 : G12 → G3 → G123}
           {f1_23 : G1 → G23 → G123}
           (associate : ∀ (F : | piω G1 |) (G : | piω G2 |) (H : | piω G3 |),
                          f1_23 F (f23 G H) = f12_3 (f12 F G) H)
           (F F' : | piω G1 |) (G G' : | piω G2 |) (H H' : | piω G3|) :
  f1_23 F (f23 G H) = f1_23 F' (f23 G' H') ->
  f12_3 (f12 F G) H = f12_3 (f12 F' G') H'
  := fun E =>
      inverse (associate F G H) @ (E @ associate F' G' H').


Definition pi_assocH_gen_law (G1 G2 G3 G12 G23 G123 : Type)
           (f12 : G1 → G2 → G12)
           (f23 : G2 → G3 → G23)
           (f12_3 : G12 → G3 → G123)
           (f1_23 : G1 → G23 → G123)
           (P12 : forall {x y z w}, (x = y) -> (z = w) -> f12 x z = f12 y w := ap2 f12)
           (P23 : forall {x y z w}, (x = y) -> (z = w) -> f23 x z = f23 y w := ap2 f23) 
           (P1_23 : forall {F F' G G' H H'}, F = F' -> f23 G H = f23 G' H' ->
                   f1_23 F (f23 G H) = f1_23 F' (f23 G' H'))                  
           (P12_3 : forall {F F' G G' H H'},
                      (f12 F G = f12 F' G') -> (H = H') ->
                      f12_3 (f12 F G) H = f12_3 (f12 F' G') H' :=
                    fun _ _ _ _ _ _ e e' => ap2 f12_3 e e')
           (P1_23_refl : forall {F G H}, P1_23 (eq_refl F) (eq_refl (f23 G H)) = eq_refl _)
           (associate : ∀ (F : | piω G1 |) (G : | piω G2 |) (H : | piω G3 |),
                          f1_23 F (f23 G H) = f12_3 (f12 F G) H)
           (F F' : | piω G1 |) (G G' : | piω G2 |) (H H' : | piω G3|) 
           (hComp := higher_composable_assoc_gen associate F F' G G' H H') 
           (f : |piω G1 [F,F']|) (g : |piω G2 [G,G']|) (h : |piω G3 [H,H']|) :
           hComp (P1_23 f (P23 _ _ _ _ g h)) = P12_3 _ _ _ _ _ _ (P12 _ _ _ _ f g) h.
  unfold hComp, higher_composable_assoc_gen.
  destruct f, g, h. simpl in *. 
  rewrite P1_23_refl. unfold P12_3. unfold ap2, equal_f; simpl. 
  rewrite inverse_inv_L. reflexivity.
Defined.

Definition higher_composable_assoc_gen2  (G1 G2 G3 G12 G23 G123 : Type)
           (f12 : G1 → G2 → G12)
           (f23 : G2 → G3 → G23)
           (f12_3 : G12 → G3 → G123)
           (f1_23 : G1 → G23 → G123)
           (P12 : forall {x y z w}, (x = y) -> (z = w) -> f12 x z = f12 y w := ap2 f12)
           (P23 : forall {x y z w}, (x = y) -> (z = w) -> f23 x z = f23 y w := ap2 f23) 
           (P1_23 : forall {F F' G G' H H'}, F = F' -> f23 G H = f23 G' H' ->
                   f1_23 F (f23 G H) = f1_23 F' (f23 G' H'))                  
           (P12_3 : forall {F F' G G' H H'},
                      (f12 F G = f12 F' G') -> (H = H') ->
                      f12_3 (f12 F G) H = f12_3 (f12 F' G') H' :=
                    fun _ _ _ _ _ _ e e' => ap2 f12_3 e e')
           (P1_23_refl : forall {F G H}, P1_23 (eq_refl F) (eq_refl (f23 G H)) = eq_refl _)
           (associate : ∀ (F : | piω G1 |) (G : | piω G2 |) (H : | piω G3 |),
                          f1_23 F (f23 G H) = f12_3 (f12 F G) H)
           (F F' : | piω G1 |) (G G' : | piω G2 |) (H H' : | piω G3|) 
           (hComp := higher_composable_assoc_gen associate F F' G G' H H') 
           (f f': |piω G1 [F,F']|) (g g': |piω G2 [G,G']|) (h h' : |piω G3 [H,H']|) 
           (compV : (piω (f = f') ** piω (P23 _ _ _ _ g h = P23 _ _ _ _ g' h') ==>
                         piω (P1_23 f (P23 _ _ _ _ g h) = P1_23 f' (P23 _ _ _ _ g' h')))) 
           (associate2 := pi_assocH_gen_law f12 f23 f12_3 f1_23
                                         (@P1_23) (@P1_23_refl)
                                         associate F F' G G' H H': ∀ f g h,
 |piω (f12_3 (f12 F G) H = f12_3 (f12 F' G') H') [hComp
    (P1_23 f (P23 _ _ _ _ g h)), P12_3 _ _ _ _ _ _ (P12 _ _ _ _ f g) h]|)
           (compV2 := piCompGen2 (piω G1) (piω G23) (piω G123) f1_23
                                 (@P1_23 F F' G G' H H') _ _
                                 (inverse (associate F G H)) (associate F' G' H')
                                 f f' (P23 _ _ _ _ g h) (P23 _ _ _ _ g' h') compV)
: Composable (pi (f = f')) (pi (P23 _ _ _ _ g h = P23 _ _ _ _ g' h'))
             (pi (P12_3 _ _ _ _ _ _ (P12 _ _ _ _ f g) h = P12_3 _ _ _ _ _ _ (P12 _ _ _ _ f' g') h'))
:= {| compo := transport_GHomL (inversE (associate2 f g h))
               °° (transport_GHomR (associate2 f' g' h') °° compV2) |}.


CoInductive Id_ind' : ∀ (A B' A' C' C'': Type) (f' : A' -> B' -> C')
                       (g : A -> C' -> C'')
                       (p : forall x1 x1' y1 y1' y2 y2',
                              (piω (x1 = x1') **
                               piω (f' y1 y2 = f' y1' y2'))
                              ==> piω (g x1 (f' y1 y2) = g x1' (f' y1' y2'))), Type :=
  mkId_ind' :  ∀ (A B' A' C' C'': Type) (f' : A' -> B' -> C')
                       (g : A -> C' -> C'')
                       (p : forall x1 x1' y1 y1' y2 y2',
                              (piω (x1 = x1') **
                               piω (f' y1 y2 = f' y1' y2'))
                              ==> piω (g x1 (f' y1 y2) = g x1' (f' y1' y2'))),
    (∀ x1 y1 y2 , p x1 x1 y1 y1 y2 y2 @@ (eq_refl,eq_refl) = eq_refl) ->
    (∀ x1 x1' y1 y1' y2 y2',
       Id_ind' _ (fun x y => p x1 x1'  y1 y1' y2 y2' @@ (x,y)) (fun (f1 f1':x1=x1')  (g1 g1' : y1 =y1') (g2 g2' : y2 = y2') => (p  x1 x1' y1 y1' y2 y2') << (f1,ap2 f' g1 g2) , (f1' ,ap2 f' g1' g2')>>))
    -> Id_ind' f' g p.

Definition Id_ind'_refl (A A' B' C' C'': Type) (f' : A' -> B' -> C')
                       (g : A -> C' -> C'')
                       (p : forall x1 x1' y1 y1' y2 y2',
                              (piω (x1 = x1') **
                               piω (f' y1 y2 = f' y1' y2'))
                              ==> piω (g x1 (f' y1 y2) = g x1' (f' y1' y2')))
                                              (e:Id_ind' f' g p) :
  ∀ x1 y1 y2 , p x1 x1 y1 y1 y2 y2 @@ (eq_refl,eq_refl) = eq_refl.
  destruct e. exact e.
Defined.

Definition Id_ind'_hom (A A' B' C' C'': Type)  (f' : A' -> B' -> C')
                       (g : A -> C' -> C'')
                       (p : forall x1 x1' y1 y1' y2 y2',
                              (piω (x1 = x1') **
                               piω (f' y1 y2 = f' y1' y2'))
                              ==> piω (g x1 (f' y1 y2) = g x1' (f' y1' y2'))) (e:Id_ind' f' g p) :
∀ x1 x1' y1 y1' y2 y2',
       Id_ind' _ (fun x y => p x1 x1' y1 y1' y2 y2' @@ (x,y)) (fun (f1 f1':x1=x1') (g1 g1' : y1 =y1') (g2 g2' : y2 = y2') => (p  x1 x1' y1 y1' y2 y2') << (f1,ap2 f' g1 g2) , (f1',ap2 f' g1' g2')>>).
  destruct e. exact i.
Defined.


CoFixpoint append_right_id_ind' (A A' B' C' C'' D E: Type)
           (f' : A' -> B' -> C')
           (g : (piω A ** piω C') ==> piω C'') 
           (h : |piω D|)
           (k : C'' -> D -> E)
           (a1 a2 : A) 
           (a1' a2' : A') (b1' b2' : B') 
           (H : Id_ind' (ap2 f' (h':=b2'))
        (λ (x : a1 = a2) (y : f' a1' b1' = f' a2' b2'),
         (g << (a1, f' a1' b1'), (a2, f' a2' b2') >>) @@ (x, y))
        (λ (f1 f1' : a1 = a2) (g1 g1' : a1' = a2')
         (g2 g2' : b1' = b2'),
         (g << (a1, f' a1' b1'), (a2, f' a2' b2') >>) <<
         (f1, ap2 f' g1 g2), (f1', ap2 f' g1' g2') >>)) 
           (compoK := piComp_V k)
 : Id_ind' (@ap2 _ _ _ f' a1' a2' b1' b2') 
          (fun c c' => (identity h) ° 
                       (g << (a1,f' a1' b1'),(a2, f' a2' b2')>> @@ (c,c')))
         (fun (x1 x1' : |piω (a1 = a2)|)  
            (y1 y1' : |piω (a1' = a2')|) (y2 y2' : |piω (b1' = b2')|) =>
               (@append_right 
                  (piω (g @@ (a1, f' a1' b1') = g @@ (a2, f' a2' b2')))
                  (piω (h= h))
                  (piω (_ = _))
                  ((g << (a1, f' a1' b1'), (a2, f' a2' b2') >>) 
                     @@ (x1 , ap2 f' y1 y2))
                  ((g << (a1, f' a1' b1'), (a2, f' a2' b2') >>) 
                     @@ (x1', ap2 f' y1' y2'))
                    (identity h) _)
         °° ((g <<(a1, f' a1' b1'),(a2,f' a2' b2')>>) 
               <<(x1,ap2 f' y1 y2),(x1',ap2 f' y1' y2')>>)).
apply mkId_ind'. 
- intros. pose (Id_ind'_refl H x1 y1 y2). 
  simpl in *. rewrite e. reflexivity.
- intros. simpl. 
  exact (@append_right_id_ind'
          (a1 = a2)  
          (a1' = a2') (b1' = b2') (f' a1' b1' = f' a2' b2')
          (g @@ (a1, f' a1' b1')  = g @@ (a2, f' a2' b2'))
          (h = h) (k (g @@ (a1, f' a1' b1')) h = 
                    k (g @@ (a2, f' a2' b2')) h)
          (ap2 f' (h':=b2')) 
          (g <<(a1, f' a1' b1'),(a2,f' a2' b2')>>) 
          (identity h) (@ap2 _ _ _ k _ _ _ _)
          x1 x1' y1 y1' y2 y2'
          (Id_ind'_hom H x1 x1' y1 y1' y2 y2')).
Defined.


CoFixpoint append_left_id_ind' (A A' B' C' C'' D E: Type)
           (f' : A' -> B' -> C')
           (g : (piω A ** piω C') ==> piω C'') 
           (h : |piω D|)
           (k : D -> C'' -> E)
           (a1 a2 : A)  
           (a1' a2' : A') (b1' b2' : B') 
           (H : Id_ind'  (ap2 f' (h':=b2'))
        (λ (x : a1 = a2) (y : f' a1' b1' = f' a2' b2'),
         (g << (a1, f' a1' b1'), (a2, f' a2' b2') >>) @@ (x, y))
        (λ (f1 f1' : a1 = a2)  (g1 g1' : a1' = a2')
         (g2 g2' : b1' = b2'),
         (g << (a1, f' a1' b1'), (a2, f' a2' b2') >>) <<
         (f1, ap2 f' g1 g2), (f1', ap2 f' g1' g2') >>)) 
           (compoK := piComp_V k)
 : Id_ind' (@ap2 _ _ _ f' a1' a2' b1' b2') 
          (fun c c' => (g << (a1,f' a1' b1'),(a2, f' a2' b2')>> @@ (c,c')) 
                         ° (identity h))
         (fun (x1 x1' : |piω (a1 = a2)|)  
            (y1 y1' : |piω (a1' = a2')|) (y2 y2' : |piω (b1' = b2')|) =>
               (@append_left
                  (piω (h= h))
                  (piω (g @@ (a1, f' a1' b1') = g @@ (a2, f' a2' b2')))
                  (piω (_ = _))
                  (identity h)
                  ((g << (a1, f' a1' b1'), (a2, f' a2' b2') >>) 
                     @@ (x1, ap2 f' y1 y2))
                  ((g << (a1, f' a1' b1'), (a2, f' a2' b2') >>) 
                     @@ (x1' , ap2 f' y1' y2'))
                     _)
         °° ((g <<(a1, f' a1' b1'),(a2,f' a2' b2')>>) 
               <<(x1 ,ap2 f' y1 y2),(x1' ,ap2 f' y1' y2')>>)).
apply mkId_ind'. 
- intros. pose (Id_ind'_refl H x1 y1 y2). 
  simpl in *. rewrite e. reflexivity.
- intros. simpl. 
  exact (@append_left_id_ind' 
          (a1 = a2) 
          (a1' = a2') (b1' = b2') (f' a1' b1' = f' a2' b2')
          (g @@ (a1, f' a1' b1')  = g @@ (a2, f' a2' b2'))
          (h = h) (k h (g @@ (a1, f' a1' b1')) = 
                    k h (g @@ (a2, f' a2' b2')))
          (ap2 f' (h':=b2')) 
          (g <<(a1, f' a1' b1'),(a2,f' a2' b2')>>) 
          (identity h) (@ap2 _ _ _ k _ _ _ _)
          x1 x1'  y1 y1' y2 y2'
          (Id_ind'_hom H x1 x1'  y1 y1' y2 y2')).
Defined.

Definition pi_assocH_gen_Id_ind (G1 G2 G3 G23 G123 : Type)
           (f23 : G2 → G3 → G23)
           (f1_23 : G1 → G23 → G123)
           (P23 : forall {x y z w}, (x = y) -> (z = w) -> f23 x z = f23 y w := ap2 f23) 
           (P1_23 : forall F F' G G' H H', 
                   (piω (F = F') **
                    piω (f23 G H = f23 G' H') ) ==>
                   (piω (f1_23 F (f23 G H) = f1_23 F' (f23 G' H'))))
           (F F' : | piω G1 |) (G G' : | piω G2 |) (H H' : | piω G3|) 
           (P1_23_hom := fun f f' g g' h h' =>
                        (P1_23 F F' G G' H H' << (f, P23 _ _ _ _ g h) ,
                         (f', P23 _ _ _ _ g' h') >>)) 
           (f f': |piω G1 [F,F']|) (g g': |piω G2 [G,G']|) (h h' : |piω G3 [H,H']|)
           (P1_23_refl : Id_ind' 
                             (ap2 (P23 G G' H H') (h':=h'))
                             (fun x y => P1_23_hom f f' g g' h h' @@ (x,y))
                             (fun xf xf'  xg xg' xh xh' => 
                                 P1_23_hom f f' g g' h h' <<
              (xf,ap2 (P23 G G' H H') xg xh),
              (xf', ap2 (P23 G G' H H') xg' xh') >>)) 
           v v'
           (Y  : v = f1_23 F (f23 G H))
           (Y' : f1_23 F' (f23 G' H') = v') 
           (apP1_23 :=fun f f' g g' h h' =>  
                    piCompGen2 (piω G1) (piω G23) (piω G123) f1_23
                               (fun x y => @P1_23 F F' G G' H H' @@ (x,y)) v v'
                               Y Y' f f' (P23 _ _ _ _ g h) (P23 _ _ _ _ g' h')
                               (P1_23_hom f f' g g' h h')) : 
  Id_ind' (ap2 (P23 G G' H H') (h':=h'))
         (λ X Y, apP1_23 f f' g g' h h' @@ (X,Y))
         (fun xf xf' xg xg' xh xh' => apP1_23 f f' g g' h h' <<
              (xf ,ap2 (P23 G G' H H') xg xh),
              (xf', ap2 (P23 G G' H H') xg' xh')  >>).
  pose (@transport_GHomR (piω G123) _ (f1_23 F' (f23 G' H')) v' Y' °° 
                         (P1_23 F F' G G' H H')).

  apply (@append_left_id_ind'
          (F = F')           (G = G') (H = H') (f23 G H = f23 G' H')
          (f1_23 F (f23 G H) = v')
          (v = f1_23 F (f23 G H))
          (v = v') (P23 G G' H H')
          g0 Y concat
          f f' g g' h h'). 

  exact (@append_right_id_ind'
          (F = F') 
          (G = G') (H = H') (f23 G H = f23 G' H')
          (f1_23 F (f23 G H) = f1_23 F' (f23 G' H'))
          (f1_23 F' (f23 G' H') = v')
          (f1_23 F (f23 G H) = v')
          (P23 G G' H H')
          (P1_23 F F' G G' H H') Y' concat f f' g g' h h' P1_23_refl).

Defined.

Definition pi_assocH_gen_Id_ind_simple (G1 G2 G3 G12 G23 G123 : Type)
           (f12 : G1 → G2 → G12)
           (f23 : G2 → G3 → G23)
           (f12_3 : G12 → G3 → G123)
           (f1_23 : G1 → G23 → G123)
           (P12 : forall {x y z w}, (x = y) -> (z = w) -> f12 x z = f12 y w := ap2 f12)
           (P23 : forall {x y z w}, (x = y) -> (z = w) -> f23 x z = f23 y w := ap2 f23) 
           (P1_23 : forall F F' G G' H H', 
                   (piω (F = F') **
                    piω (f23 G H = f23 G' H') ) ==>
                   (piω (f1_23 F (f23 G H) = f1_23 F' (f23 G' H'))))
           (P12_3 : forall {F F' G G' H H'},
                      (f12 F G = f12 F' G') -> (H = H') ->
                      f12_3 (f12 F G) H = f12_3 (f12 F' G') H' :=
                    fun _ _ _ _ _ _ e e' => ap2 f12_3 e e')
           (F F' : | piω G1 |) (G G' : | piω G2 |) (H H' : | piω G3|) 
           (P1_23_refl : Id_ind' f23 f1_23
                                (fun F F' G G' H H' => P1_23 F F' G G' H H')) 
           (associate : ∀ (F : | piω G1 |) (G : | piω G2 |) (H : | piω G3 |),
                          f1_23 F (f23 G H) = f12_3 (f12 F G) H)
 (hComp := higher_composable_assoc_gen associate F F' G G' H H') 
 (apP1_23 :=fun f f' g g' h h' =>  
                    piCompGen2 (piω G1) (piω G23) (piω G123) f1_23
                               (fun x y => @P1_23 F F' G G' H H' @@ (x,y)) _ _
                               (inverse (associate F G H)) (associate F' G' H')
                               f f'
                               (P23 _ _ _ _ g h) (P23 _ _ _ _ g' h')
                               (P1_23 F F' G G' H H' << (f, P23 _ _ _ _ g h) ,
                         (f', P23 _ _ _ _ g' h') >>))
  (associate2 := pi_assocH_gen_law f12 f23 f12_3 f1_23
                                    (fun F F' G G' H H'  x y => @P1_23 F F' G G' H H' @@ (x,y))
                                    (Id_ind'_refl P1_23_refl)
                                         associate F F' G G' H H': ∀ f g h,
 |piω (f12_3 (f12 F G) H = f12_3 (f12 F' G') H') [hComp
                                                     (P1_23 _ _ _ _ _ _ @@ (f,P23 _ _ _ _ g h)), P12_3 _ _ _ _ _ _ (P12 _ _ _ _ f g) h]|)
: Id_ind' (P23 G G' H H')
         (λ X Y,
          hComp (P1_23 F F' G G' H H' @@ (X, Y))) apP1_23.
  pose (P1_23_hom_refl := Id_ind'_hom P1_23_refl F F' G G' H H').
  apply mkId_ind'. 
- intros. unfold apP1_23, piCompGen2, P23. simpl. 
  pose (Id_ind'_refl P1_23_hom_refl x1 y1 y2). simpl in *.
  rewrite e. reflexivity.
 - intros f1 f1' f2 f2' g2 g2'. 
   apply pi_assocH_gen_Id_ind.
   exact (Id_ind'_hom P1_23_hom_refl f1 f1' f2 f2' g2 g2' ). 
Defined.
 
CoFixpoint pi_assocH_gen : forall (G1 G2 G3 G12 G23 G123 : Type)
           (f12 : G1 → G2 → G12)
           (f23 : G2 → G3 → G23)
           (f12_3 : G12 → G3 → G123)
           (f1_23 : G1 → G23 → G123)
           (P12 : forall {x y z w}, (x = y) -> (z = w) -> f12 x z = f12 y w := ap2 f12)
           (P23 : forall {x y z w}, (x = y) -> (z = w) -> f23 x z = f23 y w := ap2 f23) 
           (P1_23 : forall F F' G G' H H', 
                   (piω (F = F') **
                    piω (f23 G H = f23 G' H') ) ==>
                   (piω (f1_23 F (f23 G H) = f1_23 F' (f23 G' H'))))                  
           (P12_3 : forall {F F' G G' H H'},
                      (f12 F G = f12 F' G') -> (H = H') ->
                      f12_3 (f12 F G) H = f12_3 (f12 F' G') H' :=
                    fun _ _ _ _ _ _ e e' => ap2 f12_3 e e')
           (associate : ∀ (F : | piω G1 |) (G : | piω G2 |) (H : | piω G3 |),
                          f1_23 F (f23 G H) = f12_3 (f12 F G) H)
           (F F' : | piω G1 |) (G G' : | piω G2 |) (H H' : | piω G3|) 
           (hComp := higher_composable_assoc_gen associate F F' G G' H H') 
           (f f': |piω G1 [F,F']|) (g g': |piω G2 [G,G']|) (h h' : |piω G3 [H,H']|)
           (P1_23_refl : Id_ind'  f23 f1_23
                                (fun f f'  g g' h h' => P1_23 f f' g g' h h'))
           (comp1_23 : forall f f' g g' h h',
                      (piω (f = f') ** piω (P23 _ _ _ _ g h = P23 _ _ _ _ g' h') ==>
                           piω (P1_23 _ _ _ _ _ _ @@ (f,P23 _ _ _ _ g h) = P1_23 _ _ _ _ _ _ @@ (f',P23 _ _ _ _ g' h')))
            := fun f f' g g' h h' =>
                 P1_23 F F' G G' H H' << (f, P23 _ _ _ _ g h) ,
              (f', P23 _ _ _ _ g' h') >>)
           (hComp := higher_composable_assoc_gen associate F F' G G' H H')
           (associate2 := pi_assocH_gen_law f12 f23 f12_3 f1_23
                                            (fun F F' G G' H H' x y => P1_23 F F' G G' H H'  @@ (x,y))
                                            (Id_ind'_refl P1_23_refl)
                                             associate F F' G G' H H': ∀ f g h,
                         |piω (f12_3 (f12 F G) H = f12_3 (f12 F' G') H') [hComp
    (P1_23 _ _ _ _ _ _ @@ (f,P23 _ _ _ _ g h)), P12_3 _ _ _ _ _ _ (P12 _ _ _ _ f g) h]|)
  (hComp' := fun f f' g g' h h' =>
       @higher_composable_assoc_gen2 G1 G2 G3 G12 G23 G123 f12 f23 f12_3 f1_23
                                     (fun F F' G G' H H' x y => P1_23 F F' G G' H H'  @@ (x,y)) (fun x y z => Id_ind'_refl P1_23_refl x y z) associate F F'  G G' H H' f f' g g' h h'
                                     (comp1_23  f f' g g' h h')) , 
  @associativityH
    (((piω G1) [F, F']) [f,f'])
    (((piω G2) [G, G']) [g,g'])
    (((piω G3) [H, H']) [h,h'])
    (((piω G12) [f12 F G, f12 F' G']) [P12 _ _ _ _ f g, P12 _ _ _ _ f' g'])
    (((piω G23) [f23 G H, f23 G' H']) [P23 _ _ _ _ g h, P23 _ _ _ _ g' h'])
    (((piω G123 ) [f12_3 (f12 F G) H, f12_3 (f12 F' G') H'])
                     [P12_3 _ _ _ _ _ _ (P12 _ _ _ _ f g) h,P12_3 _ _ _ _ _ _ (P12 _ _ _ _ f' g') h'])
    _ (piComp_V (@P12 _ _ _ _)  _ _ _ _) (piComp_V (@P23 _ _ _ _) _ _ _ _) 
    (piComp_V (@P12_3 _ _ _ _ _ _) _ _ _ _)
    (hComp' f f' g g' h h').
   intros.
   pose (apPV := fun f f' g g' h h' =>
                     piCompGen2 (piω G1) (piω G23) (piω G123) f1_23
                                (fun x y => @P1_23 F F' G G' H H' @@ (x,y)) _ _
                                 (inverse (associate F G H)) (associate F' G' H')
                                 f f' (@P23 _ _ _ _ g h) (@P23 _ _ _ _ g' h') (comp1_23 f f' g g' h h')).

   pose (apP1_23_refl := pi_assocH_gen_Id_ind_simple f12 f12_3 P1_23
                                      F F' G G' H H' P1_23_refl associate).
   apply mkAssociativityH. refine (existT _ _ _).
   
   - exact (pi_assocH_gen_law (@P12 _ _ _ _) (@P23 _ _ _ _) (@P12_3 _ _ _ _ _ _ )
          (fun X Y => hComp (@P1_23 _ _ _ _ _ _ @@ (X,Y)))
          (fun f f' g g' h h' x y => apPV f f' g g' h h'  @@ (x,y)) 
          (Id_ind'_refl apP1_23_refl) associate2 f f' g g' h h').

   - intros ff ff' gg gg' hh hh'.
     exact (pi_assocH_gen
                   (F = F') (G = G') (H = H') 
                   (f12 F G = f12 F' G') (f23 G H = f23 G' H')
                   (f12_3 (f12 F G) H = f12_3 (f12 F' G') H')
          (@P12 _ _ _ _) (@P23 _ _ _ _) (@P12_3 _ _ _ _ _ _ )
          (fun X Y => hComp (@P1_23 _ _ _ _ _ _ @@ (X,Y))) apPV associate2
          f f' g g' h h' ff ff' gg gg' hh hh' apP1_23_refl).
Defined.


CoFixpoint pi_assocH_gen_Id_ind_init (G1 G2 G3 G23 G123 : Type)
           (f23 : G2 → G3 → G23)
           (f1_23 : G1 → G23 → G123)
           (P23 : forall {x y z w}, (x = y) -> (z = w) -> f23 x z = f23 y w := ap2 f23) 
           (P1_23 : forall F F' G G' H H', 
                   (piω (F = F') **
                    piω (f23 G H = f23 G' H') ) ==>
                                                 (piω (f1_23 F (f23 G H) = f1_23 F' (f23 G' H')))
           := fun x1 x1' y1 y1' y2 y2' => piComp_V_ f1_23
              x1 x1' (f23 y1 y2) (f23 y1' y2')) :
      Id_ind' f23 f1_23 P1_23.
apply mkId_ind'. intros. reflexivity.
intros F F' G G' H H'.
exact (pi_assocH_gen_Id_ind_init (F = F') (G = G') 
                                 (H = H') (f23 G H = f23 G' H')
                                 (f1_23 F (f23 G H) = f1_23 F' (f23 G' H')) (@P23 G G' H H')
                                 (fun a b => @P1_23 F F' G G' H H' @@ (a,b))).
Defined.

Definition pi_assocH_gen_simple (G1 G2 G3 G12 G23 G123 : Type)
           (f12 : G1 → G2 → G12)
           (f23 : G2 → G3 → G23)
           (f12_3 : G12 → G3 → G123)
           (f1_23 : G1 → G23 → G123)
           (P12 : forall {x y z w}, (x = y) -> (z = w) -> f12 x z = f12 y w := ap2 f12)
           (P23 : forall {x y z w}, (x = y) -> (z = w) -> f23 x z = f23 y w := ap2 f23) 
           (P1_23 : forall F F' G G' H H', 
                   (piω (F = F') **
                    piω (f23 G H = f23 G' H') ) ==>
                                                 (piω (f1_23 F (f23 G H) = f1_23 F' (f23 G' H')))
           := fun x1 x1' y1 y1' y2 y2' => piComp_V_ f1_23
              x1 x1' (f23 y1 y2) (f23 y1' y2'))                  
           (P12_3 : forall {F F' G G' H H'},
                      (f12 F G = f12 F' G') -> (H = H') ->
                      f12_3 (f12 F G) H = f12_3 (f12 F' G') H' :=
                    fun _ _ _ _ _ _ e e' => ap2 f12_3 e e')
           (associate : ∀ (F : | piω G1 |) (G : | piω G2 |) (H : | piω G3 |),
                          f1_23 F (f23 G H) = f12_3 (f12 F G) H)
           (F F' : | piω G1 |) (G G' : | piω G2 |) (H H' : | piω G3|) 
           (hComp := higher_composable_assoc_gen associate F F' G G' H H') 
           (f f': |piω G1 [F,F']|) (g g': |piω G2 [G,G']|) (h h' : |piω G3 [H,H']|)
:=
  pi_assocH_gen f12 f12_3 P1_23 associate F F' G G' H H' f f' g g' h h'
                 (pi_assocH_gen_Id_ind_init f23 f1_23).

CoFixpoint pi_associativity' (T : Type) : @associativity' (piω T) _.
apply mkAssociativity'.
- intros. apply mkAssociativityH. refine (existT _ _ _ ).
  + intros. exact (inverse (concat_assoc f g h)). 
  + intros F F' G G' H H'. apply mkAssociativityH. refine (existT _ _ _ ).
    * intros . unfold compo. simpl.
      exact (pi_assocH_gen_law  concat concat concat concat (fun F F' G G' H H' e e' => concat_LR e e') (fun _ _ _ => eq_refl) (fun  F G H => inverse (concat_assoc F G H)) F F' G G' H H' f g h).
    * intros.
      exact (pi_assocH_gen_simple concat concat concat concat (fun  F G H => inverse (concat_assoc F G H)) F F' G G' H H' f f' g g' h h').
- intros. apply pi_associativity'.
Defined.

Definition pi_associativity (T:Type) := assoc'_assoc (pi_associativity' T).

Definition higher_composable_idR_gen {G H : Type} (h:H)
           {f : G → H → G} (idR : ∀ (g : | piω G |), f g h = g)
           (g g' : | piω G |) :
  f g h = f g' h -> g = g'
  := fun E => inverse (idR g) @ (E @ idR g').

Definition pi_idR_gen_law (G H: Type) (h:H)
           (f : G → H → G)
           (P : forall {g g'}, g = g' -> h = h -> f g h = f g' h)                  
           (P_refl : forall {g}, P (eq_refl g) (eq_refl h) = eq_refl _) 
           (idR : ∀ (g : | piω G |), f g h = g)
           (g g' : | piω G |)
           (hComp := higher_composable_idR_gen h idR g g') 
           (e : |piω G[g,g']|)  :
           hComp (P e (eq_refl h)) = e. 
  unfold hComp, higher_composable_idR_gen.
  destruct e. simpl in *. 
  rewrite P_refl. rewrite idpath_L. rewrite inverse_inv_L. reflexivity.
Defined.

Definition piCompGen1 (T U V: ωPreCat) (f : |T| -> | U| -> |V|)  
           {x y : |T| } (h:|U|)
           (P : (|T[x,y]|) -> (|U[h,h]|) -> |V[f x h, f y h]|)
           (v1:|V|) (v2:|V|)
           (law1 : |V [v1, f x h]|)  (law2 : |V [f y h, v2]|)
           (e e' : |T[x,y]|) 
           (compV : (T[x,y][e,e'] ** U[h,h][identity _ , identity _]) ==>
                                              V[_,_][P e (identity _), P e' (identity _)]) : 
  (T[x,y][e,e'] ** U[h,h][identity _ , identity _]) ==>
   V [v1, v2][(law2 ° P e (identity _)) ° law1, (law2 ° P e' (identity _)) ° law1]
:= append_left law1 (law2 ° P e _) (law2 ° P e' _) 
   °° (append_right (P e _) (P e' _) law2
     °° compV). 

Definition higher_composable_idR_gen2  (G H: Type) (h:H)
           (f : G → H → G)
           (P : forall {g g'}, g = g' -> h = h -> f g h = f g' h)                  
           (P_refl : forall {g}, P (eq_refl g) (eq_refl h) = eq_refl _) 
           (idR : ∀ (g : | piω G |), f g h = g)
           (g g' : | piω G |)
           (hComp := higher_composable_idR_gen h idR g g') 
           (e e' : |piω G[g,g']|)
           (compV : (piω (e = e') ** piω (eq_refl h = eq_refl h)) ==> piω (P e _ = P e' _)) 
           (idR2 := pi_idR_gen_law f (@P) (@P_refl) idR g g' : ∀ e,
                   |piω (g = g') [hComp (P e _), e]|) 
           (compV2 := piCompGen1 (piω G) (piω H) (piω G) f h
                                 (@P g g') _ _
                                 (inverse (idR g)) (idR g') e e' compV)
: (piω (e = e')  ** piω (eq_refl h = eq_refl h)) ==> piω (e = e')
:= transport_GHomL (inversE (idR2 e)) °° (transport_GHomR (idR2 e') °° compV2).

CoInductive Id_ind1 (A B C: Type) (f : A -> B -> C) (b:B)
            (p : forall x1 x1',
                   (piω (x1 = x1') ** piω (b=b))
                     ==> piω (f x1 b = f x1' b)) : Type :=
  mkId_ind1 :  
    (∀ x1  , p x1 x1 @@ (eq_refl,eq_refl) = eq_refl) ->
    (∀ x1 x1',
       @Id_ind1 _ _ _ (fun x y => p x1 x1' @@ (x,y)) eq_refl
                (fun (f1 f1':x1=x1')  =>(p x1 x1') << (f1,_) , (f1',_)>>))
    -> Id_ind1 f b p.

Definition Id_ind1_refl (A B C: Type) (f : A -> B -> C) (b:B)
            (p : forall x1 x1',
                   (piω (x1 = x1') ** piω (b=b))
                     ==> piω (f x1 b = f x1' b))
                       (e:Id_ind1 f b p) :
  ∀ x1  , p x1 x1 @@ (eq_refl, eq_refl) = eq_refl.
  destruct e. exact e.
Defined.

Definition Id_ind1_hom (A B C: Type) (f : A -> B -> C) (b:B)
            (p : forall x1 x1',
                   (piω (x1 = x1') ** piω (b=b))
                     ==> piω (f x1 b = f x1' b))
            (e:Id_ind1 f b p)  :
∀ x1 x1',
       @Id_ind1 _ _ _ (fun x y => p x1 x1' @@ (x,y)) eq_refl
                (fun (f1 f1':x1=x1')  =>(p x1 x1') << (f1,_) , (f1',_)>>).
  destruct e. exact i.
Defined.


CoFixpoint append_right_id_ind1 (A  C' C'' D E: Type)
           (g : (piω A ** piω C') ==> piω C'') 
           (h : |piω D|) (c:|piω C'|)
           (k : C'' -> D -> E)
           (a1 a2 : A) 
           (H : Id_ind1
                  (λ (x : a1 = a2) (y : c=c),
                   (g << (a1, c), (a2, c) >>) @@ (x, y)) eq_refl
                  (λ (f1 f1' : a1 = a2),
                   (g << (a1,c), (a2, c) >>)
                      << (f1, eq_refl), (f1', eq_refl) >>)) 
           (compoK := piComp_V k)
 : Id_ind1 (fun X X' => (identity h) ° 
                   (g << (a1,c),(a2, c)>> @@ (X,X'))) eq_refl
         (fun (x1 x1' : |piω (a1 = a2)|)  =>
               (@append_right 
                  (piω (g @@ (a1, c) = g @@ (a2, c)))
                  (piω (h= h))
                  (piω (_ = _))
                  ((g << (a1, c), (a2, c) >>) 
                     @@ (x1 , eq_refl))
                  ((g << (a1, c), (a2, c) >>) 
                     @@ (x1', eq_refl))
                    (identity h) _)
         °° ((g <<(a1, c),(a2,c)>>) 
               <<(x1,eq_refl),(x1',eq_refl)>>)).
apply mkId_ind1. 
- intros. pose (Id_ind1_refl H x1). 
  simpl in *. rewrite e. reflexivity.
- intros. simpl. 
  exact (@append_right_id_ind1
          (a1 = a2)  (c = c)
          (g @@ (a1, c)  = g @@ (a2, c))
          (h = h) (k (g @@ (a1, c)) h = 
                    k (g @@ (a2, c)) h)
          (g <<(a1, c),(a2,c)>>) 
          (identity h) eq_refl (@ap2 _ _ _ k _ _ _ _)
          x1 x1' 
          (Id_ind1_hom H x1 x1')).
Defined.

CoFixpoint append_left_id_ind1 (A C' C'' D E: Type)
           (g : (piω A ** piω C') ==> piω C'') 
           (h : |piω D|) (c:|piω C'|)
           (k : D -> C'' -> E)
           (a1 a2 : A)  
           (H : Id_ind1
              (λ (x : a1 = a2) (y : c = c),
                 (g << (a1, c), (a2, c) >>) @@ (x, y)) eq_refl
              (λ (f1 f1' : a1 = a2) ,
                 (g << (a1, c), (a2, c) >>) <<
                     (f1, eq_refl), (f1', eq_refl) >>)) 
           (compoK := piComp_V k)
 : Id_ind1 (fun X X' => (g << (a1,c),(a2, c)>> @@ (X,X')) 
                         ° (identity h)) eq_refl
           (fun (x1 x1' : |piω (a1 = a2)|)  =>
                (@append_left
                  (piω (h= h))
                  (piω (g @@ (a1, c) = g @@ (a2, c)))
                  (piω (_ = _))
                  (identity h)
                  ((g << (a1, c), (a2, c) >>) 
                     @@ (x1, eq_refl))
                  ((g << (a1, c), (a2, c) >>) 
                     @@ (x1' , eq_refl))
                     _)
         °° ((g <<(a1, c),(a2,c)>>) 
               <<(x1 ,eq_refl),(x1' ,eq_refl)>>)).
apply mkId_ind1. 
- intros. pose (Id_ind1_refl H x1). 
  simpl in *. rewrite e. reflexivity.
- intros. simpl. 
  exact (@append_left_id_ind1
          (a1 = a2) (c = c) 
          (g @@ (a1, c)  = g @@ (a2, c))
          (h = h) (k h (g @@ (a1, c)) = 
                    k h (g @@ (a2, c)))
          (g <<(a1, c),(a2,c)>>) 
          (identity h) eq_refl (@ap2 _ _ _ k _ _ _ _)
          x1 x1'
          (Id_ind1_hom H x1 x1')).
Defined.

Definition pi_idR_gen_Id_ind (G H : Type) (h:H)
           (f : G → H → G)
           (P : forall g g', 
                   (piω (g = g') ** piω (h=h)) ==>
                   piω (f g h = f g' h))
           (g g' : | piω G |)
           (P1_23_hom := fun e e' h h' =>
                        (P g g' << (e,h) , (e',h')>>)) 
           (e e' : |piω G [g,g']|)
           (P_refl : Id_ind1 
                       (fun x y => P1_23_hom e e' eq_refl eq_refl @@ (x,y)) eq_refl
                       (fun xf xf' => P1_23_hom e e' eq_refl eq_refl << (xf,_),( xf',_) >>)) 
           v v'
           (Y  : v = f g h)
           (Y' : f g' h = v') 
           (apP1_23 :=fun e e' =>  
                    piCompGen1 (piω G) (piω H) (piω G) f h
                                 (fun x y => @P g g' @@ (x,y)) v v' Y Y' e e' (P1_23_hom e e' _ _)) :
  Id_ind1 (λ X Y, apP1_23 e e' @@ (X,Y)) eq_refl
         (fun xf xf' => apP1_23 e e' << (xf,_) , (xf',_) >>).
  pose (@transport_GHomR (piω G) _ (f g' h) v' Y' °° 
                         (P g g')).
  simpl.
  apply (@append_left_id_ind1
          (g = g') (h = h) (f g h = v')
          (v = f g h)  (v = v') 
          g0 Y eq_refl concat
          e e').

  exact (@append_right_id_ind1
          (g = g') (h = h) (f g h = f g' h) (f g' h = v')
          (f g h = v') (P g g') Y' eq_refl concat e e' P_refl).
Defined.
 

Definition pi_idR_gen_Id_ind_simple (G H : Type) (h:H)
           (f : G → H → G)
           (P : forall g g', 
                   (piω (g = g') ** piω (h=h)) ==>
                   piω (f g h = f g' h))
           (g g' : | piω G |)
           (P_refl : Id_ind1 f h (fun e e' => P e e'))
           (idR : ∀ (g : | piω G |), f g h = g)
 (hComp := higher_composable_idR_gen h idR g g') 
 (idR2 := pi_idR_gen_law f (fun g g' x y => (@P g g') @@ (x ,y)) (Id_ind1_refl P_refl) idR g g' :
            ∀ e,
                   |piω (g = g') [hComp (P g g' @@ (e,eq_refl)), e]|) 
 (apP := fun e e' => piCompGen1 (piω G) (piω H) (piω G) f h
                                (fun x y => (@P g g')@@ (x,y)) _ _
                                (inverse (idR g)) (idR g') e e' (P g g' <<(e,eq_refl),(e',eq_refl)>>)) :
  Id_ind1 (λ e e', hComp (P g g' @@ (e,e'))) eq_refl apP.
  pose (P_hom_refl := Id_ind1_hom P_refl g g').
  apply mkId_ind1.
- intros. unfold apP, piCompGen1. simpl. 
  pose (Id_ind1_refl P_hom_refl x1). simpl in *. unfold identity. simpl.
  rewrite e. reflexivity.
 - intros e e'.
   apply pi_idR_gen_Id_ind.
   exact (Id_ind1_hom P_hom_refl e e').
Defined.


CoFixpoint pi_idR_gen (G H : Type) (h:H)
           (f : G → H → G)
           (P : forall g g', 
                   (piω (g = g') ** piω (h=h)) ==>
                   piω (f g h = f g' h))                  
           (idR : ∀ (g : | piω G |), f g h = g)
           (g g' : | piω G |)
           (hComp := higher_composable_idR_gen h idR g g') 
           (e e' : |piω G[g,g']|)
           (P_refl : Id_ind1 f h (fun e e' => P e e'))
           (comp : forall e e',
                      (piω (e = e') ** piω (eq_refl = eq_refl)) ==> piω (P g g' @@ (e,_) = P g g' @@ (e',_))
            := fun e e' => P g g' << (e,eq_refl), (e',eq_refl) >>) 
           (idR2 := pi_idR_gen_law f (fun g g' X Y => (@P g g')@@(X,Y)) (Id_ind1_refl P_refl) idR g g' :
            ∀ e,
                   |piω (g = g') [hComp (P g g' @@ (e,eq_refl)), e]|)
  (hComp' := fun e e' =>
               @higher_composable_idR_gen2 G H h f (fun g g' X Y => (@P g g')@@(X,Y))
                                             (Id_ind1_refl P_refl) idR g g' e e'
                                     (comp  e e')) :
  @compoIdR_H
    (((piω G) [g, g']) [e,e'])
    (((piω H) [h, h]) [@identity (piω H) h,@identity (piω H) h]) (identity _) _
    {| compo := hComp' e e'|}.
   intros.
   pose (apPV := fun e e' =>piCompGen1 (piω G) (piω H) (piω G) f h
                                (fun x y => (@P g g')@@ (x,y)) _ _
                                (inverse (idR g)) (idR g') e e' (P g g' <<(e,eq_refl),(e',eq_refl)>>)).

   pose (apP_refl := pi_idR_gen_Id_ind_simple P g g' P_refl idR).
   refine (mkCompoIdR_H _ _ _ _ _).   
   - refine (pi_idR_gen_law (fun X Y => hComp (@P _ _ @@ (X,Y)))  (fun e e' x y => apPV e e' @@ (x,y)) 
          (Id_ind1_refl apP_refl) idR2 e e').

   - intros ee ee'.
     exact (pi_idR_gen (g = g') (h = h) eq_refl
          (fun X Y => hComp (@P _ _ @@ (X,Y))) apPV idR2 e e' ee ee' apP_refl).
Defined.


CoFixpoint pi_idR_gen_Id_ind_init (G H G': Type) (h:H)
           (f : G → H → G')
           (P : forall g g', 
                   (piω (g = g') ** piω (h=h)) ==>
                   piω (f g h = f g' h)   
           := fun x1 x1' => piComp_V_ f
              x1 x1' h h) :
      Id_ind1 f h P.
apply mkId_ind1. intros. reflexivity.
intros g g'.
exact (pi_idR_gen_Id_ind_init (g = g') (h = h) _ eq_refl (fun X Y => P g g' @@ (X,Y))).
Defined.

Definition pi_idR_gen_simple (G H : Type) (h:H)
           (f : G → H → G)
           (P : forall g g', 
                   (piω (g = g') ** piω (h=h)) ==>
                   piω (f g h = f g' h)   
           := fun x1 x1' => piComp_V_ f
              x1 x1' h h)                  
           (idR : ∀ (g : | piω G |), f g h = g)
           (g g' : | piω G |)
           (hComp := higher_composable_idR_gen h idR g g') 
           (e e' : |piω G[g,g']|)          
:=
  pi_idR_gen P idR g g' e e' (pi_idR_gen_Id_ind_init h f).

CoFixpoint pi_CompoIdR (T : Type) : @compoIdR (piω T) _.
apply mkCompoIdr.
- intros. refine (mkCompoIdR_H _ _ _ _ _).
  + intros. exact (idpath_R g). 
  + intros g g'. refine (mkCompoIdR_H _ _ _ _ _).
    * intros e. unfold compo. simpl.
      exact (pi_idR_gen_law concat (fun g g'  e e' => concat_LR e e') (fun _ => eq_refl) idpath_R g g' e).
    * intros e e'.
      exact (pi_idR_gen_simple eq_refl concat idpath_R g g' e e').
- intros. apply pi_CompoIdR.
Defined.


Definition higher_composable_idL_gen {G H : Type} (g:G)
           {f : G → H → H} (idL : ∀ (h : | piω H |), f g h = h)
           (h h' : | piω H |) :
  f g h = f g h' -> h = h'
  := fun E => inverse (idL h) @ (E @ idL h').

Definition pi_idL_gen_law (G H: Type) (g:G)
           (f : G → H → H)
           (P : forall {h h'}, g = g -> h = h' -> f g h = f g h')                  
           (P_refl : forall {h}, P (eq_refl g) (eq_refl h) = eq_refl _) 
           (idL : ∀ (h : | piω H |), f g h = h)
           (h h' : | piω H |)
           (hComp := higher_composable_idL_gen g idL h h') 
           (e : |piω H[h,h']|)  :
           hComp (P (eq_refl g) e) = e. 
  unfold hComp, higher_composable_idL_gen.
  destruct e. simpl in *. 
  rewrite P_refl. rewrite idpath_L. rewrite inverse_inv_L. reflexivity.
Defined.

Definition piCompGen1' (T U V: ωPreCat) (f : |T| -> | U| -> |V|)  
           (g: |T|) {x y:|U| }
           (P : (|T[g,g]|) -> (|U[x,y]|) -> |V[f g x, f g y]|)
           (v1:|V|) (v2:|V|)
           (law1 : |V [v1, f g x]|)  (law2 : |V [f g y, v2]|)
           (e e' : |U[x,y]|) 
           (compV : (T[g,g][identity _ , identity _] ** U[x,y][e,e']) ==>
                                              V[_,_][P (identity _) e, P (identity _) e']) : 
  (T[g,g][identity _ , identity _] ** U[x,y][e,e']) ==>
   V [v1, v2][(law2 ° P (identity _) e) ° law1, (law2 ° P (identity _) e') ° law1]
:= append_left law1 (law2 ° P _ e) (law2 ° P _ e') 
   °° (append_right (P _ e) (P _ e') law2
     °° compV). 

Definition higher_composable_idL_gen2  (G H: Type) (g:G)
           (f : G → H → H)
           (P : forall {h h'}, g = g -> h = h' -> f g h = f g h')                  
           (P_refl : forall {h}, P (eq_refl g) (eq_refl h) = eq_refl _) 
           (idL : ∀ (h : | piω H|), f g h = h)
           (h h' : | piω H |)
           (hComp := higher_composable_idL_gen g idL h h') 
           (e e' : |piω H[h,h']|)
           (compV : (piω (eq_refl g = eq_refl g) ** piω (e = e')) ==> piω (P _ e = P _ e')) 
           (idL2 := pi_idL_gen_law f (@P) (@P_refl) idL h h' : ∀ e,
                   |piω (h = h') [hComp (P _ e), e]|) 
           (compV2 := piCompGen1' (piω G) (piω H) (piω H) f g
                                 (@P h h') _ _
                                 (inverse (idL h)) (idL h') e e' compV)
: (piω (eq_refl g = eq_refl g) ** piω (e = e')) ==> piω (e = e')
:= transport_GHomL (inversE (idL2 e)) °° (transport_GHomR (idL2 e') °° compV2).

CoInductive Id_ind1' (A B C: Type) (f : A -> B -> C) (a:A)
            (p : forall x1 x1',
                   (piω (a=a) ** piω (x1 = x1'))
                     ==> piω (f a x1 = f a x1')) : Type :=
  mkId_ind1' :  
    (∀ x1, p x1 x1 @@ (eq_refl,eq_refl) = eq_refl) ->
    (∀ x1 x1',
       @Id_ind1' _ _ _ (fun x y => p x1 x1' @@ (x,y)) eq_refl
                (fun (f1 f1':x1=x1')  =>(p x1 x1') << (_,f1) , (_ , f1')>>))
    -> Id_ind1' f a p.

Definition Id_ind1'_refl (A B C: Type) (f : A -> B -> C) (a:A)
            (p : forall x1 x1',
                   (piω (a=a) ** piω (x1 = x1'))
                     ==> piω (f a x1 = f a x1'))
                       (e:Id_ind1' f a p) :
  ∀ x1  , p x1 x1 @@ (eq_refl, eq_refl) = eq_refl.
  destruct e. exact e.
Defined.

Definition Id_ind1'_hom (A B C: Type) (f : A -> B -> C) (a:A)
            (p : forall x1 x1',
                   (piω (a=a) ** piω (x1 = x1'))
                     ==> piω (f a x1 = f a x1'))
            (e:Id_ind1' f a p)  :
∀ x1 x1',
       @Id_ind1' _ _ _ (fun x y => p x1 x1' @@ (x,y)) eq_refl
                (fun (f1 f1':x1=x1')  =>(p x1 x1') << (_,f1) , (_,f1')>>).
  destruct e. exact i.
Defined.

CoFixpoint append_right_id_ind1' (A  C' C'' D E: Type)
           (g : (piω A ** piω C') ==> piω C'') 
           (h : |piω D|) (a:|piω A|)
           (k : C'' -> D -> E)
           (c1 c2 : C') 
           (H : Id_ind1'
                  (λ (x : a = a) (y : c1=c2),
                   (g << (a, c1), (a, c2) >>) @@ (x, y)) eq_refl
                  (λ (f1 f1' : c1 = c2),
                   (g << (a,c1), (a, c2) >>)
                      << (eq_refl, f1), (eq_refl, f1') >>)) 
           (compoK := piComp_V k)
 : Id_ind1' (fun X X' => (identity h) ° 
                   (g << (a,c1),(a, c2)>> @@ (X,X'))) eq_refl
         (fun (x1 x1' : |piω (c1 = c2)|)  =>
               (@append_right 
                  (piω (g @@ (a, c1) = g @@ (a, c2)))
                  (piω (h= h))
                  (piω (_ = _))
                  ((g << (a, c1), (a, c2) >>) 
                     @@ (eq_refl,x1))
                  ((g << (a, c1), (a, c2) >>) 
                     @@ (eq_refl,x1'))
                    (identity h) _)
         °° ((g <<(a,c1),(a,c2)>>) 
               <<(eq_refl,x1),(eq_refl,x1')>>)).
apply mkId_ind1'. 
- intros. pose (Id_ind1'_refl H x1). 
  simpl in *. rewrite e. reflexivity.
- intros. simpl. 
  exact (@append_right_id_ind1'
          (a = a)  (c1 = c2)
          (g @@ (a, c1)  = g @@ (a, c2))
          (h = h) (k (g @@ (a, c1)) h = 
                    k (g @@ (a, c2)) h)
          (g <<(a, c1),(a,c2)>>) 
          (identity h) eq_refl (@ap2 _ _ _ k _ _ _ _)
          x1 x1' 
          (Id_ind1'_hom H x1 x1')).
Defined.

CoFixpoint append_left_id_ind1' (A C' C'' D E: Type)
           (g : (piω A ** piω C') ==> piω C'') 
           (h : |piω D|) (a:|piω A|)
           (k : D -> C'' -> E)
           (c1 c2 : C')  
           (H : Id_ind1'
              (λ (x : a = a) (y : c1 = c2),
                 (g << (a, c1), (a, c2) >>) @@ (x, y)) eq_refl
              (λ (f1 f1' : c1 = c2) ,
                 (g << (a, c1), (a, c2) >>) <<
                     (eq_refl,f1), (eq_refl,f1') >>)) 
           (compoK := piComp_V k)
 : Id_ind1' (fun X X' => (g << (a,c1),(a,c2)>> @@ (X,X')) 
                         ° (identity h)) eq_refl
           (fun (x1 x1' : |piω (c1 = c2)|)  =>
                (@append_left
                  (piω (h= h))
                  (piω (g @@ (a, c1) = g @@ (a, c2)))
                  (piω (_ = _))
                  (identity h)
                  ((g << (a, c1), (a, c2) >>) 
                     @@ (eq_refl,x1))
                  ((g << (a, c1), (a, c2) >>) 
                     @@ (eq_refl,x1'))
                     _)
         °° ((g <<(a, c1),(a,c2)>>) 
               <<(eq_refl,x1),(eq_refl,x1')>>)).
apply mkId_ind1'. 
- intros. pose (Id_ind1'_refl H x1). 
  simpl in *. rewrite e. reflexivity.
- intros. simpl. 
  exact (@append_left_id_ind1'
          (a = a) (c1 = c2) 
          (g @@ (a, c1)  = g @@ (a, c2))
          (h = h) (k h (g @@ (a, c1)) = 
                    k h (g @@ (a, c2)))
          (g <<(a, c1),(a,c2)>>) 
          (identity h) eq_refl (@ap2 _ _ _ k _ _ _ _)
          x1 x1'
          (Id_ind1'_hom H x1 x1')).
Defined.

Definition pi_idL_gen_Id_ind (G H : Type) (g:G)
           (f : G → H → H)
           (P : forall h h', 
                   (piω (g = g) ** piω (h=h')) ==>
                   piω (f g h = f g h'))
           (h h' : | piω H |)
           (P1_23_hom := fun e e' H H' =>
                        (P h h' << (e,H) , (e',H')>>)) 
           (e e' : |piω H[h,h']|)
           (P_refl : Id_ind1' 
                       (fun x y => P1_23_hom eq_refl eq_refl e e' @@ (x,y)) eq_refl
                       (fun xf xf' => P1_23_hom eq_refl eq_refl e e' << (_,xf),(_,xf') >>)) 
           v v'
           (Y  : v = f g h)
           (Y' : f g h' = v') 
           (apP1_23 :=fun e e' =>  
                    piCompGen1' (piω G) (piω H) (piω H) f g
                                 (fun x y => @P h h' @@ (x,y)) v v' Y Y' e e' (P1_23_hom _ _ e e')) :
  Id_ind1' (λ X Y, apP1_23 e e' @@ (X,Y)) eq_refl
         (fun xf xf' => apP1_23 e e' << (_,xf) , (_,xf') >>).
  pose (@transport_GHomR (piω H) _ (f g h') v' Y' °° 
                         (P h h')).

  apply (@append_left_id_ind1'
          (g = g) (h = h') (f g h = v')
          (v = f g h)  (v = v') 
          g0 Y eq_refl concat
          e e').

  exact (@append_right_id_ind1'
          (g = g) (h = h') (f g h = f g h') (f g h' = v')
          (f g h = v') (P h h') Y' eq_refl concat e e' P_refl).
Defined.
 

Definition pi_idL_gen_Id_ind_simple (G H : Type) (g:G)
           (f : G → H → H)
           (P : forall h h', 
                   (piω (g = g) ** piω (h=h')) ==>
                   piω (f g h = f g h'))
           (h h' : | piω H |)
           (P_refl : Id_ind1' f g (fun e e' => P e e'))
           (idL : ∀ (h : | piω H |), f g h = h)
 (hComp := higher_composable_idL_gen g idL h h') 
 (idR2 := pi_idL_gen_law f (fun h h' x y => (@P h h') @@ (x ,y)) (Id_ind1'_refl P_refl) idL h h' :
            ∀ e,  |piω (h = h') [hComp (P h h' @@ (eq_refl,e)), e]|) 
 (apP := fun e e' => piCompGen1' (piω G) (piω H) (piω H) f g
                                (fun x y => (@P h h')@@ (x,y)) _ _
                                (inverse (idL h)) (idL h') e e' (P h h' <<(eq_refl,e),(eq_refl,e')>>)) :
  Id_ind1' (λ e e', hComp (P h h' @@ (e,e'))) eq_refl apP.
  pose (P_hom_refl := Id_ind1'_hom P_refl h h').
  apply mkId_ind1'.
- intros. unfold apP, piCompGen1'. simpl. 
  pose (Id_ind1'_refl P_hom_refl x1). simpl in *. unfold identity. simpl.
  rewrite e. reflexivity.
 - intros e e'.
   apply pi_idL_gen_Id_ind.
   exact (Id_ind1'_hom P_hom_refl e e').
Defined.


CoFixpoint pi_idL_gen (G H : Type) (g:G)
           (f : G → H → H)
           (P : forall h h', 
                   (piω (g = g) ** piω (h=h')) ==>
                   piω (f g h = f g h'))                  
           (idL : ∀ (h : | piω H|), f g h = h)
           (h h' : | piω H |)
           (hComp := higher_composable_idL_gen g idL h h') 
           (e e' : |piω H[h,h']|)
           (P_refl : Id_ind1' f g (fun e e' => P e e'))
           (comp : forall e e',
                     (piω (eq_refl = eq_refl)**piω (e = e') ) ==>
                              piω (P h h' @@ (_,e) = P h h' @@ (_,e'))
            := fun e e' => P h h' << (eq_refl,e), (eq_refl,e') >>) 
           (idL2 := pi_idL_gen_law f (fun h h' X Y => (@P h h')@@(X,Y)) (Id_ind1'_refl P_refl) idL h h' :
            ∀ e,
                   |piω (h = h') [hComp (P h h' @@ (eq_refl,e)), e]|)
  (hComp' := fun e e' =>
               @higher_composable_idL_gen2 G H g f (fun h h' X Y => (@P h h')@@(X,Y))
                                             (Id_ind1'_refl P_refl) idL h h' e e'
                                     (comp  e e')) :
  @compoIdL_H
    (((piω G) [g, g]) [@identity (piω G) g,@identity (piω G) g])
    (((piω H) [h, h']) [e,e']) (identity _) _
    {| compo := hComp' e e'|}.
   intros.
   pose (apPV := fun e e' =>piCompGen1' (piω G) (piω H) (piω H) f g
                                (fun x y => (@P h h')@@ (x,y)) _ _
                                (inverse (idL h)) (idL h') e e' (P h h' <<(eq_refl,e),(eq_refl,e')>>)).

   pose (apP_refl := pi_idL_gen_Id_ind_simple P h h' P_refl idL).
   refine (mkCompoIdL_H _ _ _ _ _).   
   - refine (pi_idL_gen_law (fun X Y => hComp (@P _ _ @@ (X,Y)))  (fun e e' x y => apPV e e' @@ (x,y)) 
          (Id_ind1'_refl apP_refl) idL2 e e').

   - intros ee ee'.
     exact (pi_idL_gen (g = g) (h = h') eq_refl
          (fun X Y => hComp (@P _ _ @@ (X,Y))) apPV idL2 e e' ee ee' apP_refl).
Defined.


CoFixpoint pi_idL_gen_Id_ind_init (G H G': Type) (g:G)
           (f : G → H → G')
           (P : forall h h', 
                   (piω (g = g) ** piω (h=h')) ==>
                   piω (f g h = f g h')   
           := fun x1 x1' => piComp_V_ f
              g g x1 x1') :
      Id_ind1' f g P.
apply mkId_ind1'. intros. reflexivity.
intros h h'.
exact (pi_idL_gen_Id_ind_init (g = g) (h = h') _ eq_refl (fun X Y => P h h' @@ (X,Y))).
Defined.

Definition pi_idL_gen_simple (G H : Type) (g:G)
           (f : G → H → H)
           (P : forall h h', 
                   (piω (g = g) ** piω (h=h')) ==>
                   piω (f g h = f g h')   
           := fun x1 x1' => piComp_V_ f g g x1 x1')                  
           (idL : ∀ (h : | piω H|), f g h = h)
           (h h' : | piω H |)
           (hComp := higher_composable_idL_gen g idL h h') 
           (e e' : |piω H[h,h']|)          
:=
  pi_idL_gen P idL h h' e e' (pi_idL_gen_Id_ind_init g f).

CoFixpoint pi_CompoIdL (T : Type) : @compoIdL (piω T) _.
apply mkCompoIdL.
- intros. refine (mkCompoIdL_H _ _ _ _ _).
  + intros. exact (idpath_L h). 
  + intros h h'. refine (mkCompoIdL_H _ _ _ _ _).
    * intros e. unfold compo. simpl.
      exact (pi_idL_gen_law concat (fun h h' e e' => concat_LR e e')
                            (fun _ => eq_refl) idpath_L h h' e).
    * intros e e'.
      exact (pi_idL_gen_simple eq_refl concat idpath_L h h' e e').
- intros. apply pi_CompoIdL.
Defined.


CoInductive Id_ind'' : ∀ (A B: ωPreCat) (f : A ==> B), Type :=
  mkId_ind'' : ∀ (A B: ωPreCat) (f : A ==> B),
               (∀ x, (f << x,x >>) @@ identity x = identity (f @@ x)) ->
               (∀ x y, Id_ind'' (A[x,y]) (B[f @@ x, f @@ y]) (f << x,y >>)) ->
               Id_ind'' A B f.

Definition Id_ind''_here (A B: ωPreCat) (f : A ==> B) (H : Id_ind'' A B f) x :
               (f << x,x >>) @@ identity x = identity (f @@ x).
destruct H. apply e.
Defined.
  
Definition Id_ind''_hom (A B: ωPreCat) (f : A ==> B) (H : Id_ind'' A B f) x y :
               Id_ind'' (A[x,y]) (B[f @@ x, f @@ y]) (f << x,y >>).
destruct H. apply i.
Defined.

Definition transport_GHomL_eq_J_i_eq_gen_eq (T T':Type) (f g : piω T ==> piω T')
           (x y : T) (e : forall x, f @@ x = g @@ x)
           (f_refl: Id_ind'' _ _ f) (g_refl: Id_ind'' _ _  g) E :
          (@transport_GHomL_eq_J (piω T') _ _ _ (inverse (e x)) °°
              (@transport_GHomR_eq_J (piω T') _ _ _  (e y) °° (f << x,y >>))) @@ E =
          (g << x, y >>) @@ E.
  destruct E. simpl. repeat rewrite transport_paths_r.
  unfold identity; simpl. setoid_rewrite (Id_ind''_here f_refl x).
  setoid_rewrite (Id_ind''_here g_refl x). apply inverse_inv_L.
Defined.

CoFixpoint Id_ind''_append_right (C C'' D E: Type)
           (g : piω C ==> piω C'')
           (h : |piω D|)
           (k : C'' -> D -> E)
           (a1 a2 : C)
           (x1 x2 : | piω (a1= a2)|)
           (H : Id_ind'' (piω (x1= x2)) (piω ((g << a1, a2 >>) @@ x1 =
                                                          (g << a1, a2 >>) @@ x2))
                        ((g << a1, a2 >>) << x1, x2 >>))
           (compoK := piComp_V k)
 : Id_ind''  (piω (x1 = x2))
            (piω (identity h ° ((g << a1, a2 >>) @@ x1) =
                        identity h ° ((g << a1, a2 >>) @@ x2)))
            ((@append_right
                  (piω (g @@ a1= g @@ a2))
                  (piω (h= h))
                  (piω (_ = _))
                  ((g << a1,a2 >>) @@ x1)
                  ((g << a1,a2 >>) @@ x2)
                  (identity h) _)
         °° ((g <<a1,a2>>) <<x1,x2>>)).

apply mkId_ind''. intro y1; simpl.
setoid_rewrite (Id_ind''_here H y1). reflexivity.
intros y1 y2. simpl.
exact (Id_ind''_append_right (a1 = a2) (g @@ a1 = g @@ a2) (h = h) (k (g @@ a1) h = k (g @@ a2) h)
                           (g << a1, a2 >>) (identity h) (@ap2 _ _ _ k _ _ _ _) x1 x2
     y1 y2 (Id_ind''_hom H y1 y2)).
Defined.

CoFixpoint Id_ind''_append_left (C C'' D E: Type)
           (g : piω C ==> piω C'')
           (h : |piω D|)
           (k : D -> C'' -> E)
           (a1 a2 : C)
           (x1 x2 : | piω (a1= a2)|)
           (H : Id_ind'' (piω (x1= x2)) (piω ((g << a1, a2 >>) @@ x1 =
                                                          (g << a1, a2 >>) @@ x2))
                        ((g << a1, a2 >>) << x1, x2 >>))
           (compoK := piComp_V k)
 : Id_ind''  (piω (x1 = x2))
            (piω (((g << a1, a2 >>) @@ x1) ° identity h =
                        ((g << a1, a2 >>) @@ x2) ° identity h))
            ((@append_left
                  (piω (h= h))
                  (piω (g @@ a1= g @@ a2))
                  (piω (_ = _))
                  (identity h)
                  ((g << a1,a2 >>) @@ x1)
                  ((g << a1,a2 >>) @@ x2)
                   _)
         °° ((g <<a1,a2>>) <<x1,x2>>)).
apply mkId_ind''. intro y1; simpl.
setoid_rewrite (Id_ind''_here H y1). reflexivity.
intros y1 y2. simpl.
exact (Id_ind''_append_left (a1 = a2) (g @@ a1 = g @@ a2) (h = h) (k h (g @@ a1) = k h (g @@ a2))
                           (g << a1, a2 >>) (identity h) (@ap2 _ _ _ k _ _ _ _) x1 x2
     y1 y2 (Id_ind''_hom H y1 y2)).
Defined.

CoFixpoint transport_GHomL_eq_J_i_eq_gen (T T':Type) (f g : piω T ==> piω T')  
           (x y : T) (e : forall x, f @@ x = g @@ x) 
           (f_refl: Id_ind'' _ _ f) (g_refl: Id_ind'' _ _  g) :
  @GHom_eq (piω T [x,y]) (piω T' [g @@ x, g @@ y]) 
          (@transport_GHomL_eq_J (piω T') _ _ _ (inverse (e x)) °° 
              (@transport_GHomR_eq_J (piω T') _ _ _ (e y) °° (f << x,y >>)))
          (g << x, y >>).
refine (@mkGHom_eq_J (piω T [x, y]) (piω T' [g @@ x, g @@ y]) _ _ _ _).
exact (transport_GHomL_eq_J_i_eq_gen_eq x y e f_refl g_refl). 
intros. apply (transport_GHomL_eq_J_i_eq_gen (x = y) (g @@ x = g @@ y) 
              (@transport_GHomL_eq_J (piω T') _ _ _ (inverse (e x)) °° 
               (@transport_GHomR_eq_J (piω T') _ _ _ (e y) °° (f << x,y >>)))
              (g << x, y >>) x0 y0 
             (transport_GHomL_eq_J_i_eq_gen_eq x y e f_refl g_refl)).

clear x0 y0. apply mkId_ind''. intro x1; simpl.
setoid_rewrite (Id_ind''_here (Id_ind''_hom f_refl x y) x1). reflexivity. 
intros x1 y1. simpl.

apply mkId_ind''. intro x2; simpl in *.
pose (Id_ind''_here (Id_ind''_hom (Id_ind''_hom f_refl x y) x1 y1) x2).
setoid_rewrite e0.
reflexivity. 
intros.
apply (@Id_ind''_append_left (x = y) (f @@ x = g @@ y)  (g @@ x = f @@ x) (g @@ x = g @@ y)
     (@transport_GHomR_eq_J (piω T') _ _ _  (e y) °° (f << x,y >>))
     (transport (λ X : T', g @@ x = X) 
               (inverse (e x)) (identity (g @@ x))) concat x1 y1 x0 y0).
exact (@Id_ind''_append_right (x = y) (f @@ x = f @@ y) (f @@ y = g @@ y) (f @@ x = g @@ y)
                             (f << x,y >>)
     (transport (λ X : T', f @@ y = X) (e y) (identity (f @@ y))) concat x1 y1 x0 y0
     (Id_ind''_hom (Id_ind''_hom (Id_ind''_hom f_refl x y) x1 y1) x0 y0)).

exact (Id_ind''_hom g_refl _ _). 
Defined.


CoFixpoint append_left_id_ind'' {T T' U : Type}
           (k : T ->  T' -> U)
           (compK := piComp_V k)
           (f : |piω T|) (x0 y0 : |piω T'|) (x1 y1 : |piω (x0 = y0)|) :
  Id_ind'' (piω (x1 = y1)) (piω (x1 ° (identity f) = y1 ° (identity f)))
          (append_left (identity f) x1 y1).
apply mkId_ind''. intro H. destruct H. reflexivity. 
intros. apply (append_left_id_ind'' (f = f) (x0 = y0) (k f x0 = k f y0) (@ap2 _ _ _ k _ _ _ _)).
Defined.

Definition transport_GHomL_eq_J_id_ind {T:Type} {x y z : T } (f : x = y) :
  Id_ind'' (piω (y = z)) (piω (x = z)) (@transport_GHomL (piω T) x y z  f).
apply mkId_ind''. intro H; destruct H. reflexivity.
intros. apply mkId_ind''. intro H; destruct H. reflexivity.
intros. simpl. apply (@append_left_id_ind'' (x = y) (y = z) (x = z) concat f).
Defined.

Definition transport_GHomL_eq_J_eq_fun {T:Type} {x y z : T } (f : x = y) H:
   (@transport_GHomL_eq_J (piω T) x y z f) @@ H =
   (@transport_GHomL (piω T) x y z f) @@ H :=  
  concat_R H (transport_paths_r f eq_refl). 

Definition transport_GHomL_eq_J_eq {T:Type} {x y z : T } (f : x = y) :
  GHom_eq _ _ (@transport_GHomL_eq_J (piω T) x y z f) (@transport_GHomL (piω T) x y z f).
apply (mkGHom_eq_J _ _ (fun e => transport_GHomL_eq_J_eq_fun f e)).
intros. apply transport_GHomL_eq_J_i_eq_gen.
apply transport_GHomL_eq_J_id_ind. 
apply transport_GHomL_eq_J_id_ind.
Defined.

CoFixpoint append_right_id_ind'' {T' T U : Type}
           (k : T' ->  T -> U)
           (compK := piComp_V k)
           (f : |piω T|) (x0 y0 : |piω T'|) (x1 y1 : |piω (x0 = y0)|) :
  Id_ind'' (piω (x1 = y1)) (piω ((identity f) ° x1 = (identity f) ° y1))
          (append_right x1 y1 (identity f)).
apply mkId_ind''. intro H. destruct H. reflexivity.
intros. apply (append_right_id_ind'' (x0 = y0) (f = f) (k x0 f = k y0 f) (@ap2 _ _ _ k _ _ _ _)).
Defined.

Definition transport_GHomR_eq_J_id_ind {T:Type} {x y z : T } (f : x = y) :
  Id_ind'' (piω (z = x)) (piω (z = y)) (@transport_GHomR (piω T) z x y f).
apply mkId_ind''. intro H; destruct H. reflexivity.
intros. apply mkId_ind''. intro H; destruct H. reflexivity.
intros. simpl. apply (@append_right_id_ind'' (z = x) (x = y) (z = y) concat f).
Defined.

Definition transport_GHomR_eq_J_eq_fun {T:Type} {x y z : T } (f : x = y) H:
   (@transport_GHomR_eq_J (piω T) z x y f) @@ H =
   (@transport_GHomR (piω T) z x y f) @@ H :=  
  concat_L H (transport_paths_r f eq_refl). 

Definition transport_GHomR_eq_J_eq {T:Type} {x y z : T } (f : x = y) :
  GHom_eq _ _ (@transport_GHomR_eq_J (piω T) z x y f) (@transport_GHomR (piω T) z x y f).
apply (mkGHom_eq_J _ _ (fun e => transport_GHomR_eq_J_eq_fun f e)).
intros. apply transport_GHomL_eq_J_i_eq_gen.
apply transport_GHomR_eq_J_id_ind. 
apply transport_GHomR_eq_J_id_ind.
Defined.

CoFixpoint pi_transport_is_canonical T : @transport_is_canonical (piω T) _.
apply mkTransport_compat.
- intros. apply transport_GHomL_eq_J_eq.
- intros. apply transport_GHomR_eq_J_eq.
- intros. apply pi_transport_is_canonical.
Defined.

(* piω T is a ωcat*)

Instance pi_IsOmegaCategory (T : Type) : IsOmegaCategory (piω T) :=
  {| _transport := _;
     _transport_is_canonical := pi_transport_is_canonical T;
     _idR := pi_CompoIdR T ;
     _idL := pi_CompoIdL T;
     _compo_ωFunctor := pi_compo_ωFunctor T;
     _assoc := pi_associativity T
|}.

Definition piW T : ωcat := (piω T; pi_IsOmegaCategory T).


Definition picellpath_fun (T : Type) (x y : |piω T|)
           (e : |(piω T)[x, y]|) : x = y := e.

(* piω T is a univalent ωcat*)

Definition piIsUnivalent_retr (T:Type) (x y : T) :
  section (@picellpath_fun _ x y) (cell_path (piW T) (y:=y)).
  intro e. destruct e. reflexivity.
Defined.
  
Definition piIsUnivalent_sect (T:Type) (x y : T) :
 section (cell_path (piW T) (y:=y)) (@picellpath_fun _ x y).
  red. intros. destruct x0. reflexivity.
Defined.

CoFixpoint piIsUnivalent (T:Type) : IsUnivalent (piW T).
apply mkIsUnivalent.
- intros. 
  apply (BuildIsEquiv (@piIsUnivalent_retr _ x y) 
                      (@piIsUnivalent_sect _ x y)).
  intro e. destruct e. reflexivity.
- intros x y. exact (piIsUnivalent (x = y)).
Defined.



