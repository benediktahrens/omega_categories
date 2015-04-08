Add LoadPath "." as OmegaCategories.
Require Export Unicode.Utf8_core.
Require Import path GType omega_categories. 

(** a stronger notion of commutative diagrams **)
(** which is used to construct the fundamental groupoid **)

(* Definition of internal transports *)

Notation "G [ A , B ]" := (hom' G A B) (at level 80).
Notation "| G |" := (objects G.1) (at level 80).
Notation "A ** B" := (prod' A B) (at level 90).
Notation " A ==> B " := (GHom A.1 B.1) (at level 90).

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

CoInductive transport_eq_compat_type : ∀ G (_trans : _transport_eq G), Type :=
  mkTransport_eq_compat_type : ∀ (G : ωPreCat) (_trans : _transport_eq G),
  (∀ n x x' y (c : cell n (G[x,y])) (e : x = x'),
   transport (fun X => cell _ (G [X,_])) e c = cellGHom _ _ _ (transport_GHomL_eq_here (inverse e)) c)
  ->
  (∀ n x y y' (c : cell n (G[x,y])) (e : y = y'),
     transport (fun X => cell _ (G [_,X])) e c = cellGHom _ _ _ (transport_GHomR_eq_here e) c) ->
  (∀ {x y : |G| },  @transport_eq_compat_type (G[x,y]) _) ->
   @transport_eq_compat_type G _.

Class transport_eq (G:ωPreCat) := mkTransport_eq
{
  _transport :> _transport_eq G;
  _transport_is_canonical : transport_eq_compat_type _ _transport
}.

Definition transport_GHom_eq_hom' (G:ωPreCat) (_transport : transport_eq G)
           {x y : |G| } : transport_eq  (G[x,y]).
  econstructor. destruct _transport as [H H_can]. destruct H_can. apply t.
Defined.

Hint Extern 1 (transport_eq (?G[?x,?z])) => apply (transport_GHom_eq_hom' _) : typeclass_instances.


CoInductive commutativeTriangle_tranport  (A B C : ωPreCat) {_transport : transport_eq C}
                             (F : A ==> B) (G : B ==> C) (H : A ==> C)  : Type :=
  mkCommutativeTriangle_tranport : ∀ (comm : ∀ x, (G °° F) @@ x =  H @@ x),
                (∀ x y, @commutativeTriangle_tranport (A [x, y]) (B [F @@ x, F @@ y])
                                   (C[H @@ x, H @@ y]) _
                                   (F << x , y >>) 
                                   (transport_GHomL_eq_here (inverse (comm x)) °°
                                     (transport_GHomR_eq_here (comm y) °°
                                        (G << F @@ x , F @@ y >>)))
                                   (H << x , y >>)) ->
                 @commutativeTriangle_tranport A B C _ F G H.

CoFixpoint CommutativeTriangle_tranport G `{transport_eq G} :
  commutativeTriangle G :=
  mkCommutativeTriangle
    (fun A B => commutativeTriangle_tranport A B G)
    (fun x y => CommutativeTriangle_tranport (G[x,y])).

Definition generalTriangle G `{transport_eq G} :=
  {| _commutativeTriangle := CommutativeTriangle_tranport G |}.

(* commutative square *)

CoInductive commutativeSquare_tranport  (A B C D : ωPreCat) {_transport : transport_eq D}
                             (U : A ==> B) (F : A ==> C) (V : C ==> D) (G : B ==> D) : Type :=
  mkCommutativeSquare_tranport : ∀ (comm : ∀ x, (V °°F) @@ x =  (G °° U) @@ x),
                (∀ x y, @commutativeSquare_tranport (A [x, y]) (B [U @@ x, U @@ y])
                                   (C [F @@ x, F @@ y]) (D[(G°°U) @@ x, (G°°U) @@ y]) _
                                   (U << x , y >>) (F << x , y >>)
                                   (transport_GHomL_eq_here (inverse (comm x)) °°
                                     (transport_GHomR_eq_here (comm y) °°
                                        (V << F @@ x , F @@ y >>)))
                                   (G << U @@ x , U @@ y >>)) ->
                 @commutativeSquare_tranport A B C D _ U F V G.

CoFixpoint CommutativeSquare_tranport G `{transport_eq G} :
  commutativeSquare G :=
  mkCommutativeSquare
    (fun A B C => commutativeSquare_tranport A B C G)
    (fun x y => CommutativeSquare_tranport (G[x,y])).

Definition generalSquare G `{transport_eq G} :=
  {| _commutativeSquare := CommutativeSquare_tranport G |}.

Definition transport_eq_compat_here (G:ωPreCat) (_transport : transport_eq G):
           ∀ n x y y' (c : cell n (G[x,y])) (e : y = y'),
     transport (fun X => cell _ (G [_,X])) e c = cellGHom _ _ _
                                            (transport_GHomR_eq_here e) c.
  destruct _transport as [H' [H]]. destruct H. apply e0.
Defined.

Definition transport_eq_compat_hom (G:ωPreCat) (_transport : transport_eq G)
           {x y : |G| } : @transport_eq (G[x,y]).
  refine (mkTransport_eq _ _ _). destruct _transport as [H' H]. destruct H. apply t.
Defined.

Hint Extern 1 (@transport_eq (?G[?x,?z]) _) => apply (@transport_eq_compat_hom _ _) : typeclass_instances.

Definition transport_cell_eqLR (G:ωPreCat) (_transport : transport_eq G)
           n x x' y y' (c : cell n (G[x,y])) (e : (x,y) = (x',y')) 
           (e0 := path_prod_split e):
   pack_prod _ _ (transport (fun X => cell _ (G [fst X,snd X])) e c) = cellGHom _ _ _ (transport_GHomL_eq_here (inverse (fst e0))) (cellGHom _ _ _ (transport_GHomR_eq_here (snd e0)) c).
  rewrite transport_path_prod_split.
  destruct _transport as [H' H]. destruct H. etransitivity.
  apply (ap (transport (λ x0 : | G |,
      cell n (G [fst (x0, snd (x', y')), snd (x0, snd (x', y'))])) (fst (path_prod_split e))) (e2 _ _ _ _ _ _)).
  apply e1.
Defined.

Fixpoint eq_cell_comp n (G G' G'':ωPreCat) (c: cell n G)
         (f : G ==> G') (f' : G' ==> G'') 
         {struct n}:
  f' `@c` (f `@c` c) = (f' °° f) `@c` c.
destruct n. 
- exact eq_refl.
- apply path_sigma_uncurried. simpl. exists eq_refl. simpl. 
  apply (eq_cell_comp n (G [fst c.1, snd c.1]) 
                       (G' [f @@ (fst c.1), f @@ (snd c.1)])
                       (G'' [f' @@ (f @@ (fst c.1)), f' @@ (f @@ (snd c.1))])
                       c.2 
         (f << fst c.1, snd c.1 >>) 
         (f' << f @@ (fst c.1), f @@ (snd c.1) >>)).
Defined.

Fixpoint eq_cell_assoc2 n (G G' G'' G''':ωPreCat) (c: cell n G)
         (f : G ==> G') (f' : G' ==> G'') (f'' : G'' ==> G''')
         {struct n}:
  (f'' °° (f' °° f)) `@c` c = ((f'' °° f') °° f) `@c` c.
destruct n. 
- exact eq_refl.
- apply path_sigma_uncurried. simpl. exists eq_refl. simpl. 
  apply (eq_cell_assoc2 n (G [fst c.1, snd c.1]) 
           (G' [f @@ (fst c.1), f @@ (snd c.1)])
           (G'' [f' @@ (f @@ (fst c.1)), f' @@ (f @@ (snd c.1))]) 
           (G''' [f'' @@ (f' @@ (f @@ fst c .1)), f'' @@ (f' @@ (f @@ snd c .1))])
           c.2 
         (f << fst c .1, snd c .1 >>) 
         (f' << f @@ fst c .1, f @@ snd c .1 >>)
         (f'' << f' @@ (f @@ fst c .1), f' @@ (f @@ snd c .1) >>)).
Defined.

Fixpoint prod_hom'_comp n (G G' G'' H H' H'':ωPreCat) 
         (f : G ==> G') (f' : G' ==> G'') (g : H ==> H') (g' : H' ==> H'') c {struct n}:
  cellGHom n (G ** H) (G'' ** H'') (prod_hom' f' g' °° prod_hom' f g) c =
  cellGHom n (G ** H) (G'' ** H'') (prod_hom' (f' °° f) (g' °° g)) c.
destruct n.
- reflexivity. 
-  apply path_sigma_uncurried. simpl. exists eq_refl. simpl. 
   apply (prod_hom'_comp  n
                (G[fst (fst c .1), fst (snd c .1)])
                (G'[f @@ fst (fst c .1), f @@ fst (snd c .1)])
                (G'' [f' @@ (f @@ fst (fst c .1)), f' @@ (f @@ fst (snd c .1))])
                (H[snd (fst c .1), snd (snd c .1)])
                (H'[g @@ snd (fst c .1), g @@ snd (snd c .1)])
                (H'' [g' @@ (g @@ snd (fst c .1)), g' @@ (g @@ snd (snd c .1))])
         (f << fst (fst c .1), fst (snd c .1) >>)
         (f' << f @@ fst (fst c .1), f @@ fst (snd c .1) >>)
         (g << snd (fst c .1), snd (snd c .1) >>)
         (g' << g @@ snd (fst c .1), g @@ snd (snd c .1) >>) c.2).
Defined.

Definition path_prod_split_fst {A B : Type} (z z' : A * B) (x : (fst z = fst z')) (y : (snd z = snd z')) : fst (path_prod_split (path_prod _ _ x y)) = x.
  destruct z, z'. simpl in *. destruct x, y. reflexivity.
Defined.

Definition path_prod_split_snd {A B : Type} (z z' : A * B) (x : (fst z = fst z')) (y : (snd z = snd z')) : snd (path_prod_split (path_prod _ _ x y)) = y.
  destruct z, z'. simpl in *. destruct x, y. reflexivity.
Defined.

Definition transport_hom {G G' H H':ωPreCat} (e:G = H) (e' : G' = H') :
           G ==> G' -> H ==> H'. 
  destruct e, e'. exact id.
Defined.

Definition transport_hom_concat (G G' H H' K K' :ωPreCat) (e:G = H) (e' : G' = H')
           (f:H = K) (f' : H' = K') F:
  transport_hom f f' (transport_hom e e' F) = transport_hom (e @ f) (e' @ f') F.
  destruct e, e',f , f'. reflexivity. 
Defined.

Fixpoint GComp_cellGHom n (G H K: ωPreCat) (f: G ==> H) (g: H ==> K) 
         (c:cell n G) {struct n} : 
  (g °° f) `@c` c = g `@c` (f `@c` c).
destruct n.
- reflexivity.
- refine (path_sigma' _ _ _). reflexivity. 
  simpl. exact (GComp_cellGHom n (G [fst c .1, snd c .1])
                               (H [f @@ fst c .1, f @@ snd c .1])
                               (K [g @@ (f @@ fst c .1), g @@ (f @@ snd c .1)])
                               (f << fst c .1, snd c .1 >>)
                               (g << f @@ fst c .1, f @@ snd c .1 >>) c.2).
Defined.

Definition commutativeSquare_tranport_to_commutativeSquare
         (D : ωPreCat) `{transport_eq D} A B C U F V G :
  @commutativeSquareHere D (generalSquare D) A B C U F V G ->
  @commutativeSquareHere D (canonicalSquare D) A B C U F V G.
  intros X n.
  generalize dependent D. generalize dependent C.
  generalize dependent B. generalize dependent A.  
  induction n; intros; rename cG into c.
- destruct X. exact (comm c).
- destruct c as [[x y] c], X. refine (path_sigma' _ _ _).
  + exact (path_prod (V @@ (F @@ x), V @@ (F @@ y))
                     (G @@ (U @@ x), G @@ (U @@ y)) (comm x) (comm y)).
  + etransitivity. apply transport_cell_eqLR; auto.
    rewrite path_prod_split_fst, path_prod_split_snd.
    pose (IHn _ _ _ _ _ _ _ _ _ (c0 x y) c). simpl in *.
    rewrite <- (GComp_cellGHom _ _ _ _ _ (transport_GHomR_eq_here (comm y))).
    rewrite <- GComp_cellGHom. 
    rewrite <- e.
    repeat rewrite <- eq_cell_comp.
    rewrite <- (eq_cell_comp n (A[x, y]) (C [F @@ x, F @@ y])
                               _ c (F << x, y >>)
               (transport_GHomL_eq_here (inverse (comm x))
    °° (transport_GHomR_eq_here (comm y) °° (V << F @@ x, F @@ y >>)))).
    rewrite <- eq_cell_comp. simpl. 
    rewrite <- (eq_cell_comp n (C [F @@ x, F @@ y]) (D [V @@ (F @@ x), V @@ (F @@ y)])
                               _ _ (V << F @@ x, F @@ y >>)
               (transport_GHomR_eq_here (comm y))).
    rewrite <- (eq_cell_comp n (A[x, y])
                             (C [F @@ x, F @@ y]) (D [V @@ (F @@ x), V @@ (F @@ y)])
                             _ (F << x, y >>) (V << F @@ x, F @@ y >>)).
    reflexivity. 
Defined.

Definition commutativeTriangle_to_commutativeTriangle_cell           
         (C : ωPreCat) `{HC :transport_eq C} A B F G H :
  @commutativeTriangleHere C (generalTriangle C) A B F G H ->
  @commutativeTriangleHere C (canonicalTriangle C) A B F G H.
  intros X n.
  generalize dependent C. generalize dependent B. generalize dependent A.  
  induction n; intros; rename cG into c.
- destruct X. exact (comm c).
- destruct c as [[x y] c], X. refine (path_sigma' _ _ _).
  + exact (path_prod (G @@ (F @@ x), G @@ (F @@ y))
                     (H @@ x, H @@ y) (comm x) (comm y)).
  + etransitivity. apply transport_cell_eqLR; auto.
    rewrite path_prod_split_fst, path_prod_split_snd.
    pose (IHn _ _ _ _ _ _ _ (c0 x y) c). simpl in *.
    rewrite <- (GComp_cellGHom _ _ _ _ _ (transport_GHomR_eq_here (comm y))).
    rewrite <- GComp_cellGHom. 
    rewrite <- e.
    repeat rewrite <- eq_cell_comp.
    rewrite <- (eq_cell_comp n (A[x, y]) (B [F @@ x, F @@ y])
                               _ c (F << x, y >>)
               (transport_GHomL_eq_here (inverse (comm x))
     °° (transport_GHomR_eq_here (comm y) °° (G << F @@ x, F @@ y >>)))).
    rewrite <- eq_cell_comp. simpl. 
    rewrite <- (eq_cell_comp n (B [F @@ x, F @@ y]) (C [G @@ (F @@ x),G @@ (F @@ y)])
                               _ _ (G << F @@ x, F @@ y >>)
               (transport_GHomR_eq_here (comm y))).
    rewrite <- (eq_cell_comp n (A[x, y])
                             (B [F @@ x, F @@ y]) (C [G @@ (F @@ x), G @@ (F @@ y)])
                             _ (F << x, y >>) (G << F @@ x, F @@ y >>)).
    reflexivity. 
Defined.

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
            `{transport_eq K}
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
     interchangeV G1 G2 G H1 H2 H K1 K2 K compK.

CoInductive interchangeH (G H K : ωPreCat) `{transport_eq K} 
            {compGHK : Composable G.1 H.1 K.1}: Type :=
  mkInterchangeH : 
    (* the law *)
    (∀ (f f' f'' : |G|) (g g' g'' : |H|),
      interchangeV
        (G [f, f']) (G [f', f'']) (G [f, f'']) 
        (H [g, g']) (H [g', g'']) (H [g, g'']) 
        (K [g ° f, g' ° f']) (K [g' ° f', g'' ° f'']) 
        _ (H0 := transport_GHom_eq_hom' _ _) _) -> 
    (* the co-induction step *)
    (∀ (f f' : |G|) (g g' : |H|),
      @interchangeH (G [f, f']) (H [g, g']) (K [g ° f, g' ° f']) _ _) ->
      interchangeH G H K.

CoInductive interchange (G : ωPreCat) `{transport_eq G} : Type :=
mkInterchange : 
        (* the law *)
        (∀ (x y z : |G|), interchangeH (G [x,y]) (G [y,z]) (G [x,z]))
        ->
        (* the co-induction step *)
        (∀ (x y :   |G|), @interchange (G [x,y]) _) ->
        interchange G.


CoFixpoint interchangeV_interchange {G1 G2 G H1 H2 H K1 K2 K : ωPreCat}
            `{transport_eq K}
            {compG : Composable G1.1 G2.1 G.1}
            {compH : Composable H1.1 H2.1 H.1}
            (compK : Composable K1.1 K2.1 K.1)
            {comp1 : Composable G1.1 H1.1 K1.1}
            {comp2 : Composable G2.1 H2.1 K2.1}
            {compGHK : Composable G.1 H.1 K.1} :
  interchangeV G1 G2 G H1 H2 H K1 K2 _ compK ->
  @commutativeSquareHere K (generalSquare K)
                    ((G1 ** H1)**(G2**H2)) (G**H) (K1**K2) 
                    (prod_hom compG compH)
                    (prod_hom' (@compo _ _ _ comp1) (@compo _ _ _ comp2))
                    compo compo.
intros [[i s]]. refine (mkCommutativeSquare_tranport _ _ _ _ _ _ _ _ _ _ ).
- intros [[f1 g1] [f2 g2]]. exact (i f1 f2 g1 g2).
- intros [[f1 g1] [f2 g2]] [[f1' g1'] [f2' g2']]. 
  exact (interchangeV_interchange _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                   (s f1 f1' f2 f2' g1 g1' g2 g2')).
Defined.
 
CoFixpoint interchangeH_interchange {G H K : ωPreCat} `{transport_eq K} 
           {compGHK : Composable G.1 H.1 K.1}:
  interchangeH G H K -> @preservesCompo (G**H) K (@compo _ _ _ compGHK)
           (generalSquare K).
intros [i s]. refine (mkPreservesCompo _ _ _ _ _).
- intros [f g] [f' g'] [f'' g''].
  exact (interchangeV_interchange _ (i f f' f'' g g' g'')).
- intros [f g] [f' g']. 
  exact (interchangeH_interchange _ _ _ _ _ (s f f' g g')).
Defined.

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


CoFixpoint idCompoH_preservesId {G H K : ωPreCat} {composable : Composable G.1 H.1 K.1} :
  idCompoH G H K -> preservesId (G**H) K compo.
intro Idcompo; destruct Idcompo. apply mkPreservesId.
- intros. destruct x. apply e.
- intros. destruct x, y.
  exact (idCompoH_preservesId (G [o,o1]) (H[o0, o2]) (K [o0 ° o, o2 ° o1]) _ (i _ _ _ _)). 
Defined.

CoFixpoint interchange_idcompo_compo_ωFunctor (G : ωPreCat) `{transport_eq G} :
  interchange G -> idCompo G -> @compo_ωFunctor G (generalSquare G).
intros [i s] [id idh]. apply mkcompo_ωFunctor.
- intros x y z. exact (interchangeH_interchange (i x y z),
                       idCompoH_preservesId  (id x y z)).
- intros x y. exact (interchange_idcompo_compo_ωFunctor  _ _ (s x y) (idh x y)).
Defined.




(** a more inlined version of unitalityL and unitalityR **)

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

CoFixpoint compoIdL_H_unitalityL (G H : ωPreCat)
           (candidate_id : |G|)
           `{transport_eq H}
            {composable : Composable G.1 H.1 H.1} :
  compoIdL_H G H candidate_id ->
  @commutativeTriangleHere _ (generalTriangle H) (ωterminal ** H)
                      (G ** H)  
                      (prod_hom' (GPoint candidate_id) (GId H.1))
                      compo (ωterminal_unitL H).
intro X. refine (mkCommutativeTriangle_tranport _ _ _ _ _ _ _ _).
- intros. destruct X as [idL X]. exact (idL (snd x)).
- intros. destruct X as [idL X]. 
  apply (compoIdL_H_unitalityL _ _ _ _ _ (X (snd x) (snd y))).
Defined.
 
CoFixpoint compoIdL_unitalityL (G : ωPreCat) `{HG : transport_eq G} :
  compoIdL G -> @unitalityL G (generalTriangle G).
intro H. apply mkUnitalityL.
- intros. destruct H. apply compoIdL_H_unitalityL; auto.
- intros. destruct H. apply compoIdL_unitalityL; auto.
Defined.

CoFixpoint compoIdR_H_unitalityR (G H : ωPreCat)
           (candidate_id : |H|)
           `{_transport : transport_eq G}
           {composable : Composable G.1 H.1 G.1} :
  compoIdR_H G H candidate_id ->
  @commutativeTriangleHere _ (generalTriangle G) (G ** ωterminal)
                      (G ** H)
                      (prod_hom' (GId G.1) (GPoint candidate_id))
                      compo (ωterminal_unitR G).
intro X. refine (mkCommutativeTriangle_tranport _ _ _ _ _ _ _ _).
- intros. destruct X as [idR X]. exact (idR (fst x)).
- intros. destruct X as [idR X]. 
  apply (compoIdR_H_unitalityR _ _ _ _ _ (X (fst x) (fst y))).
Defined.
 
CoFixpoint compoIdR_unitalityR (G : ωPreCat) `{HG: transport_eq G} :
  compoIdR G -> @unitalityR G (generalTriangle G).
intro H. apply mkUnitalityR.
- intros. destruct H. apply compoIdR_H_unitalityR; auto.
- intros. destruct H. apply compoIdR_unitalityR; auto.
Defined.



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
            `{transport_eq G}
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
  associativityH G1 G2 G3 G12 G23 G.


CoInductive associativity' (G : ωPreCat) `{transport_eq G} : Type := 
mkAssociativity' :
        (∀ (x y z t : |G|), 
           associativityH (G [x,y]) (G [y,z]) (G [z,t]) (G[x,z]) (G[y,t]) (G[x,t]))->
        (* the co-induction step *)
        (∀ (x y :   |G|), @associativity' (G [x,y]) _) ->
        @associativity' G _.


CoFixpoint assocH_assoc (G1 G2 G3 G12 G23 G : ωPreCat)
            `{HG: transport_eq G}
            {comp12 : Composable G1.1 G2.1 G12.1}
            {comp23 : Composable G2.1 G3.1 G23.1}
            {comp12_3 : Composable G12.1 G3.1 G.1}
            {comp1_23 : Composable G1.1 G23.1 G.1} :
  associativityH G1 G2 G3 G12 G23 G ->
  @commutativeSquareHere G (generalSquare G) (G1 ** (G2 ** G3))
                     (G12 ** G3) (G1 ** G23) 
                     (prod_hom1 G3.1 _)
                     (prod_hom' (GId G1.1) (@compo _ _ _ _))
                     (@compo _ _ _ _) (@compo _ _ _ _).
intro H. refine (mkCommutativeSquare_tranport _ _ _ _ _ _ _ _ _ _).
- intros. destruct H as [[a H]]. destruct x as [x [y z]]. apply a.
- intros. destruct H as [[a H]]. destruct x as [f [g h]], y as [f' [g' h']]. 
  apply (assocH_assoc _ _ _ _ _ _ _ _ _ _ _ (H f f' g g' h h')).
Defined.
 
CoFixpoint assoc'_assoc (G : ωPreCat) `{transport_eq G} :
  associativity' G -> @associativity G (generalSquare G).
intro H'. apply mkAssociativity.
- intros. destruct H'. apply assocH_assoc; auto.
- intros. destruct H'. apply assoc'_assoc; auto.
Defined.

CoFixpoint assoc_gen_assoc_canonical (G : ωPreCat) `{transport_eq G} :
  @associativity G (generalSquare G) ->
  @associativity G (canonicalSquare G).
intros [X Xs]. refine (mkAssociativity _ _ _); intros. 
- exact (commutativeSquare_tranport_to_commutativeSquare _ _ _ _ _ _ _ _ (X x y z t)).
- exact (assoc_gen_assoc_canonical (G[x,y]) _ (Xs x y)).
Defined. 

CoFixpoint unitalityL_gen_unitalityL_canonical (G : ωPreCat) `{transport_eq G} :
  @unitalityL G (generalTriangle G) ->
  @unitalityL G (canonicalTriangle G).
intros [X Xs]. refine (mkUnitalityL _ _ _); intros. 
- exact (commutativeTriangle_to_commutativeTriangle_cell _ _ _ _ _ _ (X x y)).
- exact (unitalityL_gen_unitalityL_canonical (G[x,y]) _ (Xs x y)).
Defined. 

CoFixpoint unitalityR_gen_unitalityR_canonical (G : ωPreCat) `{transport_eq G} :
  @unitalityR G (generalTriangle G) ->
  @unitalityR G (canonicalTriangle G).
intros [X Xs]. refine (mkUnitalityR _ _ _); intros. 
- exact (commutativeTriangle_to_commutativeTriangle_cell _ _ _ _ _ _ (X x y)).
- exact (unitalityR_gen_unitalityR_canonical (G[x,y]) _ (Xs x y)).
Defined. 

CoFixpoint preservesCompo_gen_preservesCompo_canonical
           (G H : ωPreCat) f `{transport_eq H} :
  @preservesCompo G H f (generalSquare H) ->
  @preservesCompo G H f (canonicalSquare H).
intros [X Xs]. refine (mkPreservesCompo _ _ _ _ _); intros. 
- exact (commutativeSquare_tranport_to_commutativeSquare _ _ _ _ _ _ _
           _ (X x y z)).
- exact (preservesCompo_gen_preservesCompo_canonical _ _ _ _ (Xs x y)).
Defined. 

CoFixpoint compo_ωFunctor_gen_compo_ωFunctor_canonical (G : ωPreCat) `{transport_eq G} :
  @compo_ωFunctor G (generalSquare G) ->
  @compo_ωFunctor G (canonicalSquare G).
intros [X Xs]. refine (mkcompo_ωFunctor _ _ _); intros. 
- specialize (X x y z). destruct X. split.
  + exact (preservesCompo_gen_preservesCompo_canonical _ _ _ p).
  + exact p0.
- exact (compo_ωFunctor_gen_compo_ωFunctor_canonical (G[x,y]) _ (Xs x y)).
Defined. 







