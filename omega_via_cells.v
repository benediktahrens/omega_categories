Add LoadPath "." as OmegaCategories.
Require Export Unicode.Utf8_core.
Require Import path GType omega_categories type_to_omega_cat.

(** * Globular sets, basic definitions  *)

(** First, a notation for [existT], the quantifier over [Type]s *)

Set Implicit Arguments.

(*** Cellular machinery ***)

Fixpoint cell (n:nat) (G:ωPreCat) : Type := match n with 
 0 => |G|
|S n => {xy :|G| * |G| & cell n (G [fst xy,snd xy])}
end.

Fixpoint sitcomp p n (G:ωPreCat) : Type := match p with 
     0 => {xyz :|G| * |G| * |G| &
              prod
               (cell n (G [fst xyz,fst (snd xyz)]))
               (cell n (G [fst (snd xyz),snd (snd xyz)]))}             
  | S p => {xy :|G| * |G| & 
                sitcomp p n (G [fst xy,snd xy])}
  end.

Fixpoint cellGHom n (G H: ωPreCat) (f: G ==> H) (cG : cell n G) {struct n}: cell n H.
destruct n.
- exact (f @@ cG).
- exact ((f @@ (fst cG.1),f @@ (snd cG.1));
         cellGHom n (G[fst cG.1, snd cG.1]) 
                  (H[f @@ fst cG.1, f @@ snd cG.1]) (f<<fst cG.1,snd cG.1>>) cG.2).
Defined.

Fixpoint cellProd n G H (cG : cell n G) (cH : cell n H) {struct n} : cell n (G ** H).
destruct n.
- exact (cG,cH).
- exact ((fst cG.1, fst cH.1, (snd cG.1, snd cH.1));
         cellProd n (G [fst cG .1,snd cG .1]) (H [fst cH .1,snd cH .1]) cG.2 cH.2).
Defined.

Definition cellCompo n (G H K : ωPreCat) (_comp :Composable G.1 H.1 K.1) :
           cell n G → cell n H → cell n K :=
  fun c c' => @cellGHom n (G**H) K compo (cellProd _ _ _ c c').

Definition cellComposition {n} {G: ωPreCat} {x y z : |G| } :
           cell n (G[x,y]) → cell n (G[y,z]) → cell n (G[x,z]) :=
  cellCompo n (G[x,y]) (G[y,z]) (G[x,z]) _.

Fixpoint sitcompGHom p n {G H: ωPreCat} (f: G ==> H) (cG : sitcomp p n G) {struct p}:
  sitcomp p n H.
destruct p.
- exists (f @@ fst cG.1, (f @@ fst (snd cG.1), f @@ snd (snd cG.1))).
  exact (@cellGHom n (G [fst cG.1,fst (snd cG.1)]) (H[f @@ fst cG .1, f @@ fst (snd cG .1)]) (f<<_,_>>) (fst cG.2), 
                @cellGHom n (G [fst (snd cG.1),snd (snd cG.1)]) (H[f @@ fst (snd cG .1), f @@ snd (snd cG .1)]) (f<<_,_>>) (snd cG.2)).
- exact ((f @@ (fst cG.1),f @@ (snd cG.1));
         sitcompGHom p n (G[fst cG.1, snd cG.1]) 
                  (H[f @@ fst cG.1, f @@ snd cG.1]) (f<<fst cG.1,snd cG.1>>) cG.2).
Defined.

Fixpoint sitcompProd {p n G H} (cG : sitcomp p n G) (cH : sitcomp p n H) {struct p}: 
  sitcomp p n (G ** H).
destruct p.
- exists (fst cG.1, fst cH.1, 
          (fst (snd cG.1), fst (snd cH.1), 
           (snd (snd cG.1), snd (snd cH.1)))). simpl in *.
  exact (cellProd _ _ _ (fst cG.2) (fst cH.2), cellProd _ _ _ (snd cG.2) (snd cH.2)).
- exact ((fst cG.1, fst cH.1, (snd cG.1, snd cH.1));
         sitcompProd p n (G [fst cG .1,snd cG .1]) (H [fst cH .1,snd cH .1]) cG.2 cH.2).
Defined.

Definition sitcompCompo p n (G H K : ωPreCat) (_comp :Composable G.1 H.1 K.1) :
  sitcomp p n G → sitcomp p n H → sitcomp p n K :=
  fun c c' => @sitcompGHom p n (G**H) K compo (sitcompProd c c').

Definition sitcompComposition {p n} {G: ωPreCat} {x y z : |G| } : 
  sitcomp p n (G[x,y]) → sitcomp p n (G[y,z]) → sitcomp p n (G[x,z]) :=
  sitcompCompo p n (G[x,y]) (G[y,z]) (G[x,z]) _.

Definition fold_cell {n G x y} (c : cell n (G[x,y])) : cell (S n) G.
  exists (x,y). exact c.
Defined.

(*** Cellular definition of the interchange law ***)

Fixpoint evalcomp {p n G} (s:sitcomp p n G) {struct p} : cell (S (p+n)) G.
  destruct p. 
  - exact (fold_cell (@cellComposition n _ _ _ _
                                       (fst s.2) (snd s.2))).
  - exact (s.1;evalcomp p n (G[fst s.1,snd s.1]) s.2).
Defined.

Inductive sitech p n (G:ωPreCat) x y z :=
mksitech : sitcomp p n (G[x,y]) -> sitcomp p n (G[y,z]) -> sitech p n G x y z.

Definition vertComp p n G x y z (ech:sitech p n G x y z) : cell (S (p + n)) (G[x,z]).
  destruct ech as [s s0]. exact (cellComposition (evalcomp s) (evalcomp s0)). 
Defined.

Definition horComp p n G x y z (ech:sitech p n G x y z) : cell (S (p + n)) (G[x,z]).
  destruct ech as [s s0]. exact (evalcomp (sitcompComposition s s0)).
Defined.

CoInductive interchange_cell : ∀ (G : ωPreCat), Type :=
mkInterchange_cell : ∀ G,
        (* the law *)
        (∀ p n x y z (s: sitech p n G x y z), 
           horComp s = vertComp s) ->
        (* the co-induction step *)
        (∀ (x y :   |G|), interchange_cell (G [x,y])) ->
        interchange_cell G.

(*** J for cells ***)

Fixpoint identity_cell n (G:ωPreCat) (x:|G|) {struct n} : cell n (G[x,x]).
destruct n.
- exact (identity x).
- exact ((identity x, identity x); identity_cell n  (G [x, x]) (identity x)). 
Defined. 

Fixpoint J_cell n (T:Type) (x:|piω T|) 
         (P : forall y, cell n ((piω T)[x,y]) -> Type) y e
         (c : P x (identity_cell n _ x)) {struct n} : P y e.
destruct n.
- destruct e. exact c.
- simpl in *. destruct e as [(e1,e2) e]. destruct e1.
  exact (J_cell n (x = x) eq_refl (fun y e => P x ((eq_refl,y); e)) _ _ c).
Defined.

(*** Compatibility with transport_eq ***)

CoInductive transport_eq_compat_type : ∀ G (_trans : transport_eq G), Type :=
  mkTransport_eq_compat_type : ∀ (G : ωPreCat) (_trans : transport_eq G),
  (∀ n x x' y (c : cell n (G[x,y])) (e : x = x'),
   transport (fun X => cell _ (G [X,_])) e c = cellGHom _ _ _ (transport_GHomL_eq_here (inverse e)) c)
  ->
  (∀ n x y y' (c : cell n (G[x,y])) (e : y = y'),
     transport (fun X => cell _ (G [_,X])) e c = cellGHom _ _ _ (transport_GHomR_eq_here e) c) ->
  (∀ {x y : |G| },  @transport_eq_compat_type (G[x,y]) _) ->
   @transport_eq_compat_type G _.

Class transport_eq_compat G (_trans : transport_eq G) := mkTransport_eq_compat
{
  _transport_eq_compat : transport_eq_compat_type _trans
}.

(*** interchange G -> interchange_cell G ***)

Inductive sitech' p n (G H K:ωPreCat) (_comp :Composable G.1 H.1 K.1) :=
mksitech' : sitcomp p n G -> sitcomp p n H -> sitech' p n G H K _comp.

Definition vertComp' p n G H K (_comp :Composable G.1 H.1 K.1)
           (ech:sitech' p n G H K _comp) : cell (S (p + n)) K.
  destruct ech as [s s0]. exact (cellCompo _ _ _ K _comp (evalcomp s) (evalcomp s0)). 
Defined.

Definition horComp' p n G H K (_comp :Composable G.1 H.1 K.1)
           (ech:sitech' p n G H K _comp) : cell (S (p + n)) K.
  destruct ech as [s s0]. 
  exact (evalcomp (@sitcompCompo p n _ _ _ _comp s s0)).
Defined.

Definition transport_eq_compat_here (G:ωPreCat) (_transport : transport_eq G)
           (_transport_compat : transport_eq_compat _transport) :
           ∀ n x y y' (c : cell n (G[x,y])) (e : y = y'),
     transport (fun X => cell _ (G [_,X])) e c = cellGHom _ _ _ (transport_GHomR_eq_here e) c.  destruct _transport_compat as [H]. destruct H. apply e0.
Defined.

Definition transport_eq_compat_hom (G:ωPreCat) (_transport : transport_eq G)
           (_transport_compat : transport_eq_compat _transport)
           {x y : |G| } : @transport_eq_compat (G[x,y]) _.
  econstructor. destruct _transport_compat as [H]. destruct H. apply t.
Defined.

Hint Extern 1 (@transport_eq_compat (?G[?x,?z]) _) => apply (@transport_eq_compat_hom _ _) : typeclass_instances.

Definition transport_cell_eqLR (G:ωPreCat) (_transport : transport_eq G)
           (_transport_compat : transport_eq_compat _transport)
           n x x' y y' (c : cell n (G[x,y])) (e : (x,y) = (x',y')) 
           (e0 := path_prod_split e):
   pack_prod _ _ (transport (fun X => cell _ (G [fst X,snd X])) e c) = cellGHom _ _ _ (transport_GHomL_eq_here (inverse (fst e0))) (cellGHom _ _ _ (transport_GHomR_eq_here (snd e0)) c).
  rewrite transport_path_prod_split.
  destruct _transport_compat as [H]. destruct H. etransitivity.
  apply (ap (transport (λ x0 : | G |,
      cell n (G [fst (x0, snd (x', y')), snd (x0, snd (x', y'))])) (fst (path_prod_split e))) (e2 _ _ _ _ _ _)).
  apply e1.
Defined.

Fixpoint eq_cell_assoc n (G G' G'' G''':ωPreCat) (c: cell n G)
         (f : G ==> G') (f' : G' ==> G'') (f'' : G'' ==> G''')
         {struct n}:  cellGHom _ _ _ f'' (cellGHom _ _ _ f' (cellGHom _ _ _  f c)) 
                      = cellGHom _ _ _  (f'' °° (f' °° f)) c.
destruct n. 
- exact eq_refl.
- apply path_sigma_uncurried. simpl. exists eq_refl. simpl. 
  apply (eq_cell_assoc n (G [fst c.1, snd c.1]) 
                       (G' [f @@ (fst c.1), f @@ (snd c.1)])
                       (G'' [f' @@ (f @@ (fst c.1)), f' @@ (f @@ (snd c.1))])
                       (G''' [f'' @@ (f' @@ (f @@ (fst c.1))),
                              f'' @@ (f' @@ (f @@ (snd c.1)))])
                       c.2 
         (f << fst c.1, snd c.1 >>) 
         (f' << f @@ (fst c.1), f @@ (snd c.1) >>)
         (f'' << f' @@ (f @@ (fst c.1)), f' @@ (f @@ (snd c.1)) >>)).
Defined.

Notation "g °°° f" := (cellCompo _ _ _ _ _ f g) (at level 20).

Fixpoint interchangeV_equiv n (G1 G2 G H1 H2 H K1 K2 K : ωPreCat)
            (_transport : transport_eq K)
            (_transport_comp : transport_eq_compat _transport)
            {compG : Composable G1.1 G2.1 G.1}
            {compH : Composable H1.1 H2.1 H.1}
            (compK : Composable K1.1 K2.1 K.1)
            {comp1 : Composable G1.1 H1.1 K1.1}
            {comp2 : Composable G2.1 H2.1 K2.1}
            {compGHK : Composable G.1 H.1 K.1}
            (i : interchangeV G1 G2 G H1 H2 H K1 K2 _transport compK)
            (f1 : cell n G1) (f2 : cell n G2) 
            (g1 : cell n H1) (g2 : cell n H2) {struct n}: 
  (g2 °°° f2) °°° (g1 °°° f1) = (g2 °°° g1) °°° (f2 °°° f1).
destruct n; destruct i; destruct s.
- apply x. 
- apply path_sigma_uncurried. simpl. exists (path_prod_uncurried ((fst g2 .1 ° fst f2 .1) ° (fst g1 .1 ° fst f1 .1),
     (snd g2 .1 ° snd f2 .1) ° (snd g1 .1 ° snd f1 .1))
     ((fst g2 .1 ° fst g1 .1) ° (fst f2 .1 ° fst f1 .1),
     (snd g2 .1 ° snd g1 .1) ° (snd f2 .1 ° snd f1 .1)) (x _ _ _ _, x _ _ _ _)). 
  fold cell.
  specialize (i (fst f1.1) (snd f1.1) (fst f2.1) (snd f2.1)
                  (fst g1.1) (snd g1.1) (fst g2.1) (snd g2.1)).
  pose (eq := interchangeV_equiv n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i (f1 .2) (f2 .2) (g1 .2) (g2 .2)).
  etransitivity. apply transport_cell_eqLR; auto.
  etransitivity. apply (@eq_cell_assoc n
             (K1 [(fst g1.1) ° (fst f1.1), (snd g1.1) ° (snd f1.1)] **
              K2 [(fst g2.1) ° (fst f2.1), (snd g2.1) ° (snd f2.1)])).
  match goal with | [ |- cellGHom _ _ _ ?f _ = _] => pose (morph := f) end.
  fold morph.
  assert (morph = (transport_GHomL_eq_here
            (inverse (x (fst f1 .1) (fst f2 .1) (fst g1 .1) (fst g2 .1)))
          °° (transport_GHomR_eq_here
                (x (snd f1 .1) (snd f2 .1) (snd g1 .1) (snd g2 .1))
              °° (compo << (fst g1 .1 ° fst f1 .1, fst g2 .1 ° fst f2 .1),
                  (snd g1 .1 ° snd f1 .1, snd g2 .1 ° snd f2 .1) >>)))).
  unfold morph. repeat rewrite path_prod_uncurried_split. reflexivity.
  rewrite H0. exact eq.
Defined.

Fixpoint interchangeH_equiv p n
            (G H K : ωPreCat) (_trans : transport_eq K)
            (_transport_comp : transport_eq_compat _trans)
            {compGHK : Composable G.1 H.1 K.1}
            (ech : sitech' p n G H K compGHK) {struct p}:
            interchangeH G H _trans -> horComp' ech = vertComp' ech.
destruct p; intro i; destruct ech, i.
- apply path_sigma_uncurried. simpl. exists (path_prod_uncurried _ _ (eq_refl,eq_refl)).
  specialize (i (fst s.1) (fst (snd s.1)) (snd (snd s.1)) 
                (fst s0.1) (fst (snd s0.1)) (snd (snd s0.1))).
  exact  (interchangeV_equiv _ _ i _ _ _ _).
- apply path_sigma_uncurried. exists (path_prod_uncurried _ _ (eq_refl,eq_refl)).
  exact (interchangeH_equiv p n 
             (G [fst s.1, snd s.1]) (H [fst s0.1, snd s0.1]) _
             (transport_GHom_eq_hom' _trans) _ _ 
             (mksitech' _ _ _ _ (K [(fst s0.1) ° (fst s.1),
                           (snd s0.1) ° (snd s.1)])
                        _ s.2 s0.2) 
             (i0 _ _ _ _)).
Defined.

CoFixpoint interchange_equiv (G:ωPreCat) (_transport : transport_eq G) 
            (_transport_comp : transport_eq_compat _transport) :            
  @interchange G _ -> interchange_cell G.
  intro H; apply mkInterchange_cell; destruct H.
  - intros p n x y z s. destruct s.
    exact (@interchangeH_equiv p n (G [x, y]) (G [y, z]) (G [x, z]) _ _ _ 
                              (mksitech' _ _ _ _ _ _ s s0) (i x y z)).
  - intros x y. exact (interchange_equiv (G [x, y]) _ _ (i0 x y)).
Defined.


(*** piω_transport_eq is compatible with transport of cells ***)


Fixpoint append_left_refl n (T U V : Type) (f : T → U → V) (x : T) (z : U)
           (X : | piω (x = x) ** piω (z = z) |)
           (_comp := piComp_V (ap2 f (h':=z)) (fst X) (fst X) (snd X) (snd X)) {struct n} :
 identity_cell n (piω (ap2 f (fst X) (snd X) = ap2 f (fst X) (snd X))) eq_refl =
 cellGHom n (piω (snd X = snd X) [eq_refl, eq_refl])
           (piω (ap2 f (fst X) (snd X) = ap2 f (fst X) (snd X)) [
  eq_refl ° eq_refl, eq_refl ° eq_refl])
           (@append_left (piω (fst X = fst X)) (piω (snd X = snd X))
            (piω (ap2 f (fst X) (snd X) = ap2 f (fst X) (snd X))) eq_refl eq_refl eq_refl _comp)
           (identity_cell n (piω (snd X = snd X)) eq_refl).
destruct n; try reflexivity; apply path_sigma_uncurried; exists eq_refl; simpl.
exact (append_left_refl n (x = x) (z = z) (f x z = f x z) (ap2 f (h':=z)) (fst X) (snd X) 
                             (eq_refl, eq_refl)). 
Defined.

Fixpoint append_right_refl n (T U V : Type) (f : T → U → V) (x : T) (z : U)
           (X : | piω (x = x) ** piω (z = z) |)
           (_comp := piComp_V (ap2 f (h':=z)) (fst X) (fst X) (snd X) (snd X)) {struct n} :
 identity_cell n (piω (ap2 f (fst X) (snd X) = ap2 f (fst X) (snd X))) eq_refl =
 cellGHom n (piω (fst X = fst X) [eq_refl, eq_refl])
           (piω (ap2 f (fst X) (snd X) = ap2 f (fst X) (snd X)) [
  eq_refl ° eq_refl, eq_refl ° eq_refl])
           (@append_right (piω (fst X = fst X)) (piω (snd X = snd X))
            (piω (ap2 f (fst X) (snd X) = ap2 f (fst X) (snd X))) eq_refl eq_refl eq_refl _comp)
           (identity_cell n (piω (fst X = fst X)) eq_refl).
destruct n; try reflexivity; apply path_sigma_uncurried; exists eq_refl; simpl.
exact (append_right_refl n (x = x) (z = z) (f x z = f x z) (ap2 f (h':=z)) (fst X) (snd X) 
                             (eq_refl, eq_refl)). 
Defined.

Arguments J_cell : clear implicits.

Definition piω_transport_eq_compat T : transport_eq_compat (piω_transport_eq' T). 
  econstructor; generalize dependent T; cofix; intro T. 
  apply mkTransport_eq_compat_type.
  - intros. destruct e. simpl. apply (J_cell n T x (fun y e => _) y c). clear y c.
    destruct n; try reflexivity; apply path_sigma_uncurried; exists eq_refl; simpl.
    unfold identity, concat; simpl.
    destruct n; try reflexivity; apply path_sigma_uncurried; exists eq_refl; simpl.
    destruct n; try reflexivity; apply path_sigma_uncurried; exists eq_refl; simpl.
    exact (@append_left_refl n (x=x) (x=x) (x=x) concat eq_refl eq_refl (eq_refl,eq_refl)). 
  - intros. destruct e. simpl. apply (J_cell n T x (fun y e => _) y c). clear y c.
    destruct n; try reflexivity; apply path_sigma_uncurried; exists eq_refl; simpl.
    destruct n; try reflexivity; apply path_sigma_uncurried; exists eq_refl; simpl.
    destruct n; try reflexivity; apply path_sigma_uncurried; exists eq_refl; simpl.
    exact (@append_right_refl n (x=x) (x=x) (x=x) concat eq_refl eq_refl (eq_refl,eq_refl)). 
  - intros. exact (piω_transport_eq_compat (x = y)). 
Defined.

(*** interchange_cell for piω ***)

Definition piω_interchange (T:Type) : interchange_cell (piω T) :=
  interchange_equiv (piω_transport_eq_compat T) (pi_interchange T).




