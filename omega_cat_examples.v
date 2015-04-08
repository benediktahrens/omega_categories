Add LoadPath "." as OmegaCategories.
Require Export Unicode.Utf8_core.
Require Import Omega BinInt. 
Require Import path GType omega_categories omega_categories_transport type_to_omega_cat Integers. 

Set Implicit Arguments.

Notation "| G |" := (objects G) (at level 80).
Notation "G [ A , B ]" := (hom G A B) (at level 80).
Notation "A ** B" := (product A B) (at level 90).
Notation " A ==> B " := (GHom A B) (at level 90).


(** The empty type *)
Inductive Empty : Type := .

(** 
- The empty globular set *)

Definition empty : GType := Delta Empty.

(** 
- The discrete one, parameterised by any set X0, i.e., X0 in dim 0 and empty elsewhere *)

CoFixpoint Discrete (X0 : Type) : GType := @mkGType X0 (fun _ _ => empty).

(** Some technical definitions *)

Definition transport_IsωPreCat G G' (e:G = G') (compG : IsωPreCat G) :
  e # compG = {| _comp := e # (@_comp _ compG); _id := e # (@_id _ compG) |}.
  destruct e, compG. reflexivity.
Defined.

Definition path_IsωPreCat G (compG compG' : IsωPreCat G) :
  (@_comp _ compG = @_comp _ compG') -> (@_id _ compG = @_id _ compG') ->
  compG = compG'.
  destruct compG,compG'; simpl.
  intros e e'; destruct e, e'. reflexivity.
Defined.

Definition Decidable_to_bool P (H : Decidable P) : bool :=
  match H with
      inl _ => true
    | inr _ => false
  end. 

Definition decpaths_nat_refl g : decpaths_nat g g = inl eq_refl.
  induction g.
  - reflexivity.
  - simpl. rewrite IHg. reflexivity.
Defined.

Definition decpaths_nat_neq g g' ( e : ~~ g = g') : {e' : ~~ g = g' & decpaths_nat g g' = inr e'}.
  generalize dependent g'. induction g; destruct g'; intro e.
  - simpl in *. exists e. destruct (e eq_refl).
  - simpl. refine (existT _ _ eq_refl).
  - simpl. refine (existT _ _ eq_refl).
  - simpl. assert (~~ g = g'). intro H. destruct (e (ap S H)).
    specialize (IHg g' H). destruct IHg as [e' IHg]. exists (λ e0 : S g = S g',
      match e0 in (_ = y) return (y = S g' → path.Empty) with
      | eq_refl =>
          λ H0 : S g = S g',
          eq_ind_r (λ _ : nat, path.Empty)
            (e'
               (f_equal (λ e1 : nat, match e1 with
                                     | 0 => g
                                     | S n => n
                                     end) H0))
            (f_equal (λ e1 : nat, match e1 with
                                  | 0 => g
                                  | S n => n
                                  end) H0)
      end eq_refl).
    rewrite IHg. reflexivity.  
Defined.

Definition unapS m n : S m = S n -> m = n. intro. inversion H. auto. Defined.

Definition decpaths_nat_refl' g g' (e: g = g') : {e' : g = g' & decpaths_nat g g' = inl e'}.
  generalize dependent g'. induction g; destruct g'; intro e.
  - exists eq_refl. reflexivity.
  - inversion e. 
  - inversion e.
  - specialize (IHg g' (unapS e)). destruct IHg. exists (f_equal S x).
    simpl. rewrite e0. reflexivity. 
Defined.

(** Definitions around empty (initial) and terminal objects *)

CoFixpoint init_empty (G : GType) : empty ==> G :=
  mkGHom empty G (fun x => match x with end)
         (fun x y => (init_empty _)). 

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

Instance uncomposable_left (G H : GType) : Composable empty G H.
  econstructor. generalize dependent G; generalize dependent H; cofix. 
  intros H G. assert (|empty  ** G| -> |H|). intros (x,y); destruct x.
  apply (mkGHom _ _ X).
  simpl; intros. apply (uncomposable_left ( H [X x, X x']) (G[snd x, snd x'])).
Defined.

Definition uncomposable_right (G H : GType) : Composable G empty H.
  econstructor. generalize dependent G; generalize dependent H; cofix. 
  intros H G. assert (|G ** empty| -> |H|). intros (x,y); destruct y.
  apply (mkGHom _ _ X).
  simpl; intros. apply (uncomposable_right ( H [X x, X x']) (G[fst x, fst x'])).
Defined.

CoFixpoint Compo_empty : Compo empty.
apply mkCompo; intros. apply uncomposable_left.
apply Compo_empty.
Defined.

CoFixpoint Id_empty : Id empty.
apply mkId; intros. destruct x.
apply Id_empty.
Defined.

Instance empty_CompoGType : IsωPreCat empty :=
  {| _comp := Compo_empty; _id := Id_empty|}. 

Definition CGempty : ωPreCat := (empty; empty_CompoGType).

Definition transport_hom_GType {G G' H H':GType} (e:H = G) (e' : H' = G') :
           G ==> G' -> H ==> H'. 
  destruct e, e'. exact id.
Defined.

Notation "G [ A , B ]" := (hom' G A B) (at level 80).

Notation "| G |" := (objects G.1) (at level 80).

Notation "A ** B" := (prod' A B) (at level 90).

Notation " A ==> B " := (A.1 ==> B.1) (at level 90).

(* Instance transport_terminal : transport_eq ωterminal *)
(*   := canonical_transport _. *)


Definition terminal_is_hprop G `(G = ωterminal) n (x y : cell n G) : x = y.
  generalize x y. clear x y. rewrite H. induction n. destruct x, y; reflexivity.
  intros. destruct x as [[x x'] c], y as [[y y'] c']. 
  destruct x, x', y ,y'. refine (path_sigma' _ _ _ ). reflexivity. apply IHn. 
Defined. 

Definition empty_is_false_fun G (f: G ==> CGempty) n (c : cell n G) T : T c.
  pose (c' := cellGHom _ _ _ f c). destruct n. destruct c'.
  destruct c' as [[y y' ] c']. destruct y. 
Defined. 

Definition empty_is_false G (f: G = CGempty) n (c : cell n G) T : T c.
  apply empty_is_false_fun. rewrite f. apply GId. 
Defined.

CoFixpoint prod_empty_L G H : G ==> CGempty -> (G ** H) ==> CGempty.
  intro f. refine (mkGHom _ _ _ _).  
  intros [x y]. destruct (f @@ x).
  intros [x x'] [y y']. exact (prod_empty_L (G [x, y]) (H [x', y']) (f <<x,y>>)).
Defined.

CoFixpoint prod_empty_R G H : H ==> CGempty -> (G ** H) ==> CGempty.
  intro f. refine (mkGHom _ _ _ _).  
  intros [x y]. destruct (f @@ y).
  intros [x x'] [y y']. exact (prod_empty_R (G [x, y]) (H [x', y']) (f <<x',y'>>)).
Defined.

Definition unique_morphism G (f g : G ==> ωterminal) : GHom_eq_cell _ _ f g.
  intro n. generalize dependent G. induction n; intros G f g c. 
  - destruct (f `@c` c), (g `@c` c). reflexivity. 
  - destruct c as [[x y] c]. refine (path_sigma_uncurried _ _ _ ). simpl.
    destruct (@app _ terminal f x), (@app _ terminal f y), (@app _ terminal g x), (@app _ terminal g y).
    exists (eq_refl _). exact (IHn _ _ _ c). 
Defined.

CoFixpoint unitalityR_terminal : @unitalityR ωterminal (canonicalTriangle _).
apply mkUnitalityR.
- intros x y. apply unique_morphism. 
- intros x y. apply unitalityR_terminal.
Defined.

CoFixpoint unitalityL_terminal : @unitalityL ωterminal (canonicalTriangle _).
apply mkUnitalityL.
- intros x y. apply unique_morphism. 
- intros x y. apply unitalityL_terminal.
Defined.

Definition unique_morphism_empty G (f g: G ==> CGempty) : GHom_eq_cell _ _ f g.
  intros n c; destruct n. 
  - destruct (f `@c` c).
  - destruct c as [[x y] c]. destruct (f @@ x).
Defined.

CoFixpoint unitalityR_empty : @unitalityR CGempty (canonicalTriangle _).
apply mkUnitalityR.
- intros x y. apply unique_morphism_empty. 
- intros x y. apply unitalityR_empty.
Defined.

CoFixpoint unitalityL_empty : @unitalityL CGempty (canonicalTriangle _).
apply mkUnitalityL.
- intros x y. apply unique_morphism_empty. 
- intros x y. apply unitalityL_empty.
Defined.

CoFixpoint associativity_terminal : @associativity ωterminal (canonicalSquare _).
apply mkAssociativity.
- intros x y z t. apply unique_morphism. 
- intros x y. apply associativity_terminal.
Defined.

CoFixpoint associativity_empty : @associativity CGempty (canonicalSquare _).
apply mkAssociativity.
- intros x y z t. apply unique_morphism_empty. 
- intros x y. apply associativity_empty.
Defined.

CoFixpoint preservesCompo_terminal G (f : G ==> ωterminal): @preservesCompo _ _ f (canonicalSquare _).
apply mkPreservesCompo.
- intros. apply unique_morphism. 
- intros x y. apply preservesCompo_terminal.
Defined.

CoFixpoint preservesId_terminal G (f : G ==> ωterminal): @preservesId _ _ f.
apply mkPreservesId.
- intros. destruct (identity (f @@ x)), ((f << x, x >>) @@ identity x). reflexivity. 
- intros x y. apply preservesId_terminal.
Defined.

CoFixpoint compo_ωFunctor_terminal : @compo_ωFunctor ωterminal (canonicalSquare _).
apply mkcompo_ωFunctor.
- intros. split. apply preservesCompo_terminal. apply preservesId_terminal.
- intros. apply compo_ωFunctor_terminal.
Defined.

CoFixpoint preservesCompo_empty G (f : G ==> CGempty): @preservesCompo _ _ f (canonicalSquare _).
apply mkPreservesCompo.
- intros. apply unique_morphism_empty. 
- intros x y. apply preservesCompo_empty.
Defined.

CoFixpoint preservesId_empty G (f : G ==> CGempty): @preservesId _ _ f.
apply mkPreservesId.
- intros. destruct (identity (f @@ x)).
- intros x y. apply preservesId_empty.
Defined.

CoFixpoint compo_ωFunctor_empty : @compo_ωFunctor CGempty (canonicalSquare _).
apply mkcompo_ωFunctor.
- intros. split. apply preservesCompo_empty. apply preservesId_empty.
- intros. apply compo_ωFunctor_empty.
Defined.


Definition path_unitalityR G H `(H = G) :
  @unitalityR G (canonicalTriangle _) -> @unitalityR H (canonicalTriangle _).
  destruct H0. exact id.
Defined. 

Definition path_unitalityL G H `(H = G) :
  @unitalityL G (canonicalTriangle _) -> @unitalityL H (canonicalTriangle _).
  destruct H0. exact id.
Defined. 

CoFixpoint preservesCompo_empty_domL G H (f : CGempty ** G ==> H):
  @preservesCompo _ _ f (canonicalSquare _).
apply mkPreservesCompo.
- intros. intros n c.  match goal with | |- ?T =>
       refine (@empty_is_false_fun _ _ n c (fun c => T))  end. 
  apply prod_empty_R. apply (prod_empty_L CGempty (G[_,_])). apply GId.
- intros x y. apply (preservesCompo_empty_domL (G[_,_])).
Defined.

CoFixpoint preservesCompo_empty_domR G H (f : G ** CGempty ==> H):
  @preservesCompo _ _ f (canonicalSquare _).
apply mkPreservesCompo.
- intros. intros n c.  match goal with | |- ?T =>
       refine (@empty_is_false_fun _ _ n c (fun c => T))  end. 
  apply prod_empty_R. apply (prod_empty_R (G[_,_]) CGempty). apply GId.
- intros x y. apply (preservesCompo_empty_domR (G[_,_])).
Defined.

Definition path_preservesCompo G H H' (e : H = H') (f : G ==> H) :
  @preservesCompo G H' (transport (fun X => _ ==> X) e f) (canonicalSquare _) ->
  @preservesCompo G H f (canonicalSquare _).
  destruct e. exact id.
Defined.

Definition path_preservesCompo' G G' H (e : G = G') (f : G ==> H) :
  @preservesCompo G' H (transport (fun X => X ==> _) e f) (canonicalSquare _) ->
  @preservesCompo G H f (canonicalSquare _).
  destruct e. exact id.
Defined.

CoFixpoint preservesId_empty_domL G H (f : CGempty ** G ==> H): preservesId _ _ f.
apply mkPreservesId.
- intros [x y]. destruct x.
- intros [x x'] [y y']. destruct x.
Defined.

CoFixpoint preservesId_empty_domR G H (f : G ** CGempty ==> H): preservesId _ _ f.
apply mkPreservesId.
- intros [x y]. destruct y.
- intros [x x'] [y y']. destruct x'.
Defined.

Definition path_preservesId G H H' (e : H = H') (f : G ==> H) :
  @preservesId G H' (transport (fun X => _ ==> X) e f) ->
  @preservesId G H f.
  destruct e. exact id.
Defined.

Definition path_preservesId' G G' H (e : G = G') (f : G ==> H) :
  @preservesId G' H (transport (fun X => X ==> _) e f) ->
  @preservesId G H f .
  destruct e. exact id.
Defined.

Definition path_compo_ωFunctor H H' (e : H = H') :
  @compo_ωFunctor H (canonicalSquare _) -> @compo_ωFunctor H' (canonicalSquare _).
  destruct e. exact id.
Defined.


Definition path_associativity H H' (e : H = H') :
  @associativity H (canonicalSquare _) -> @associativity H' (canonicalSquare _).
  destruct e. exact id.
Defined.


Instance terminal_IsOmegaCategory : IsOmegaCategory ωterminal _ _ :=
  {| _idR := unitalityR_terminal ;
     _idL := unitalityL_terminal ;
     _compo_ωFunctor := compo_ωFunctor_terminal;
     _assoc := associativity_terminal
|}.

Definition ω_terminal : wild_ωcat := (ωterminal; terminal_IsOmegaCategory).

(** The omega category of the circle S1 *)

Definition GS1 := @mkGType unit (λ _ _ : unit,
                  @mkGType nat  (λ z z', if Decidable_to_bool (decpaths_nat z z') 
                                         then terminal
                                         else empty)).

Notation "G [ A , B ]" := (hom G A B) (at level 80).

Definition GS1_eq_terminal (g g':nat) : g = g' -> (GS1 [tt, tt]) [g, g'] = terminal.
  destruct 1. unfold hom'; simpl. rewrite decpaths_nat_refl. reflexivity.
Defined.

Definition GS1_neq_empty (g g':nat) : ~~ g = g' -> (GS1 [tt, tt]) [g, g'] = empty.
  unfold hom'; simpl; intro H. rewrite (decpaths_nat_neq H).2. reflexivity.
Defined.

Definition Compo_S1 : Compo GS1.
apply mkCompo; intros. 
- econstructor. apply (mkGHom (product (hom GS1 x y) (hom GS1 y z)) (hom GS1 x z)
                              (fun z => fst z + snd z)).
  + destruct x, y ,z. intros [e e'] [h h'].
    exact (match decpaths_nat e h with
             | inl H => match decpaths_nat e' h' with
                          | inl H' => transport_hom_GType
                                        (ap2 _ (GS1_eq_terminal H) (GS1_eq_terminal H'))
                                        (GS1_eq_terminal (ap2 plus H H'))
                                        (@compo _ _ _ (composable_id_left _))
                          | inr H' => transport_hom_GType
                                        (ap2 _ eq_refl (GS1_neq_empty H'))
                                        eq_refl
                                        (@compo _ _ _ (uncomposable_right _ _))
                        end
             | inr H =>  transport_hom_GType
                                        (ap2 _ (GS1_neq_empty H) eq_refl)
                                        eq_refl
                                        (@compo _ _ _ (uncomposable_left _ _))
           end).
- apply mkCompo; intros; simpl.
   + destruct (decpaths_nat x0 y0); destruct (decpaths_nat y0 z); destruct (decpaths_nat x0 z);
     simpl; intros; try apply composable_id_left; try apply composable_id_right;
     try apply uncomposable_left; try apply uncomposable_right.
     destruct (n (e @ e0)).
   + destruct (decpaths_nat x0 y0); try apply Compo_terminal; apply Compo_empty.
Defined.

Definition Id_S1 : Id GS1.
  apply mkId.
  - intro. exact 0.
  - intros x y. destruct x, y.  apply mkId.
    + intro z. rewrite (GS1_eq_terminal (eq_refl z)). exact tt.
    + intros z z'. simpl. destruct (decpaths_nat z z'). apply Id_terminal. apply Id_empty.
Defined.

Instance CompoGType_S1 : IsωPreCat GS1 := 
{| _comp := Compo_S1; _id := Id_S1|}. 

Definition CGS1 : ωPreCat := (GS1; CompoGType_S1).

Notation "G [ A , B ]" := (hom' G A B) (at level 80).

Definition CGS1_eq_terminal (g g':nat) : g = g' -> (CGS1 [tt, tt]) [g, g'] = ωterminal.
  destruct 1. unfold hom'; simpl. refine (path_sigma' _ _ _).
  - rewrite decpaths_nat_refl. reflexivity.
  - rewrite transport_IsωPreCat. apply path_IsωPreCat; simpl.
    + unfold compoHom. simpl. rewrite decpaths_nat_refl. reflexivity. 
    + unfold idHom. simpl. rewrite decpaths_nat_refl. reflexivity. 
Defined.

Definition CGS1_neq_empty (g g':nat) : ~~ g = g' -> (CGS1 [tt, tt]) [g, g'] = CGempty.
  unfold hom'; simpl; intro H. refine (path_sigma' _ _ _).
  - rewrite (decpaths_nat_neq H).2. reflexivity.
  - rewrite transport_IsωPreCat. apply path_IsωPreCat; simpl.
    + unfold compoHom. simpl. rewrite (decpaths_nat_neq H).2. reflexivity. 
    + unfold idHom. simpl. rewrite (decpaths_nat_neq H).2. reflexivity. 
Defined.

Definition unitalityR_S1 : @unitalityR CGS1 (@canonicalTriangle _).
apply mkUnitalityR.
- intros. destruct x, y. intros n c. destruct n.
  + apply Plus.plus_0_r.
  + destruct c as [[[x x'] [y y']] c]. destruct x', y'.
    refine (path_sigma' _ _ _). simpl. refine (path_prod _ _ _ _).
    apply Plus.plus_0_r. apply Plus.plus_0_r. 
    case (decpaths_nat x y); intro H. 
    apply (terminal_is_hprop (CGS1_eq_terminal H)).
    apply (empty_is_false (CGS1_neq_empty H)).
- intros. destruct x, y.
  apply mkUnitalityR; intros x y.  
  case (decpaths_nat x y); intros H c n.
  apply (terminal_is_hprop (CGS1_eq_terminal H)).
  apply (empty_is_false (CGS1_neq_empty H)). 
  case (decpaths_nat x y); intros H.
  apply (path_unitalityR (CGS1_eq_terminal H) unitalityR_terminal). 
  apply (path_unitalityR (CGS1_neq_empty H) unitalityR_empty). 
Defined. 

Definition unitalityL_S1 : @unitalityL CGS1 (@canonicalTriangle _).
apply mkUnitalityL.
- intros. destruct x, y. intros n c. destruct n.
  + apply Plus.plus_0_l.
  + destruct c as [[[x' x] [y' y]] c]. destruct x', y'.
    refine (path_sigma' _ _ _). simpl. refine (path_prod _ _ _ _).
    apply Plus.plus_0_l. apply Plus.plus_0_l.
    case (decpaths_nat x y); intro H.
    apply (terminal_is_hprop (CGS1_eq_terminal H)).
    apply (empty_is_false (CGS1_neq_empty H)).
- intros. destruct x, y.
  apply mkUnitalityL; intros x y.  
  case (decpaths_nat x y); intros H c n.
  apply (terminal_is_hprop (CGS1_eq_terminal H)).
  apply (empty_is_false (CGS1_neq_empty H)). 
  case (decpaths_nat x y); intros H.
  apply (path_unitalityL (CGS1_eq_terminal H) unitalityL_terminal). 
  apply (path_unitalityL (CGS1_neq_empty H) unitalityL_empty). 
Defined.

CoFixpoint compo_ωFunctor_S1 : @compo_ωFunctor CGS1 (canonicalSquare _).
apply mkcompo_ωFunctor. 
- intros x y z. destruct x, y, z. split.
  + apply mkPreservesCompo.
  * intros [x x'] [y y'] [z z'] n c.  
    case (decpaths_nat x y); intro H.
    case (decpaths_nat x' y'); intro H'.
    case (decpaths_nat y z); intro G.
    case (decpaths_nat y' z'); intro G'.
    apply terminal_is_hprop. simpl.
    exact (CGS1_eq_terminal (ap2 plus (H @ G) (H' @ G'))).
    match goal with | |- ?T =>
           refine (@empty_is_false_fun _ _ n c (fun c => T))  end. 
    apply prod_empty_R. refine (prod_empty_R ((CGS1 [tt, tt])[y,z]) ((CGS1 [tt, tt])[y', z']) _).
    rewrite (CGS1_neq_empty G'). apply GId.
    match goal with | |- ?T =>
           refine (@empty_is_false_fun _ _ n c (fun c => T))  end. 
    apply prod_empty_R. refine (prod_empty_L ((CGS1 [tt, tt])[y,z]) ((CGS1 [tt, tt])[y', z']) _).
    rewrite (CGS1_neq_empty G). apply GId.
    match goal with | |- ?T =>
           refine (@empty_is_false_fun _ _ n c (fun c => T))  end. 
    apply prod_empty_L. refine (prod_empty_R ((CGS1 [tt, tt])[x,y]) ((CGS1 [tt, tt])[x', y']) _).
    rewrite (CGS1_neq_empty H'). apply GId.
    match goal with | |- ?T =>
           refine (@empty_is_false_fun _ _ n c (fun c => T))  end. 
    apply prod_empty_L. refine (prod_empty_L ((CGS1 [tt, tt])[x,y]) ((CGS1 [tt, tt])[x', y']) _).
    rewrite (CGS1_neq_empty H). apply GId.
  * intros [x x'] [y y'].
    case (decpaths_nat x y); intro H.
    case (decpaths_nat x' y'); intro H'.
    refine (path_preservesCompo (CGS1_eq_terminal (ap2 plus H H')) _ _).
    apply preservesCompo_terminal.
    refine (@path_preservesCompo' _ ((CGS1 [tt, tt] [x,y]) ** CGempty) _ _ _ _).
    rewrite <- (CGS1_neq_empty H'). reflexivity. 
    apply preservesCompo_empty_domR.
    refine (@path_preservesCompo' _ (CGempty ** (CGS1 [tt, tt] [x',y'])) _ _ _ _).
    rewrite <- (CGS1_neq_empty H). reflexivity. 
    apply preservesCompo_empty_domL.
  + apply mkPreservesId.
    * intros [x x']. refine (terminal_is_hprop _ 0 _ (identity (x' ° x))).
      apply (CGS1_eq_terminal eq_refl).    
    * intros [x x'] [y y'].  
      case (decpaths_nat x y); intro H.
      case (decpaths_nat x' y'); intro H'.
      refine (path_preservesId (CGS1_eq_terminal (ap2 plus H H')) _ _).
      apply preservesId_terminal.
      refine (@path_preservesId' _ ((CGS1 [tt, tt] [x,y]) ** CGempty) _ _ _ _).
      rewrite <- (CGS1_neq_empty H'). reflexivity. 
      apply preservesId_empty_domR.
      refine (@path_preservesId' _ (CGempty ** (CGS1 [tt, tt] [x',y'])) _ _ _ _).
      rewrite <- (CGS1_neq_empty H). reflexivity. 
      apply preservesId_empty_domL.
- intros x y. destruct x, y. 
  apply mkcompo_ωFunctor.
  + intros x y z. split.
    * case (decpaths_nat x z); intro H.
      refine (path_preservesCompo (CGS1_eq_terminal H) _ _).
      apply preservesCompo_terminal.
      refine (path_preservesCompo (CGS1_neq_empty H) _ _).
      apply preservesCompo_empty.
    * case (decpaths_nat x z); intro H.
      refine (path_preservesId (CGS1_eq_terminal H) _ _).
      apply preservesId_terminal.
      refine (path_preservesId (CGS1_neq_empty H) _ _).
      apply preservesId_empty.
  + intros x y.
    case (decpaths_nat x y); intro H.
    refine (path_compo_ωFunctor (eq_sym (CGS1_eq_terminal H)) _).
    apply compo_ωFunctor_terminal.
    refine (path_compo_ωFunctor (eq_sym (CGS1_neq_empty H)) _).
    apply compo_ωFunctor_empty.
Defined.

CoFixpoint associativity_S1 : @associativity CGS1 (canonicalSquare _).
apply mkAssociativity. 
- intros x y z t n c. destruct x, y, z, t. destruct n.
  + apply Plus.plus_assoc.
  + destruct c as [[[x [x' x'']] [y [y' y'']]] c].
    refine (path_sigma' _ _ _). refine (path_prod _ _ _ _).
    apply Plus.plus_assoc. apply Plus.plus_assoc.
    case (decpaths_nat x y); intro H.
    case (decpaths_nat x' y'); intro H'.
    case (decpaths_nat x'' y''); intro H''.
    apply terminal_is_hprop. exact (CGS1_eq_terminal (ap2 plus (ap2 plus H H') H'')).
    match goal with | |- ?T =>
           refine (@empty_is_false_fun _ _ n c (fun c => T))  end. 
    refine (prod_empty_R ((CGS1 [tt, tt])[x,y]) (((CGS1 [tt, tt])[x',y']) ** ((CGS1 [tt, tt])[x'',y''])) _).
    refine (prod_empty_R ((CGS1 [tt, tt])[x',y']) ((CGS1 [tt, tt])[x'', y'']) _).
    rewrite (CGS1_neq_empty H''). apply GId.
    match goal with | |- ?T =>
           refine (@empty_is_false_fun _ _ n c (fun c => T))  end. 
    refine (prod_empty_R ((CGS1 [tt, tt])[x,y]) (((CGS1 [tt, tt])[x',y']) ** ((CGS1 [tt, tt])[x'',y''])) _).
    refine (prod_empty_L ((CGS1 [tt, tt])[x',y']) ((CGS1 [tt, tt])[x'', y'']) _).
    rewrite (CGS1_neq_empty H'). apply GId.
    match goal with | |- ?T =>
           refine (@empty_is_false_fun _ _ n c (fun c => T))  end. 
    refine (prod_empty_L ((CGS1 [tt, tt])[x,y]) (((CGS1 [tt, tt])[x',y']) ** ((CGS1 [tt, tt])[x'',y''])) _).
    rewrite (CGS1_neq_empty H). apply GId.
- intros x y. destruct x, y.  apply mkAssociativity. 
  + intros x y z t n c. 
    case (decpaths_nat x y); intro H.
    case (decpaths_nat y z); intro H'.
    case (decpaths_nat z t); intro H''.
    apply terminal_is_hprop. exact (CGS1_eq_terminal (H @ H' @ H'')).
    match goal with | |- ?T =>
           refine (@empty_is_false_fun _ _ n c (fun c => T))  end. 
    refine (prod_empty_R _ _ _). refine (prod_empty_R _ _ _).
    rewrite (CGS1_neq_empty H''). apply GId.
    match goal with | |- ?T =>
           refine (@empty_is_false_fun _ _ n c (fun c => T))  end. 
    refine (prod_empty_R _ _ _). refine (prod_empty_L _ _ _).
    rewrite (CGS1_neq_empty H'). apply GId.
    match goal with | |- ?T =>
           refine (@empty_is_false_fun _ _ n c (fun c => T))  end. 
    refine (prod_empty_L _ _ _). rewrite (CGS1_neq_empty H). apply GId.
  + intros x y. case (decpaths_nat x y); intro H.
    refine (path_associativity (eq_sym (CGS1_eq_terminal H)) _).
    apply associativity_terminal.
    refine (path_associativity (eq_sym (CGS1_neq_empty H)) _).
    apply associativity_empty.
Defined.

Instance S1_IsOmegaCategory : IsOmegaCategory CGS1 _ _ :=
  {| _idR := unitalityR_S1;
     _idL := unitalityL_S1;
     _compo_ωFunctor := compo_ωFunctor_S1;
     _assoc := associativity_S1
|}.

Definition ωS1 : wild_ωcat := (CGS1; S1_IsOmegaCategory).

