Add LoadPath "." as OmegaCategories.
Require Export Unicode.Utf8_core.
Require Import Omega BinInt. 
Require Import path GType omega_categories type_to_omega_cat Integers. 

Set Implicit Arguments.

Notation "| G |" := (objects G) (at level 80).
Notation "G [ A , B ]" := (hom G A B) (at level 80).
Notation "A ** B" := (product A B) (at level 90).
Notation " A ==> B " := (GHom A B) (at level 90).


(** 
- The constant globular set (parameterised by any set X0) *)
CoFixpoint Delta (X0 : Type) : GType := @mkGType X0 (fun _ _ => Delta X0).


(** The empty type *)
Inductive Empty : Type := .

(** 
- The empty globular set *)

Definition empty : GType := Delta Empty.

(** 
- The terminal one: *)

Definition terminal : GType := Delta unit.

(** 
- The discrete one, parameterised by any set X0, i.e., X0 in dim 0 and empty elsewhere *)

CoFixpoint Discrete (X0 : Type) : GType := @mkGType X0 (fun _ _ => empty).

(** The S1 *)

(* Definition GS1 := @mkGType unit (λ _ _ : unit, *)
(*                   @mkGType Int  (λ z z', match decpaths_int z z' with *)
(*                                            | inl _ => terminal *)
(*                                            | inr _ => empty *)
(*                                          end)). *)
Definition GS1 := @mkGType unit (λ _ _ : unit,
                  @mkGType nat  (λ z z', match decpaths_nat z z' with
                                           | inl _ => terminal
                                           | inr _ => empty
                                         end)).

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

Definition GS1_eq_terminal (g g':nat) : g = g' -> (GS1 [tt, tt]) [g, g'] = terminal.
  destruct 1. unfold hom'; simpl. rewrite decpaths_nat_refl. reflexivity.
Defined.

Definition GS1_neq_empty (g g':nat) : ~~ g = g' -> (GS1 [tt, tt]) [g, g'] = empty.
  unfold hom'; simpl; intro H. rewrite (decpaths_nat_neq H).2. reflexivity.
Defined.

(* Definition GS1 := @mkGType unit (fun _ _ => @mkGType Z (fun _ _ => terminal)). *)

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

Definition CGterminal : ωPreCat := (terminal; terminal_CompoGType).

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

Definition Compo_S1 : Compo GS1.
apply mkCompo; intros.
- econstructor. apply (mkGHom (product (hom GS1 x y) (hom GS1 y z)) (hom GS1 x z)
                              (fun z => fst z + snd z)).
  + intros [e e'] [h h']. 
    case (decpaths_nat e h); intro. case (decpaths_nat e' h'); intro.
    * (* pose (GS1_eq_terminal e0). pose (GS1_eq_terminal e1). *)
      (* pose (GS1_eq_terminal (ap2 plus e0 e1)). *)
      (* simpl in *. rewrite e2, e3, e4. apply compo.  *)
      destruct e0, e1. simpl. repeat rewrite decpaths_nat_refl. apply compo.
    * pose (GS1_neq_empty n). simpl in *. rewrite e1. apply uncomposable_right.
    * pose (GS1_neq_empty n). simpl in *. rewrite e0. apply uncomposable_left.
- apply mkCompo; intros; simpl.
   + case (decpaths_nat x0 y0); case (decpaths_nat y0 z); case (decpaths_nat x0 z);
     simpl; intros; try apply composable_id_left; try apply composable_id_right; try apply uncomposable_left; try apply uncomposable_right.
     destruct (n (e0 @ e)).
   + case (decpaths_nat x0 y0); intro; try apply Compo_terminal; apply Compo_empty.
Defined.

Definition Id_S1 : Id GS1.
  apply mkId.
  - intro. exact 0.
  - intros. apply mkId.
    + intro z. simpl. case (decpaths_nat z z); intro. exact tt. destruct (n eq_refl).
    + intros z z'. simpl. case (decpaths_nat z z'); simpl; intro. apply Id_terminal.
      apply Id_empty.
Defined.

Instance CompoGType_S1 : IsωPreCat GS1 := 
{| _comp := Compo_S1; _id := Id_S1|}. 

Definition CGS1 : ωPreCat := (GS1; CompoGType_S1).

Notation "G [ A , B ]" := (hom' G A B) (at level 80).

Notation "| G |" := (objects G.1) (at level 80).

Notation "A ** B" := (prod' A B) (at level 90).

Notation " A ==> B " := (A.1 ==> B.1) (at level 90).

Instance transport_terminal : _transport_eq CGterminal
  := canonical_transport _.

CoFixpoint unique_morphism G (f g : G ==> CGterminal) : GHom_eq _ _ f g.
refine (mkGHom_eq_J _ _ _ _).
- intros. destruct (f @@ x), (g @@ x); reflexivity.
- intros. apply unique_morphism.
Defined.

CoFixpoint transport_is_canonical_canonical_terminal :
  transport_is_canonical (canonical_transport CGterminal).
apply mkTransport_compat.
- intros. apply unique_morphism. 
- intros. apply unique_morphism. 
- intros. apply transport_is_canonical_canonical_terminal.  
Defined.

Instance transport_terminal' : transport_eq CGterminal :=
  {| _transport_is_canonical := transport_is_canonical_canonical_terminal |}.

CoFixpoint compoIdR_Hterminal H h _trans comp :
  @compoIdR_H CGterminal H h _trans comp.
refine (mkCompoIdR_H _ _ _ _ _).
- intro g. match goal with | |- ?e = _ => destruct e, g end. reflexivity.
- intros e e'. apply compoIdR_Hterminal.
Defined.

CoFixpoint compoIdR_terminal _trans : @compoIdR CGterminal _trans.
apply mkCompoIdr.
- intros. apply compoIdR_Hterminal.
- intros. apply compoIdR_terminal.
Defined.

CoFixpoint compoIdL_Hterminal H h _trans comp :
  @compoIdL_H H CGterminal h _trans comp.
refine (mkCompoIdL_H _ _ _ _ _).
- intro g. match goal with | |- ?e = _ => destruct e, g end. reflexivity.
- intros e e'. apply compoIdL_Hterminal.
Defined.

CoFixpoint compoIdL_terminal _trans : @compoIdL CGterminal _trans.
apply mkCompoIdL.
- intros. apply compoIdL_Hterminal.
- intros. apply compoIdL_terminal.
Defined.

CoFixpoint compoIdR_Hempty H h _trans comp:
  @compoIdR_H CGempty H h _trans comp.
refine (mkCompoIdR_H _ _ _ _ _).
- destruct g.
- intros e e'. apply compoIdR_Hempty.
Defined.

CoFixpoint compoIdR_empty _trans : @compoIdR CGempty _trans.
apply mkCompoIdr.
- intros. apply compoIdR_Hempty.
- intros. apply compoIdR_empty.
Defined.

CoFixpoint compoIdL_Hempty H h _trans comp:
  @compoIdL_H H CGempty h _trans comp.
refine (mkCompoIdL_H _ _ _ _ _).
- intro g; destruct g.
- intros e e'. apply compoIdL_Hempty.
Defined.

CoFixpoint compoIdL_empty _trans : @compoIdL CGempty _trans.
apply mkCompoIdL.
- intros; apply compoIdL_Hempty.
- intros; apply compoIdL_empty.
Defined.

Instance transport_S1 : _transport_eq CGS1
  := canonical_transport _.

CoFixpoint empty_morphism H (f g : CGempty ==> H) : GHom_eq _ _ f g.
refine (mkGHom_eq_J _ _ _ _).
- intros. destruct x.
- intros. apply empty_morphism.
Defined.

CoFixpoint transport_is_canonical_canonical_empty :
  transport_is_canonical (canonical_transport CGempty).
apply mkTransport_compat.
- intros. apply empty_morphism. 
- intros. apply empty_morphism. 
- intros. apply transport_is_canonical_canonical_empty.  
Defined.

Definition transport_GHom_eq G H G' H' (eG : G = G') (eH: H = H') f g :
  GHom_eq G' H'
          (transport (fun X => X ==> H') eG (transport (fun X => G ==> X) eH f))
          (transport (fun X => X ==> H') eG (transport (fun X => G ==> X) eH g))
          -> GHom_eq G H f g.
  destruct eG, eH. auto.
Defined.


Definition CGS1_eq_terminal (g g':nat) : g = g' -> (CGS1 [tt, tt]) [g, g'] = CGterminal.
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


CoFixpoint transport_is_canonical_canonical_S1 :
  transport_is_canonical (canonical_transport CGS1).
apply mkTransport_compat.
- intros. refine (mkGHom_eq_J _ _ _ _).
  + intros. reflexivity.
  + destruct e, z. intros n m. case (decpaths_nat n m); intro H. 
      * refine (transport_GHom_eq (CGS1_eq_terminal H) (CGS1_eq_terminal H) _ _ _).
        apply unique_morphism.
      * refine (transport_GHom_eq (CGS1_neq_empty H) (CGS1_neq_empty H) _ _ _).
        apply empty_morphism.
- intros. refine (mkGHom_eq_J _ _ _ _).
  + intros. reflexivity.
  + destruct e, x. intros n m. case (decpaths_nat (n+0) (m+0)); intro H. 
      * refine (transport_GHom_eq eq_refl (CGS1_eq_terminal H) _ _ _).
        apply unique_morphism.
      * assert (H0 : ~~ n = m). intro e; apply H. repeat rewrite <- plus_n_O. auto.
        refine (transport_GHom_eq (CGS1_neq_empty H0) (CGS1_neq_empty H) _ _ _).
        apply empty_morphism.
- intros. destruct x, y.
  apply mkTransport_compat.
  + intros n m p. intro e. destruct e. unfold transport_GHomL_compat. simpl.
    case (decpaths_nat n p); intro H. 
    * refine (transport_GHom_eq (CGS1_eq_terminal H) (CGS1_eq_terminal H) _ _ _).
      apply unique_morphism.
    * refine (transport_GHom_eq (CGS1_neq_empty H) (CGS1_neq_empty H) _ _ _).
      apply empty_morphism.
  + intros n m p. intro e. destruct e. unfold transport_GHomL_compat. simpl.
    case (decpaths_nat n m); intro H. 
    * refine (transport_GHom_eq (CGS1_eq_terminal H) (CGS1_eq_terminal H) _ _ _).
      apply unique_morphism.
    * refine (transport_GHom_eq (CGS1_neq_empty H) (CGS1_neq_empty H) _ _ _).
      apply empty_morphism.
  + intros n m. case (decpaths_nat n m); intro H. 
    unfold transport_GHom_eq_hom. simpl. rewrite (CGS1_eq_terminal H).
    apply transport_is_canonical_canonical_terminal.  
    unfold transport_GHom_eq_hom. simpl. rewrite (CGS1_neq_empty H).
    apply transport_is_canonical_canonical_empty.  
Defined.

Instance transport_S1' : transport_eq CGS1 :=
    {| _transport_is_canonical := transport_is_canonical_canonical_S1 |}.


Definition path_compoIdR_H (G G' H : ωPreCat) (candidate_id : | H |)
           (_trans' : transport_eq G') 
           (composable' : Composable G'.1 H.1 G'.1)
           (e :  G = G') :
  (forall _trans composable, @compoIdR_H G H candidate_id _trans composable) ->
  @compoIdR_H G' H candidate_id _trans' composable'.
intro. specialize (X (inverse e # _trans') (transport (fun X => Composable X.1 _ X.1) (inverse e) composable')).
refine (mkCompoIdR_H _ _ _ _ _).
-  destruct e, X. apply idR.
- intros g g'. destruct X, e. apply c. 
Defined.  

Definition path_compoIdR (G G' : ωPreCat)
           (_trans' : transport_eq G') (e :  G = G') :
  (forall _trans, @compoIdR G _trans) -> @compoIdR G' _trans'.
intro. specialize (X (inverse e # _trans')). refine (mkCompoIdr _ _ _).
-  destruct e, X. apply c.
- intros g g'. destruct X, e. apply c0. 
Defined.  


Definition compoIdR_S1 : compoIdR CGS1.
apply mkCompoIdr.
- intros. refine (mkCompoIdR_H _ _ _ _ _).
  + intros. symmetry. apply plus_n_O.
  + destruct x, y. intros. 
    case (decpaths_nat g g'); intro H. 
    apply (path_compoIdR_H _ _ (inverse (CGS1_eq_terminal H)) (compoIdR_Hterminal _ _)).
    apply (path_compoIdR_H _ _ (inverse (CGS1_neq_empty H)) (compoIdR_Hempty _ _)).
 - intros. destruct x,y. apply mkCompoIdr.
  + intros g g'. case (decpaths_nat g g'); intro H. 
    apply (path_compoIdR_H _ _ (inverse (CGS1_eq_terminal H)) (compoIdR_Hterminal _ _)).
    apply (path_compoIdR_H _ _ (inverse (CGS1_neq_empty H)) (compoIdR_Hempty _ _)).
  + intros g g'. case (decpaths_nat g g'); intro H.
    apply (path_compoIdR _ (inverse (CGS1_eq_terminal H)) compoIdR_terminal).
    apply (path_compoIdR _ (inverse (CGS1_neq_empty H)) compoIdR_empty).
Defined.


Definition path_compoIdL_H (G G' H : ωPreCat) (candidate_id : | H |)
           (_trans' : transport_eq G') 
           (composable' : Composable H.1 G'.1  G'.1)
           (e :  G = G') :
  (forall _trans composable, @compoIdL_H H G candidate_id _trans composable) ->
  @compoIdL_H H G' candidate_id _trans' composable'.
  intro. destruct e, (X _trans' composable'). refine (mkCompoIdL_H _ _ _ _ _); auto.
Defined.

Definition path_compoIdL (G G' : ωPreCat)
           (_trans' : transport_eq G') (e :  G = G') :
  (forall _trans, @compoIdL G _trans) -> @compoIdL G' _trans'.
  intro. destruct e, (X _trans'). refine (mkCompoIdL _ _ _); auto.
Defined.  

Definition compoIdL_S1 : compoIdL CGS1.
apply mkCompoIdL.
- intros. refine (mkCompoIdL_H _ _ _ _ _).
  + intros. reflexivity. 
  + destruct x, y. intros g g'. 
    case (decpaths_nat g g'); intro H. 
    apply (path_compoIdL_H _ _ (inverse (CGS1_eq_terminal H)) (compoIdL_Hterminal _ _)).
    apply (path_compoIdL_H _ _ (inverse (CGS1_neq_empty H)) (compoIdL_Hempty _ _)).
 - intros. destruct x,y. apply mkCompoIdL.
  + intros g g'. case (decpaths_nat g g'); intro H. 
    apply (path_compoIdL_H _ _ (inverse (CGS1_eq_terminal H)) (compoIdL_Hterminal _ _)).
    apply (path_compoIdL_H _ _ (inverse (CGS1_neq_empty H)) (compoIdL_Hempty _ _)).
  + intros g g'. case (decpaths_nat g g'); intro H.
    apply (path_compoIdL _ (inverse (CGS1_eq_terminal H)) compoIdL_terminal).
    apply (path_compoIdL _ (inverse (CGS1_neq_empty H)) compoIdL_empty).
Defined.


CoFixpoint idCompoH_terminalL G : @idCompoH CGterminal G G (composable_id_left G.1).
apply mkIdCompoH. intros. reflexivity.
intros. apply idCompoH_terminalL.
Defined.

CoFixpoint idCompoH_terminalR G : @idCompoH G CGterminal G (composable_id_right G.1).
  apply mkIdCompoH. intros. reflexivity.
  intros. apply idCompoH_terminalR.
Defined.

CoFixpoint idCompoH_terminal_gen comp : @idCompoH CGterminal CGterminal CGterminal comp.
apply mkIdCompoH. intros f g. destruct (identity g ° identity f), (identity (g ° f)); reflexivity.
intros. apply idCompoH_terminal_gen.
Defined.

CoFixpoint idCompo_terminal : idCompo CGterminal.
  apply mkIdCompo. intros. exact (idCompoH_terminal_gen _).
  intros. apply idCompo_terminal.
Defined.

CoFixpoint idCompoH_emptyL G H comp : @idCompoH CGempty G H comp.
apply mkIdCompoH. intros. destruct f. 
intros. apply idCompoH_emptyL.
Defined.

CoFixpoint idCompoH_emptyR G H comp : @idCompoH G CGempty H comp.
apply mkIdCompoH. intros. destruct g.
intros. apply idCompoH_emptyR.
Defined.

CoFixpoint idCompo_empty : idCompo CGempty.
apply mkIdCompo. intros. apply idCompoH_emptyL.
intros. apply idCompo_empty.
Defined.

Definition CGS1_eq_terminal_contr (g g':nat) (eq:g = g') : 
 forall (e e' : |(CGS1 [tt, tt]) [g, g']|), e = e'.
rewrite (CGS1_eq_terminal eq). destruct e, e'. reflexivity. 
Defined.

Definition path_idCompoH (G G' H H' K K' : ωPreCat)
           (comp : Composable G'.1 H'.1 K'.1)
           (eG :  G = G') (eH :  H = H') (eK : K = K') :
  (forall comp, @idCompoH G H K comp) -> @idCompoH G' H' K' comp.
  intro. destruct eG, eH, eK, (X comp). refine (mkIdCompoH _ _); auto.
Defined.  

CoFixpoint idCompo_S1 : idCompo CGS1.
apply mkIdCompo.
- intros. destruct x, y, z. apply mkIdCompoH.
  + intros f g. apply (CGS1_eq_terminal_contr eq_refl).
  + intros f f' g g'.
    case (decpaths_nat f f'); intro Hf.
    case (decpaths_nat g g'); intro Hg.
    assert (Hfg : g ° f = g' ° f'). destruct Hf, Hg. reflexivity. 
    apply (path_idCompoH _ (inverse (CGS1_eq_terminal Hf)) (inverse (CGS1_eq_terminal Hg))
                         (inverse (CGS1_eq_terminal Hfg)) idCompoH_terminal_gen).
    apply (path_idCompoH _ eq_refl (inverse (CGS1_neq_empty Hg))
                         eq_refl (idCompoH_emptyR _ _)).
    apply (path_idCompoH _ (inverse (CGS1_neq_empty Hf)) eq_refl 
                         eq_refl (idCompoH_emptyL _ _)).
- intros. destruct x, y. refine (mkIdCompo _ _).
  + intros.  case (decpaths_nat x y); intro Hf.
    case (decpaths_nat y z); intro Hg.
    apply (path_idCompoH _ (inverse (CGS1_eq_terminal Hf)) (inverse (CGS1_eq_terminal Hg))
                         (inverse (CGS1_eq_terminal (Hf@Hg))) idCompoH_terminal_gen).
    apply (path_idCompoH _ eq_refl (inverse (CGS1_neq_empty Hg))
                         eq_refl (idCompoH_emptyR _ _)).
    apply (path_idCompoH _ (inverse (CGS1_neq_empty Hf)) eq_refl 
                         eq_refl (idCompoH_emptyL _ _)).
  + intros. case (decpaths_nat x y); intro Hf.
    rewrite (CGS1_eq_terminal Hf). exact idCompo_terminal.
    rewrite (CGS1_neq_empty Hf). exact idCompo_empty.
Defined.

CoFixpoint interchangeV_terminal G1 G2 G3 G4 G5 G6 G7 G8 trans comp1 comp2 comp3 comp4 comp5 comp6 :
  @interchangeV G1 G2 G3 G4 G5 G6 G7 G8 CGterminal trans comp1 comp2 comp3 comp4 comp5 comp6.
apply mkInterchangeV. refine (existT _ _ _).
- intros. match goal with | |- ?e = ?e' => destruct e, e' end. reflexivity.
- intros. apply interchangeV_terminal.
Defined.

CoFixpoint interchangeH_terminal G H trans comp :
  @interchangeH G H CGterminal trans comp.
apply mkInterchangeH. 
- intros. apply interchangeV_terminal. 
- intros. apply interchangeH_terminal.
Defined.

CoFixpoint interchange_terminal trans : @interchange CGterminal trans.
apply mkInterchange.
- intros. apply interchangeH_terminal. 
- intros. apply interchange_terminal.
Defined.

CoFixpoint interchangeV_empty1 G1 G2 G3 G4 G5 G6 G7 G8 trans comp1 comp2 comp3 comp4 comp5 comp6 :
  @interchangeV CGempty G1 G2 G3 G4 G5 G6 G7 G8 trans comp1 comp2 comp3 comp4 comp5 comp6.
apply mkInterchangeV. refine (existT _ _ _).
- intros. destruct f1.
- intros. apply interchangeV_empty1.
Defined.

CoFixpoint interchangeV_empty2 G1 G2 G3 G4 G5 G6 G7 G8 trans comp1 comp2 comp3 comp4 comp5 comp6 :
  @interchangeV G1 CGempty  G2 G3 G4 G5 G6 G7 G8 trans comp1 comp2 comp3 comp4 comp5 comp6.
apply mkInterchangeV. refine (existT _ _ _).
- intros. destruct f2.
- intros. apply interchangeV_empty2.
Defined.

CoFixpoint interchangeV_empty3 G1 G2 G3 G4 G5 G6 G7 G8 trans comp1 comp2 comp3 comp4 comp5 comp6 :
  @interchangeV G1 G2 G3 CGempty G4 G5 G6 G7 G8 trans comp1 comp2 comp3 comp4 comp5 comp6.
apply mkInterchangeV. refine (existT _ _ _).
- intros. destruct g1.
- intros. apply interchangeV_empty3.
Defined.

CoFixpoint interchangeV_empty4 G1 G2 G3 G4 G5 G6 G7 G8 trans comp1 comp2 comp3 comp4 comp5 comp6 :
  @interchangeV G1 G2 G3 G4 CGempty G5 G6 G7 G8 trans comp1 comp2 comp3 comp4 comp5 comp6.
apply mkInterchangeV. refine (existT _ _ _).
- intros. destruct g2.
- intros. apply interchangeV_empty4.
Defined.

CoFixpoint interchangeH_emptyL G H trans comp :
  @interchangeH CGempty G H trans comp.
apply mkInterchangeH. 
- intros f. destruct f.  
- intros. apply interchangeH_emptyL.
Defined.

CoFixpoint interchangeH_emptyR G H trans comp :
  @interchangeH G CGempty H trans comp.
apply mkInterchangeH. 
- intros f f' f'' g. destruct g.  
- intros. apply interchangeH_emptyR.
Defined.

CoFixpoint interchange_empty trans : @interchange CGempty trans.
apply mkInterchange.
- intros. apply interchangeH_emptyL. 
- intros. apply interchange_empty.
Defined.


Definition path_interchangeV G1 G2 G3 G4 G5 G6 G7 G8 G9 G1' G2' G3' G4' G5' G6' G7' G8' G9'
           trans comp1 comp2 comp3 comp4 comp5 comp6 
           (e1 : G1 = G1') (e2 : G2 = G2') (e3 : G3 = G3')
           (e4 : G4 = G4') (e5 : G5 = G5') (e6 : G6 = G6')
           (e7 : G7 = G7') (e8 : G8 = G8') (e9 : G9 = G9'):
  (forall _trans comp1 comp2 comp3 comp4 comp5 comp6,
    @interchangeV G1 G2 G3 G4 G5 G6 G7 G8 G9 _trans comp1 comp2 comp3 comp4 comp5 comp6) ->
  @interchangeV G1' G2' G3' G4' G5' G6' G7' G8' G9' trans comp1 comp2 comp3 comp4 comp5 comp6.
  intro. destruct e1, e2, e3, e4, e5, e6, e7, e8, e9, (X trans comp1 comp2 comp3 comp4 comp5 comp6).
  apply mkInterchangeV. refine (existT _ _ _). apply s.1. apply s.2.  
Defined.

Definition path_interchangeH G1 G2 G3  G1' G2' G3'
           trans comp1 
           (e1 : G1 = G1') (e2 : G2 = G2') (e3 : G3 = G3'):
  (forall _trans comp1, @interchangeH G1 G2 G3  _trans comp1) ->
  @interchangeH G1' G2' G3' trans comp1.
  intro. destruct e1, e2, e3, (X trans comp1). apply mkInterchangeH; auto.
Defined.

Definition path_interchange G1 G1' trans (e1 : G1 = G1') :
  (forall _trans, @interchange G1 _trans) -> @interchange G1' trans.
  intro. destruct e1, (X trans). apply mkInterchange; auto.
Defined.

CoFixpoint interchange_S1 : @interchange CGS1 _.
apply mkInterchange.
- intros. destruct x, y ,z. apply mkInterchangeH.
  + intros. case (decpaths_nat f f'); intro Hf.
    case (decpaths_nat f' f''); intro Hf'.
    case (decpaths_nat g g'); intro Hg.
    case (decpaths_nat g' g''); intro Hg'.
    assert (H : g ° f= g'' ° f''). destruct Hf, Hf', Hg, Hg'. reflexivity.
    apply (path_interchangeV _ _ _ _ _ _ _ eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                             (inverse (CGS1_eq_terminal H))
                             (interchangeV_terminal _ _ _ _ _ _ _ _)).
    apply (path_interchangeV _ _ _ _ _ _ _ eq_refl eq_refl eq_refl eq_refl (inverse (CGS1_neq_empty Hg'))
                             eq_refl eq_refl eq_refl eq_refl
                             (@interchangeV_empty4 _ _ _ _ _ _ _ _)).
    apply (path_interchangeV _ _ _ _ _ _ _ eq_refl eq_refl eq_refl (inverse (CGS1_neq_empty Hg))
                             eq_refl eq_refl eq_refl eq_refl eq_refl
                             (@interchangeV_empty3 _ _ _ _ _ _ _ _)).
    apply (path_interchangeV _ _ _ _ _ _ _ eq_refl (inverse (CGS1_neq_empty Hf')) eq_refl eq_refl
                             eq_refl eq_refl eq_refl eq_refl eq_refl
                             (@interchangeV_empty2 _ _ _ _ _ _ _ _)).
    apply (path_interchangeV _ _ _ _ _ _ _ (inverse (CGS1_neq_empty Hf)) eq_refl eq_refl eq_refl
                             eq_refl eq_refl eq_refl eq_refl eq_refl
                             (@interchangeV_empty1 _ _ _ _ _ _ _ _)).
  + intros.
    case (decpaths_nat f f'); intro Hf.
    case (decpaths_nat g g'); intro Hg.
    assert (H : g ° f= g' ° f'). destruct Hf, Hg. reflexivity.
    apply (path_interchangeH _ _ eq_refl eq_refl (inverse (CGS1_eq_terminal H))
                             (interchangeH_terminal _ _)).
    apply (path_interchangeH _ _ eq_refl (inverse (CGS1_neq_empty Hg)) eq_refl
                             (@interchangeH_emptyR _ _)).
    apply (path_interchangeH _ _ (inverse (CGS1_neq_empty Hf)) eq_refl eq_refl 
                             (@interchangeH_emptyL _ _)).
- intros. destruct x, y.  apply mkInterchange.
  + intros.
    case (decpaths_nat x y); intro Hf.
    case (decpaths_nat y z); intro Hg.
    apply (path_interchangeH _ _ eq_refl eq_refl (inverse (CGS1_eq_terminal (Hf @ Hg)))
                             (interchangeH_terminal _ _)).
    apply (path_interchangeH _ _ eq_refl (inverse (CGS1_neq_empty Hg)) eq_refl
                             (@interchangeH_emptyR _ _)).
    apply (path_interchangeH _ _ (inverse (CGS1_neq_empty Hf)) eq_refl eq_refl 
                             (@interchangeH_emptyL _ _)).
  + intros. case (decpaths_nat x y); intro Hf.
    apply (path_interchange _ (inverse (CGS1_eq_terminal Hf)) interchange_terminal).
    apply (path_interchange _ (inverse (CGS1_neq_empty Hf)) interchange_empty).
Defined.

CoFixpoint associativityH_terminal G1 G2 G3 G12 G23 trans comp1 comp2 comp3 comp4 :
  @associativityH G1 G2 G3 G12 G23 CGterminal trans comp1 comp2 comp3 comp4.
apply mkAssociativityH. refine (existT _ _ _).
- intros. match goal with | |- ?e = ?e' => destruct e, e' end. reflexivity.
- intros. apply associativityH_terminal.
Defined.

CoFixpoint associativityH_empty1 G1 G2 G3 G12 G23 trans comp1 comp2 comp3 comp4 :
  @associativityH CGempty G1 G2 G3 G12 G23 trans comp1 comp2 comp3 comp4.
apply mkAssociativityH. refine (existT _ _ _).
- intros. destruct f.
- intros. apply associativityH_empty1.
Defined.

CoFixpoint associativityH_empty2 G1 G2 G3 G12 G23 trans comp1 comp2 comp3 comp4 :
  @associativityH G1 CGempty G2 G3 G12 G23 trans comp1 comp2 comp3 comp4.
apply mkAssociativityH. refine (existT _ _ _).
- intros. destruct g.
- intros. apply associativityH_empty2.
Defined.

CoFixpoint associativityH_empty3 G1 G2 G3 G12 G23 trans comp1 comp2 comp3 comp4 :
  @associativityH G1 G2 CGempty G3 G12 G23 trans comp1 comp2 comp3 comp4.
apply mkAssociativityH. refine (existT _ _ _).
- intros. destruct h.
- intros. apply associativityH_empty3.
Defined.

CoFixpoint associativity'_terminal trans : @associativity' CGterminal trans.
apply mkAssociativity'. 
- intros. apply associativityH_terminal. 
- intros. apply associativity'_terminal.
Defined.

Definition associativity_terminal trans : @associativity CGterminal trans :=
  assoc'_assoc (associativity'_terminal trans).

CoFixpoint associativity'_empty trans : @associativity' CGempty trans.
apply mkAssociativity'. 
- intros. apply associativityH_empty1. 
- intros. apply associativity'_empty.
Defined.

Definition path_associativityH G1 G2 G3 G12 G23 G
           G1' G2' G3' G12' G23' G'
           trans comp12 comp23 comp12_3 comp1_23
           (e1 : G1 = G1') (e2 : G2 = G2') (e3 : G3 = G3')
           (e12 : G12 = G12') (e23 : G23 = G23') (e : G = G') :
  (forall _trans comp12 comp23 comp12_3 comp1_23,
     @associativityH G1 G2 G3 G12 G23 G  _trans comp12 comp23 comp12_3 comp1_23) ->
  @associativityH G1' G2' G3' G12' G23' G' trans comp12 comp23 comp12_3 comp1_23.
  intro. destruct e1, e2, e3, e12, e23, e, (X trans comp12 comp23 comp12_3 comp1_23).
  apply mkAssociativityH; auto.
Defined.

Arguments associativityH : clear implicits.

Definition path_associativity G G' trans (e : G = G') :
  (forall _trans , @associativity' G _trans) -> @associativity' G' trans.
  intro. destruct e. apply X. 
Defined.

Definition associativity'_S1 : @associativity' CGS1 _.
  apply mkAssociativity'.
  - intros. destruct x, y ,z, t. apply mkAssociativityH. refine (existT _ _ _).
    + intros. apply Plus.plus_assoc.
    + intros. case (decpaths_nat f f'); intro Hf.
      case (decpaths_nat g g'); intro Hg.
      case (decpaths_nat h h'); intro Hh.
      assert (H : h ° (g ° f) = h' ° (g' ° f')). destruct Hf, Hg, Hh. reflexivity. 
      exact (path_associativityH _ _ _ _ _ eq_refl eq_refl eq_refl eq_refl eq_refl 
                             (inverse (CGS1_eq_terminal H)) 
                             (@associativityH_terminal _ _ _ _ _)).
      exact (path_associativityH _ _ _ _ _ eq_refl eq_refl (inverse (CGS1_neq_empty Hh))
                                 eq_refl eq_refl eq_refl 
                                 (@associativityH_empty3 _ _ _ _ _)).
      exact (path_associativityH _ _ _ _ _ eq_refl (inverse (CGS1_neq_empty Hg)) eq_refl 
                                 eq_refl eq_refl eq_refl 
                                 (@associativityH_empty2 _ _ _ _ _)).
      exact (path_associativityH _ _ _ _ _ (inverse (CGS1_neq_empty Hf)) eq_refl eq_refl 
                                 eq_refl eq_refl eq_refl 
                                 (@associativityH_empty1 _ _ _ _ _)).
  - intros. destruct x, y. apply mkAssociativity'.
  + intros.
    case (decpaths_nat x y); intro Hf.
    case (decpaths_nat y z); intro Hg.
    case (decpaths_nat z t); intro Hh.
      exact (path_associativityH _ _ _ _ _ eq_refl eq_refl eq_refl eq_refl eq_refl 
                             (inverse (CGS1_eq_terminal (Hf@Hg@Hh))) 
                             (@associativityH_terminal _ _ _ _ _)).
      exact (path_associativityH _ _ _ _ _ eq_refl eq_refl (inverse (CGS1_neq_empty Hh))
                                 eq_refl eq_refl eq_refl 
                                 (@associativityH_empty3 _ _ _ _ _)).
      exact (path_associativityH _ _ _ _ _ eq_refl (inverse (CGS1_neq_empty Hg)) eq_refl 
                                 eq_refl eq_refl eq_refl 
                                 (@associativityH_empty2 _ _ _ _ _)).
      exact (path_associativityH _ _ _ _ _ (inverse (CGS1_neq_empty Hf)) eq_refl eq_refl 
                                 eq_refl eq_refl eq_refl 
                                 (@associativityH_empty1 _ _ _ _ _)).
  + intros. case (decpaths_nat x y); intro Hf.
    apply (path_associativity _ (inverse (CGS1_eq_terminal Hf)) associativity'_terminal).
    apply (path_associativity _ (inverse (CGS1_neq_empty Hf)) associativity'_empty).
Defined.

Definition associativity_S1 : @associativity CGS1 _ :=
  assoc'_assoc associativity'_S1.

Definition terminal_compo_ωFunctor : @compo_ωFunctor CGterminal _ :=
  interchange_idcompo_compo_ωFunctor (interchange_terminal _) idCompo_terminal.

Definition S1_compo_ωFunctor : @compo_ωFunctor CGS1 _ :=
  interchange_idcompo_compo_ωFunctor interchange_S1 idCompo_S1.

Instance terminal_IsOmegaCategory : IsOmegaCategory CGterminal :=
  {| _tran := _;
     _idR := compoIdR_terminal _;
     _idL := compoIdL_terminal _;
     _compo_ωFunctor := terminal_compo_ωFunctor;
     _assoc := associativity_terminal _
|}.

Definition ω_terminal : ωcat := (CGterminal; terminal_IsOmegaCategory).

Instance S1_IsOmegaCategory : IsOmegaCategory CGS1 :=
  {| _tran := _;
     _idR := compoIdR_S1;
     _idL := compoIdL_S1;
     _compo_ωFunctor := S1_compo_ωFunctor;
     _assoc := associativity_S1
|}.

Definition ωS1 : ωcat := (CGS1; S1_IsOmegaCategory).

