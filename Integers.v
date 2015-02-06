Require Import path.

Inductive Pos : Type :=
| one : Pos
| succ_pos : Pos -> Pos.

Definition not (T : Type) := T -> Empty. 

Notation "~~ A" := (not A) (at level 75).

Definition one_neq_succ_pos (z : Pos) : ~~ (one = succ_pos z)
  := fun p => transport (fun s => match s with one => unit | succ_pos t => Empty end) p tt.

Definition succ_pos_injective {z w : Pos} (p : succ_pos z = succ_pos w) : z = w
  := transport (fun s => z = (match s with one => w | succ_pos a => a end)) p (eq_refl z).

Inductive Int : Type :=
| neg : Pos -> Int
| zero : Int
| pos : Pos -> Int.

Definition neg_injective {z w : Pos} (p : neg z = neg w) : z = w
  := transport (fun s => z = (match s with neg a => a | zero => w | pos a => w end)) p (eq_refl z).

Definition pos_injective {z w : Pos} (p : pos z = pos w) : z = w
  := transport (fun s => z = (match s with neg a => w | zero => w | pos a => a end)) p (eq_refl z).

Definition neg_neq_zero {z : Pos} : ~~ (neg z = zero)
  := fun p => transport (fun s => match s with neg a => z = a | zero => Empty | pos _ => Empty end) p (eq_refl z).

Definition pos_neq_zero {z : Pos} : ~~ (pos z = zero)
  := fun p => transport (fun s => match s with pos a => z = a | zero => Empty | neg _ => Empty end) p (eq_refl z).

Definition neg_neq_pos {z w : Pos} : ~~ (neg z = pos w)
  := fun p => transport (fun s => match s with neg a => z = a | zero => Empty | pos _ => Empty end) p (eq_refl z).

(* And prove that they are a set. *)

Class Decidable (A : Type) :=
  dec : A + (~~ A).
Arguments dec A {_}.

Class DecidablePaths (A : Type) :=
  dec_paths : forall (x y : A), Decidable (x = y).
Global Existing Instance dec_paths.

Definition comp {T U V} (f : T -> U) (g:U -> V) := fun x => g (f x).

Notation "g 'o' f" := (comp f g) (at level 50).

Global Instance decpaths_int : DecidablePaths Int.
Proof.
  intros [n | | n] [m | | m].
  revert m; induction n as [|n IHn]; intros m; induction m as [|m IHm].
  exact (inl eq_refl).
  exact (inr (fun p => one_neq_succ_pos _ (neg_injective p))).
  exact (inr (fun p => one_neq_succ_pos _ (inverse (neg_injective p)))).
  destruct (IHn m) as [p | np].
  exact (inl (ap neg (ap succ_pos (neg_injective p)))).
  exact (inr (fun p => np (ap neg (succ_pos_injective (neg_injective p))))).
  exact (inr neg_neq_zero).
  exact (inr neg_neq_pos).
  exact (inr (neg_neq_zero o inverse)).
  exact (inl eq_refl).
  exact (inr (pos_neq_zero o inverse)).
  exact (inr (neg_neq_pos o inverse)).
  exact (inr pos_neq_zero).
  revert m; induction n as [|n IHn]; intros m; induction m as [|m IHm].
  exact (inl eq_refl).
  exact (inr (fun p => one_neq_succ_pos _ (pos_injective p))).
  exact (inr (fun p => one_neq_succ_pos _ (inverse (pos_injective p)))).
  destruct (IHn m) as [p | np].
  exact (inl (ap pos (ap succ_pos (pos_injective p)))).
  exact (inr (fun p => np (ap pos (succ_pos_injective (pos_injective p))))).
Defined.

Instance decpaths_nat : DecidablePaths nat.
intros x. induction x.
- destruct y.
 + left ;reflexivity.
 + right; intro H; inversion H.
- induction y.
  + right; intro H; inversion H.
  + case (IHx y). intro H. left. exact (f_equal S H).
    intro H; right. intro e. inversion e. apply (H H1).
Defined.


(* Successor is an autoequivalence of [Int]. *)

Definition succ_int (z : Int) : Int
  := match z with
       | neg (succ_pos n) => neg n
       | neg one => zero
       | zero => pos one
       | pos n => pos (succ_pos n)
     end.

Definition pred_int (z : Int) : Int
  := match z with
       | neg n => neg (succ_pos n)
       | zero => neg one
       | pos one => zero
       | pos (succ_pos n) => pos n
     end.

Fixpoint plus_pos (z z' : Pos) : Pos := match z with
     | one => succ_pos z'
     | succ_pos p => succ_pos (plus_pos p z')
   end.

Fixpoint pos_sub (x y:Pos) : Int :=
  match x, y with
    | one, one => zero
    | one, succ_pos n => neg n
    | succ_pos n, one => pos n
    | succ_pos n, succ_pos n' => pos_sub n n'                             
  end.

Definition plus_int (z z' : Int) : Int
  := match z,z' with
       | neg n, neg n' => neg (plus_pos n n')
       | pos n, pos n' => pos (plus_pos n n')
       | zero, _ => z'
       | _ , zero => z                        
       | pos n, neg n' => pos_sub n n'
       | neg n, pos n' => pos_sub n' n
     end.

Notation "z '.+' z'" := (plus_int z z') (at level 50).

Fixpoint plus_assoc (z z' z'': Int) : z .+ (z' .+ z'') = (z .+ z') .+ z''.
Admitted.

Fixpoint plus_left (z z' z'': Int) : z .+ z' = z .+ z'' -> z' = z''.
Admitted. 