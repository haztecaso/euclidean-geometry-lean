import tactic

def different3 {T : Type*} (A B C : T) := (A ≠ B ∧ A ≠ C ∧ B ≠ C)

notation p `xor` q := (p ∧ ¬ q) ∨ (q ∧ ¬ p)

def xor3 (p q r : Prop) : Prop := (p ∧ ¬ q ∧ ¬ r) ∨ (¬ p ∧ q ∧ ¬ r) ∨ (¬ p ∧ ¬ q ∧ r)

structure Segment (Point : Type*) := (A B : Point) (diff : A ≠ B)

structure Triangle (Point : Type*) := (A B C : Point) (diff : different3 A B C)