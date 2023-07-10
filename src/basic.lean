def neq3 {T : Type*} (A B C : T) := (A ≠ B ∧ A ≠ C ∧ B ≠ C)

def xor3 (p q r : Prop) : Prop := (p ∧ ¬ q ∧ ¬ r) ∨ (¬ p ∧ q ∧ ¬ r) ∨ (¬ p ∧ ¬ q ∧ r)
