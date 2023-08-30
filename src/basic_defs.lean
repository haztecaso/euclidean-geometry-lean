/-- Relación que establece que tres términos de un tipo son distintos. -/
def neq3 {T : Type*} (A B C : T) := (A ≠ B ∧ A ≠ C ∧ B ≠ C)

/-- Definición de xor entre tres proposiciones. -/
def xor3 (p q r : Prop) : Prop := 
  (p ∧ ¬ q ∧ ¬ r) ∨ (¬ p ∧ q ∧ ¬ r) ∨ (¬ p ∧ ¬ q ∧ r)
