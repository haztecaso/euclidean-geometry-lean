import tactic

def different3 {T : Type*} (A B C : T) := (A ≠ B ∧ A ≠ C ∧ B ≠ C)

def xor3 (p q r : Prop) : Prop := (p ∧ ¬ q ∧ ¬ r) ∨ (¬ p ∧ q ∧ ¬ r) ∨ (¬ p ∧ ¬ q ∧ r)

structure Segment (Point : Type*) := (A B : Point) (diff : A ≠ B)

structure Triangle (Point : Type*) := (A B C : Point) (diff : different3 A B C)

class has_lies_on (Point Line : Type*) :=
  (lies_on : Point → Line → Prop)
  
namespace has_lies_on

infix ` ~ ` : 50 := lies_on

def points_in_line {Point Line : Type*} [has_lies_on Point Line] (A B : Point) (l : Line) :=
  A ~ l ∧ B ~ l

def collinear {Point : Type*} (Line: Type*) [has_lies_on Point Line] (A B C : Point) : Prop := 
  ∃ l : Line, A ~ l ∧ B ~ l ∧ C ~ l

namespace push_neg
lemma non_collinear {Point : Type*} (Line: Type*) [has_lies_on Point Line] (A B C : Point) : 
  ¬ collinear Line A B C ↔  ∀ x : Line, (¬ A ~ x ∨ ¬ B ~ x ∨ ¬ C ~ x)
:= begin 
  rw [collinear, push_neg.not_exists_eq],
  split,
  { intros h x, 
    specialize h x, 
    rw [push_neg.not_and_distrib_eq, push_neg.not_and_distrib_eq] at h,
    exact h },
  { intros h x, 
    specialize h x, 
    rw [push_neg.not_and_distrib_eq, push_neg.not_and_distrib_eq],
    exact h }
end 
end push_neg


def is_common_point {Point Line : Type*} [has_lies_on Point Line] (A : Point) (l m : Line) := 
  A ~ l ∧ A ~ m 

def have_common_point (Point : Type*) {Line : Type*} [has_lies_on Point Line]
  (l m : Line) := 
  ∃ A : Point, is_common_point A l m

end has_lies_on