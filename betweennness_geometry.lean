import basic
import incidence_geometry

open has_lies_on

class betweenness_geometry (Point : Type*) (Line : Type*) extends incidence_geometry Point Line :=
  (between: Point → Point → Point → Prop)
  (b1 (A B C: Point) : between A B C → different3 A B C ∧ collinear Line A B C ∧ between C B A)
  (b2 (A B : Point): A ≠ B → ∃ C : Point, between A B C)
  -- (b3 (A B C : Point): different3 A B C ∧ (∃ l : Line, lies_on A l ∧ lies_on B l ∧ lies_on C l) → ())
  -- (b4 (A B C : Point): ¬ collinear Line A B C → )