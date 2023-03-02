import basic
import incidence_geometry

open has_lies_on

class order_geometry (Point : Type*) (Line : Type*) extends incidence_geometry Point Line :=
  (between: Point → Point → Point → Prop)
  (b1 (A B C: Point) : between A B C → different3 A B C ∧ collinear Line A B C ∧ between C B A)
  (b2 (A B : Point): A ≠ B → ∃ C : Point, between A B C)
  (b3 (A B C : Point) (h: collinear Line A B C): xor3 (between A B C) (between B A C) (between C A B))
  -- (b4 (A B C : Point): ¬ collinear Line A B C → )

notation A `*` B `*` C := order_geometry.between A B C


instance (Point Line: Type) [bg: order_geometry Point Line]: has_mem Point (Segment Point) := 
  ⟨λ P S, P = S.A ∨ P = S.B ∨ bg.between P S.A S.B⟩

instance (Point Line: Type) [bg: order_geometry Point Line]: has_mem Point (Triangle Point) := 
  ⟨λ P T, 
    P   ∈ (⟨T.A, T.B, T.diff.1⟩   : Segment Point) 
    ∨ P ∈ (⟨T.A, T.C, T.diff.2.1⟩ : Segment Point) 
    ∨ P ∈ (⟨T.B, T.C, T.diff.2.2⟩ : Segment Point)⟩

namespace betweenness_geometry

end betweenness_geometry