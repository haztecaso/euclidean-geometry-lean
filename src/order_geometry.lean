import basic
import incidence_geometry

open incidence_geometry

class order_geometry (Point Line : Type*) extends incidence_geometry Point Line :=
  (between: Point → Point → Point →  Prop)
  (notation A `*` B `*` C := between A B C)
  (B11 {A B C: Point} (h : A * B * C) : different3 A B C ∧ collinear Line A B C ∧ C * B * A)
  (B12 {A B C: Point} (h : A * B * C) : C * B * A)
  (B2 {A B : Point} (h : A ≠ B): ∃ C : Point, A * B * C)
  (B3 {A B C : Point} (h : collinear Line A B C): xor3 (A * B * C) (B * A * C) (A * C * B))
  (B4 {A B C D : Point} {l : Line} (h_non_collinear : ¬ collinear Line A B C) 
      (hlABC : ¬ (A ~ l ∨ B ~ l ∨ C ~ l)) (hlD : D ~ l) (hADB : A * D * B)
      : (∃ E ,  E ~ l ∧ (A * E * C)) xor (∃ E, E ~ l ∧ (B * E * C)))

structure Segment (Point : Type*) := (A B : Point) (diff : A ≠ B)

instance (Point Line : Type) [og: order_geometry Point Line]: has_mem Point (Segment Point) := 
  ⟨λ P S, P = S.A ∨ P = S.B ∨ og.between P S.A S.B⟩

structure Triangle (Point : Type*) := (A B C : Point) (diff : different3 A B C)

instance (Point Line : Type) [order_geometry Point Line]: has_mem Point (Triangle Point) := 
  ⟨λ P T, 
    P   ∈ (⟨T.A, T.B, T.diff.1⟩   : Segment Point) 
    ∨ P ∈ (⟨T.A, T.C, T.diff.2.1⟩ : Segment Point) 
    ∨ P ∈ (⟨T.B, T.C, T.diff.2.2⟩ : Segment Point)⟩

namespace order_geometry

notation A `*` B `*` C := between A B C

end order_geometry