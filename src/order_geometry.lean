import basic
import incidence_geometry

open incidence_geometry
open_locale classical

class order_geometry (Point Line : Type*) extends incidence_geometry Point Line :=
  (between: Point → Point → Point →  Prop)
  (notation A `*` B `*` C := between A B C)
  (B11 {A B C: Point} (h : A * B * C) : different3 A B C ∧ collinear Line A B C ∧ C * B * A)
  (B12 {A B C: Point} (h : A * B * C) : C * B * A)
  (B2 {A B : Point} (h : A ≠ B): ∃ C : Point, A * B * C)
  (B3 {A B C : Point} (h : collinear Line A B C): xor3 (A * B * C) (B * A * C) (A * C * B))
  (B4 {A B C D : Point} {l : Line} (h_non_collinear : ¬ collinear Line A B C) 
      (hlABC : ¬ (A ~ l ∨ B ~ l ∨ C ~ l)) (hlD : D ~ l) (hADB : A * D * B)
      : xor (∃ E ,  E ~ l ∧ (A * E * C)) (∃ E, E ~ l ∧ (B * E * C)))

-- structure Triangle (Point : Type*) := (A B C : Point) (diff : different3 A B C)

-- instance (Point Line : Type) [order_geometry Point Line] : has_mem Point (Triangle Point) := 
--   ⟨λ P T, 
--       P ∈ (Segment.mk T.A T.B T.diff.1) 
--     ∨ P ∈ (Segment.mk T.A T.C T.diff.2.1) 
--     ∨ P ∈ (Segment.mk T.B T.C T.diff.2.2)⟩


namespace order_geometry

variables {Point Line : Type*} [og : order_geometry Point Line]

lemma between_symm (A B C : Point) : (og.between A B C) ↔ (og.between C B A) :=
begin
  split,
  { intro h, exact og.B12 h },
  { intro h, exact og.B12 h },
end

structure Segment (Point : Type*) := (A B : Point) (diff : A ≠ B)

instance : has_mem Point (Segment Point) := 
⟨λ P S, P = S.A ∨ P = S.B ∨ (og.between S.A P S.B)⟩

/- TODO: Usar instancia de mem -/
def segment_intersect_line (S : Segment Point) (l : Line) := 
∃ P : Point, (P = S.A ∨ P = S.B ∨ (og.between S.A P S.B)) ∧ P ~ l

def line_same_side (l: Line) (A B : outside_line_points Point l) := 
A = B ∨ (∃ h : ↑A ≠ ↑B, ¬ @segment_intersect_line Point Line og (Segment.mk A B h) l)

variable (Point)

theorem line_same_side_refl (l : Line) : reflexive (@line_same_side Point Line og l) := 
begin
  intro P,
  left,
  refl,
end 

theorem line_same_side_symm (l : Line) : symmetric (@line_same_side Point Line og l) := 
begin
  intros P Q h,
  cases h with h1 h2,
  { left, rw h1 },
  { cases h2 with h h2, 
    right,
    use h.symm,
    rw segment_intersect_line at h2 ⊢,
    push_neg at h2 ⊢, 
    intro A,
    specialize h2 A,
    rw between_symm,
    tauto },
end

theorem line_same_side_trans (l : Line) : transitive (@line_same_side Point Line og l) := 
begin
  intros A B C hAB hBC,
  cases hAB,
  { rw hAB, exact hBC },
  { cases hBC, 
    { rw ← hBC, right, exact hAB }, 
    { cases hAB with hAneB hAB,
      cases hBC with hBneC hBC,
      by_cases hAC : A = C,
      { left, exact hAC },
      { right, 
        let hAC' := (outside_line_points_lift_ne Point l A C).mp hAC,
        use hAC',
        rw segment_intersect_line at hAB hBC ⊢, 
        push_neg at hAB hBC ⊢, 
        rintros P (h1|h2|h3),
        { apply hAB P, left, exact h1 },
        { apply hBC P, right, left, exact h2 },
        { by_cases h_collinear : ¬ collinear Line (↑A: Point) ↑B ↑C,
          { /- Case 1 in Hartshorne -/
            by_contra hDl,
            rw [collinear_comm2, collinear_comm, collinear_comm2] at h_collinear,
            have hlABC : ¬ (↑A ~ l ∨ ↑C ~ l ∨ ↑B ~ l),
            { push_neg, 
              split,
              { apply hAB (↑A : Point), left, exact rfl },
              { split, 
                { apply hBC (↑C : Point), right, left, exact rfl }, 
                { apply hBC (↑B : Point), left, exact rfl }}}, 
            cases (B4 h_collinear hlABC hDl h3).or,
            { cases h with E h, 
              apply (and_not_self (E ~ l)).mp,
              refine ⟨h.left, _⟩, 
              apply hAB E,
              right, right,
              exact h.right },
            { cases h with E h, 
              apply (and_not_self (E ~ l)).mp,
              refine ⟨h.left, _⟩, 
              apply hBC E,
              right, right,
              apply B12,
              exact h.right },
            },
          { /- Case 2 in Hartshorne -/
            push_neg at h_collinear, 
            cases h_collinear with m h,
            have hD : ∃ D : Point, D ~ l ∧ ¬ D ~ m, { sorry },
            cases hD with D hD,
            have hDA : D ≠ ↑A , { sorry },
            have hE : ∃ E : Point, D * ↑A * E, { cases (og.B2 hDA) with E hE, use E, exact hE },
            cases hE with E hE,
            have hDAE_collinear : collinear Line D A E, { exact (og.B11 hE).right.left },
            sorry }
          }}}},
end

theorem line_same_side_equiv (l : Line) : equivalence (@line_same_side Point Line og l) :=
⟨line_same_side_refl Point l, line_same_side_symm Point l, line_same_side_trans Point l⟩

def LineSide.setoid [og : order_geometry Point Line] (l : Line) : setoid (outside_line_points Point l) :=
{ r := line_same_side l, iseqv := line_same_side_equiv Point l }
local attribute [instance] LineSide.setoid

def LineSide [og : order_geometry Point Line] (l : Line) := quotient (LineSide.setoid Point l)
def LineSide.reduce [og : order_geometry Point Line] (l : Line) : outside_line_points Point l → LineSide Point l := quot.mk (line_same_side l)
instance [og : order_geometry Point Line] (l : Line) : has_lift (outside_line_points Point l) (LineSide Point l) := ⟨LineSide.reduce Point l⟩ 
instance [og : order_geometry Point Line] (l : Line) : has_coe  (outside_line_points Point l) (LineSide Point l) := ⟨LineSide.reduce Point l⟩ 

theorem plane_separation (Point Line : Type*) [og : order_geometry Point Line] (l : Line) (A B : outside_line_points Point l): 
  ¬ A ≈ B ↔ :=
begin
  split,
  { rw segment_intersect_line, 
    intro h, 
    cases h with P hP,
    rcases hP with ⟨hP, hPl⟩,
    sorry },
  { sorry }
end

end order_geometry