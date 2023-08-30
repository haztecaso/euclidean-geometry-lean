import .basic ..incidence_geometry.propositions

open incidence_geometry

namespace order_geometry
variables {Point : Type*} (Line : Type*) [og : order_geometry Point Line]
local notation A `*` B `*` C := og.between A B C

/-- 
Hilbert's theorem 3.
Para dos puntos distintos existe un tercero entre ellos
-/
lemma point_between_given {A C : Point} (hAC : A ≠ C): ∃ B : Point, A * B * C := 
begin
  let AC := line Line hAC,
  have hE : ∃ E : Point, ¬ E ~ AC.val, { exact line_external_point AC.val },
  cases hE with E hE,
  have hAE : A ≠ E, { sorry }, 
  have hF : ∃ F : Point, A * E * F, { exact og.B2 hAE }, 
  cases hF with F hF,
  have hFC : F ≠ C, { sorry }, 
  have hG : ∃ G : Point, F * C * G, { exact og.B2 hFC }, 
  cases hG with G hG,
  have hGE : G ≠ E, { sorry }, 
  let GE := line Line hGE,
  have sAC : Seg Point := {
    A := A,
    B := C,
    neq := hAC,
  },
  let h := @seg_intersect_line Point Line og sAC GE,
  -- rw ← segment_intersect_line at h,
  -- have hB : segment_intersect_line
  sorry
end

variable (Point)

/-- La relación de estar del mismo lado de una línea es reflexiva. -/
lemma same_side_line_refl (l : Line) : 
  reflexive (@same_side_line Point Line og l) := 
begin
  intro P,
  left,
  refl,
end 

/-- La relación de estar del mismo lado de una línea es simétrica. -/
lemma same_side_line_symm (l : Line) : 
  symmetric (@same_side_line Point Line og l) := 
begin
  intros P Q h,
  cases h with h1 h2,
  { left, rw h1 },
  { cases h2 with h h2, 
    right,
    use h.symm,
    rw seg_intersect_line at h2 ⊢,
    push_neg at h2 ⊢, 
    intros A hA,
    apply h2 A,
    sorry },
end

-- /-- 
-- Lema útil para demostrar la transitividad de la relación de estar del mismo lado de una línea.
-- Se demuestra la transitividad para puntos no colineares.
-- -/
-- lemma same_side_line'_trans_noncollinear_case 
--   (l : Line) (A B C : outside_line_points Point l) 
--   (h: ¬ collinear Line (↑A:Point) ↑B ↑C) :
-- (same_side_line' l A B) → (same_side_line' l B C) → (same_side_line' l A C):= 
-- begin
--   sorry
-- end

/-- 
La relación de estar del mismo lado de una línea es transitiva.
Esta es la propiedad más difícil de demostrar. 
Para esto reducimos la demostración a dos casos:
- Tres puntos no colineares. Tratado en el lema anterior.
- Tres puntos colineares. Reducible mediante construcciones al caso anterior.
-/
lemma same_side_line_trans (l : Line) : 
  transitive (@same_side_line Point Line og l) := 
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
        use hAC,
        rw seg_intersect_line at hAB hBC ⊢, 
        push_neg at hAB hBC ⊢, 
        rintros P (h1|h2|h3),
        { apply hAB P, left, exact h1 },
        { apply hBC P, right, left, exact h2 },
        { by_cases h_collinear : ¬ collinear Line (↑A: Point) ↑B ↑C,
          { /- Case 1 in Hartshorne -/
            by_contra hDl,
            rw [collinear_symm2, collinear_symm, collinear_symm2] 
              at h_collinear,
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
            have hE : ∃ E : Point, D * ↑A * E,
              { cases (og.B2 hDA) with E hE, use E, exact hE },
            cases hE with E hE,
            have hDAE_collinear : collinear Line D A E,
              { exact (og.B11 hE).right.left },
            sorry }
          }}}},
end

/-- La relación de estar del mismo lado del plano respecto de una línea es de 
equivalencia. -/
theorem same_side_line_equiv (l : Line) :
  equivalence (@same_side_line Point Line og l) :=
  ⟨same_side_line_refl Point l, 
    same_side_line_symm Point l, 
    same_side_line_trans Point l⟩

/-- Teorema de separación del plano. -/
theorem plane_separation {Point Line : Type*} [og : order_geometry Point Line] 
  (l : Line) {A B : Point} (hAB: A ≠ B) :
  seg_intersect_line (Seg.mk hAB) l ↔ ¬ A = B :=
begin
  split,
  { rw seg_intersect_line, 
    intro h, 
    cases h with P hP,
    rcases hP with ⟨hP, hPl⟩,
    sorry },
  { sorry }
end

end order_geometry