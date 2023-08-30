import .basic ..incidence_geometry.propositions

/-!
# Sideness

En este fichero se plantea una formalización de la demostración de que la 
relación de estar del mismo lado del plano respecto de una línea es una relación 
de equivalencia. Queda pendiente terminar la demostración de la transitividad.

**Atención:** la relación considerada no es la misma que la definida en 
`order_geometry.basic`. En ese fichero se define la relación entre todos los 
puntos del plano, mientras que aquí se consideran sólo los externos a la recta 
considerada, como en el libro de Hartshorne.

-/

namespace incidence_geometry

/-- Conjunto de puntos de una línea. -/
def line_points (Point : Type*) {Line : Type*} [incidence_geometry Point Line] 
  (l: Line) := { A : Point | A ~ l }

/-- Conjunto de puntos externos a una línea. -/
def outside_line_points 
  (Point : Type*) {Line : Type*} [incidence_geometry Point Line] (l: Line) := 
  { A : Point | ¬ A ~ l }

instance (Point Line : Type*) [incidence_geometry Point Line] : 
  has_coe Line (set Point) := 
  { coe := line_points Point }

lemma line_points_lift_eq 
  (Point : Type*) {Line : Type*} [incidence_geometry Point Line] 
  (l : Line) (A B : line_points Point l) : 
  A = B ↔ (↑A : Point) = ↑B :=
by exact subtype.ext_iff

lemma line_points_lift_ne 
  (Point : Type*) {Line : Type*} [incidence_geometry Point Line] 
  (l : Line) (A B : line_points Point l) : 
  A ≠ B ↔ (↑A : Point) ≠ ↑B :=
by rw [ne.def, line_points_lift_eq]

lemma outside_line_points_lift_eq 
  (Point : Type*) {Line : Type*} [incidence_geometry Point Line] 
  (l : Line) (A B : outside_line_points Point l) : 
  A = B ↔ (↑A : Point) = ↑B :=
by exact subtype.ext_iff

lemma outside_line_points_lift_ne 
  (Point : Type*) {Line : Type*} [incidence_geometry Point Line] 
  (l : Line) (A B : outside_line_points Point l) :
  A ≠ B ↔ (↑A : Point) ≠ ↑B :=
by rw [ne.def, outside_line_points_lift_eq]

end incidence_geometry

open incidence_geometry

namespace order_geometry
variables {Point Line : Type*} [og : order_geometry Point Line]
local notation A `*` B `*` C := og.between A B C

/--
Relación de estar del mismo lado del plano respecto de una línea.
Dos puntos externos a una línea están del mismo lado de la línea si el segmento 
que los une no interseca a la línea.

TODO: Cambiar? Esta no es exactamente la definición del Hartshorne ya que en el 
libro está definida solo cuando los puntos son externos a la línea. Nosotros 
incluiremos esta hipótesis sólo en los casos donde sea necesario.
-/
def same_side_line' (l: Line) (A B : outside_line_points Point l) := 
  A = B ∨ (∃ h : ↑A ≠ ↑B, 
    ¬ @segment_intersect_line Point Line og (Seg.mk A B h) l)


variable (Point)

/-- La relación de estar del mismo lado de una línea es reflexiva. -/
lemma same_side_line'_refl (l : Line) : 
  reflexive (@same_side_line' Point Line og l) := 
begin
  intro P,
  left,
  refl,
end 

/-- La relación de estar del mismo lado de una línea es simétrica. -/
lemma same_side_line'_symm (l : Line) : 
  symmetric (@same_side_line' Point Line og l) := 
begin
  intros P Q h,
  cases h with h1 h2,
  { left, rw h1 },
  { cases h2 with h h2, 
    right,
    use h.symm,
    rw segment_intersect_line at h2 ⊢,
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
lemma same_side_line'_trans (l : Line) : 
  transitive (@same_side_line' Point Line og l) := 
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
theorem same_side_line'_equiv (l : Line) :
  equivalence (@same_side_line' Point Line og l) :=
  ⟨same_side_line'_refl Point l, 
    same_side_line'_symm Point l, 
    same_side_line'_trans Point l⟩

/-- Instancia de la clase setoid para la relación. -/
def PlaneSide.setoid 
  [og : order_geometry Point Line] (l : Line) : 
  setoid (outside_line_points Point l) :=
  { r := same_side_line' l, iseqv := same_side_line'_equiv Point l }

local attribute [instance] PlaneSide.setoid

/-- Conjunto cociente de los lados de una línea. -/
def PlaneSide [og : order_geometry Point Line] (l : Line) := 
  quotient (PlaneSide.setoid Point l)

def PlaneSide.reduce [og : order_geometry Point Line] (l : Line) : 
  outside_line_points Point l → PlaneSide Point l := 
  quot.mk (same_side_line' l)

instance [og : order_geometry Point Line] (l : Line) : 
  has_lift (outside_line_points Point l) (PlaneSide Point l) := 
  ⟨PlaneSide.reduce Point l⟩ 
instance [og : order_geometry Point Line] (l : Line) : 
  has_coe  (outside_line_points Point l) (PlaneSide Point l) := 
  ⟨PlaneSide.reduce Point l⟩ 

/-- Teorema de separación del plano. -/
theorem plane_separation 
  (Point Line : Type*) [og : order_geometry Point Line] 
  (l : Line) (A B : outside_line_points Point l) (hAB: A ≠ B) :
  @segment_intersect_line Point Line og 
    (Seg.mk A B ((outside_line_points_lift_ne Point l A B).mp hAB)) l
    ↔ ¬ A ≈ B :=
begin
  split,
  { rw segment_intersect_line, 
    intro h, 
    cases h with P hP,
    rcases hP with ⟨hP, hPl⟩,
    sorry },
  { sorry }
end

-- def line_points_different_to 
--   (Point : Type*) {Line : Type*} [incidence_geometry Point Line] 
--   (l: Line) (P : line_points Point l) := 
--   { A : Point | A ~ l ∧ A ≠ P }

end order_geometry