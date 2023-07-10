import basic
import incidence_geometry

open incidence_geometry
open_locale classical

/-!
# Axiomas de orden

En este fichero se enuncian los axiomas de orden de la geometría euclídea plana y se definen
entidades y demuestran resultados que dependen de estos axiomas.

## Notaciones

- Se mantiene el uso de la relación de incidencia A ~ l.
- Se utiliza la notación local A * B * C para la relación de orden.

-/

/-- Geometría del orden, clase que engloba los axiomas para la relación de orden. -/
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


namespace order_geometry

variables {Point Line : Type*} [og : order_geometry Point Line]

local notation A `*` B `*` C := og.between A B C

lemma between_symm (A B C : Point) : (A * B * C) ↔ (C * B * A) :=
begin
  split,
  { intro h, exact og.B12 h },
  { intro h, exact og.B12 h },
end

/-- 
Los segmentos están implementados mediante estructuras determinadas por dos puntos distintos.
-/
structure Segment (Point : Type*) := 
  (A B : Point) 
  (diff : A ≠ B)

/--
Relación de pertenencia entre puntos y segmentos.
Un punto está en un segmento si coincide con uno de los extremos o está entre ellos.
-/
instance : has_mem Point (Segment Point) := ⟨λ P seg, P = seg.A ∨ P = seg.B ∨ (seg.A * P * seg.B)⟩

/--
Relación de intersección entre segmentos y líneas.
Un segmento se interseca con una línea si tienen un punto en común
-/
def segment_intersect_line [order_geometry Point Line] (S : Segment Point) (l : Line) := 
∃ P : Point, P ∈ S ∧ P ~ l

/-- Un triángulo está determinado por tres puntos no alineados -/
structure Triangle (Point Line: Type*) [order_geometry Point Line] := 
  (A B C : Point) 
  (non_collinear : ¬ collinear Line A B C)

lemma Triangle.diff {Point Line: Type*} [order_geometry Point Line] (T : Triangle Point Line) : different3 T.A T.B T.C :=
begin  
  exact non_collinear_diff Line T.non_collinear,
end

-- instance (Point Line : Type) [order_geometry Point Line] : has_mem Point (Triangle Point) := 
--   ⟨λ P T, 
--       P ∈ (Segment.mk T.A T.B T.diff.1) 
--     ∨ P ∈ (Segment.mk T.A T.C T.diff.2.1) 
--     ∨ P ∈ (Segment.mk T.B T.C T.diff.2.2)⟩

structure Ray (Point : Type*) := 
  (A B: Point)
  (diff : A ≠ B)

instance [order_geometry Point Line] : has_mem Point (Ray Point) :=
  ⟨λ P ray, begin
    by_cases P ≠ ray.B,
    { exact P = ray.A ∨ ¬ ray.A ∈ Segment.mk P ray.B h },
    { exact true, },
  end ⟩

structure Angle (Point Line: Type*) [order_geometry Point Line] :=
  (r1 r2 : Ray Point)
  (vertex : r1.A = r2.A)
  (non_collinear : ¬ collinear Line r1.A r1.B r2.B)


def Angle.A {Point Line: Type*} [order_geometry Point Line] (α : Angle Point Line) : Point := α.r1.A

def Angle.B {Point Line: Type*} [order_geometry Point Line] (α : Angle Point Line) : Point := α.r1.B

def Angle.C {Point Line: Type*} [order_geometry Point Line] (α : Angle Point Line) : Point := α.r2.B

lemma Angle.diff {Point Line: Type*} [order_geometry Point Line] (α : Angle Point Line) : different3 α.A α.B α.C :=
begin  
  exact non_collinear_diff Line α.non_collinear,
end

def Angle.mk_from_points [order_geometry Point Line] (B A C : Point) (h : ¬ collinear Line A B C): Angle Point Line := 
begin
  let diff := non_collinear_diff Line h,
  let r1 := Ray.mk A B diff.left,
  let r2 := Ray.mk A C diff.right.left,
  have vertex : r1.A = r2.A, { refl },
  exact ⟨r1, r2, vertex, h⟩
end

variable (Line)

/-- 
Hilbert's theorem 3
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
  have sAC : Segment Point := {
    A := A,
    B := C,
    diff := hAC,
  },
  let h :=@segment_intersect_line Point Line og sAC GE,
  -- rw ← segment_intersect_line at h,
  -- have hB : segment_intersect_line
  sorry
end

variable {Line}

/--
Relación de estar del mismo lado del plano respecto de una línea.
Dos puntos externos a una línea están del mismo lado de la línea si el segmento que los 
une no interseca a la línea.
-/
def plane_same_side (l: Line) (A B : outside_line_points Point l) := 
  A = B ∨ (∃ h : ↑A ≠ ↑B, ¬ @segment_intersect_line Point Line og (Segment.mk A B h) l)

def plane_same_side' (l: Line) (A B : Point) := 
  A = B ∨ (∃ h : A ≠ B, ¬ @segment_intersect_line Point Line og (Segment.mk A B h) l)


variable (Point)

/-- La relación de estar del mismo lado de una línea es reflexiva. -/
lemma plane_same_side_refl (l : Line) : reflexive (@plane_same_side Point Line og l) := 
begin
  intro P,
  left,
  refl,
end 


/-- La relación de estar del mismo lado de una línea es simétrica. -/
lemma plane_same_side_symm (l : Line) : symmetric (@plane_same_side Point Line og l) := 
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
-- lemma plane_same_side_trans_noncollinear_case (l : Line) (A B C : outside_line_points Point l) (h: ¬ incidence_geometry.collinear Line (↑A:Point) ↑B ↑C) :
-- (plane_same_side l A B) → (plane_same_side l B C) → (plane_same_side l A C):= 
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
lemma plane_same_side_trans (l : Line) : transitive (@plane_same_side Point Line og l) := 
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

/-- La relación de estar del mismo lado del plano respecto de una línea es . -/
theorem plane_same_side_equiv (l : Line) : equivalence (@plane_same_side Point Line og l) :=
⟨plane_same_side_refl Point l, plane_same_side_symm Point l, plane_same_side_trans Point l⟩

/-- Instancia de la clase setoid para la relación. -/
def PlaneSide.setoid [og : order_geometry Point Line] (l : Line) : setoid (outside_line_points Point l) :=
{ r := plane_same_side l, iseqv := plane_same_side_equiv Point l }
local attribute [instance] PlaneSide.setoid

/-- Conjunto cociente de los lados de una línea. -/
def PlaneSide [og : order_geometry Point Line] (l : Line) := quotient (PlaneSide.setoid Point l)
def PlaneSide.reduce [og : order_geometry Point Line] (l : Line) : outside_line_points Point l → PlaneSide Point l := quot.mk (plane_same_side l)
instance [og : order_geometry Point Line] (l : Line) : has_lift (outside_line_points Point l) (PlaneSide Point l) := ⟨PlaneSide.reduce Point l⟩ 
instance [og : order_geometry Point Line] (l : Line) : has_coe  (outside_line_points Point l) (PlaneSide Point l) := ⟨PlaneSide.reduce Point l⟩ 

/-- 
Teorema de separación del plano.
El enunciado original consiste en dos partes. La primera se corresponde con demostrar que la relación de estar 
-/
theorem plane_separation (Point Line : Type*) [og : order_geometry Point Line] (l : Line) (A B : outside_line_points Point l) (hAB: A ≠ B): 
  @segment_intersect_line Point Line og (Segment.mk A B ((outside_line_points_lift_ne Point l A B).mp hAB)) l ↔ ¬ A ≈ B :=
begin
  split,
  { rw segment_intersect_line, 
    intro h, 
    cases h with P hP,
    rcases hP with ⟨hP, hPl⟩,
    sorry },
  { sorry }
end

def line_points_different_to (Point : Type*) {Line : Type*} [incidence_geometry Point Line] (l: Line) (P : line_points Point l) := { A : Point | A ~ l ∧ A ≠ P }

def line_same_side (l: Line) (P : line_points Point l) (A B : line_points_different_to Point l P) := 
A = B ∨ (∃ h : ↑A ≠ ↑B, ¬ @segment_intersect_line Point Line og (Segment.mk A B h) l)



end order_geometry