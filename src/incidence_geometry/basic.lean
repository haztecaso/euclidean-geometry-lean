import tactic ..basic_defs

/-!
# Axiomas de incidencia

En este fichero se enuncian los axiomas de incidencia, se definen conceptos 
básicos y demuestran resultados elementales.

## Notaciones

- Se utiliza la notación A ~ l para la relación de incidencia.

-/

/-- Geometría de incidencia, clase que engloba los axiomas para la relación de 
incidencia. -/
class incidence_geometry (Point Line : Type*) :=
  (lies_on : Point → Line → Prop)
  (infix ` ~ ` : 50 := lies_on)
  (I1 {A B : Point} (h : A ≠ B): ∃! l : Line, A ~ l ∧ B ~ l)
  (I2 (l : Line) : ∃ A B : Point, A ≠ B ∧ A ~ l ∧ B ~ l)
  (I3 : ∃ A B C : Point, neq3 A B C ∧ ¬ ∃ l : Line,  A ~ l ∧ B ~ l ∧ C ~ l)

namespace incidence_geometry

infix ` ~ ` : 50 := lies_on

/-- Función que dados dos puntos distintos devuelve la línea que pasa por ellos.
-/
noncomputable def line 
  {Point : Type*} (Line : Type*) [incidence_geometry Point Line]
  {A B : Point} (h : A ≠ B) :
  { l : Line // A ~ l ∧  B ~ l } := 
begin
  let hAB := I1 h,
  rw exists_unique at hAB,
  let P := λ l : Line, A ~ l ∧  B ~ l,
  have hlP : ∃ l : Line, P l, { tauto },
  exact classical.indefinite_description P hlP,
end

/-- 
Función que dados dos puntos distintos devuelve la línea que pasa por ellos,
con la propiedad de unicidad. 
-/
noncomputable def line_unique 
  {Point : Type*} (Line : Type*) [incidence_geometry Point Line] 
  {A B : Point} (h : A ≠ B) :
  { l : Line // (A ~ l ∧ B ~ l) ∧ ∀ l' : Line, A ~ l' ∧ B ~ l' → l' = l } := 
begin
  let hAB := I1 h,
  rw exists_unique at hAB,
  let P := λ l : Line, (A ~ l ∧  B ~ l) ∧ ∀ l' : Line, A ~ l' ∧ B ~ l' → l' = l,
  have hlP : ∃ l : Line, P l, { tauto },
  exact classical.indefinite_description P hlP,
end

/-- Relación de colinearidad. Determina si tres puntos están en una misma línea.
-/
def collinear {Point : Type*} (Line: Type*) [incidence_geometry Point Line]
  (A B C : Point) : Prop := ∃ l : Line, A ~ l ∧ B ~ l ∧ C ~ l

/-- La colinearidad es simétrica en los dos primeros argumentos. -/
@[simp] lemma collinear_symm
  {Point : Type*} (Line: Type*) [incidence_geometry Point Line] 
  (A B C : Point) : collinear Line A B C ↔ collinear Line B A C := 
begin
  split,
  { intro h, cases h with l h, use l, tauto },
  { intro h, cases h with l h, use l, tauto },
end

/-- La colinearidad es simétrica en el primer y tercer argumento. -/
@[simp] lemma collinear_symm2
  {Point : Type*} (Line: Type*) [incidence_geometry Point Line] 
  (A B C : Point) : collinear Line A B C ↔ collinear Line C B A := 
begin
  split,
  { intro h, cases h with l h, use l, tauto },
  { intro h, cases h with l h, use l, tauto },
end

/-- Lema para 'empujar' la negación dentro de la proposición de que tres puntos 
no sean colineares. -/
lemma push_neg.non_collinear 
  {Point : Type*} (Line: Type*) [incidence_geometry Point Line] 
  (A B C : Point) : 
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

/-- Dado un punto existe otro punto distinto. -/
lemma exist_neq_point 
  {Point : Type*} (Line: Type*) [ig: incidence_geometry Point Line] 
  (A : Point) :
  ∃ B : Point, A ≠ B :=
begin
  rcases ig.I3 with ⟨P, Q, _, ⟨⟨hPQ, _, _⟩, _⟩⟩,
  by_cases A = P,
  { use Q, rw h, exact hPQ }, 
  { use P }, 
end

/-- Dados tres puntos no colineares, los dos primeros son distintos. 
Lema auxiliar para demostrar `non_collinear_neq`. -/
lemma non_collinear_neq1 
  {Point : Type*} (Line: Type*) [incidence_geometry Point Line] 
  {A B C : Point} (h_non_collinear: ¬ collinear Line A B C) : 
  A ≠ B :=
begin
  rw push_neg.non_collinear at h_non_collinear,
  by_contra h_contra,
  by_cases A ≠ C,
  { 
    let lAC := line Line h,
    specialize h_non_collinear lAC.val,
    rw [← push_neg.not_and_distrib_eq, ← push_neg.not_and_distrib_eq] 
      at h_non_collinear,
    have h_collinear : A ~ ↑lAC ∧ B ~ ↑lAC ∧ C ~ ↑lAC,
    { rw ← h_contra,
      exact ⟨lAC.property.left, lAC.property.left, lAC.property.right⟩ },
    tauto },
  { push_neg at h,
    cases exist_neq_point Line A with P hP,
    let l := line Line hP,
    have h_collinear : A ~ l.val ∧ B ~ l.val ∧ C ~ l.val,
    { rw [←h, ←h_contra],
      exact ⟨l.property.left, l.property.left,l.property.left⟩ },
    specialize h_non_collinear l.val,
    rw [← push_neg.not_and_distrib_eq, ← push_neg.not_and_distrib_eq]
      at h_non_collinear,
    tauto },
end

/-- Dados tres puntos no colineares, son distintos entre ellos. -/
lemma non_collinear_neq 
  {Point : Type*} (Line: Type*) [incidence_geometry Point Line] 
  {A B C : Point} (h_non_collinear: ¬ collinear Line A B C) :
  neq3 A B C :=
begin
  by_contra h_contra,
  rw [neq3, push_neg.not_and_distrib_eq, push_neg.not_and_distrib_eq] 
    at h_contra,
  push_neg at h_contra,
  cases h_contra,
  { let h := non_collinear_neq1 Line h_non_collinear, tauto },
  { cases h_contra,
    { rw [collinear_symm, collinear_symm2] at h_non_collinear,
      let h := non_collinear_neq1 Line h_non_collinear, 
      tauto }, 
    { rw collinear_symm2 at h_non_collinear,
      let h := non_collinear_neq1 Line h_non_collinear, 
      tauto } },
end

/-- Determina si dos puntos están en una línea dada. -/
def points_in_line 
  {Point Line : Type*} [incidence_geometry Point Line] 
  (A B : Point) (l : Line) :=
  A ~ l ∧ B ~ l

/-- Determina si A es un punto común de dos líneas dadas -/
def is_common_point 
  {Point Line : Type*} [incidence_geometry Point Line] 
  (A : Point) (l m : Line) := 
  A ~ l ∧ A ~ m 

/-- Determina si dos líneas tienen un punto en común -/
def have_common_point 
  (Point : Type*) {Line : Type*} [incidence_geometry Point Line]
  (l m : Line) := 
  ∃ A : Point, is_common_point A l m




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
