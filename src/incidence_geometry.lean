import geometry.euclidean.basic
import basic

/-!
# Axiomas de incidencia

En este fichero se enuncian los axiomas de incidencia de la geometría euclídea
plana y se definen entidades y demuestran resultados que dependen de estos axiomas.

## Notaciones

- Se utiliza la notación A ~ l para la relación de incidencia entre puntos y rectas

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

/-- Función que dados dos puntos distintos devuelve la línea que pasa por ellos. -/
noncomputable def line {Point : Type*} (Line : Type*) [incidence_geometry Point Line] 
{A B : Point} (h : A ≠ B): 
  { l : Line // A ~ l ∧  B ~ l } := 
begin
  let hAB := I1 h,
  rw exists_unique at hAB,
  let P := λ l : Line, A ~ l ∧  B ~ l,
  have hlP : ∃ l : Line, P l, { tauto },
  exact classical.indefinite_description P hlP,
end

/-- Conjunto de puntos de una línea. -/
def line_points (Point : Type*) {Line : Type*} [incidence_geometry Point Line] (l: Line) := { A : Point | A ~ l }

/-- Conjunto de puntos externos a una línea. -/
def outside_line_points (Point : Type*) {Line : Type*} [incidence_geometry Point Line] (l: Line) := { A : Point | ¬ A ~ l }

instance (Point Line : Type*) [incidence_geometry Point Line] : has_coe Line (set Point) := { coe := line_points Point }

lemma line_points_lift_eq (Point : Type*) {Line : Type*} [incidence_geometry Point Line] (l : Line) (A B : line_points Point l) : A = B ↔ (↑A : Point) = ↑B :=
begin
  exact subtype.ext_iff
end

lemma line_points_lift_ne (Point : Type*) {Line : Type*} [incidence_geometry Point Line] (l : Line) (A B : line_points Point l) : A ≠ B ↔ (↑A : Point) ≠ ↑B :=
begin
  rw [ne.def, line_points_lift_eq],
end

lemma outside_line_points_lift_eq (Point : Type*) {Line : Type*} [incidence_geometry Point Line] (l : Line) (A B : outside_line_points Point l) : A = B ↔ (↑A : Point) = ↑B :=
begin
  exact subtype.ext_iff
end

lemma outside_line_points_lift_ne (Point : Type*) {Line : Type*} [incidence_geometry Point Line] (l : Line) (A B : outside_line_points Point l) : A ≠ B ↔ (↑A : Point) ≠ ↑B :=
begin
  rw [ne.def, outside_line_points_lift_eq],
end

/-- Proposición que determina si dos puntos están en una línea dada. -/
def points_in_line {Point Line : Type*} [incidence_geometry Point Line] (A B : Point) (l : Line) :=
  A ~ l ∧ B ~ l

/-- Relación de colinearidad. Determina si tres puntos están en una misma línea. -/
def collinear {Point : Type*} (Line: Type*) [incidence_geometry Point Line] (A B C : Point) : Prop := 
  ∃ l : Line, A ~ l ∧ B ~ l ∧ C ~ l

/-- La relación de colinearidad es conmutativa en los dos primeros argumentos -/
@[simp] lemma collinear_comm {Point : Type*} (Line: Type*) [incidence_geometry Point Line] (A B C : Point) : 
  collinear Line A B C ↔ collinear Line B A C := 
begin
  split,
  { intro h, cases h with l h, use l, tauto },
  { intro h, cases h with l h, use l, tauto },
end

/-- La relación de colinearidad es conmutativa en el primer y tercer argumento -/
@[simp] lemma collinear_comm2 {Point : Type*} (Line: Type*) [incidence_geometry Point Line] (A B C : Point) : 
  collinear Line A B C ↔ collinear Line C B A := 
begin
  split,
  { intro h, cases h with l h, use l, tauto },
  { intro h, cases h with l h, use l, tauto },
end

namespace push_neg
lemma non_collinear {Point : Type*} (Line: Type*) [incidence_geometry Point Line] (A B C : Point) : 
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

lemma exist_neq_point {Point : Type*} (Line: Type*) [ig: incidence_geometry Point Line] (A : Point) :
  ∃ B : Point, A ≠ B :=
begin
  rcases ig.I3 with ⟨P, Q, _, ⟨⟨hPQ, _, _⟩, _⟩⟩,
  by_cases A = P,
  { use Q, rw h, exact hPQ }, 
  { use P }, 
end

lemma non_collinear_neq1 {Point : Type*} (Line: Type*) [incidence_geometry Point Line] {A B C : Point} (h_non_collinear: ¬ collinear Line A B C): 
  A ≠ B :=
begin
  rw push_neg.non_collinear at h_non_collinear,
  by_contra h_contra,
  by_cases A ≠ C,
  { 
    let lAC := line Line h,
    specialize h_non_collinear lAC.val,
    rw [← push_neg.not_and_distrib_eq, ← push_neg.not_and_distrib_eq] at h_non_collinear,
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
    rw [← push_neg.not_and_distrib_eq, ← push_neg.not_and_distrib_eq] at h_non_collinear,
    tauto },
end

lemma non_collinear_neq {Point : Type*} (Line: Type*) [incidence_geometry Point Line] {A B C : Point} (h_non_collinear: ¬ collinear Line A B C): 
  neq3 A B C :=
begin
  by_contra h_contra,
  rw [neq3, push_neg.not_and_distrib_eq, push_neg.not_and_distrib_eq] at h_contra,
  push_neg at h_contra,
  cases h_contra,
  { let h := non_collinear_neq1 Line h_non_collinear,
    tauto },
  { cases h_contra,
    { rw [collinear_comm, collinear_comm2] at h_non_collinear,
      let h := non_collinear_neq1 Line h_non_collinear, 
      tauto }, 
    { rw collinear_comm2 at h_non_collinear,
      let h := non_collinear_neq1 Line h_non_collinear, 
      tauto } },
end

/-- Determina si A es un punto común de dos líneas dadas -/
def is_common_point {Point Line : Type*} [incidence_geometry Point Line] (A : Point) (l m : Line) := 
  A ~ l ∧ A ~ m 

/-- Determina si dos líneas tienen un punto en común -/
def have_common_point (Point : Type*) {Line : Type*} [incidence_geometry Point Line]
  (l m : Line) := 
  ∃ A : Point, is_common_point A l m

-- TODO: resolver o borrar? Ahora mismo no se está usando...
-- lemma line_def_comm {Point : Type*} (Line : Type*) [incidence_geometry Point Line] 
-- {A B : Point} (hAB : A ≠ B): ∀ P: Point,  P ~ (line Line hAB).val ↔ P ~ (line Line hAB.symm).val := begin
--   intro P,
--   split,
--   { intro hP, by_contra h, sorry },
--   { sorry },
-- end

/-- Un punto externo a la línea determinada por dos puntos es distinto de estos dos puntos. -/
lemma line_external_ne {Point : Type*} (Line : Type*) [incidence_geometry Point Line] 
  {A B C: Point} (hAB : A ≠ B) (hC : ¬ C ~ (line Line hAB).val): A ≠ C ∧ B ≠ C :=
begin
let AB := line Line hAB,
split,
{ by_contra h,
  have hC : C ~ AB.val,
  { sorry },
  sorry },
{ sorry },
end

/-- 
Función que dados dos puntos distintos devuelve la línea que pasa por ellos,
 con la propiedad de unicidad. 
-/
noncomputable def line_unique {Point : Type*} (Line : Type*) [incidence_geometry Point Line] 
{A B : Point} (h : A ≠ B): 
  { l : Line // (A ~ l ∧ B ~ l) ∧ ∀ l' : Line, A ~ l' ∧ B ~ l' → l' = l } := 
begin
  let hAB := I1 h,
  rw exists_unique at hAB,
  let P := λ l : Line, (A ~ l ∧  B ~ l) ∧ ∀ l' : Line, A ~ l' ∧ B ~ l' → l' = l,
  have hlP : ∃ l : Line, P l, { tauto },
  exact classical.indefinite_description P hlP,
end

/-- Dos líneas distintas tienen como mucho un punto en común. -/
lemma disctinct_lines_one_common_point {Point Line : Type*} [ig : incidence_geometry Point Line] :
  ∀ l m : Line, l ≠ m → (∃! A : Point, is_common_point A l m) ∨ (¬ have_common_point Point l m) := 
begin
  intros l m,
  contrapose,
  push_neg,
  rintro ⟨not_unique, hlm⟩,
  rw exists_unique at not_unique,
  push_neg at not_unique,
  cases hlm with A hA,
  rcases not_unique A hA with ⟨B, ⟨hB, hAB⟩⟩,
  rw ne_comm at hAB,
  exact unique_of_exists_unique (ig.I1 hAB) ⟨hA.left,hB.left⟩ ⟨hA.right,hB.right⟩,
end

lemma non_collinear_ne_lines {Point : Type*} (Line : Type*) [ig: incidence_geometry Point Line] (A B C: Point) (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C):
 ¬ collinear Line A B C → (line Line hAB).val ≠ (line Line hAC).val ∧ (line Line hAB).val ≠ (line Line hBC).val ∧ (line Line hAC).val ≠ (line Line hBC).val
 := 
 begin
  intro h_noncollinear,
  rw push_neg.non_collinear at h_noncollinear,
  by_contra h,
  rw [push_neg.not_and_distrib_eq, push_neg.not_and_distrib_eq] at h,
  push_neg at h,
  let AB := line Line hAB,
  let AC := line Line hAC,
  let BC := line Line hBC,
  rcases h with (h | h | h), 
  { rcases h_noncollinear (line Line hAB).val with (hA | hB | hC),
    { exact hA AB.prop.left },
    { exact hB AB.prop.right },
    { rw h at hC, exact hC AC.prop.right }
    },
  { rcases h_noncollinear AB.val with (hA | hB | hC),
    { exact hA AB.prop.left },
    { exact hB AB.prop.right },
    { rw h at hC, exact hC BC.prop.right }},
  { rcases h_noncollinear AC.val with (hA | hB | hC),
    { exact hA AC.prop.left },
    { rw h at hB, exact hB BC.prop.left },
    { exact hC AC.prop.right }},
 end

/-- Existen tres líneas distintas que no pasan por ningún punto común. -/
lemma disctinct_lines_not_concurrent {Point Line : Type*} [ig : incidence_geometry Point Line] :
  ∃ l m n: Line, (l ≠ m ∧ l ≠ n ∧ m ≠ n) ∧
  ¬ ∃ P : Point, is_common_point P l m ∧ is_common_point P l n ∧ is_common_point P m n
  :=
begin
  rcases ig.I3 with ⟨A, B, C, ⟨⟨hAB, hAC, hBC⟩, h_noncollinear⟩⟩,
  let AB := line Line hAB,
  let AC := line Line hAC,
  let BC := line Line hBC,
  use [AB, AC, BC],
  let hABC := non_collinear_ne_lines Line A B C hAB hAC hBC h_noncollinear,
  refine ⟨hABC, _⟩, 
  by_contra h,
  cases h with P hP,
  repeat {rw is_common_point at hP},
  rcases hP with ⟨⟨hPAB, hPAC⟩, ⟨-, hPBC⟩, -⟩,
  have hAP : P ≠ A, 
  { by_contra h,
    rw h at hPBC,
    push_neg at h_noncollinear,
    exact h_noncollinear BC hPBC BC.prop.left BC.prop.right,
  },
  exact hABC.left (unique_of_exists_unique (ig.I1 hAP) ⟨hPAB, AB.prop.left⟩ ⟨hPAC, AC.prop.left⟩),
end

/-- Para cada línea existe un punto externo a ella. -/
lemma line_external_point {Point Line : Type*} [ig : incidence_geometry Point Line] :
  ∀ l : Line, ∃ A : Point, ¬ A ~ l :=
begin
  rcases ig.I3 with ⟨A, B, C, ⟨_, h1⟩⟩,
  by_contra h2,
  push_neg at h1,
  push_neg at h2,
  cases h2 with l hl,
  have hAl: A ~ l, { tauto },
  have hBl: B ~ l, { tauto },
  have hCl: C ~ l, { tauto },
  specialize h1 l hAl hBl,
  exact h1 hCl
end

/-- Para caada punto existe una línea que no pasa por él. -/
lemma point_external_line {Point Line : Type*} [ig : incidence_geometry Point Line]: 
  ∀ A: Point, ∃ l: Line, ¬ A ~ l :=
begin
  intro A,
  rcases @disctinct_lines_not_concurrent Point Line ig with ⟨l, m, n, ⟨-, h⟩⟩,
  rw push_neg.not_exists_eq at h,
  specialize h A,
  repeat { rw is_common_point at h },
  repeat { rw push_neg.not_and_distrib_eq at h },
  have h : ¬ A ~ l ∨ ¬ A ~ m ∨ ¬ A ~ n, { tauto },
  rcases h with (h1 | h2 | h3),
  { use l },
  { use m },
  { use n },
end

/-- Si dos líneas que determinan tres puntos son iguales, entonces la tercera también coincide. -/
lemma eq_lines_determined_by_points {Point : Type*} (Line : Type*) [ig: incidence_geometry Point Line] {A B C : Point} 
  (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) :
  ((line Line hAB).val = (line Line hAC).val) → (line Line hAB).val = (line Line hBC).val := 
begin
  intro hABAC,

  sorry
end

/-- Para cada punto existen al menos dos líneas que pasan por él. -/
lemma point_has_two_lines {Point Line : Type*} [ig: incidence_geometry Point Line]: 
  ∀ A: Point, ∃ l m: Line, l ≠ m ∧ A ~ l ∧ A ~ m :=
begin
  intro P,
  rcases ig.I3 with ⟨A, B, C, ⟨⟨hAB, hAC, hBC⟩, h_noncollinear⟩⟩,
  push_neg at h_noncollinear,
  let AB := line Line hAB,
  by_cases hPAB : P ~ ↑AB,
  { 
    let h2 := h_noncollinear,
    specialize h2 AB AB.property.1 AB.property.2,
    have hCP : C ≠ P, { by_contra h', rw ← h' at hPAB, tauto },
    let CP := line Line hCP,
    use [AB, CP],
    refine ⟨_, hPAB, CP.property.right⟩,
    by_contra h3,
    have h3' : AB.val = CP.val, { tauto },
    let hlCP := CP.property,
    rw ← h3' at hlCP,
    tauto,
  },
  { 
    -- IDEA: AP y BP pasan por P y deben ser distintas 
    -- Ya que si AP = BP entonces A B y P son colineares 
    -- y P ~ AB, lo que contradice la que ¬ P ~ AB.
    have hAP : A ≠ P,
    { by_contra h, 
      rw ← h at hPAB,
      exact hPAB AB.prop.left },
    have hBP : B ≠ P,
    { by_contra h, 
      rw ← h at hPAB,
      exact hPAB AB.prop.right },
    let AP := line Line hAP,
    let BP := line Line hBP,
    have h2 : AP.val ≠ BP.val, 
    { by_contra h,
      let hhh := AP.prop,

      let HHH := eq_lines_determined_by_points Line hAB hAP hBP,

      have hPAB' : P ~ AB.val, 
      { sorry },
      exact hPAB hPAB',
      },
    use [AP, BP],
    exact ⟨h2, AP.property.right, BP.property.right⟩ },
end

end incidence_geometry
