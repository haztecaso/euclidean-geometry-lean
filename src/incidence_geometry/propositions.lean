import .basic

namespace incidence_geometry

/-- Un punto externo a la línea determinada por dos puntos es distinto de estos 
dos puntos. -/
lemma line_external_ne 
  {Point : Type*} (Line : Type*) [incidence_geometry Point Line] 
  {A B C: Point} (hAB : A ≠ B) (hC : ¬ C ~ (line Line hAB).val) : 
  A ≠ C ∧ B ≠ C :=
begin
  let AB := line Line hAB,
  rw [← push_neg.not_eq, ← push_neg.not_eq, ← push_neg.not_or_eq],
  intro h,
  cases h,
  { rw ← h at hC, exact hC AB.property.1 },
  { rw ← h at hC, exact hC AB.property.2 },
end

/-- Dos líneas distintas tienen como mucho un punto en común. -/
lemma neq_lines_one_common_point 
  (Point : Type*) {Line : Type*} [ig : incidence_geometry Point Line] :
  ∀ l m : Line, l ≠ m → 
    (∃! A : Point, is_common_point A l m) 
    ∨ (¬ have_common_point Point l m) := 
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
  exact unique_of_exists_unique (ig.I1 hAB) ⟨hA.1, hB.1⟩ ⟨hA.2, hB.2⟩
end

/-- Tres puntos no colineares determinan tres líneas distintas. -/
lemma non_collinear_ne_lines 
  {Point : Type*} (Line : Type*) [ig: incidence_geometry Point Line] 
  (A B C: Point) 
  (h_noncollinear : ¬ collinear Line A B C)
  -- Las hipótesis de que los puntos son distintos son innecesarias puesto que 
  -- podrían derivarse de  `non_collinear_neq`. Están incluidas para darles un 
  -- nombre y poder construir las líneas correspondientes en el enunciado.
  (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) :
  (line Line hAB).val ≠ (line Line hAC).val 
  ∧ (line Line hAB).val ≠ (line Line hBC).val 
  ∧ (line Line hAC).val ≠ (line Line hBC).val := 
 begin
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
lemma neq_lines_not_concurrent 
  {Point Line : Type*} [ig : incidence_geometry Point Line] :
  ∃ l m n: Line, 
    (l ≠ m ∧ l ≠ n ∧ m ≠ n) 
    ∧ ¬ ∃ P : Point, is_common_point P l m 
    ∧ is_common_point P l n 
    ∧ is_common_point P m n
  :=
begin
  rcases ig.I3 with ⟨A, B, C, ⟨⟨hAB, hAC, hBC⟩, h_noncollinear⟩⟩,
  let AB := line Line hAB,
  let AC := line Line hAC,
  let BC := line Line hBC,
  use [AB, AC, BC],
  let hABC := non_collinear_ne_lines Line A B C h_noncollinear hAB hAC hBC,
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
  exact hABC.left (unique_of_exists_unique 
    (ig.I1 hAP) ⟨hPAB, AB.prop.left⟩ ⟨hPAC, AC.prop.left⟩),
end

/-- Para cada línea existe un punto externo a ella. -/
lemma line_external_point 
  {Point Line : Type*} [ig : incidence_geometry Point Line] :
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
lemma point_external_line 
  {Point Line : Type*} [ig : incidence_geometry Point Line] : 
  ∀ A: Point, ∃ l: Line, ¬ A ~ l :=
begin
  intro A,
  rcases @neq_lines_not_concurrent Point Line ig with ⟨l, m, n, ⟨-, h⟩⟩,
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

-- /-- Si dos líneas que determinan tres puntos son iguales, entonces la tercera 
-- también coincide. -/
-- lemma eq_lines_determined_by_points 
--   {Point : Type*} (Line : Type*) [ig: incidence_geometry Point Line] 
--   {A B C : Point} (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) :
--   ((line Line hAB).val = (line Line hAC).val) → 
--     (line Line hAB).val = (line Line hBC).val := 
-- begin
--   intro hABAC,
--   sorry
-- end

-- /-- Para cada punto existen al menos dos líneas que pasan por él. -/
-- lemma point_has_two_lines 
--   {Point Line : Type*} [ig: incidence_geometry Point Line] :
--   ∀ A: Point, ∃ l m: Line, l ≠ m ∧ A ~ l ∧ A ~ m :=
-- begin
--   intro P,
--   rcases ig.I3 with ⟨A, B, C, ⟨⟨hAB, hAC, hBC⟩, h_noncollinear⟩⟩,
--   push_neg at h_noncollinear,
--   let AB := line Line hAB,
--   by_cases hPAB : P ~ ↑AB,
--   { 
--     let h2 := h_noncollinear,
--     specialize h2 AB AB.property.1 AB.property.2,
--     have hCP : C ≠ P, { by_contra h', rw ← h' at hPAB, tauto },
--     let CP := line Line hCP,
--     use [AB, CP],
--     refine ⟨_, hPAB, CP.property.right⟩,
--     by_contra h3,
--     have h3' : AB.val = CP.val, { tauto },
--     let hlCP := CP.property,
--     rw ← h3' at hlCP,
--     tauto,
--   },
--   { 
--     -- IDEA: AP y BP pasan por P y deben ser distintas 
--     -- Ya que si AP = BP entonces A B y P son colineares 
--     -- y P ~ AB, lo que contradice la que ¬ P ~ AB.
--     have hAP : A ≠ P,
--     { by_contra h, 
--       rw ← h at hPAB,
--       exact hPAB AB.prop.left },
--     have hBP : B ≠ P,
--     { by_contra h, 
--       rw ← h at hPAB,
--       exact hPAB AB.prop.right },
--     let AP := line Line hAP,
--     let BP := line Line hBP,
--     have h2 : AP.val ≠ BP.val, 
--     { by_contra h,
--       let hhh := AP.prop,
--       let HHH := eq_lines_determined_by_points Line hAB hAP hBP,
--       have hPAB' : P ~ AB.val, 
--       { sorry },
--       exact hPAB hPAB',
--       },
--     use [AP, BP],
--     exact ⟨h2, AP.property.right, BP.property.right⟩ },
-- end

end incidence_geometry