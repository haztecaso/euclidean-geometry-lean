import data.real.basic
import geometry.euclidean.basic
import basic

open has_lies_on

class incidence_geometry (Point Line : Type*) :=
  (lies_on : Point → Line → Prop)
  (infix ` ~ ` : 50 := lies_on)
  (I1 {A B : Point} (h : A ≠ B): ∃! l : Line, A ~ l ∧ B ~ l)  -- unicidad
  (I2 (l : Line) : ∃ A B : Point, A ≠ B ∧ A ~ l ∧ B ~ l)
  (I3 : ∃ A B C : Point, different3 A B C ∧ ¬ ∃ l : Line,  A ~ l ∧ B ~ l ∧ C ~ l)

namespace incidence_geometry

infix ` ~ ` : 50 := lies_on

def points_in_line {Point Line : Type*} [incidence_geometry Point Line] (A B : Point) (l : Line) :=
  A ~ l ∧ B ~ l

def collinear {Point : Type*} (Line: Type*) [incidence_geometry Point Line] (A B C : Point) : Prop := 
  ∃ l : Line, A ~ l ∧ B ~ l ∧ C ~ l

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

def is_common_point {Point Line : Type*} [incidence_geometry Point Line] (A : Point) (l m : Line) := 
  A ~ l ∧ A ~ m 

def have_common_point (Point : Type*) {Line : Type*} [incidence_geometry Point Line]
  (l m : Line) := 
  ∃ A : Point, is_common_point A l m

/--
Given two different points get the line that passes through them
-/

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

/--
Given two different points get the unique line that passes through them
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

/-- 
Two distinct lines can have at most one point in common.
-/
lemma disctinct_lines_one_common_point {Point Line : Type*} [ig : incidence_geometry Point Line] :
  ∀ l m : Line, l ≠ m → (∃! A : Point, is_common_point A l m) ∨ (¬ have_common_point Point l m) := 
begin
  intros l m,
  contrapose!,
  rintro ⟨not_unique, hlm⟩,
  rw [exists_unique, push_neg.not_exists_eq] at not_unique,
  push_neg at not_unique,
  choose A hA using hlm,
  rcases not_unique A hA with ⟨B, ⟨hB, hAB⟩⟩,
  rw ne_comm at hAB,
  let hABlm := and.intro hA hB,
  have hABlm : (A ~ l ∧ B ~ l) ∧ A ~ m ∧ B ~ m,
  { exact ⟨⟨hA.left,hB.left⟩,⟨hA.right,hB.right⟩⟩ },
  rw ← unique_of_exists_unique (ig.I1 hAB) hABlm.1 hABlm.2,
end

/--
There exist three disctinct lines not through any common point
-/
lemma disctinct_lines_not_concurrent {Point Line : Type*} [ig : incidence_geometry Point Line] :
  ∃ l m n: Line, (l ≠ m ∧ l ≠ n ∧ m ≠ n) ∧
  ¬ ∃ P : Point, is_common_point P l m ∧ is_common_point P l n ∧ is_common_point P m n
  :=
begin
  rcases ig.I3 with ⟨A, B, C, ⟨⟨hAB, hAC, hBC⟩, h_noncollinear⟩⟩,
  rw [← collinear, push_neg.non_collinear] at h_noncollinear,
  have AB := line Line hAB,
  have AC := line Line hAC,
  have BC := line Line hBC,
  use [AB, AC, BC],
  have hABAC : AB.val ≠ AC.val, 
  { by_contra h, 
    specialize h_noncollinear AB.val,
    rcases h_noncollinear with (h1 | h2 | h3),
    { exact h1 AB.property.left },
    { exact h2 AB.property.right },
    { rw h at h3, exact h3 AC.property.right }
  }, 
  have hABBC : AB.val ≠ BC.val,
  { by_contra h,
    specialize h_noncollinear AB.val,
    rcases h_noncollinear with (h1 | h2 | h3),
    { exact h1 AB.property.left },
    { exact h2 AB.property.right },
    { rw h at h3, exact h3 BC.property.right }},
  have hACBC : AC.val ≠ BC.val,
  { by_contra h,
    specialize h_noncollinear AC.val,
    rcases h_noncollinear with (h1 | h2 | h3),
    { exact h1 AC.property.left },
    { rw h at h2, exact h2 BC.property.left },
    { exact h3 AC.property.right }},
  refine ⟨⟨hABAC, hABBC, hACBC⟩, _⟩, 
  by_contra h,
  cases h with P hP,
  repeat {rw is_common_point at hP},
  rcases hP with ⟨⟨hPAB, hPAC⟩, ⟨-, hPBC⟩, -⟩,
  have h : AB.val = AC.val,
  { by_cases hAP : A = P,
    { sorry },
    { let AP := line_unique Line hAP, 
      let hAP1 := AP.property.right,
      specialize hAP1 AB.val ⟨AB.property.1, hPAB⟩,
      let hAP2 := AP.property.right,
      specialize hAP2 AC.val ⟨AC.property.1, hPAC⟩,
      rw [hAP1, hAP2],
      },
    },
  exact hABAC h
end

/-- 
For every line there is at least one point not lying on it.
-/
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

/-- 
For every point there is at least one line not passing through it.
-/
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

/--
For every point there exist at least two distinct lines that pass through it.
-/
lemma point_has_two_lines {Point Line : Type*} [ig: incidence_geometry Point Line]: 
  ∀ A: Point, ∃ l m: Line, l ≠ m ∧ A ~ l ∧ A ~ m :=
begin
  intro P,
  rcases ig.I3 with ⟨A, B, C, ⟨⟨hAB, hAC, hBC⟩, h_noncollinear⟩⟩,
  push_neg at h_noncollinear,
  let AB := line Line hAB,
  by_cases h1 : P ~ AB.val,
  { 
    -- IDEA: Si P ~ AB, AB y CP son lineas distintas que pasan por P
    let h2 := h_noncollinear,
    specialize h2 AB AB.property.1 AB.property.2,
    have hCP : C ≠ P, { by_contra h', rw ← h' at h1, tauto },
    let CP := line Line hCP,
    use [AB, CP],
    refine ⟨_, h1, CP.property.right⟩,
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
    have hAP : A ≠ P, { sorry },
    have hBP : B ≠ P, { sorry },
    let AP := line Line hAP,
    let BP := line Line hBP,
    have h2 : AP.val ≠ BP.val, { sorry },
    use [AP, BP],
    exact ⟨h2, AP.property.2, BP.property.2⟩ },
end

end incidence_geometry