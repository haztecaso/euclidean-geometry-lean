import data.real.basic
import geometry.euclidean.basic
import basic

open has_lies_on

class incidence_geometry (Point Line : Type*) extends has_lies_on Point Line :=
  (i1 (A B : Point) : A ≠ B → ∃! l : Line, lies_on A l ∧ lies_on B l)  -- unicidad
  (i2 (l : Line) : ∃ A B : Point, A ≠ B ∧ lies_on A l ∧ lies_on B l)
  (i3 : ∃ A B C : Point, different3 A B C ∧ ¬ collinear Line A B C)

namespace incidence_geometry

/--
Given two different points get the line that passes through them
-/

noncomputable def line {Point : Type*} (Line : Type*) [incidence_geometry Point Line] 
(A B : Point) (h : A ≠ B): 
  { l : Line // points_in_line A B l } := 
begin
  let hAB := i1 A B h,
  rw exists_unique at hAB,
  let P := λ l : Line, A ~ l ∧  B ~ l,
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
  let hI1 := ig.i1 A B hAB,
  let hABlm := and.intro hA hB,
  have hABlm : (A ~ l ∧ B ~ l) ∧ A ~ m ∧ B ~ m,
  { exact ⟨⟨hA.left,hB.left⟩,⟨hA.right,hB.right⟩⟩ },
  rw ← unique_of_exists_unique hI1 hABlm.1 hABlm.2,
end

/--
There exist three disctinct lines not through any common point
-/
lemma disctinct_lines_not_concurrent {Point Line : Type*} [ig : incidence_geometry Point Line] :
  ∃ l m n: Line, l ≠ m ∧ l ≠ n ∧ m ≠ n →
  ¬ have_common_point Point l m ∧ ¬ have_common_point Point l n ∧ ¬ have_common_point Point m n
  :=
begin
  rcases ig.i3 with ⟨A, B, C, h⟩,
  rcases h.left with ⟨hAB, hAC, hBC⟩,
  have AB := line Line A B hAB,
  have AC := line Line A C hAC,
  have BC := line Line B C hBC,
  have hABAC: AB.val ≠ AC.val, { sorry },
  have hABBC: AB.val ≠ BC.val, { sorry },
  have hACBC: AC.val ≠ BC.val, { sorry },
  sorry,
end

/-- 
For every line there is at least one point not lying on it.
-/
lemma line_external_point {Point Line : Type*} [ig : incidence_geometry Point Line] :
  ∀ l : Line, ∃ A : Point, ¬ A ~ l :=
begin
  rcases ig.i3 with ⟨A, B, C, ⟨_, h1⟩⟩,
  by_contra h2,
  rw has_lies_on.collinear at h1,
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
  rcases @disctinct_lines_not_concurrent Point Line ig with ⟨l, m, n, ⟨_, h2⟩⟩,
  push_neg at h2,
  specialize h2 A,
  by_cases hAlm : is_common_point A l m,
  { 
    by_cases hAln : is_common_point A l n,
    { let h2 := h2 hAlm hAln,
      rw is_common_point at h2,
      push_neg at h2,
      by_cases A ~ m,
      { use n, exact h2 h, },
      { use m, }},
    { rw is_common_point at hAln,
      push_neg at hAln,
      by_cases A ~ l,
      { use n, exact hAln h },
      { use l }}},
  { rw is_common_point at hAlm,
    push_neg at hAlm,
    by_cases A ~ l,
    { use m, exact hAlm h, },
    { use l, }},
end

/--
For every point there exist at least two distinct lines that pass through it.
-/
lemma point_has_two_lines {Point Line : Type*} [ig: incidence_geometry Point Line]: 
  ∀ A: Point, ∃ l m: Line, l ≠ m ∧ A ~ l ∧ A ~ m :=
begin
  intro P,
  rcases ig.i3 with ⟨A, B, C, h1⟩,

  have hAB := ig.i1,
  specialize hAB A B,
  have hAnB : A ≠ B,
  { sorry },
  specialize hAB hAnB,
  rw exists_unique at hAB,
  rcases hAB with ⟨AB, ⟨hAB, -⟩⟩,

  by_cases P ~ AB,

  { 
    -- IDEA: AP y BP pasan por P y deben ser distintas 
    -- Ya que si AP = BP entonces A B y P son colineares 
    -- y P ~ AB, lo que contradice la hipótesis.
    sorry 
  },
  { 
    -- IDEA: Si P ~ AB, AB y CP son lineas distintas que pasan por P
    sorry },
end

end incidence_geometry