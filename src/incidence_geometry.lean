import tactic
namespace incidence_geometry
noncomputable

constant Point: Type
constant Line: Type

constant lies_on (p: Point) (l: Line) : Prop
local infix ` ~ `:50 := lies_on

/-- 
For any two distinct points A, B, there exists a unique line containing A, B. 
-/
axiom I1: ∀ A B: Point, A ≠ B → ∃! l: Line, A ~ l ∧ B ~ l

/--
Every line contains at least two different points.
-/
axiom I2: ∀ l:Line, ∃ A B: Point, A ≠ B ∧ A ~ l ∧ B ~ l

def collinear (A B C: Point) := ∃ l:Line, A ~ l ∧ B ~ l ∧ C ~ l

/-- 
There exist three noncollinear points.
-/
axiom I3: ∃ A B C: Point, ¬ collinear A B C

/-- 
Three noncollinear points must be different
-/
lemma noncollinear_diff (A B C: Point): 
  ¬ collinear A B C → A ≠ B ∧ B ≠ C ∧ A ≠ C := 
begin
  sorry
end

def have_common_point (l m: Line) := ∃ A:Point, A ~ l ∧ A ~ m
def no_common_points (l m: Line) := ¬ have_common_point l m
def is_common_point (A: Point) (l m: Line) := A ~ l ∧ A ~ m

lemma common_points_and_lines_eq (l m: Line) (A B: Point) : 
  is_common_point A l m ∧ is_common_point B l m ↔ (A ~ l ∧ B ~ l) ∧ (A ~ m ∧ B ~ m) := 
begin
  split,
  { rintro ⟨⟨hAl, hAm⟩, ⟨hBl, hBm⟩⟩,
    exact ⟨⟨hAl, hBl⟩, ⟨hAm, hBm⟩⟩ },
  { rintro ⟨⟨hAl, hBl⟩, ⟨hAm, hBm⟩⟩,
    exact ⟨⟨hAl, hAm⟩, ⟨hBl, hBm⟩⟩ }
end

/-- 
Two distinct lines can have at most one point in common.
-/
lemma disctinct_lines_one_common_point: 
  ∀ l m: Line, l ≠ m → (
    (∃! A: Point, is_common_point A l m) ∨ (no_common_points l m)
  ) := 
begin
  intros l m,
  contrapose,
  intro h,
  push_neg,
  push_neg at h,
  cases h with not_unique hlm,
  rw [exists_unique, push_neg.not_exists_eq] at not_unique,
  push_neg at not_unique,
  rw [no_common_points, push_neg.not_not_eq] at hlm,
  cases hlm with A hA,
  rw ← is_common_point at hA,
  specialize not_unique A hA,
  rcases not_unique with ⟨B, ⟨hB, hAB⟩⟩,
  rw ne_comm at hAB,
  have hI1 := I1,
  specialize hI1 A B hAB,
  have h: (A ~ l ∧ B ~ l) ∧ (A ~ m ∧ B ~ m),
  { rw ← common_points_and_lines_eq, 
    exact ⟨hA, hB⟩ },
  rw ← unique_of_exists_unique hI1 (and.left h) (and.right h),
end

/-- 
For every line there is at least one point not lying on it.
-/
lemma line_external_point: ∀ l: Line, ∃ A: Point, ¬ A ~ l :=
begin
  have hI3:= I3,
  rcases hI3 with ⟨A, B, C, h1⟩,
  by_contra h2,
  rw collinear at h1,
  push_neg at h1,
  push_neg at h2,
  cases h2 with l hlA,
  have hlB := hlA,
  have hlC := hlA,
  specialize hlA A,
  specialize hlB B,
  specialize hlC C,
  specialize h1 l hlA hlB,
  exact h1 hlC
end

/-- 
For every point there is at least one line not passing through it.
-/
lemma point_external_line: ∀ A: Point, ∃ l: Line, ¬ A ~ l :=
begin
  sorry 
end

noncomputable 
def line (A B:Point) (h: A ≠ B) : Line × Prop := begin
  -- have hAB := I1,
  -- specialize hAB A B H,
  -- cases hAB with l hl,
  -- exact (l,hl)
  sorry
end

#check line

/--
For every point there exist at least two distinct lines that pass through it.
-/
lemma point_has_two_lines: 
  ∀ A: Point, ∃ l m: Line, l ≠ m ∧ A ~ l ∧ A ~ m :=
begin
  intro P,
  have hI3:= I3,
  rcases hI3 with ⟨A, B, C, h1⟩,

  have hAB := I1,
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