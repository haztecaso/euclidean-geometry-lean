import tactic
namespace incidence_geometry

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

/-- 
There exist three noncollinear lemma disctinct_lines_one_common_point' (l m: Line) (hNE: l ≠ m): 
…{
  use x,
  by_contra,
  sorry
}
endpoints.
-/
axiom I3: ∃ A B C: Point, ∃ l m : Line, l ≠ m ∧ A ~ l 


def have_common_point (l m: Line) := ∃ A:Point, A ~ l ∧ A ~ m
def no_common_points (l m: Line) := ¬ have_common_point l m
def is_common_point (A: Point) (l m: Line) := A ~ l ∧ A ~ m

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
  cases h with not_unique common,
  rw [exists_unique, push_neg.not_exists_eq] at not_unique,
  rw [no_common_points, push_neg.not_not_eq] at common,
  cases common with A hA,
  rw ← is_common_point at hA,
  push_neg at not_unique,
  specialize not_unique A hA,
  cases not_unique with B hB,
  cases hB with hB hBA,
  have hI1 := I1,
  specialize hI1 B A,
  specialize hI1 hBA,
  rw exists_unique at hI1,
  cases hI1 with n hn,
  cases hn with hABn hnl,
  have hnm := hnl,
  specialize hnl l,
  specialize hnm m,
  cases hA with hAl hAm,
  cases hB with hBl hBm,
  have hln: l = n, 
  { apply hnl, split, exact hBl, exact hAl },
  have hmn: m = n, 
  { apply hnm, split, exact hBm, exact hAm },
  rw [hln, hmn],
end

/-- 
For every line there is at least one point not lying on it.
-/
lemma line_external_point: ∀ l: Line, ∃ A: Point, ¬ lies_on A l :=
begin
  sorry
end

/-- 
For every point there is at least one line not passing through it.
-/
lemma point_external_line: ∀ A: Point, ∃ l: Line, ¬ lies_on A l :=
begin
  sorry 
end

/--
For every point there exist at least two distinct lines that pass through it.
-/
lemma point_has_two_lines: 
  ∀ A: Point, ∃ l m: Line, l ≠ m ∧ lies_on A l ∧ lies_on A m :=
begin
  sorry
end

end incidence_geometry