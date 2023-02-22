import tactic
import set_theory.zfc.basic
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

def is_common_point (A: Point) (l m: Line) := A ~ l ∧ A ~ m

def no_common_points (l m: Line) := ∀ A: Point, (A ~ l → ¬ A ~ m) ∧ (A ~ m → ¬ A ~ l)

lemma equiv_common_points (l m: Line):
  have_common_point l m ↔ ¬ no_common_points l m :=
begin
  split,
  {
    intros h1 h2,
    cases h1 with A h1,
    specialize h2 A,
    cases h1 with hAl hAm,
    cases h2,
    have hF: A ~ m ∧ ¬ A ~ m,
    { split, 
      exact hAm,
      exact h2_left hAl },
    { 
      rw ← and_not_self (A ~ m), 
      exact hF
    }
  },
  {
    intro h1,
    rw have_common_point,
    rw no_common_points at h1,
    rw push_neg.not_forall_eq at h1,
    cases h1 with x h1,
    rw push_neg.not_and_distrib_eq at h1,
    rw push_neg.not_implies_eq at h1,
    rw push_neg.not_implies_eq at h1,
    push_neg at h1,
    use x,
    cases h1,
    { exact h1 },
    { rw and_comm, exact h1 }
  }
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
  intro hnelm,
  by_contra h,
  push_neg at h,
  cases h with h have_common,
  rw ← equiv_common_points at have_common,
  cases have_common with x hx,
  rw [exists_unique, not_exists] at h,
  specialize h x,
  push_neg at h,
  rw ← is_common_point at hx,
  specialize h hx,
  cases h with y hy,
  cases hy with hy hyx,
  have i1:=I1,
  specialize i1 y x hyx,
  rw exists_unique at i1,
  cases i1 with n hn,
  cases hn with hnl hn1,
  have hn2 := hn1,
  specialize hn1 l,
  specialize hn2 m,
  have hln: l = n ,
  { apply hn1, 
  split,
  cases hy, exact hy_left,
  cases hx, exact hx_left },
  have hmn: m = n ,
  { apply hn2,
  split,
  cases hy, exact hy_right,
  cases hx, exact hx_right },
  have hlm: l = m,
  { rw [hln, hmn] },
  rw ← and_not_self (l = m),
  split,
  exact hlm,
  exact hnelm,
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