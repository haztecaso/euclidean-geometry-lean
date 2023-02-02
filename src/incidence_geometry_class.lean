class incidence_geometry (Point: Type) (Line: Type):=
  (lies_on: Point → Line → Prop)
  (i1: ∀ A B: Point, A ≠ B → ∃ l: Line, lies_on A l ∧ lies_on B l
    ∧ (∀ l2:Line, lies_on A l2 ∧ lies_on B l2 →  l = l2))  -- unicidad
  (i2: ∀ l:Line, ∃ A B: Point, A ≠ B ∧ lies_on A l ∧ lies_on B l)
  -- (i3: )

namespace incidence_geometry

variables {Point Line: Type} [incidence_geometry Point Line]

/-- Two distinct lines can have at most one point in common. -/
lemma disctinct_lines_one_common_point: 
  ∀ l m: Line, l ≠ m → (
    ∃ A: Point, lies_on A l ∧ lies_on A m → ∀ B: Point, lies_on B l → A = B
  ) := 
begin
  assume l m,
  intro h,
  fapply exists.intro,
  
  sorry
end

end incidence_geometry