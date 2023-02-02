namespace incidence_geometry

constant Point: Type
constant Line: Type
constant lies_on (p: Point) (l: Line) : Prop

/-- For any two distinct points A, B, there exists a unique line 
containing A, B. --/
axiom I1: ∀ A B: Point, A ≠ B → ∃ l: Line, 
  lies_on A l ∧ lies_on B l
  ∧ (∀ l2:Line, lies_on A l2 ∧ lies_on B l2 →  l = l2)

axiom I1' (A B: Point) (A ≠ B): ∃ l: Line,
  lies_on A l ∧ lies_on B l 
  ∧ (∀ l2:Line, lies_on A l2 ∧ lies_on B l2 →  l = l2)

/-- Every line contains at least two [different] points --/
axiom I2: ∀ l:Line, ∃ A B: Point, 
  A ≠ B ∧ lies_on A l ∧ lies_on B l

/-- There exist three noncollinear points --/
-- axiom I3: ∃ A B C: Point, ∃ l m : Line, l ≠ m ∧ lies_on A l 

lemma distinct_lines_one_common_point: 
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