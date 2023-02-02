namespace incidence_geometry

constant Point: Type
constant Line: Type
constant lies_on (p: Point) (l: Line) : Prop

/-- 
For any two distinct points A, B, there exists a unique line containing A, B. 
-/
axiom I1: ∀ A B: Point, A ≠ B → ∃ l: Line, 
  lies_on A l ∧ lies_on B l
  ∧ (∀ l2:Line, lies_on A l2 ∧ lies_on B l2 →  l = l2)

axiom I1' (A B: Point) (A ≠ B): ∃ l: Line,
  lies_on A l ∧ lies_on B l 
  ∧ (∀ l2:Line, lies_on A l2 ∧ lies_on B l2 →  l = l2)

/--
Every line contains at least two different points.
--/
axiom I2: ∀ l:Line, ∃ A B: Point, 
  A ≠ B ∧ lies_on A l ∧ lies_on B l

/-- 
There exist three noncollinear points.
TODO: Terminar de escribir axioma
-/
axiom I3: ∃ A B C: Point, ∃ l m : Line, l ≠ m ∧ lies_on A l 

/-- 
Two distinct lines can have at most one point in common.
-/
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