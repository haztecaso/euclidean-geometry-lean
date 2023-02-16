namespace incidence_geometry

constant Point: Type
constant Line: Type
constant lies_on (p: Point) (l: Line) : Prop

local infix ` ~ `:50 := lies_on

/-- 
For any two distinct points A, B, there exists a unique line containing A, B. 
-/

axiom I1: ∀ A B: Point, A ≠ B → ∃! l: Line, A ~ l ∧ B ~ l
axiom I1' (A B: Point) (A ≠ B): ∃! l: Line, A ~ l ∧ B ~ l 


/--
Every line contains at least two different points.
--/
axiom I2: ∀ l:Line, ∃ A B: Point, A ≠ B ∧ A ~ l ∧ B ~ l

/-- 
There exist three noncollinear points.
TODO: Terminar de escribir axioma
-/
axiom I3: ∃ A B C: Point, ∃ l m : Line, l ≠ m ∧ A ~ l 

def common_point (l m: Line) (A: Point) := A ~ l ∧ A ~ m
def no_common_points (l m: Line) := ∀ A: Point, (A ~ l → ¬ A ~ m) ∧ (A ~ m → ¬ A ~ l)


/-- 
Two distinct lines can have at most one point in common.
-/
lemma disctinct_lines_one_common_point: 
  ∀ l m: Line, l ≠ m → (
    (∃! A: Point, common_point l m A) ∨ (no_common_points l m)
  ) := 
begin
  intros l m,
  intro h,
  -- rw exists_unique,
  have hIl:=I2, 
  have hIm:=I2, 

  specialize hIl l,
  specialize hIm m,
  cases hIl with A hI2',
  cases hI2' with B hI2'',
  cases hI2'' with hAB hAlBl,
  cases hAlBl with hAl hBl,

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