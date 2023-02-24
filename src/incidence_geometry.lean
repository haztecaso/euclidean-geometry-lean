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
There exist three different noncollinear points.
-/
axiom I3: ∃ A B C: Point, (A ≠ B ∧ A ≠ C ∧ B≠ C) ∧ ¬ collinear A B C

/--
Given two different points get the line that passes through them
-/
noncomputable def line (A B:Point) (h: A ≠ B): 
  { l: Line // A ~ l ∧ B ~ l ∧ ∀ l' : Line,  A ~ l' ∧ B ~ l' → l' = l } := 
begin
  have hAB := I1 A B h,
  rw exists_unique at hAB,
  let P := λ l:Line,  A ~ l ∧ B ~ l ∧ ∀ l' : Line,  A ~ l' ∧ B ~ l' → l' = l,
  have hlP: ∃ l :Line, P l, { tauto },
  exact classical.indefinite_description P hlP,
end

/--
Given a point there exist another two different points different to it
-/
lemma exist_ne_points (A: Point) :
  ∃ B C:Point, A ≠ B ∧ A ≠ C ∧ B ≠ C := 
begin
  rcases I3 with ⟨P, Q, R, h⟩,
  by_cases hAP: A = P,
  { use Q, use R, rw hAP, exact h.left },
  { by_cases hAQ: A = Q,
    { use P, use R, rw hAQ, tauto },
    { use P, use Q, tauto }},
end

/--
For any point there exist one point different to it
-/
lemma exist_ne_point (A:Point): ∃ B:Point, A ≠ B := 
begin
  rcases exist_ne_points A with ⟨B, -, ⟨hAB, -, -⟩⟩,
  use B,
end

def is_common_point (A: Point) (l m: Line) := A ~ l ∧ A ~ m
def have_common_point (l m: Line) := ∃ A:Point, is_common_point A l m

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
  ∀ l m: Line, l ≠ m → (∃! A: Point, is_common_point A l m) ∨ (¬ have_common_point l m) := 
begin
  intros l m,
  contrapose!,
  rintro ⟨not_unique, hlm⟩,
  rw [exists_unique, push_neg.not_exists_eq] at not_unique,
  push_neg at not_unique,
  choose A hA using hlm,
  rcases not_unique A hA with ⟨B, ⟨hB, hAB⟩⟩,
  rw ne_comm at hAB,
  let hI1 := I1 A B hAB,
  let hABlm := and.intro hA hB,
  rw common_points_and_lines_eq at hABlm,
  rw ← unique_of_exists_unique hI1 hABlm.1 hABlm.2,
end

/--
There exist three disctinct lines not through any common point
-/
lemma disctinct_lines_not_concurrent:
  ∃ l m n: Line, l ≠ m ∧ l ≠ n ∧ m ≠ n →
  ¬ have_common_point l m ∧ ¬ have_common_point l n ∧ ¬ have_common_point m n
  :=
begin
  rcases I3 with ⟨A, B, C, h⟩,
  rcases h.left with ⟨hAB, hAC, hBC⟩,
  have AB := line A B hAB,
  have AC := line A C hAC,
  have BC := line B C hBC,
  have hABAC: AB.val ≠ AC.val, { sorry },
  have hABBC: AB.val ≠ BC.val, { sorry },
  have hACBC: AC.val ≠ BC.val, { sorry },
  sorry
end

/-- 
For every line there is at least one point not lying on it.
-/
lemma line_external_point: ∀ l: Line, ∃ A: Point, ¬ A ~ l :=
begin
  rcases I3 with ⟨A, B, C, ⟨-, h1⟩⟩,
  by_contra h2,
  rw collinear at h1,
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
lemma point_external_line: ∀ A: Point, ∃ l: Line, ¬ A ~ l :=
begin
  intro A,
  rcases I3 with ⟨P, Q, R, ⟨⟨hPQ, hPR, hQR⟩, h2⟩⟩,
  rw collinear at h2,
  by_cases hAP: A = P,
  { 
    let QR := line Q R hQR,
    use QR.val,
    rw hAP,
    rw push_neg.not_exists_eq at h2,
    specialize h2 QR,
    rw push_neg.not_and_distrib_eq at h2,
    rw push_neg.not_and_distrib_eq at h2,
    sorry
  },
  { sorry },
end

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