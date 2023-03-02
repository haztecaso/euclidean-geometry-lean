import data.set
import incidence_geometry

-- constants A B C : Type

-- def ABCPoint : set Type := {A, B, C}
-- def ABCLine : set ABCPoint := {{A, B}, {B,C}}

-- instance : has_mem ABCPoint ABCLine := ⟨λ P l, P ∈ (l: set Type) ⟩


-- def f := λ a : ABCPoint, λ l : ABCLine, a ∈ l

-- variables {α : Type*}
-- def contains_element_in_powerset (s : set α) : Prop :=
--   ∃ x ∈ s, ∃ y ∈ set.powerset s, x ∈ y

-- def f (P : ABCPoint) (l : ABCLine) := ∃ x ∈ P, ∃ y ∈ l, x ∈ y

-- instance : incidence_geometry ABCPoint ABCLine := { 
--   lies_on := λ a b, a ∈ b,
--    i1 := sorry,
--    i2 := begin
--      intro l,
--    end,
--    i3 := sorry }

@[ext] structure Point := (x : ℝ) (y : ℝ)

-- y = mx + b
@[ext] structure Line := (m : ℝ) (b : ℝ)

noncomputable def line_from_points (A B : Point) : Line :=
  let m := (B.y-A.y)/(B.x-A.x) in ⟨m,A.y-m*A.x⟩

instance : incidence_geometry Point Line := { 
  lies_on := λ P l, P.y = P.x * l.m + l.b,
  i1 := begin
    intros A B hAB,
    rw exists_unique,
    -- let l : Line := ⟨(B.y-A.y)/(B.x-A.x), A.y-(B.y-A.y)/(B.x-A.x)*A.x⟩,
    let l := line_from_points A B,
    use l,
    simp,
    split,
    { split, 
      { sorry },
      { sorry }},
    { intros l' h1 h2,
      sorry }
  end,
  i2 := begin
    intro l,
    let A : Point := ⟨0, l.b⟩,
    let B : Point := ⟨-l.b/l.m, 0⟩,
    use [A, B],
    split,
    { sorry },
    { sorry },
  end,
  i3 := begin
    let A : Point := ⟨0, 0⟩,
    let B : Point := ⟨0, 1⟩,
    let C : Point := ⟨1, 1⟩,
    use [A, B, C],
    rw has_lies_on.collinear,
    by_contra hl,
    rcases hl with ⟨l, ⟨hAl, hBl, hCl⟩⟩,
    sorry
  end
  }

-- def is_in_line :  :=

-- def R2Line (P Q : R2Point):= { X : R2Point |  }
