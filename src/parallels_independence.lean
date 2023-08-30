import data.set.function data.finset.card .congruence_geometry.basic

open incidence_geometry

/-- Dos líneas son paralelas si no tienen ningún punto en común. -/
def parallel (Point : Type*) {Line : Type*} [ig : incidence_geometry Point Line] 
  (l m : Line) : Prop := ¬ ∃ P : Point, is_common_point P l m

/-- **Axioma de las paralelas**: Dadas una línea y un punto externo a ella existe 
una única línea que pasa por el punto y es paralela a la primera línea. -/
def P (Point Line : Type*) [ig : incidence_geometry Point Line] := 
  ∀ (l : Line) (A : Point), ¬ A ~ l → ∃! m : Line, A ~ m ∧ parallel Point l m

inductive myPoint
  | A | B | C | D | E

-- instance : nonempty myPoint := ⟨myPoint.A⟩ 

instance : decidable_eq myPoint := sorry

def myLine := { l : finset myPoint // l.card = 2 }

def myLine.mk {A B : myPoint} (h : A ≠ B) : myLine := { 
  val := {A, B},
  property := finset.card_doubleton h
}

def lies_on (P : myPoint) (l : myLine) : Prop := P ∈ l.val

def myIncidenceGeometry : incidence_geometry myPoint (myLine) := { 
  lies_on := λ P l, P ∈ l.val,
  I1 := begin
    intros A B hAB,
    let l := myLine.mk hAB,
    rw exists_unique,
    use l,
    split,
    { sorry },
    { intros m h,
      sorry },
  end,
  I2 := begin
    intro l,
    sorry
  end,
  I3 := begin 
    use myPoint.A,
    use myPoint.B,
    use myPoint.C,
    split,
    { sorry },
    { push_neg, 
      intros l hA hB hC,
      sorry },
  end }

-- Opcion B: mediante biyecciones
-- def myLine := { l : set myPoint // ∃ f : myPoint → ℕ, set.bij_on f l {0, 1}}

-- def myLine.mk {P Q: myPoint} (hPQ : P ≠ Q) : myLine :=
-- { val := {P, Q},
--   property := begin 
--     let f : myPoint → ℕ  := begin sorry end,
--     use f,
--     rw set.bij_on,
--     rw set.maps_to,
--     rw set.inj_on,
--     rw set.surj_on,
--     sorry
--   end
-- }

-- noncomputable def myLine.A (l : myLine) : myPoint := begin
--   choose f hf using l.property,
--   exact (function.inv_fun_on f l.val) 0,
-- end

-- noncomputable def myLine.B (l : myLine) : myPoint := begin
--   choose f hf using l.property,
--   exact (function.inv_fun_on f l.val) 1,
-- end

-- noncomputable def myLine.neq (l : myLine) : l.A ≠ l.B := begin
--   rw myLine.A,
--   rw myLine.B,
--   rw ne,
--   by_contra h,
--   sorry
-- end

-- def myIncidenceGeometry : incidence_geometry myPoint (myLine) := { 
--   lies_on := λ P l, P ∈ l.val,
--   I1 := begin
--     intros P Q hPQ,
--     rw exists_unique,
--     let lPQ := myLine.mk hPQ,
--     use lPQ,
--     split,
--     { split, 
--       { sorry },
--       { sorry }},
--     { sorry }
--   end,
--   I2 := begin
--     intros l,
--     l.val
--     sorry
--   end,
--   I3 := begin
--     sorry
--   end,
--   }

/-- El axioma de las paralelas es independiente de los axiomas de incidencia. -/
theorem incidence_geometry_parallels_independence (Point Line : Type*) : 
  ¬ (∀ ig: incidence_geometry Point Line, @P Point Line ig) := 
begin
  push_neg,
  have ig : incidence_geometry Point Line,
  { sorry },
  use ig,
  rw P,
  push_neg,
  sorry
end

/-- El axioma de las paralelas es independiente de los axiomas de congruencia.-/
theorem congruence_geometry_parallels_independence (Point Line : Type*) : 
  ¬ (∀ cg: congruence_geometry Point Line, 
      @P Point Line cg.to_incidence_geometry) := 
begin
  push_neg,
  sorry
end