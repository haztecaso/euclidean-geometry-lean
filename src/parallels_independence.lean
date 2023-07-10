import congruence_geometry

open incidence_geometry

def parallel (Point : Type*) {Line : Type*} [ig : incidence_geometry Point Line] (l m : Line) : Prop := 
  ¬ ∃ P : Point, is_common_point P l m

def P (Point Line : Type*) [ig : incidence_geometry Point Line] : Prop :=
  ∀ l : Line, ∀ A : Point, ∃! m : Line, A ~ m ∧ parallel Point l m

/-- El axioma de las paralelas es independiente de los axiomas de incidencia. -/
theorem incidence_geometry_parallels_independence (Point Line : Type*) : 
  ¬ (∀ ig: incidence_geometry Point Line, @P Point Line ig) := 
begin
  push_neg,
  sorry
end

/-- El axioma de las paralelas es independiente de los axiomas de congruencia . -/
theorem congruence_geometry_parallels_independence (Point Line : Type*) : 
  ¬ (∀ cg: congruence_geometry Point Line, @P Point Line cg.to_incidence_geometry) := 
begin
  push_neg,
  sorry
end