import basic
import geometry.euclidean.basic


structure incidence_geometry (Point Line : Type*) :=
  (lies_on : Point → Line → Prop)

variables {Point Line : Type*}

/-- Determina si A es un punto común de dos líneas dadas -/
def is_common_point (i: incidence_geometry Point Line) (A : Point) (l m : Line) : Prop := 
  i.lies_on A l ∧ i.lies_on A m 

/-- Determina si dos líneas tienen un punto en común -/
def have_common_point (i : incidence_geometry Point Line) (l m : Line) : Prop := 
  ∃ A : Point, is_common_point i A l m

def parallel (i: incidence_geometry Point Line) (l m : Line) : Prop := 
  ¬ ∃ P : Point, is_common_point i P l m

def I1 (i : incidence_geometry Point Line) : Prop := 
  ∀ A B : Point, A ≠ B → ∃! l : Line, i.lies_on A l
def I2 (i : incidence_geometry Point Line) : Prop := 
  ∀ l : Line, ∃ A B : Point, A ≠ B ∧ i.lies_on A l ∧ i.lies_on B l
def I3 (i : incidence_geometry Point Line) : Prop :=
  ∃ A B C : Point, different3 A B C ∧ ¬ ∃ l : Line, i.lies_on A l ∧ i.lies_on B l ∧ i.lies_on C l

def P (i : incidence_geometry Point Line) : Prop :=
  ∀ l : Line, ∀ A : Point, ∃! m : Line, i.lies_on A m ∧ parallel i l m

def myPoint : set ℕ := {1,2,3,4,5},
def Line : set (set ℕ):= {{1,2}, {1,3}, {1,4}, {1,5}, {2,3}, {2, 4}, {2,5}, {3,4}, {3,5}, {4,5}},

/-- El axioma de las paralelas es independiente de los axiomas de incidencia. -/
theorem indepIP : ¬ (∀ Point Line : Type*, ∀ i: incidence_geometry Point Line, (I1 i ∧ I2 i ∧ I3 i) → P i):= begin
  intro h,
  sorry
end