import basic
import geometry.euclidean.basic
import data.finset

structure incidence_geometry (Point Line : Type*) :=
  (lies_on : Point → Line → Prop)
  (infix ` ~ ` : 50 := lies_on)
  (I1 {A B : Point} (h : A ≠ B): ∃! l : Line, A ~ l ∧ B ~ l)
  (I2 (l : Line) : ∃ A B : Point, A ≠ B ∧ A ~ l ∧ B ~ l)
  (I3 : ∃ A B C : Point, different3 A B C ∧ ¬ ∃ l : Line,  A ~ l ∧ B ~ l ∧ C ~ l)

variables {Point Line : Type*}

/-- Determina si A es un punto común de dos líneas dadas -/
def is_common_point (i: incidence_geometry Point Line) (A : Point) (l m : Line) : Prop := 
  i.lies_on A l ∧ i.lies_on A m 

/-- Determina si dos líneas tienen un punto en común -/
def have_common_point (i : incidence_geometry Point Line) (l m : Line) : Prop := 
  ∃ A : Point, is_common_point i A l m

def parallel (i: incidence_geometry Point Line) (l m : Line) : Prop := 
  ¬ ∃ P : Point, is_common_point i P l m

def P (i : incidence_geometry Point Line) : Prop :=
  ∀ l : Line, ∀ A : Point, ∃! m : Line, i.lies_on A m ∧ parallel i l m

inductive myPoint
  | A | B | C | D | E

-- def myLine : set (set myPoint) := {{myPoint.A, myPoint.B}, {myPoint.B}}

-- structure myLine (line : set myPoint) :=
--   (h : Prop := line.)

-- otra idea es considerar una biyeccion con bool
def myLine := { l : finset myPoint // l.card = 2 }



-- def ej : myLine := {
--   val := begin
--     let e := finset.empty,
--     let a := finset.cons e myPoint.A,

--   end,
--   property := _ 
-- }

def lies_on (P : myPoint) (l : myLine) : Prop := P ∈ l.val




def myIncidenceGeometry : incidence_geometry myPoint (myLine) := { 
  lies_on := λ P l, P ∈ l.val,
  I1 := begin
    intros A B hAB,
    let l : myLine := ⟨{A, B}, sorry⟩,
    rw exists_unique,
    use l,
    split,
    { tauto },
    { intros m h,
      
      sorry },
  end,
  I2 := _,
  I3 := _ }

/-- El axioma de las paralelas es independiente de los axiomas de incidencia. -/
theorem indepIP : ¬ (∀ Point Line : Type*, ∀ i: incidence_geometry Point Line, P i):= begin
  intro h,
  sorry
end