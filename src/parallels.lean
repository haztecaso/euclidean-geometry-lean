import basic
import incidence_geometry

open incidence_geometry

def parallel (Point : Type*) {Line : Type*} [incidence_geometry Point Line]
(l m : Line) := ¬ ∃ P : Point, is_common_point P l m

axiom P {Point Line : Type*} [incidence_geometry Point Line] (l : Line) (P: Point) :
  ∃! m : Line, P ~ m ∧ parallel Point l m
