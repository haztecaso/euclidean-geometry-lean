import Mathlib.Logic.ExistsUnique
import Mathlib.Logic.Basic
import Hilbert.Basic

class IncidenceGeometry (Point Line : Type*) where
  lies_on : Point → Line → Prop
  I1 {A B : Point} (_h : A ≠ B) : ∃! l : Line, lies_on A l ∧ lies_on B l ∧
      ∀ l' : Line, lies_on A l' ∧ lies_on B l' → l' = l
  I2 (l : Line) : ∃ A B : Point, A ≠ B ∧ lies_on A l ∧ lies_on B l
  I3 : ∃ A B C : Point, A ≠ B ∧ B ≠ C ∧ A ≠ C ∧
      ¬∃ l : Line, lies_on A l ∧ lies_on B l ∧ lies_on C l

namespace IncidenceGeometry

variable {Point Line : Type*} [IncidenceGeometry Point Line]

scoped infix:50 " ~ " => IncidenceGeometry.lies_on

noncomputable def unique_line {A B : Point} (h : A ≠ B) :
    { l : Line // A ~ l ∧ B ~ l ∧ ∀ l' : Line, A ~ l' ∧ B ~ l' → l' = l } :=
  have h1 := I1 h
  ⟨h1.choose, h1.choose_spec.1.1, h1.choose_spec.1.2.1, h1.choose_spec.1.2.2⟩

noncomputable def line {A B : Point} (h : A ≠ B) : Line :=
  (unique_line h).val

def collinear (Line : Type*) [IncidenceGeometry Point Line] (A B C : Point) : Prop :=
  ∃ l : Line, A ~ l ∧ B ~ l ∧ C ~ l

@[simp] lemma collinear_symm (A B C : Point) :
    collinear Line A B C ↔ collinear Line B A C := by
  constructor
  · rintro ⟨l, hA, hB, hC⟩
    exact ⟨l, hB, hA, hC⟩
  · rintro ⟨l, hB, hA, hC⟩
    exact ⟨l, hA, hB, hC⟩

@[simp] lemma collinear_symm2 (A B C : Point) :
    collinear Line A B C ↔ collinear Line C B A := by
  constructor
  · rintro ⟨l, hA, hB, hC⟩
    exact ⟨l, hC, hB, hA⟩
  · rintro ⟨l, hC, hB, hA⟩
    exact ⟨l, hA, hB, hC⟩

lemma push_neg.non_collinear (A B C : Point) :
    ¬ collinear Line A B C ↔ ∀ x : Line, (¬ A ~ x) ∨ (¬ B ~ x) ∨ (¬ C ~ x) := by
  unfold collinear
  rw [not_exists]
  simp only [not_and_or]

lemma exist_neq_point (A : Point) : ∃ B : Point, A ≠ B := by
  sorry

lemma non_collinear_neq {A B C : Point} (h_non_collinear : ¬ collinear Line A B C) :
    neq3 A B C := by
  sorry

def points_in_line (A B : Point) (l : Line) := A ~ l ∧ B ~ l

def is_common_point (A : Point) (l m : Line) := A ~ l ∧ A ~ m

def have_common_point (l m : Line) := ∃ A : Point, is_common_point A l m

lemma line_external_ne {A B C : Point} (hAB : A ≠ B) (hC : ¬ C ~ (line (Line := Line) hAB)) :
    A ≠ C ∧ B ≠ C := by
  sorry

lemma neq_lines_have_at_most_one_common_point {l m : Line} (h : l ≠ m) :
    (∃! A : Point, is_common_point A l m) ∨ (¬ have_common_point (Point := Point) l m) := by
  sorry

lemma non_collinear_ne_lines {A B C : Point} (h_noncollinear : ¬ collinear Line A B C)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) :
    (line (Line := Line) hAB) ≠ (line hAC) ∧
    (line (Line := Line) hAB) ≠ (line hBC) ∧
    (line (Line := Line) hAC) ≠ (line hBC) := by
  sorry

lemma exist_neq_lines_not_concurrent :
    ∃ l m n : Line, (l ≠ m ∧ l ≠ n ∧ m ≠ n) ∧
      ¬ ∃ P : Point, is_common_point P l m ∧ is_common_point P l n ∧ is_common_point P m n := by
  sorry

lemma line_has_external_point (l : Line) : ∃ P : Point, ¬ P ~ l := by
  sorry

lemma point_has_external_line (A : Point) : ∃ l : Line, ¬ A ~ l := by
  sorry

lemma eq_lines_determined_by_points {A B C : Point} (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) :
    ((line (Line := Line) hAB) = (line hAC)) → (line (Line := Line) hAB) = (line hBC) := by
  sorry
