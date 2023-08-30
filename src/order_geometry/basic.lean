import ..incidence_geometry.basic

open incidence_geometry
open_locale classical

/-!
# Axiomas de orden

En este fichero se enuncian los axiomas de orden de la geometría euclídea plana y se definen
entidades y demuestran resultados que dependen de estos axiomas.

## Notaciones

- Se mantiene el uso de la relación de incidencia A ~ l.
- Se utiliza la notación local A * B * C para la relación de orden.

-/

/-- Geometría del orden, clase que engloba los axiomas para la relación de orden. -/
class order_geometry (Point Line : Type*) extends incidence_geometry Point Line :=
  (between: Point → Point → Point →  Prop)
  (notation A `*` B `*` C := between A B C)
  (B11 {A B C: Point} (h : A * B * C) : neq3 A B C ∧ collinear Line A B C ∧ C * B * A)
  (B12 {A B C: Point} (h : A * B * C) : C * B * A)
  (B2 {A B : Point} (h : A ≠ B): ∃ C : Point, A * B * C)
  (B3 {A B C : Point} (h : collinear Line A B C): xor3 (A * B * C) (B * A * C) (A * C * B))
  (B4 {A B C D : Point} {l : Line} (h_non_collinear : ¬ collinear Line A B C) 
      (hlABC : ¬ (A ~ l ∨ B ~ l ∨ C ~ l)) (hlD : D ~ l) (hADB : A * D * B)
      : xor (∃ E ,  E ~ l ∧ (A * E * C)) (∃ E, E ~ l ∧ (B * E * C)))


namespace order_geometry

variables {Point Line : Type*} [og : order_geometry Point Line]

local notation A `*` B `*` C := og.between A B C

/-- La relación between es simétrica en el primer y tercer argumento. -/
lemma between_symm (A B C : Point) : (A * B * C) ↔ (C * B * A) :=
begin
  split,
  { intro h, exact og.B12 h },
  { intro h, exact og.B12 h },
end

/-- 
Los segmentos están implementados mediante estructuras determinadas por dos puntos distintos.
-/
structure Segment (Point : Type*) := 
  (A B : Point) 
  (neq : A ≠ B)

/-- Un punto pertenece a un segmento si coincide con uno de los extremos o está entre ellos. -/
def Segment.in {Point : Type*} (seg : Segment Point) (Line : Type*) [og : order_geometry Point Line]  (P : Point) : Prop := 
  P = seg.A ∨ P = seg.B ∨ (og.between seg.A P seg.B)

/--
Relación de pertenencia entre puntos y segmentos.
Un punto está en un segmento si coincide con uno de los extremos o está entre ellos.
-/
instance [order_geometry Point Line] : has_mem Point (Segment Point) := ⟨λ P seg, seg.in Line P⟩

/--
Relación de intersección entre segmentos y líneas.
Un segmento se interseca con una línea si tienen un punto en común
-/
def segment_intersect_line [order_geometry Point Line] (S : Segment Point) (l : Line) := 
∃ P : Point, P ∈ S ∧ P ~ l

/-- Un triángulo está determinado por tres puntos no alineados -/
structure Triangle (Point Line: Type*) [order_geometry Point Line] := 
  (A B C : Point) 
  (non_collinear : ¬ collinear Line A B C)

lemma Triangle.non_collinear_symm {Point Line: Type*} [order_geometry Point Line] (T : Triangle Point Line) : ¬ collinear Line T.B T.A T.C :=
begin  
  rw collinear_symm,
  exact T.non_collinear,
end

lemma Triangle.non_collinear_symm' {Point Line: Type*} [order_geometry Point Line] (T : Triangle Point Line) : ¬ collinear Line T.C T.A T.B :=
begin  
  rw [collinear_symm2, collinear_symm],
  exact T.non_collinear,
end

lemma Triangle.neq {Point Line: Type*} [order_geometry Point Line] (T : Triangle Point Line) : neq3 T.A T.B T.C :=
begin  
  exact non_collinear_neq Line T.non_collinear,
end

-- instance (Point Line : Type) [order_geometry Point Line] : has_mem Point (Triangle Point) := 
--   ⟨λ P T, 
--       P ∈ (Segment.mk T.A T.B T.neq.1) 
--     ∨ P ∈ (Segment.mk T.A T.C T.neq.2.1) 
--     ∨ P ∈ (Segment.mk T.B T.C T.neq.2.2)⟩

structure Ray (Point : Type*) := 
  (A B: Point)
  (neq : A ≠ B)

instance [order_geometry Point Line] : has_mem Point (Ray Point) :=
  ⟨λ P ray, begin
    by_cases P ≠ ray.B,
    { exact P = ray.A ∨ ¬ ray.A ∈ Segment.mk P ray.B h },
    { exact true, },
  end ⟩

structure Angle (Point Line: Type*) [order_geometry Point Line] :=
  (r1 r2 : Ray Point)
  (vertex : r1.A = r2.A)
  (non_collinear : ¬ collinear Line r1.A r1.B r2.B)


def Angle.A {Point Line: Type*} [order_geometry Point Line] (α : Angle Point Line) : Point := α.r1.A

def Angle.B {Point Line: Type*} [order_geometry Point Line] (α : Angle Point Line) : Point := α.r1.B

def Angle.C {Point Line: Type*} [order_geometry Point Line] (α : Angle Point Line) : Point := α.r2.B

lemma Angle.neq {Point Line: Type*} [order_geometry Point Line] (α : Angle Point Line) : neq3 α.A α.B α.C :=
begin  
  exact non_collinear_neq Line α.non_collinear,
end

def Angle.mk_from_points [order_geometry Point Line] (B A C : Point) (h : ¬ collinear Line A B C): Angle Point Line := 
begin
  let neq := non_collinear_neq Line h,
  let r1 := Ray.mk A B neq.left,
  let r2 := Ray.mk A C neq.right.left,
  have vertex : r1.A = r2.A, { refl },
  exact ⟨r1, r2, vertex, h⟩
end


end order_geometry