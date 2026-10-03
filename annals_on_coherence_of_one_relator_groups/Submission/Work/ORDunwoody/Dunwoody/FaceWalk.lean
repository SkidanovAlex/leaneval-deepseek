/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The boundary walks of the faces of `Λ''` (step (G2), continued)

`Dunwoody/Source.lean` defines the vertices of the subdivided complex `Λ''` and its cells
(`Cell`, the sub-edges of a positive generator edge) and pattern points (`MidV`, the midpoints).

This file defines, for every face `(r, c)` of the Cayley complex — `r` a defining relator and `c`
a base point — the **boundary walk of `Λ''`**: the list of vertices visited when the word
`FreeGroup.toWord r` is read at `c`, with each generator edge subdivided by the geodesic data
`GeoData` and each cell split at its pattern point.

The walk is a `List (Vertex D)`, alternating between old vertices and pattern points.  Its
structure is what the pattern construction uses:

* the *visits* (the pattern points on the walk) and their labels `Sym2 V` (the edge of `T` the
  cell maps onto);
* the *arcs* between consecutive visits (the old vertices, which are connected in `Λ''` by edges
  avoiding the pattern);
* the fact that the walk is closed (`mk (toWord r) ∈ ker π`) and that it is a walk in the graph
  of `Λ''`.

Nothing here uses the simple connectivity of `Λ`; the side functions of the wall system are
defined from `φ` and the labels (see `DESIGN_N13.md`).
-/
import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.Source

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody.Dunwoody

open Work.ORDunwoody.Cayley

variable {G : Type u} [Group G] {V : Type u} [MulAction G V]
variable {T : GTree G V} {t₀ : V} {P : FinPresentation G}
variable {D : GeoData T t₀ P}

/-! ## The group element read off a word -/

/-- The group element reached by reading the word `w` at `a`. -/
def endPt (P : FinPresentation G) (a : G) : List (Fin P.n × Bool) → G
  | [] => a
  | x :: w => endPt P (a * CayV.genE P x) w

@[simp] theorem endPt_nil (P : FinPresentation G) (a : G) : endPt P a [] = a := rfl

@[simp] theorem endPt_cons (P : FinPresentation G) (a : G) (x : Fin P.n × Bool)
    (w : List (Fin P.n × Bool)) :
    endPt P a (x :: w) = endPt P (a * CayV.genE P x) w := rfl

/-- The group element read off a word is the product of the letters. -/
theorem endPt_eq_mul (P : FinPresentation G) (a : G) (w : List (Fin P.n × Bool)) :
    endPt P a w = a * P.π (FreeGroup.mk w) := by
  induction w generalizing a with
  | nil => rw [endPt_nil, ← FreeGroup.one_eq_mk, map_one, mul_one]
  | cons x w ih =>
      rw [endPt_cons, ih]
      have hmk : FreeGroup.mk (x :: w) = FreeGroup.mk [x] * FreeGroup.mk w := by
        rw [show (x :: w) = [x] ++ w from rfl, ← FreeGroup.mul_mk]
      rw [hmk, map_mul, ← CayV.genF_eq_mk]
      simp only [CayV.genE]
      group

/-- Reading a defining relator at any base point returns to the base point. -/
theorem endPt_toWord_eq (P : FinPresentation G) {r : FreeGroup (Fin P.n)} (hr : r ∈ P.rel)
    (a : G) : endPt P a (FreeGroup.toWord r) = a := by
  rw [endPt_eq_mul, FreeGroup.mk_toWord]
  have hker : r ∈ MonoidHom.ker P.π := by
    rw [P.ker_eq]
    exact Subgroup.subset_normalClosure hr
  rw [(MonoidHom.mem_ker.mp hker), mul_one]

/-! ## The traversals of a generator edge -/

/-- The vertices of `Λ''` visited *after* the initial vertex, when the generator edge with letter
`(j,true)` is traversed forwards from `a`.  The pattern points and the interior vertices
alternate; a collapsed generator (`L = 0`) contributes a single further vertex. -/
def edgeTailPos (D : GeoData T t₀ P) (a : G) (j : Fin P.n) : List (Vertex D) :=
  if D.L (j, true) = 0 then [Sum.inl (a * CayV.genE P (j, true), Sum.inl ())]
  else (List.finRange (D.L (j, true))).flatMap
    (fun k => [Sum.inr (⟨a, ⟨j, k⟩⟩ : MidV D), Sum.inl (pos D a j (k + 1))])

/-- The vertices of `Λ''` visited *after* the initial vertex, when the generator edge with letter
`(j,false)` (the reverse of the positive edge at `a * (genE (j,true))⁻¹`) is traversed. -/
def edgeTailNeg (D : GeoData T t₀ P) (a : G) (j : Fin P.n) : List (Vertex D) :=
  let a' := a * (CayV.genE P (j, true))⁻¹
  if D.L (j, true) = 0 then [Sum.inl (a', Sum.inl ())]
  else (List.finRange (D.L (j, true))).reverse.flatMap
    (fun k => [Sum.inr (⟨a', ⟨j, k⟩⟩ : MidV D), Sum.inl (pos D a' j k)])

/-- The tail of the boundary walk of a word: the vertices following the current one. -/
def faceAux (D : GeoData T t₀ P) (a : G) : List (Fin P.n × Bool) → List (Vertex D)
  | [] => []
  | (j, true) :: w => edgeTailPos D a j ++ faceAux D (a * CayV.genE P (j, true)) w
  | (j, false) :: w => edgeTailNeg D a j ++ faceAux D (a * (CayV.genE P (j, true))⁻¹) w

@[simp] theorem faceAux_nil (D : GeoData T t₀ P) (a : G) : faceAux D a [] = [] := rfl

@[simp] theorem faceAux_true (D : GeoData T t₀ P) (a : G) (j : Fin P.n)
    (w : List (Fin P.n × Bool)) :
    faceAux D a ((j, true) :: w) =
      edgeTailPos D a j ++ faceAux D (a * CayV.genE P (j, true)) w := rfl

@[simp] theorem faceAux_false (D : GeoData T t₀ P) (a : G) (j : Fin P.n)
    (w : List (Fin P.n × Bool)) :
    faceAux D a ((j, false) :: w) =
      edgeTailNeg D a j ++ faceAux D (a * (CayV.genE P (j, true))⁻¹) w := rfl

/-- **The boundary walk of a face of `Λ''`**: starting at the base vertex `c`, read the word `w`,
subdividing each generator edge by the geodesic data and splitting each cell at its pattern
point. -/
def faceWalk (D : GeoData T t₀ P) (c : G) (w : List (Fin P.n × Bool)) : List (Vertex D) :=
  Sum.inl (c, Sum.inl ()) :: faceAux D c w

@[simp] theorem faceWalk_eq (D : GeoData T t₀ P) (c : G) (w : List (Fin P.n × Bool)) :
    faceWalk D c w = Sum.inl (c, Sum.inl ()) :: faceAux D c w := rfl

end Work.ORDunwoody.Dunwoody
