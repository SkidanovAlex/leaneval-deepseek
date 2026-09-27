import Mathlib
import Submission.Work.Geo.DualStretch.Defs
import Submission.Work.Geo.DualStretch.Basic
import Submission.Work.Geo.DualStretch.carrier_spec
import Submission.Work.PL.Generic.mem_hullOf

/-!
# Barycentric coordinates of a point of a complex (`coord_spec`)

`Work.Geo.DualStretch.coord P x` is the barycentric-coordinate function of `x` with respect to its
carrier face `carrier P x` (the smallest face of `P` whose simplex contains `x`); it is `0` off that
face.  Here we show the specification of that function: on the carrier face the coordinates are
non-negative and sum to `1`, they represent `x` as their centre of mass, and off the carrier face
they vanish.

The existence half is the finite convex-combination representation of a point of a simplex, which is
`Work.PL.Generic.mem_hullOf` (`hullOf id s = PL.simp s`).
-/

open Set Metric
open scoped Classical

namespace Work.Geo.DualStretch

open _root_.PL (E Cx)

variable {n : ℕ}

/-- **A point of a simplex is a convex combination of its vertices**, in the form needed for
barycentric coordinates: a weight function `μ` on the ambient space, non-negative on `σ`, with
total mass `1` and centre of mass `x`. -/
theorem exists_coordOn_of_mem_simp {σ : Finset (PL.E n)} {x : PL.E n} (hx : x ∈ PL.simp σ) :
    ∃ μ : PL.E n → ℝ, (∀ w ∈ σ, 0 ≤ μ w) ∧
      (∑ w ∈ σ, μ w = 1) ∧ (∑ w ∈ σ, μ w • w = x) := by
  have hmem : x ∈ Work.PL.Generic.hullOf (id : PL.E n → PL.E n) σ := by
    rw [Work.PL.Generic.hullOf, Set.image_id]
    exact hx
  exact (Work.PL.Generic.mem_hullOf (id : PL.E n → PL.E n) σ x).mp hmem

/-- Barycentric coordinates of `x` on its carrier face: the local existence statement underlying
`Work.Geo.DualStretch.coord`. -/
theorem coord_exists (P : PL.Cx n) (hP : P.faces.Finite) {x : PL.E n} (hx : x ∈ P.space) :
    ∃ μ : PL.E n → ℝ, (∀ w ∈ Work.Geo.DualStretch.carrier P x, 0 ≤ μ w) ∧
      (∑ w ∈ Work.Geo.DualStretch.carrier P x, μ w = 1) ∧
      (∑ w ∈ Work.Geo.DualStretch.carrier P x, μ w • w = x) := by
  obtain ⟨-, hxs, -⟩ := carrier_spec P hP hx
  exact exists_coordOn_of_mem_simp hxs

theorem coord_spec {n : ℕ} (P : PL.Cx n) (hP : P.faces.Finite) {x : PL.E n} (hx : x ∈ P.space) :
    (∀ v ∈ Work.Geo.DualStretch.carrier P x,
        0 ≤ Work.Geo.DualStretch.coord P x v) ∧
      (∑ v ∈ Work.Geo.DualStretch.carrier P x,
          Work.Geo.DualStretch.coord P x v = 1) ∧
      (∑ v ∈ Work.Geo.DualStretch.carrier P x,
          Work.Geo.DualStretch.coord P x v • v = x) ∧
      (∀ v ∉ Work.Geo.DualStretch.carrier P x,
          Work.Geo.DualStretch.coord P x v = 0) := by
  classical
  have hex : ∃ μ : PL.E n → ℝ, (∀ w ∈ Work.Geo.DualStretch.carrier P x, 0 ≤ μ w) ∧
      (∑ w ∈ Work.Geo.DualStretch.carrier P x, μ w = 1) ∧
      (∑ w ∈ Work.Geo.DualStretch.carrier P x, μ w • w = x) := coord_exists P hP hx
  obtain ⟨hex0, hex1, hex2⟩ := hex.choose_spec
  have hcoord : ∀ v : PL.E n,
      Work.Geo.DualStretch.coord P x v
        = if v ∈ Work.Geo.DualStretch.carrier P x then hex.choose v else 0 := by
    intro v
    by_cases hv : v ∈ Work.Geo.DualStretch.carrier P x
    · simp only [Work.Geo.DualStretch.coord, dite_eq_left hv, dite_eq_left hex, ite_eq_left hv]
    · simp only [Work.Geo.DualStretch.coord, dite_eq_right hv, ite_eq_right hv]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hv
    rw [hcoord v, ite_eq_left hv]
    exact hex0 v hv
  · have h : ∑ v ∈ Work.Geo.DualStretch.carrier P x, Work.Geo.DualStretch.coord P x v
        = ∑ v ∈ Work.Geo.DualStretch.carrier P x, hex.choose v :=
      Finset.sum_congr rfl fun v hv => by rw [hcoord v, ite_eq_left hv]
    rw [h]; exact hex1
  · have h : ∑ v ∈ Work.Geo.DualStretch.carrier P x, Work.Geo.DualStretch.coord P x v • v
        = ∑ v ∈ Work.Geo.DualStretch.carrier P x, hex.choose v • v :=
      Finset.sum_congr rfl fun v hv => by rw [hcoord v, ite_eq_left hv]
    rw [h]; exact hex2
  · intro v hv
    rw [hcoord v, ite_eq_right hv]

end Work.Geo.DualStretch
