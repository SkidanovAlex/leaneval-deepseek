import Mathlib
import Submission.Work.Whitney.ChernRelDefs
import Submission.Work.Whitney.ChernRelSeries
import Submission.Work.Whitney.convSeries_comm
import Submission.Work.Whitney.convSeries_unit_right
import Submission.Work.Whitney.convTerm_twoTerm_geo_zero
import Submission.Work.Whitney.convTerm_twoTerm_geo_one

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The telescoping of the two-term series against the geometric series

`Work.Whitney.ChernRel.twoTermSeries z` is the Chern series `1 + z t` of a complex line bundle,
and `Work.Whitney.ChernRel.geoSeriesOf z` is the signed geometric series `Σ (-1)^i z^i t^i`, the
convolution inverse of `1 + z t`: `g₀ = 1` and `g_{i+1} = - (g_i ⌣ z)`
(`Work.Whitney.ChernRel.geoSeriesOf_succ`).

This module proves that the convolution with `1 + z t` is absorbed by the geometric series:

  `convSeries (twoTermSeries z) (convSeries u (geoSeriesOf z)) (k+1) = u (k+1)`,

i.e. `(1 + z t)·(u·(1 + z t)⁻¹) = u` in the convolution algebra of even-degree cohomology.  It is
the algebraic identity behind the *telescoping* in the Chern relation
`Σ_{j} (-1)^j c_{m-j}(E) ζ^j = 0`: the convolution inverse of the Chern series of a line bundle
cancels the sign pattern of the relation.

The proof has three layers, each of which uses a different part of the algebra of
`Submission/Work/LerayHirsch/Series.lean` and `Submission/Work/Whitney/ChernRelDefs.lean`:

* **the telescoping** `convSeries (twoTermSeries z) (geoSeriesOf z) (m+1) = 0`: only the summands
  `i = 0, 1` of the convolution survive (`twoTermSeries z i = 0` for `i ≥ 2`,
  `Work.Whitney.ChernRel.twoTermSeries_of_two_le`), and they are the `i = 0` and `i = 1` summands
  `g_{m+1}` and `z ⌣ g_m` computed in `Work.Whitney.convTerm_twoTerm_geo_zero` /
  `Work.Whitney.convTerm_twoTerm_geo_one`; since `g_{m+1} = -(g_m ⌣ z)` and `z` commutes with the
  even class `g_m`, their sum is zero.  In degree `0` the single summand is `1 ⌣ 1 = 1`;
* **the unit law of the convolution** `convSeries x y k = x k` when `y₀ = 1` and `y_j = 0` for
  `j ≥ 1` (`Work.Whitney.convSeries_unit_right`), and the commutativity
  `convSeries x y = convSeries y x` (`Work.Whitney.convSeries_comm`);
* **the assembly**: associativity of the convolution (`Work.LerayHirsch.convSeries_assoc`) moves
  the two-term series next to the geometric series, where it telescopes to the unit series, and the
  unit law removes it.
-/

namespace Work.Whitney

open Work.TangentClasses Work.Thom

noncomputable section

/-! ## The telescoping `convSeries (twoTermSeries z) (geoSeriesOf z) = 1` -/

/-- **The summands of index `≥ 2` of the convolution vanish**: at the indices `i + 2` the first
factor `twoTermSeries z (i+2)` of the convolution is `0`. -/
theorem convSeries_twoTerm_geo_interior {B : Type} [TopologicalSpace B]
    (z : Work.Thom.Coh ℤ 2 B) (m : ℕ) :
    (∑ i ∈ Finset.range m, Work.LerayHirsch.convTerm (Work.Whitney.ChernRel.twoTermSeries z)
      (Work.Whitney.ChernRel.geoSeriesOf z) (m + 1) (i + 2)) = 0 := by
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hi' : i + 2 ≤ m + 1 := by omega
  rw [Work.LerayHirsch.convTerm_pos hi']
  rw [Work.Whitney.ChernRel.twoTermSeries_of_two_le z (by omega : 2 ≤ i + 2)]
  rw [Work.Cohomology.cupH'_zero_left]
  exact Work.Whitney.ChernRel.cohTransport_zero _

/-- **The convolution of `1 + z t` with the signed geometric series in degree `0`**: the only
summand is `1 ⌣ 1 = 1`. -/
theorem convSeries_twoTerm_geo_zero {B : Type} [TopologicalSpace B]
    (z : Work.Thom.Coh ℤ 2 B) :
    Work.LerayHirsch.convSeries (Work.Whitney.ChernRel.twoTermSeries z)
      (Work.Whitney.ChernRel.geoSeriesOf z) 0 = Work.Cohomology.oneH ℤ (Work.Whitney.ssB B) := by
  unfold Work.LerayHirsch.convSeries
  rw [Finset.sum_range_one]
  rw [Work.LerayHirsch.convTerm_pos (Nat.zero_le 0)]
  rw [Work.Whitney.ChernRel.twoTermSeries_zero, Work.Whitney.ChernRel.geoSeriesOf_zero]
  rw [Work.Cohomology.cupH'_one_right]
  exact (Work.LerayHirsch.cohTransport_congr_proof _ rfl).trans (Work.Thom.cohTransport_rfl _)

/-- **The telescoping identity**: `convSeries (twoTermSeries z) (geoSeriesOf z) (m+1) = 0`, i.e. the
product `(1 + z t)·(1 - z t + z²t² - …)` has no coefficients in positive degrees. -/
theorem convSeries_twoTerm_geo_succ {B : Type} [TopologicalSpace B]
    (z : Work.Thom.Coh ℤ 2 B) (m : ℕ) :
    Work.LerayHirsch.convSeries (Work.Whitney.ChernRel.twoTermSeries z)
      (Work.Whitney.ChernRel.geoSeriesOf z) (m + 1) = 0 := by
  rw [show Work.LerayHirsch.convSeries (Work.Whitney.ChernRel.twoTermSeries z)
        (Work.Whitney.ChernRel.geoSeriesOf z) (m + 1)
      = (∑ i ∈ Finset.range m, Work.LerayHirsch.convTerm (Work.Whitney.ChernRel.twoTermSeries z)
          (Work.Whitney.ChernRel.geoSeriesOf z) (m + 1) (i + 2))
        + Work.LerayHirsch.convTerm (Work.Whitney.ChernRel.twoTermSeries z)
          (Work.Whitney.ChernRel.geoSeriesOf z) (m + 1) 1
        + Work.LerayHirsch.convTerm (Work.Whitney.ChernRel.twoTermSeries z)
          (Work.Whitney.ChernRel.geoSeriesOf z) (m + 1) 0 from by
    unfold Work.LerayHirsch.convSeries
    rw [Finset.sum_range_succ', Finset.sum_range_succ']]
  rw [convSeries_twoTerm_geo_interior, Work.Whitney.convTerm_twoTerm_geo_one z m,
    Work.Whitney.convTerm_twoTerm_geo_zero z m]
  simp

/-! ## The target -/

/-- **The two-term series cancels the geometric series**: for every even-degree series `u`,
`(1 + z t)·(u·(1 + z t)⁻¹) = u` in the convolution algebra, i.e.

  `convSeries (twoTermSeries z) (convSeries u (geoSeriesOf z)) (k+1) = u (k+1)`. -/
theorem convSeries_twoTerm_geo {B : Type} [TopologicalSpace B] (z : Work.Thom.Coh ℤ 2 B)
    (u : (i : ℕ) → Work.Thom.Coh ℤ (2 * i) B) (k : ℕ) :
    Work.LerayHirsch.convSeries (Work.Whitney.ChernRel.twoTermSeries z)
        (Work.LerayHirsch.convSeries u (Work.Whitney.ChernRel.geoSeriesOf z)) (k + 1)
      = u (k + 1) := by
  rw [← Work.LerayHirsch.convSeries_assoc (Work.Whitney.ChernRel.twoTermSeries z) u
    (Work.Whitney.ChernRel.geoSeriesOf z) (k + 1)]
  rw [Work.Whitney.ChernRel.convSeries_congr_left (y := Work.Whitney.ChernRel.geoSeriesOf z)
    (k := k + 1) (x := Work.LerayHirsch.convSeries (Work.Whitney.ChernRel.twoTermSeries z) u)
    (x' := Work.LerayHirsch.convSeries u (Work.Whitney.ChernRel.twoTermSeries z))
    (fun i _ => Work.Whitney.convSeries_comm (Work.Whitney.ChernRel.twoTermSeries z) u i)]
  rw [Work.LerayHirsch.convSeries_assoc u (Work.Whitney.ChernRel.twoTermSeries z)
    (Work.Whitney.ChernRel.geoSeriesOf z) (k + 1)]
  exact Work.Whitney.convSeries_unit_right u
    (Work.LerayHirsch.convSeries (Work.Whitney.ChernRel.twoTermSeries z)
      (Work.Whitney.ChernRel.geoSeriesOf z))
    (convSeries_twoTerm_geo_zero z) (fun j hj => by
      obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      exact convSeries_twoTerm_geo_succ z m) (k + 1)

end

end Work.Whitney
