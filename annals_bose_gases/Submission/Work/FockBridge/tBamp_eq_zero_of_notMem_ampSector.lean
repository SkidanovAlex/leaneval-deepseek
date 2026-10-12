import Mathlib.Tactic.Have
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FockBridge.Count
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `tBamp` vanishes off the amplitude sector

The windowed amplitude `tBamp χ p Φ i x = ∫_z χ(z)e^{−i⟪p,z⟫}·Φ(x_{i←z})dz` samples only the
points `z` with `χ z ≠ 0`, i.e. (by `hχ`) `z ∈ A`; replacing slot `i` of a configuration by such a
point `z` moves the slot-`i` particle *into* the box `A`, so the `A`-occupancy of `x[i↦z]` is the
*shifted* count `if x i ∈ A then n_A(x) else n_A(x)+1`.  Consequently, if `Φ` is supported in the
`A`-sector at count `k`, the amplitude can only be nonzero on the amplitude sector
`ampSector A i k = {x | if x i ∈ A then n_A(x) else n_A(x)+1 = k}`; off that sector the integrand
vanishes identically.

The combinatorial input is the one-sided locality of the occupancy: for `z ∈ B`,

  `n_B(x[i↦z]) = if x i ∈ B then n_B(x) else n_B(x)+1`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal
open Classical

namespace Work.FockBridge

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

variable {N : ℕ}

/-- **One-sided locality of the counting function.**  Replacing slot `i` by a point `z ∈ B` adds
`1` to the `B`-count precisely when the old slot-`i` value was outside `B`. -/
theorem boxCount_update_of_mem (B : Set ℝ³) (x : X N) (i : Fin N) {z : ℝ³} (hz : z ∈ B) :
    boxCount B (Function.update x i z) = boxCount B x + (if x i ∈ B then 0 else 1) := by
  classical
  rw [boxCount_eq_sum_indicator B (Function.update x i z), boxCount_eq_sum_indicator B x]
  rw [← Finset.add_sum_erase Finset.univ
        (fun j => B.indicator (fun _ => (1 : ℝ)) ((Function.update x i z) j))
        (Finset.mem_univ i),
      ← Finset.add_sum_erase Finset.univ (fun j => B.indicator (fun _ => (1 : ℝ)) (x j))
        (Finset.mem_univ i)]
  rw [Function.update_self, Set.indicator_of_mem hz]
  have hsum : (∑ j ∈ Finset.univ.erase i,
        B.indicator (fun _ => (1 : ℝ)) ((Function.update x i z) j))
      = ∑ j ∈ Finset.univ.erase i, B.indicator (fun _ => (1 : ℝ)) (x j) := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_erase] at hj
    rw [Function.update_of_ne hj.1]
  rw [hsum]
  by_cases hxi : x i ∈ B
  · rw [Set.indicator_of_mem hxi, if_pos hxi]; ring
  · rw [Set.indicator_of_notMem hxi, if_neg hxi]; ring

/-- **One-sided locality of the occupancy.**  For `z ∈ B`, the `B`-occupancy of `x[i↦z]` is the
shifted count `if x i ∈ B then n_B(x) else n_B(x)+1` — the very quantity defining `ampSector`. -/
theorem boxOccupancy_update_of_mem (B : Set ℝ³) (x : X N) (i : Fin N) {z : ℝ³} (hz : z ∈ B) :
    boxOccupancy B (Function.update x i z)
      = if x i ∈ B then boxOccupancy B x else boxOccupancy B x + 1 := by
  have h := boxCount_update_of_mem B x i hz
  simp only [boxCount] at h
  have key : ((boxOccupancy B (Function.update x i z) : ℕ) : ℝ)
      = ((if x i ∈ B then boxOccupancy B x else boxOccupancy B x + 1 : ℕ) : ℝ) := by
    rw [h]
    by_cases hxi : x i ∈ B
    · simp [hxi]
    · simp [hxi]
  exact_mod_cast key

/-- **The amplitude vanishes off the amplitude sector.**  If `χ` is supported in `A` and `Φ` is
supported in the `A`-sector of count `k`, then the windowed amplitude `tBamp χ p Φ i` is supported
in `ampSector A i k`: off that sector the integrand is identically zero. -/
theorem tBamp_eq_zero_of_notMem_ampSector {N : ℕ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχ : ∀ z, χ z ≠ 0 → z ∈ A)
    (p : EuclideanSpace ℝ (Fin 3)) {k : ℕ}
    {Φ : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℝ}
    (hΦ : ∀ x : Fin N → EuclideanSpace ℝ (Fin 3),
      x ∉ Work.FockBridge.sectorSet A k → Φ x = 0)
    (i : Fin N) {x : Fin N → EuclideanSpace ℝ (Fin 3)}
    (hx : x ∉ Work.FockBridge.ampSector A i k) :
    Work.SmallBoxTBWord.tBamp χ p Φ i x = 0 := by
  classical
  rw [Work.SmallBoxTBWord.tBamp]
  have hzero : (fun z : ℝ³ => (χ z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
      (Φ (Function.update x i z) : ℂ)) = 0 := by
    funext z
    by_cases hz : χ z = 0
    · rw [hz]; simp
    · have hzA : z ∈ A := hχ z hz
      have hocc := boxOccupancy_update_of_mem A x i hzA
      have hnot : Function.update x i z ∉ sectorSet A k := by
        rw [mem_sectorSet_iff, hocc]
        exact hx
      rw [hΦ _ hnot]; simp
  rw [hzero]
  simp

end Work.FockBridge
