/-
# The triangle wave `saw` is `2`-Lipschitz

`saw x = 1/2 - 2 |fract (x + 1/4) - 1/2|` (`Work.FQC.Defs`) is the triangle wave with period
`1`, vanishing at `0` and `1/2`, taking the value `1/2` at `1/4`.  This file rewrites it as a
distance to the lattice `1/4 + ℤ`,

  `saw x = 1/2 - 2 * infDist x (1/4 + ℤ)`,

from which the global Lipschitz estimate `|saw x - saw y| ≤ 2 |x - y|` follows from the
`1`-Lipschitz continuity of the distance function (`Metric.infDist_le_infDist_add_dist`).
This is the estimate that bounds the slope of the MNS twist `ℓ_t`.
-/
import Mathlib
import Submission.Work.FQC.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Set Function Topology
open scoped Topology NNReal

noncomputable section

namespace Work.FQC

/-- The lattice `1/4 + ℤ`, the corner set of the triangle wave. -/
def sawLattice : Set ℝ := Set.range (fun n : ℤ => (1/4 : ℝ) + n)

/-- The triangle wave is `1/2` minus twice the distance to its corner lattice. -/
theorem saw_eq_half_sub_infDist (x : ℝ) : saw x = 1 / 2 - 2 * Metric.infDist x sawLattice := by
  have hmain : |Int.fract (x + 1 / 4) - 1 / 2| = Metric.infDist x sawLattice := by
    rw [sawLattice]
    set S : Set ℝ := Set.range (fun n : ℤ => (1 / 4 : ℝ) + n) with hS
    set f := Int.fract (x + 1 / 4) with hf
    set k : ℤ := ⌊x + 1 / 4⌋ with hk
    have hxf : x + 1 / 4 = f + (k : ℝ) := by rw [hf, hk, Int.fract_add_floor]
    have hx : x - (1 / 4 + (k : ℝ)) = f - 1 / 2 := by linarith [hxf]
    have hf0 : 0 ≤ f := by rw [hf]; exact Int.fract_nonneg _
    have hf1 : f < 1 := by rw [hf]; exact Int.fract_lt_one _
    have hSne : S.Nonempty := ⟨1 / 4 + (0 : ℤ), ⟨0, by norm_num⟩⟩
    have hle : Metric.infDist x S ≤ |f - 1 / 2| :=
      calc Metric.infDist x S ≤ dist x (1 / 4 + (k : ℝ)) := Metric.infDist_le_dist_of_mem ⟨k, rfl⟩
        _ = |f - 1 / 2| := by rw [Real.dist_eq, hx]
    have hge : |f - 1 / 2| ≤ Metric.infDist x S := by
      rw [Metric.le_infDist hSne]
      rintro y ⟨n, rfl⟩
      rw [Real.dist_eq]
      by_cases h : n = k
      · rw [h, ← hx, hx]
      · have hkn : 1 ≤ |(k : ℝ) - (n : ℝ)| := by
          rw [← Int.cast_sub, ← Int.cast_abs]
          exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr (Ne.symm h))
        have hlt : |f - 1 / 2| ≤ 1 / 2 := by
          rw [abs_le]; constructor <;> linarith
        have h2 : |(k : ℝ) - (n : ℝ)| - |f - 1 / 2| ≤ |((k : ℝ) - (n : ℝ)) + (f - 1 / 2)| :=
          abs_sub_abs_le_abs_add _ _
        have h3 : x - (1 / 4 + (n : ℝ)) = ((k : ℝ) - (n : ℝ)) + (f - 1 / 2) := by
          rw [← hx]; ring
        rw [h3]
        linarith
    exact le_antisymm hge hle
  rw [saw_apply, hmain]

/-- `saw` is `2`-Lipschitz: its slope is `± 2` between corners. -/
theorem saw_lipschitz (x y : ℝ) : |saw x - saw y| ≤ 2 * |x - y| := by
  have h1 : Metric.infDist x sawLattice ≤ Metric.infDist y sawLattice + dist x y :=
    Metric.infDist_le_infDist_add_dist
  have h2 : Metric.infDist y sawLattice ≤ Metric.infDist x sawLattice + dist y x :=
    Metric.infDist_le_infDist_add_dist
  rw [Real.dist_eq] at h1 h2
  have h3 : |Metric.infDist x sawLattice - Metric.infDist y sawLattice| ≤ |x - y| := by
    rw [abs_sub_le_iff]
    exact ⟨by linarith, by linarith [abs_sub_comm x y]⟩
  rw [saw_eq_half_sub_infDist x, saw_eq_half_sub_infDist y]
  calc |1 / 2 - 2 * Metric.infDist x sawLattice - (1 / 2 - 2 * Metric.infDist y sawLattice)|
      = 2 * |Metric.infDist x sawLattice - Metric.infDist y sawLattice| := by
        rw [show (1 / 2 - 2 * Metric.infDist x sawLattice
              - (1 / 2 - 2 * Metric.infDist y sawLattice))
            = -(2 * (Metric.infDist x sawLattice - Metric.infDist y sawLattice)) by ring,
          abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 2 * |x - y| := by linarith

/-- The Lipschitz form of `saw_lipschitz`. -/
theorem lipschitzWith_saw : LipschitzWith (2 : ℝ≥0) saw := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [Real.dist_eq, Real.dist_eq, NNReal.coe_ofNat]
  exact saw_lipschitz x y

end Work.FQC

end
