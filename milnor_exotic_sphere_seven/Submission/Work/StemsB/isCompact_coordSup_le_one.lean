import Mathlib
import Submission.Work.StemsB.RadialRetraction

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The closed unit ball of the coordinate sup-norm is compact

`Work.StemsB.coordSup n v` is the sup-norm of the coordinates of `v : ℝⁿ`.  This file proves that
its closed unit ball

`{v : EuclideanSpace ℝ (Fin n) | coordSup n v ≤ 1}`

is compact.  The point is that the inequality `coordSup n v ≤ 1` is *exactly* the coordinatewise
inequality `∀ i, |v i| ≤ 1`, so the set is the cube `[-1,1]ⁿ` — compact by Tychonoff — transported
from `Fin n → ℝ` to `EuclideanSpace ℝ (Fin n) = PiLp 2 (fun _ => ℝ)` along the homeomorphism
`PiLp.homeomorph`.
-/

namespace Work.StemsB

noncomputable section

/-- Membership in the closed unit ball of the coordinate sup-norm, coordinatewise. -/
theorem coordSup_le_one_iff (n : ℕ) (v : EuclideanSpace ℝ (Fin n)) :
    coordSup n v ≤ 1 ↔ ∀ i : Fin n, v i ∈ Set.Icc (-1 : ℝ) 1 := by
  have hnn : ∀ x : ℝ, nnnorm x ≤ (1 : NNReal) ↔ x ∈ Set.Icc (-1 : ℝ) 1 := by
    intro x
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, Set.mem_Icc, abs_le, NNReal.coe_one]
  rw [coordSup, Finset.sup_le_iff]
  constructor
  · intro h i
    exact (hnn (v i)).mp (h i (Finset.mem_univ i))
  · intro h i _
    exact (hnn (v i)).mpr (h i)

/-- The closed unit ball of the coordinate sup-norm on `ℝⁿ` is compact. -/
theorem isCompact_coordSup_le_one (n : ℕ) :
    IsCompact {v : EuclideanSpace ℝ (Fin n) | coordSup n v ≤ 1} := by
  have hset : {v : EuclideanSpace ℝ (Fin n) | coordSup n v ≤ 1}
      = (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)) ⁻¹'
          (Set.univ.pi (fun _ : Fin n => Set.Icc (-1 : ℝ) 1)) := by
    ext v
    rw [Set.mem_preimage, Set.mem_univ_pi]
    exact coordSup_le_one_iff n v
  rw [hset]
  exact (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).isCompact_preimage.mpr
    (isCompact_univ_pi fun _ => isCompact_Icc)

end

end Work.StemsB
