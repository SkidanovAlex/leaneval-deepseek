import Mathlib
import Submission.Work.BW.DefsAC

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Every value of `φ ∘ p` is at most `exp (lnp φ p)`, where `lnp φ p = log (sup_i ‖φ (p i)‖)` (BW's `ln(p) = log max_λ |p(λ)|`). Needs `p ≠ 0` so that the supremum is positive. -/
theorem est14_phibound {K : Type*} [Field K] {ι : Type*} [Fintype ι] (φ : K →+* ℂ) (p : ι → K)
    (hp0 : p ≠ 0) (i : ι) : ‖φ (p i)‖ ≤ Real.exp (lnp φ p) := by
  -- the supremum of the norms is bounded (finitely many indices)
  have hbdd : BddAbove (Set.range fun i => ‖φ (p i)‖) := (Set.finite_range _).bddAbove
  have hle : ∀ j, ‖φ (p j)‖ ≤ ⨆ i, ‖φ (p i)‖ := fun j => le_ciSup hbdd j
  -- `p` is nonzero, so some value `p j` is nonzero, and `φ` is injective on the field `K`
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hp0
  have hjne : φ (p j) ≠ 0 :=
    fun hc => hj (RingHom.injective φ (hc.trans (map_zero φ).symm))
  -- hence the supremum is strictly positive and `exp (log ·)` inverts it
  have hpos : 0 < ⨆ i, ‖φ (p i)‖ :=
    lt_of_lt_of_le (norm_pos_iff.mpr hjne) (hle j)
  rw [lnp, Real.exp_log hpos]
  exact hle i

end Work.BW
