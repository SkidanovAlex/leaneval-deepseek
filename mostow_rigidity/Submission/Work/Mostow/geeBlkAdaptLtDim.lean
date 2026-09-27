import Mathlib
import Submission.Work.Mostow.geodDeps

/-!
# `Work.Mostow.geeBlkAdaptLtDim`

If a linear isometry `S` of `E m` (the chart of hyperbolic `m`-space, here
`E m = EuclideanSpace ℝ (Fin m)`) has nonzero `rotN` (i.e. is not the identity) and, after
conjugation by some `PS`, is the "value split" block map `Work.Mostow.vblk r hr RS` (identity on
the first `r` coordinates, `RS` on the remaining `m - r`), then necessarily `r < m`.

Indeed, for `r = m` the map `vblk m _ RS` is the identity (every `i : Fin m` satisfies
`i.val < m`), so the conclusion `S = PS.symm * vblk m _ RS * PS = 1` forces `rotN S = 0`,
contradicting `0 < rotN S`.  The remaining case `r < m` is the conclusion itself.
-/

namespace Work.Mostow

theorem geeBlkAdaptLtDim (m r : ℕ) (hr : r ≤ m) (S : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
    (RS : Submission.Mostow.E (m - r) ≃ₗᵢ[ℝ] Submission.Mostow.E (m - r))
    (PS : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m)
    (hPS : ∀ u : Submission.Mostow.E m, PS (S (PS.symm u)) = Work.Mostow.vblk r hr RS u)
    (hS : 0 < Submission.Mostow.rotN S) : r < m := by
  rcases Nat.lt_or_ge r m with h | h
  · exact h
  · exfalso
    have hrm : r = m := le_antisymm hr h
    -- for `r = m` the block map `vblk r hr RS` is the identity
    have hv : ∀ u : Submission.Mostow.E m, Work.Mostow.vblk r hr RS u = u := by
      intro u
      apply WithLp.ofLp_injective 2
      funext i
      exact Work.Mostow.vblk_ofLp_of_lt r hr RS u i (Nat.lt_of_lt_of_eq i.isLt hrm.symm)
    -- hence `PS * S * PS.symm = 1`, i.e. `S = 1`
    have hSid : S = 1 := by
      apply LinearIsometryEquiv.ext
      intro v
      have h1 : PS (S v) = PS v := by
        have h2 := hPS (PS v)
        rw [LinearIsometryEquiv.symm_apply_apply] at h2
        rw [hv (PS v)] at h2
        exact h2
      exact PS.injective h1
    have hrot : Submission.Mostow.rotN S = 0 := by
      rw [hSid]
      have h1 : ((1 : Submission.Mostow.E m ≃ₗᵢ[ℝ] Submission.Mostow.E m).toLinearIsometry.toContinuousLinearMap :
          Submission.Mostow.E m →L[ℝ] Submission.Mostow.E m)
          = ContinuousLinearMap.id ℝ (Submission.Mostow.E m) := by
        ext x; simp
      simp [Submission.Mostow.rotN, h1]
    linarith

end Work.Mostow
