/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The fixed-disc potential inside the annulus

If the datum `v` vanishes on the open polydisc `polydisc 0 s`, then on `polydisc 0 r` (with
`r i < s i`) the fixed-disc Cauchy potential `fiberPot R j v` — an integral over the whole disc
`‖w‖ < R` — agrees with the potential `fiberPotAnn j 0 (fiberAnnulus (s j) R) v` written as an
integral over the *annulus* `{w | s j ≤ ‖w‖ ∧ ‖w‖ < R}`.

The reason is elementary: the two integrands are the same (`(w - z j)^{-1}`), and the only
difference between the two domains is the disc `‖w‖ < s j`, where the integrand vanishes: for
`z ∈ polydisc 0 r` and `‖w‖ < s j` the point `z with z j := w` lies in `polydisc 0 s`, so the
datum is `0` there.  This is what makes the derivative estimates for `fiberPot` on `polydisc 0 r`
elementary — the kernel is bounded and smooth on the annulus, which stays away from the pole.
-/
import Mathlib
import Submission.Work.NN.Core.VanishingDefs

namespace Work.NN.Core

theorem fiberPot_eq_fiberPotAnn {n : ℕ} {j : Fin n} {R : ℝ} {r s : Fin n → ℝ}
    (hrs : ∀ i, r i < s i) (hsR : s j < R) {v : (Fin n → ℂ) → ℂ}
    (hv : Work.NN.Core.VanOn s v) (hcont : Continuous v) :
    Set.EqOn (Work.NN.Core.fiberPot R j v)
      (Work.NN.Core.fiberPotAnn j 0 (Work.NN.Core.fiberAnnulus (s j) R) v)
      (Work.CR.Flat.polydisc 0 r) := by
  intro z hz
  rw [Work.NN.Core.fiberPot_apply, Work.NN.Core.fiberPotAnn_apply]
  congr 1
  -- the two integrands coincide: `v / (w - z j) = v * ((w - z j)⁻¹)^(0+1)`
  have hf : (fun w : ℂ => v (Function.update z j w) / (w - z j))
      = fun w : ℂ => v (Function.update z j w) * ((w - z j)⁻¹) ^ (0 + 1) := by
    funext w
    rw [div_eq_mul_inv]
    norm_num
  rw [hf]
  -- rewrite both integrals over `s` as integrals of the indicator of `s`
  rw [← MeasureTheory.integral_indicator (Work.NN.Core.measurableSet_fiberAnnulus (s j) R),
      ← MeasureTheory.integral_indicator measurableSet_ball]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with w
  by_cases hw : w ∈ Metric.ball (0 : ℂ) (s j)
  · -- inside the discarded disc: the integrand vanishes, and `w` is outside the annulus
    rw [Metric.mem_ball, dist_zero_right] at hw
    have hnotann : w ∉ Work.NN.Core.fiberAnnulus (s j) R := by
      rw [Work.NN.Core.mem_fiberAnnulus]
      intro h
      exact absurd h.1 (not_le.mpr hw)
    have hwR : w ∈ Metric.ball (0 : ℂ) R := by
      rw [Metric.mem_ball, dist_zero_right]
      linarith
    have hgz : v (Function.update z j w) = 0 := by
      apply hv
      intro i
      have hmem := Work.NN.Core.mem_polydisc_update hrs hz hw
      rw [Work.CR.Flat.mem_polydisc] at hmem
      simpa only [Pi.zero_apply, sub_zero] using hmem i
    rw [Set.indicator_of_notMem hnotann, Set.indicator_of_mem hwR, hgz]
    simp
  · by_cases hwR : w ∈ Metric.ball (0 : ℂ) R
    · -- inside the fixed disc but outside the discarded one: both indicators agree
      have hann : w ∈ Work.NN.Core.fiberAnnulus (s j) R := by
        rw [Work.NN.Core.fiberAnnulus_eq_ball_diff]
        exact ⟨hwR, hw⟩
      rw [Set.indicator_of_mem hann, Set.indicator_of_mem hwR]
    · -- outside the fixed disc: both indicators vanish
      have hnotann : w ∉ Work.NN.Core.fiberAnnulus (s j) R := by
        rw [Work.NN.Core.fiberAnnulus_eq_ball_diff]
        rintro ⟨h1, _⟩
        exact hwR h1
      rw [Set.indicator_of_notMem hnotann, Set.indicator_of_notMem hwR]

end Work.NN.Core
