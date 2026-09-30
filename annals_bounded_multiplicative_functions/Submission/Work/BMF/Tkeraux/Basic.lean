import Mathlib
import Submission.Work.BMF.vkford51_defs
import Submission.Work.BMF.kern_hasSum
import Submission.Work.BMF.kern_summable
import Submission.Work.BMF.TentDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The integration kernel `kern` for every `K` (including `K = 0`)

The kernel `kern K c = (π²K/2) · tentCoeff (1/(2K)) c` of `Work.BMF.vkford51_defs` is the
Fourier coefficient sequence of the tent of width `1/(2K)`.  `Work.BMF.kern_hasSum` and
`Work.BMF.kern_summable` record this for `K ≥ 1`; here we record the degenerate case `K = 0`
(`kern 0` is the zero sequence, and the companion tent factor is killed by the prefactor `K`),
so that both statements hold for all `K : ℕ` without a side condition.  This is what
`Work.BMF.Tker_eq` needs, since the scales `r M₁^{j+1}` occurring there are not assumed to be
non-zero.
-/

namespace Work.BMF

open scoped BigOperators

noncomputable section

/-- `kern 0` vanishes identically (the prefactor `π²·0/2` is zero). -/
lemma kern_zero (c : ℤ) : kern 0 c = 0 := by
  simp [kern]

/-- The additive character has norm one. -/
lemma eZ_norm (t : ℝ) : ‖eZ t‖ = 1 := by
  unfold eZ
  rw [show (2 : ℂ) * ↑Real.pi * Complex.I * ↑t = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- **Fourier series of the tent, for every `K`.**  For all `K : ℕ` and `θ : ℝ`,
`∑_c kern K c · e(cθ) = (π²K/2) · tent (1/(2K)) θ`. -/
theorem kern_hasSum_all (K : ℕ) (θ : ℝ) :
    HasSum (fun c : ℤ => (kern K c : ℂ) * eZ ((c : ℝ) * θ))
      (((Real.pi ^ 2 * (K : ℝ) / 2) * tent (1 / (2 * (K : ℝ))) θ : ℝ) : ℂ) := by
  rcases K with _ | K
  · have h0 : (fun c : ℤ => (kern 0 c : ℂ) * eZ ((c : ℝ) * θ)) = fun _ => (0 : ℂ) := by
      funext c; rw [kern_zero]; simp
    rw [h0]
    have hz : ((Real.pi ^ 2 * ((0 : ℕ) : ℝ) / 2) * tent (1 / (2 * ((0 : ℕ) : ℝ))) θ : ℝ) = 0 := by
      norm_num
    rw [hz]
    exact hasSum_zero
  · exact kern_hasSum (K + 1) (Nat.succ_le_succ (Nat.zero_le K)) θ

/-- The kernel is absolutely summable for every `K`, including `K = 0`. -/
theorem kern_summable_norm_all (K : ℕ) : Summable (fun c : ℤ => ‖kern K c‖) := by
  rcases K with _ | K
  · have h0 : (fun c : ℤ => ‖kern 0 c‖) = fun _ => (0 : ℝ) := by
      funext c; rw [kern_zero]; simp
    rw [h0]; exact summable_zero
  · exact (kern_summable (K + 1) (Nat.succ_le_succ (Nat.zero_le K))).norm

end

end Work.BMF
