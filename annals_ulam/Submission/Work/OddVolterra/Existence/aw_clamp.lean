import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Existence.aw_data

/-!
# The clamped localised `Θ`-datum of the anchor window

The engine `Work.VolterraLong.volterra_long_exists_eps` needs a `Θ`-datum which is *continuous* on
`[a,b]² × St`, and the manifest datum `awTheta` is continuous but on `σ < s` it is the manifest
value `ThetaM n h s σ z`, whose dependence on `h` is a jet-polynomial (the manifest kernel
`KvecM` does not agree with the paper's `Kvec` for `a > σ`).  The `σ`-integral of the system,
however, only ever runs over `σ ∈ [s,b]`, so on `σ ≤ s` we are free to replace the datum by its
diagonal value `ThetaM n h s s z` — which is what the limit of the triangle values is, and which is
what `Work.OddVolterra.Window.WindowDefs.thetac` does.

`awThetaC` does this, and additionally uses on the branch `σ ≤ s` the *state cutoff centred at
`baseState s`* (rather than at `baseState σ`): this keeps the `z`-region on which the datum is
non-zero inside the ball of radius `2/5` around `baseState (max s σ)`, which is exactly the region
on which the manifest kernel is controlled (`aw_thetaM_tri_close`).  Continuity in `(s,σ,z)` is
unaffected: at `σ = s` both branches give `awCz (z - baseState s) • ThetaM n h s s z`.
-/

namespace Work.OddVolterra.Existence

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

open Work.OddVolterra

/-- The clamped localised `Θ`-datum: on the triangle `s < σ` the manifest localised kernel (with
the state cutoff centred at `baseState σ`), and on `σ ≤ s` its diagonal value, with the state
cutoff centred at `baseState s`. -/
def awThetaC (n : ℕ) (h : ℝ → ℝ) (s σ : ℝ) (z : St) : St :=
  ((awCs : ℝ → ℝ) s * (awCs : ℝ → ℝ) σ) •
    (if s < σ then (awCz : St → ℝ) (z - baseState σ) • KernelExt.ThetaM n h s σ z
     else (awCz : St → ℝ) (z - baseState s) • KernelExt.ThetaM n h s s z)

/-- On the triangle the clamped datum is the localised manifest datum. -/
lemma awThetaC_eq_awTheta {n : ℕ} {h : ℝ → ℝ} {s σ : ℝ} (z : St) (hsσ : s ≤ σ) :
    awThetaC n h s σ z = awTheta n h s σ z := by
  rcases eq_or_lt_of_le hsσ with rfl | hlt
  · rw [awThetaC, awTheta, awChiT, if_neg (lt_irrefl s), smul_smul]
  · rw [awThetaC, awTheta, awChiT, if_pos hlt, smul_smul]

/-- Evaluation of the clamped datum on the branch `σ ≤ s`. -/
lemma awThetaC_eq_of_le {n : ℕ} {h : ℝ → ℝ} {s σ : ℝ} (z : St) (hσs : σ ≤ s) :
    awThetaC n h s σ z =
      ((awCs : ℝ → ℝ) s * (awCs : ℝ → ℝ) σ) •
        ((awCz : St → ℝ) (z - baseState s) • KernelExt.ThetaM n h s s z) := by
  rw [awThetaC, if_neg (not_lt.mpr hσs)]

/-- The clamped datum vanishes when the state cutoff of the relevant branch vanishes. -/
lemma awThetaC_eq_zero {n : ℕ} {h : ℝ → ℝ} {s σ : ℝ} {z : St}
    (hz : 2 / 5 ≤ ‖z - baseState (max s σ)‖) : awThetaC n h s σ z = 0 := by
  rw [awThetaC]
  by_cases hlt : s < σ
  · rw [if_pos hlt, awCz_eq_zero (by rwa [max_eq_right hlt.le] at hz), zero_smul, smul_zero]
  · rw [if_neg hlt, awCz_eq_zero (by rwa [max_eq_left (not_lt.mp hlt)] at hz), zero_smul,
      smul_zero]

/-- **The bridge to the manifest triangle estimate.**  The difference of the clamped data is
dominated by the difference of the (un-cut-off) manifest kernels at the slope `max s σ`, which is
`σ` on the triangle and `s` on the diagonal branch. -/
lemma norm_awThetaC_sub_le (n : ℕ) (h : ℝ → ℝ) (s σ : ℝ) (z : St) :
    ‖awThetaC n h s σ z - awThetaC n 0 s σ z‖ ≤
      ‖KernelExt.ThetaM n h s (max s σ) z - KernelExt.ThetaM n 0 s (max s σ) z‖ := by
  have key : ∀ (c d : ℝ) (X Y : St), 0 ≤ c → c ≤ 1 → 0 ≤ d → d ≤ 1 →
      ‖c • (d • X) - c • (d • Y)‖ ≤ ‖X - Y‖ := by
    intro c d X Y hc0 hc1 hd0 hd1
    have heq : c • (d • X) - c • (d • Y) = (c * d) • (X - Y) := by
      rw [smul_smul c d X, smul_smul c d Y, smul_sub]
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc0 hd0)]
    exact mul_le_of_le_one_left (norm_nonneg _) (by nlinarith)
  rw [awThetaC, awThetaC]
  by_cases hlt : s < σ
  · rw [if_pos hlt, if_pos hlt, max_eq_right hlt.le]
    exact key _ _ _ _ (mul_nonneg (awCs_nonneg s) (awCs_nonneg σ))
      (by nlinarith [awCs_nonneg s, awCs_le_one s, awCs_nonneg σ, awCs_le_one σ])
      (awCz_nonneg _) (awCz_le_one _)
  · rw [if_neg hlt, if_neg hlt, max_eq_left (not_lt.mp hlt)]
    exact key _ _ _ _ (mul_nonneg (awCs_nonneg s) (awCs_nonneg σ))
      (by nlinarith [awCs_nonneg s, awCs_le_one s, awCs_nonneg σ, awCs_le_one σ])
      (awCz_nonneg _) (awCz_le_one _)

end

end Work.OddVolterra.Existence
