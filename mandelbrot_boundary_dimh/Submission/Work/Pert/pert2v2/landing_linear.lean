import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.pert2v2.tau0_pointwise_bounds
import Submission.Work.Pert.pert2v2.log_linear_bound

namespace Work.Pert.pert2v2

/-- **The `f`-independent landing time `m` with *linear* bounds in `Λ`.**

Linear-witness companion of `Work.Analysis.PertCrux.landing_data_v3` (which uses the much larger
witness `m ≈ Λ ^ 2`).  Here the witness is `m = ⌈Ξ' + 4Λ + MK + 5CW + 20⌉₊`; it satisfies

* `Ξ' + 4Λ + MK + 5CW + 20 ≤ m` and `m ≤ Ξ' + 5Λ + MK + 6CW + 40` (linear in every constant);
* `CW * (1 + log (m+1)) ≤ Λ / 16`: since `m + 1 ≤ 2 (Ξ' + 3Λ + MK + 5CW + 4)` and
  `log 2 ≤ 1`, we have `1 + log (m+1) ≤ 2 (2 + log (Ξ' + 3Λ + MK + 5CW + 4))`, and the
  hypothesis `hΛlog` compares that logarithm against the *linear* scale `Λ`
  (this is `Work.Pert.pert2v2.log_linear_bound`);
* `‖τ₀ (f₀^[m] (φ w))‖ ≤ Ξ' + 6Λ + 2MK + 6CW + 42`, from the triangle inequality with `hW`, `hMK`
  (this is `Work.Pert.pert2v2.tau0_pointwise_bounds`);
* the ball of radius `Λ` around `τ₀ (f₀^[m] (φ w))` lies in the right cone with vertex `Ξ'`: its
  real part alone dominates `Ξ' + 2Λ`, because
  `Re τ₀ (f₀^[m] (φ w)) ≥ m - MK - CW (1 + log (m+1)) ≥ Ξ' + 3Λ + 5CW + 20 - Λ / 16`
  and `5CW + 20 ≥ Λ / 16 - Λ` is immediate from `Λ ≥ 0`, `CW ≥ 0`. -/
theorem landing_linear {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {K : Set ℂ} {Ξ' MK CW Λ : ℝ} (hΞ' : 1 ≤ Ξ') (hMK0 : 0 ≤ MK) (hCW : 0 ≤ CW)
    (hΛ16 : 64 ≤ Λ) (hΛΞ : Ξ' ≤ Λ) (hΛMK : MK ≤ Λ) (hΛCW : CW ≤ Λ)
    (hΛlog : 32 * CW * (2 + Real.log (Ξ' + 3 * Λ + MK + 5 * CW + 4)) ≤ Λ)
    (hMK : ∀ w ∈ K, ‖d.E w‖ ≤ MK)
    (hW : ∀ w ∈ K, ∀ m : ℕ,
      ‖MandelDim.tau0 (f₀^[m] (d.φ w)) - ((m : ℂ) + d.E w)‖
        ≤ CW * (1 + Real.log ((m : ℝ) + 1))) :
    ∃ m : ℕ, Ξ' + 4 * Λ + MK + 5 * CW + 20 ≤ (m : ℝ) ∧
      (m : ℝ) ≤ Ξ' + 5 * Λ + MK + 6 * CW + 40 ∧
      CW * (1 + Real.log ((m : ℝ) + 1)) ≤ Λ / 16 ∧
      (∀ w ∈ K, ‖MandelDim.tau0 (f₀^[m] (d.φ w))‖ ≤ Ξ' + 6 * Λ + 2 * MK + 6 * CW + 42) ∧
      (∀ w ∈ K, ∀ z : ℂ, ‖z - MandelDim.tau0 (f₀^[m] (d.φ w))‖ ≤ Λ →
        Ξ' + 2 * Λ ≤ z.re + |z.im|) := by
  have hΛ0 : 0 ≤ Λ := by linarith
  -- The explicit witness `m = ⌈Ξ' + 4Λ + MK + 5CW + 20⌉₊`.
  obtain ⟨m, hmge, hmlt⟩ : ∃ m : ℕ,
      Ξ' + 4 * Λ + MK + 5 * CW + 20 ≤ (m : ℝ) ∧
      (m : ℝ) < Ξ' + 4 * Λ + MK + 5 * CW + 21 :=
    ⟨⌈Ξ' + 4 * Λ + MK + 5 * CW + 20⌉₊, Nat.le_ceil _,
      by have h := Nat.ceil_lt_add_one
            (show (0:ℝ) ≤ Ξ' + 4 * Λ + MK + 5 * CW + 20 by linarith)
         linarith⟩
  have hmle : (m : ℝ) ≤ Ξ' + 5 * Λ + MK + 6 * CW + 40 := by linarith
  -- The logarithmic hypothesis `hΛlog` bounds the `O(log m)` error by `Λ / 16`.
  have hκ : CW * (1 + Real.log ((m : ℝ) + 1)) ≤ Λ / 16 :=
    log_linear_bound hΞ' hMK0 hCW hΛ16 hΛlog hmlt
  refine ⟨m, hmge, hmle, hκ, ?_, ?_⟩
  · intro w hw
    obtain ⟨h1, _⟩ := tau0_pointwise_bounds d hMK hW hw m
    linarith
  · intro w hw z hz
    obtain ⟨_, h2⟩ := tau0_pointwise_bounds d hMK hW hw m
    have hzre : (MandelDim.tau0 (f₀^[m] (d.φ w))).re - Λ ≤ z.re := by
      have h3 : |z.re - (MandelDim.tau0 (f₀^[m] (d.φ w))).re| ≤ Λ := by
        have h5 := Complex.abs_re_le_norm (z - MandelDim.tau0 (f₀^[m] (d.φ w)))
        have h6 : (z - MandelDim.tau0 (f₀^[m] (d.φ w))).re
            = z.re - (MandelDim.tau0 (f₀^[m] (d.φ w))).re := by simp
        rw [h6] at h5; exact le_trans h5 hz
      linarith [neg_abs_le (z.re - (MandelDim.tau0 (f₀^[m] (d.φ w))).re)]
    have him : (0 : ℝ) ≤ |z.im| := abs_nonneg _
    linarith

end Work.Pert.pert2v2
