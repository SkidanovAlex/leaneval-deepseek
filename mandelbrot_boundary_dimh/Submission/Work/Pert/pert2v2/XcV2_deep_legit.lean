import Mathlib
import Submission.Work.Pert.Ksub2.Xcurve_bounds
import Submission.Work.Parab.Setup
import Submission.Work.Pert.nearTranslation_F0
import Submission.Work.Pert.pert2v2.deep_arith
import Submission.Work.Pert.pert2v2.mem_Qreg_of_deep_close

/-!
# `Work.Pert.pert2v2.XcV2_deep_legit`

The curve `u ↦ Xc d u = τ₀ (φ₀ u)` of a `§4.1`-datum enters the **lower cone**
`Qreg none (some (-Ξ')) = {z : Re z + Ξ' < |Im z|}` for `u` deep in the left half-plane.

The asymptotic `τ₀ (φ₀ w) = w + a log(-w) + b + o(1)` on the repelling sector `QLeft ξ₀`
(`d.φ_asymp`), used with the fixed accuracy `1` at every `u` with `Re u < -N`, controls the curve
by `z := Xc d u` with `‖z - (u + A)‖ < 1`, `A := a log(-u) + b`.  Writing `t := -u.re`,
`s := |u.im|` and `c := ‖A‖ + 1`, the two elementary consequences

* `z.re ≤ -t + c`      (real parts are `1`-Lipschitz for `‖·‖`),
* `|z.im| ≥ s - c`     (reverse triangle inequality, `‖A‖ = c - 1`),

turn the cone condition `z.re + Ξ' < |z.im|` into the *single* scalar inequality
`2c + Ξ' < t + s` (`Work.Pert.pert2v2.mem_Qreg_of_deep_close`).  Since
`c ≤ ‖a‖ log ‖u‖ + (‖a‖ π + ‖b‖ + 1) ≤ ‖a‖ log(t + s + 1) + (‖a‖ π + ‖b‖ + 1)` and
`log (t + s + 1) = o(t + s)`, the scalar inequality holds for all `t` past a threshold
`Work.Pert.pert2v2.deep_arith` — no case distinction on which of `t`, `s` dominates is needed,
because the `max (s - c) 0` in the scalar criterion absorbs the regime where `s` is small.
-/

namespace Work.Pert.pert2v2

open Complex

theorem XcV2_deep_legit {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀) {Ξ' : ℝ}
    (hΞ' : 0 < Ξ') :
    ∃ N : ℝ, ∀ u : ℂ, u.re < -N →
      Work.Pert.Xc d u ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ))) := by
  obtain ⟨a, b, hasym⟩ := d.φ_asymp
  obtain ⟨R_A, hR_A⟩ := hasym 1 one_pos
  obtain ⟨N₁, hN₁pos, hN₁⟩ :=
    deep_arith (K := ‖a‖) (L := ‖a‖ * Real.pi + ‖b‖ + 1) (Ξ := Ξ') (norm_nonneg a)
  refine ⟨max N₁ (max (d.ξ₀ + 1) (max R_A 1)), ?_⟩
  intro u hu
  set M : ℝ := max N₁ (max (d.ξ₀ + 1) (max R_A 1)) with hM
  have hN1 : N₁ ≤ M := by rw [hM]; exact le_max_left _ _
  have hξM : d.ξ₀ + 1 ≤ M := by
    rw [hM]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hRAM : R_A ≤ M := by
    rw [hM]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have h1M : (1 : ℝ) ≤ M := by
    rw [hM]
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hneg : u.re < 0 := by linarith
  have hQ : u ∈ MandelDim.QLeft d.ξ₀ := by
    refine Work.Parab.halfplane_subset_QLeft d.ξ₀ ?_
    show u.re < -d.ξ₀
    linarith
  have hRA : R_A < ‖u‖ := by
    have h1 : R_A < -u.re := by linarith
    have h2 : -u.re = |u.re| := (abs_of_neg hneg).symm
    have h3 : |u.re| ≤ ‖u‖ := Complex.abs_re_le_norm u
    linarith
  have hclose := hR_A u hQ hRA
  have hnorm_ge : M ≤ ‖u‖ := by
    have h1 : |u.re| ≤ ‖u‖ := Complex.abs_re_le_norm u
    have h2 : |u.re| = -u.re := abs_of_neg hneg
    linarith
  have hlogu1 : (1 : ℝ) ≤ ‖u‖ := by linarith
  have hlogu0 : 0 ≤ Real.log ‖u‖ := Real.log_nonneg hlogu1
  have hclog : ‖Complex.log (-u)‖ ≤ Real.log ‖u‖ + Real.pi := by
    have h := Work.Pert.norm_clog_le (-u)
    rw [norm_neg, abs_of_nonneg hlogu0] at h
    exact h
  have hnorm_le : ‖u‖ ≤ -u.re + |u.im| + 1 := by
    have h1 : ‖u‖ ≤ |u.re| + |u.im| := Complex.norm_le_abs_re_add_abs_im u
    have h2 : |u.re| = -u.re := abs_of_neg hneg
    linarith
  have hlogle : Real.log ‖u‖ ≤ Real.log (-u.re + |u.im| + 1) :=
    Real.log_le_log (lt_of_lt_of_le zero_lt_one hlogu1) hnorm_le
  set c : ℝ := ‖a * Complex.log (-u) + b‖ + 1 with hc
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hAb : ‖a * Complex.log (-u) + b‖ ≤
      ‖a‖ * Real.log (-u.re + |u.im| + 1) + (‖a‖ * Real.pi + ‖b‖) := by
    have h1 : ‖a * Complex.log (-u) + b‖ ≤ ‖a‖ * ‖Complex.log (-u)‖ + ‖b‖ := by
      calc ‖a * Complex.log (-u) + b‖ ≤ ‖a * Complex.log (-u)‖ + ‖b‖ := norm_add_le _ _
        _ = ‖a‖ * ‖Complex.log (-u)‖ + ‖b‖ := by rw [norm_mul]
    have h2 : ‖a‖ * ‖Complex.log (-u)‖ ≤ ‖a‖ * (Real.log ‖u‖ + Real.pi) :=
      mul_le_mul_of_nonneg_left hclog (norm_nonneg a)
    have h3 : ‖a‖ * Real.log ‖u‖ ≤ ‖a‖ * Real.log (-u.re + |u.im| + 1) :=
      mul_le_mul_of_nonneg_left hlogle (norm_nonneg a)
    linarith
  have hc_le : c ≤ ‖a‖ * Real.log (-u.re + |u.im| + 1) + (‖a‖ * Real.pi + ‖b‖ + 1) := by
    rw [hc]; linarith
  have harith : 2 * c + Ξ' < -u.re + |u.im| :=
    hN₁ (-u.re) (|u.im|) c (by linarith) (abs_nonneg _) hc0 hc_le
  have hclose' : ‖Work.Pert.Xc d u - (u + (a * Complex.log (-u) + b))‖ < 1 := by
    simpa only [Work.Pert.Xc, add_assoc] using hclose
  have hAc : ‖a * Complex.log (-u) + b‖ + 1 ≤ c := by rw [hc]
  exact mem_Qreg_of_deep_close (z := Work.Pert.Xc d u) (u := u)
    (A := a * Complex.log (-u) + b) (Ξ := Ξ') (c := c) hclose' hAc harith

end Work.Pert.pert2v2
