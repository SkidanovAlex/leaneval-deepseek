import Mathlib
import Submission.Work.Pert.scale_lattice
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic
import Submission.Work.Interfaces.Fatou
import Submission.Work.Interfaces.Parabolic

/-!
# PERT · the differentiability gate for `τ_f = τC σ α` on the lower gate `Qm ξ₁ α`

`τC σ α w = σ / (1 - exp (-(2πi α w)))` is the universal cover of (A.1.5); its only singularities
are the poles `w ∈ ℤ/α` where the denominator vanishes.

The gate `Qm ξ₁ α = Qreg (ξ₁ - 1/α) (-ξ₁)` is designed to avoid that lattice: `Work.Pert.scale_lattice`
shows that every point of `Qm ξ₁ α` keeps a distance `ξ₁/2` from `ℤ/α` (with `ξ₁ > 0` and
`α ∈ 𝓕₁`, i.e. `|α.im| < α.re`).  Hence

* `exp (-(2πi α w)) ≠ 1` on `Qm ξ₁ α` (otherwise `α w ∈ ℤ`, i.e. `w ∈ ℤ/α`, at distance `0`), and
* consequently `τC σ α` is holomorphic on `Qm ξ₁ α` (a quotient with everywhere-nonzero denominator).
-/

namespace Work.Pert.DiffGate

/-- The gate `Qm ξ₁ α` misses the pole lattice `ℤ/α` of `τ_f`. -/
theorem Qm_no_lattice {ξ₁ : ℝ} {α w : ℂ} (hξ₁ : 0 < ξ₁) (hα : MandelDim.InF1 α)
    (hw : w ∈ Work.Pert.Qm ξ₁ α) : ¬ ∃ m : ℤ, α * w = (m : ℂ) := by
  have hαre : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hα
  have hαne : α ≠ 0 := by
    intro h0
    rw [h0] at hαre
    simp at hαre
  rintro ⟨m, hm⟩
  have h0 : w - (m : ℂ) / α = 0 := by
    rw [sub_eq_zero, eq_div_iff hαne, mul_comm]
    exact hm
  have hlat := (Work.Pert.scale_lattice hξ₁ hα).2 hw m
  rw [h0, norm_zero] at hlat
  linarith

theorem diff_tauC_gate {σ α : ℂ} {ξ₁ : ℝ} (hξ₁ : 0 < ξ₁) (hα : MandelDim.InF1 α) :
    (∀ w ∈ Work.Pert.Qm ξ₁ α, Complex.exp (-(2 * Real.pi * Complex.I * α * w)) ≠ 1) ∧
      DifferentiableOn ℂ (Work.Pert.tauC σ α) (Work.Pert.Qm ξ₁ α) := by
  have hαne : α ≠ 0 := by
    have hαre : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hα
    intro h0
    rw [h0] at hαre
    simp at hαre
  have hnot : ∀ w ∈ Work.Pert.Qm ξ₁ α,
      Complex.exp (-(2 * Real.pi * Complex.I * α * w)) ≠ 1 := by
    intro w hw h
    have hfac : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero
      exact_mod_cast Real.pi_ne_zero
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
    have h4 : (2 * Real.pi * Complex.I) * (-(α * w)) = (2 * Real.pi * Complex.I) * (n : ℂ) := by
      rw [mul_comm (2 * Real.pi * Complex.I) (n : ℂ)]
      calc (2 * Real.pi * Complex.I) * (-(α * w)) = -(2 * Real.pi * Complex.I * α * w) := by ring
        _ = (n : ℂ) * (2 * Real.pi * Complex.I) := hn
    have h5 : -(α * w) = (n : ℂ) := mul_left_cancel₀ hfac h4
    have h6 : α * w = -(n : ℂ) := by linear_combination -h5
    have h0 : w - ((-n : ℤ) : ℂ) / α = 0 := by
      rw [show ((-n : ℤ) : ℂ) = -(n : ℂ) by simp, sub_eq_zero, eq_div_iff hαne, mul_comm]
      exact h6
    have hlat := (Work.Pert.scale_lattice hξ₁ hα).2 hw (-n)
    rw [h0, norm_zero] at hlat
    linarith
  refine ⟨hnot, ?_⟩
  rw [show Work.Pert.tauC σ α =
      fun y => σ / (1 - Complex.exp (-(2 * Real.pi * Complex.I * α * y))) from rfl]
  apply DifferentiableOn.div
  · exact differentiableOn_const σ
  · apply DifferentiableOn.sub
    · exact differentiableOn_const 1
    · fun_prop
  · intro y hy hz
    exact hnot y hy ((sub_eq_zero.mp hz).symm)

end Work.Pert.DiffGate
