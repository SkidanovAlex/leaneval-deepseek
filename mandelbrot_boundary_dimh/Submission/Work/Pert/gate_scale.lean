import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.gate
import Submission.Work.Pert.gate_derivF
import Submission.Work.Pert.scale_cauchy
import Submission.Work.Pert.scale_tau
import Submission.Work.Pert.scale_lattice

/-!
# PERT · `Work.Pert.gate_scale`: Shishikura (A.1.7)(ii) with a *scale-dependent* gate

`Work.Pert.gate` proves the `1/32` near-translation form of (A.1.7)(ii) for perturbations whose
Cauchy data are controlled on a ball of radius `ρ ≥ 1`, with the *fixed* gate `ξ₁ = 10^6`,
`ε₀ = 10^{-6}`.  The PERT assembly needs the same statement when only `ρ ≥ ρmin` is known for an
arbitrary (possibly very small) `ρmin > 0`: the gate then has to grow with `1/ρmin`, because all
the estimates are evaluated at `τ_f(w) = σ/(1 - e^{-2πiαw})`, whose size is controlled by the
lattice gap alone, while the Cauchy bound for `u'` at `τ` is of size `1/ρ`.

Concretely, for `m := min ρmin 1` the choice `ξ₁ = 10^6/m`, `ε₀ = m/10^6` works:

* `‖τ_f(w)‖ ≤ 16π m / 10^6` for the lattice gap `ξ₁ = 10^6/m` and `‖α‖ ≤ m/10^6`
  (`Work.Pert.scale_tau`), hence `τ` lies in `ball 0 (m/10^4) ⊆ ball 0 ρ`;
* `‖u'‖ ≤ 8/m` on `ball 0 (m/2)` and `‖u 0 - u τ‖ ≤ (8/m)‖τ‖` (`Work.Pert.scale_cauchy`);
* the key numeric combination is `(8/m + 4)·‖τ‖ ≤ 12/10^4 = 3/2500`, which decays exactly as
  needed to keep both errors below `1/32` (the factor `(8/m + 4)` from `‖u 0 - u τ‖` and
  `‖u 0 τ u τ‖` cancels against the `m` from the `τ`-bound and the `1/(2π‖α‖)` from the logarithm).

Everything else is the same computation as in `Work.Pert.gate` (the `E`-decomposition
`1 - s = A(1+E)` of `1 - sfun`, the principal-branch logarithm, and the derivative formula
`Work.Pert.gate_derivF`). -/

namespace Work.Pert

open MandelDim Complex

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

/-! ### elementary bounds -/

/-- `x / c ≤ 1 / c` for `x ≤ 1`, `c > 0`. -/
private lemma div_const_le_of_le_one {x c : ℝ} (hc : 0 < c) (hx : x ≤ 1) : x / c ≤ 1 / c := by
  rw [div_le_div_iff_of_pos_right hc]
  exact hx

/-- `‖2πiα‖ = 2π‖α‖`. -/
private lemma norm_two_pi_I_mul_s (α : ℂ) : ‖2 * Real.pi * I * α‖ = 2 * Real.pi * ‖α‖ := by
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]

/-- `‖σ‖ ≤ 8π‖α‖` from the normalisation `1 - σ u 0 = exp(2πiα)` and `1/2 ≤ ‖u 0‖`. -/
private lemma sigma_le_s {u : ℂ → ℂ} {σ α : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hub : ∀ z ∈ Metric.ball (0 : ℂ) ρ, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * I * α))
    (hαs : ‖α‖ ≤ 1 / 10 ^ 6) :
    ‖σ‖ ≤ 8 * Real.pi * ‖α‖ := by
  have hu0 : 1 / 2 ≤ ‖u 0‖ := (hub 0 (by simpa [Metric.mem_ball] using hρ)).1
  have hσu : σ * u 0 = 1 - Complex.exp (2 * Real.pi * I * α) := by linear_combination -hnorm
  have h1 : ‖σ‖ * ‖u 0‖ = ‖1 - Complex.exp (2 * Real.pi * I * α)‖ := by
    rw [← norm_mul, hσu]
  have h2 : ‖1 - Complex.exp (2 * Real.pi * I * α)‖
      = ‖Complex.exp (2 * Real.pi * I * α) - 1‖ := by
    rw [← norm_neg]; congr 1; ring
  have h3 : ‖2 * Real.pi * I * α‖ ≤ 1 := by
    rw [norm_two_pi_I_mul_s α]
    have hp : Real.pi * ‖α‖ ≤ 4 * (1 / 10 ^ 6 : ℝ) :=
      mul_le_mul (le_of_lt Real.pi_lt_four) hαs (norm_nonneg α) (by norm_num)
    nlinarith
  have h4 : ‖Complex.exp (2 * Real.pi * I * α) - 1‖ ≤ 2 * ‖2 * Real.pi * I * α‖ :=
    Complex.norm_exp_sub_one_le h3
  have hbound : ‖σ‖ * ‖u 0‖ ≤ 4 * Real.pi * ‖α‖ := by
    rw [h1, h2]
    calc ‖Complex.exp (2 * Real.pi * I * α) - 1‖ ≤ 2 * ‖2 * Real.pi * I * α‖ := h4
      _ = 2 * (2 * Real.pi * ‖α‖) := by rw [norm_two_pi_I_mul_s α]
      _ = 4 * Real.pi * ‖α‖ := by ring
  have hhalf : ‖σ‖ * (1 / 2) ≤ ‖σ‖ * ‖u 0‖ :=
    mul_le_mul_of_nonneg_left hu0 (norm_nonneg σ)
  nlinarith [hbound, hhalf, norm_nonneg σ, norm_nonneg α]

/-- `exp (2πiα) ≠ 1` for `0 < ‖α‖ ≤ 10^{-6}`. -/
private lemma exp_two_pi_I_ne_one_s {α : ℂ} (hαne : α ≠ 0)
    (hαs : ‖α‖ ≤ 1 / 10 ^ 6) : Complex.exp (2 * Real.pi * I * α) ≠ 1 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have h2 : α = (n : ℂ) := by
    have hfac : (2 * Real.pi * I : ℂ) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero
      exact_mod_cast Real.pi_ne_zero
    refine mul_left_cancel₀ hfac ?_
    rw [hn]; ring
  rcases eq_or_ne n 0 with h0 | h0
  · rw [h0] at h2; simp at h2; exact hαne h2
  · have hge : (1 : ℝ) ≤ ‖α‖ := by
      rw [h2, Complex.norm_intCast]
      exact_mod_cast Int.one_le_abs h0
    linarith

/-! ### the `ρmin`-parameterised pointwise estimate -/

private theorem gate_point_scale {u : ℂ → ℂ} {σ α : ℂ} {ρ ρmin : ℝ} {w : ℂ}
    (hρmin : 0 < ρmin) (hρmin1 : ρmin ≤ 1) (hρ : ρmin ≤ ρ)
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) ρ))
    (hub : ∀ z ∈ Metric.ball (0 : ℂ) ρ, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * I * α))
    (hσs : ‖σ‖ ≤ ρmin / 10 ^ 6) (hαs : ‖α‖ ≤ ρmin / 10 ^ 6)
    (hαne : α ≠ 0) (hinf : MandelDim.InF1 α)
    (hlat : ∀ k : ℤ, (10 ^ 6 / ρmin) / 2 ≤ ‖w - (k : ℂ) / α‖) :
    DifferentiableAt ℂ (liftF u σ α) w ∧ ‖liftF u σ α w - (w + 1)‖ ≤ 1 / 32 ∧
      ‖deriv (liftF u σ α) w - 1‖ ≤ 1 / 32 := by
  have hρ0 : (0 : ℝ) < ρ := lt_of_lt_of_le hρmin hρ
  have hαs1 : ‖α‖ ≤ 1 / 10 ^ 6 := le_trans hαs (div_const_le_of_le_one (by norm_num) hρmin1)
  have hαpos : 0 < ‖α‖ := norm_pos_iff.mpr hαne
  have hαre : 0 < α.re := by
    have h := hinf; simp only [MandelDim.InF1] at h
    have := abs_nonneg α.im; linarith
  have hσ8 : ‖σ‖ ≤ 8 * Real.pi * ‖α‖ := sigma_le_s hρ0 hub hnorm hαs1
  have h0mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := by simpa [Metric.mem_ball] using hρ0
  have hu0b : 1 / 2 ≤ ‖u 0‖ ∧ ‖u 0‖ ≤ 2 := hub 0 h0mem
  have hA1 : Complex.exp (2 * Real.pi * I * α) ≠ 1 := exp_two_pi_I_ne_one_s hαne hαs1
  have hσne : σ ≠ 0 := by
    intro h0; exact hA1 (by rw [← hnorm, h0]; ring)
  -- ## the point `τ = τ_f w`
  set τ : ℂ := σ / (1 - Complex.exp (-(2 * Real.pi * I * α * w))) with hτ
  have hτc : tauC σ α w = τ := by rw [tauC, hτ]
  have htz := scale_tau (σ := σ) (α := α) (ρmin := ρmin) (w := w) hρmin hσ8 hαs hαne hinf hlat
  have hζne : 1 - Complex.exp (-(2 * Real.pi * I * α * w)) ≠ 0 := htz.1
  have hτb : ‖τ‖ ≤ 16 * Real.pi * ρmin / 10 ^ 6 := by
    rw [← hτc]; exact htz.2
  have hτb2 : ‖τ‖ ≤ ρmin / 10 ^ 4 := by
    have hpile : Real.pi ≤ 3.1416 := le_of_lt Real.pi_lt_d4
    have h1 : 16 * Real.pi * ρmin / 10 ^ 6 ≤ ρmin / 10 ^ 4 := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 10 ^ 6)]
      have h2 : ρmin / 10 ^ 4 * 10 ^ 6 = 100 * ρmin := by ring
      rw [h2]
      nlinarith [hpile, hρmin, le_of_lt hρmin]
    linarith [hτb, h1]
  have hτρ : τ ∈ Metric.ball (0 : ℂ) ρ := by
    rw [Metric.mem_ball, dist_zero_right]
    have h1 : ρmin / 10 ^ 4 < ρmin := by nlinarith [hρmin]
    linarith [hτb2, h1, hρ]
  have huτ : DifferentiableAt ℂ u τ := hu.differentiableAt (Metric.isOpen_ball.mem_nhds hτρ)
  have huτb : 1 / 2 ≤ ‖u τ‖ ∧ ‖u τ‖ ≤ 2 := hub τ hτρ
  have hτ2 : ‖τ‖ ≤ ρmin / 2 := by nlinarith [hτb2, hρmin]
  have hcauchy := scale_cauchy hρmin hρ hu (fun z hz => (hub z hz).2)
  have hderiv_le : ∀ z : ℂ, ‖z‖ ≤ ρmin / 2 → ‖deriv u z‖ ≤ 8 / ρmin := hcauchy.1
  have hmvt : ‖u 0 - u τ‖ ≤ (8 / ρmin) * ‖τ‖ := hcauchy.2 τ hτ2
  -- ## the key numeric combination
  have hkey : (8 / ρmin + 4) * ‖τ‖ ≤ 3 / 2500 := by
    have h1 : 8 / ρmin * ‖τ‖ = 8 * (‖τ‖ / ρmin) := by ring
    have h2 : ‖τ‖ / ρmin ≤ (ρmin / 10 ^ 4) / ρmin :=
      div_le_div_of_nonneg_right hτb2 (le_of_lt hρmin)
    have h3 : (ρmin / 10 ^ 4) / ρmin = 1 / 10 ^ 4 := by
      field_simp
    have h4 : 8 / ρmin * ‖τ‖ ≤ 8 / 10 ^ 4 := by
      rw [h1]
      calc 8 * (‖τ‖ / ρmin) ≤ 8 * ((ρmin / 10 ^ 4) / ρmin) := by linarith
        _ = 8 / 10 ^ 4 := by rw [h3]; ring
    have h5 : 4 * ‖τ‖ ≤ 4 / 10 ^ 4 := by
      have h6 : ρmin / 10 ^ 4 ≤ 1 / 10 ^ 4 := div_const_le_of_le_one (by norm_num) hρmin1
      nlinarith [hτb2, h6]
    have h8 : (8 / ρmin + 4) * ‖τ‖ = 8 / ρmin * ‖τ‖ + 4 * ‖τ‖ := by ring
    rw [h8]
    have h9 : (8 : ℝ) / 10 ^ 4 + 4 / 10 ^ 4 = 3 / 2500 := by norm_num
    linarith [h4, h5, h9]
  -- ## `1 + τ u τ` and `1 + τ u τ - σ u τ` are nonzero
  have hτu_le : ‖τ * u τ‖ ≤ 2 * ‖τ‖ := by
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right huτb.2 (norm_nonneg τ)
  have h1pu : 1 + τ * u τ ≠ 0 := by
    have h2 : (1 : ℝ) / 2 ≤ ‖1 + τ * u τ‖ := by
      have h4 : ‖(1 : ℂ) + τ * u τ‖ = ‖1 - (-(τ * u τ))‖ := by ring_nf
      rw [h4]
      have h5 : 1 - ‖τ * u τ‖ ≤ ‖1 - (-(τ * u τ))‖ := by
        have := abs_norm_sub_norm_le (1 : ℂ) (-(τ * u τ))
        rw [norm_one, norm_neg] at this
        linarith [le_abs_self (1 - ‖τ * u τ‖)]
      have h6 : ‖τ * u τ‖ ≤ 1 / 4 := by
        have h7 : 2 * ‖τ‖ ≤ 1 / 4 := by nlinarith [hτb2, hρmin1, le_of_lt hρmin]
        linarith
      linarith
    intro h
    rw [h, norm_zero] at h2
    norm_num at h2
  have hks : 1 + τ * u τ - σ * u τ ≠ 0 := by
    have h2 : ‖σ * u τ‖ ≤ (8 * Real.pi * ‖α‖) * 2 := by
      rw [norm_mul]
      exact mul_le_mul hσ8 huτb.2 (norm_nonneg (u τ)) (by positivity)
    have h3 : 1 - ‖τ‖ * 2 ≤ ‖1 + τ * u τ‖ := by
      have h4 : ‖(1 : ℂ) + τ * u τ‖ = ‖1 - (-(τ * u τ))‖ := by ring_nf
      rw [h4]
      have h5 : 1 - ‖τ * u τ‖ ≤ ‖1 - (-(τ * u τ))‖ := by
        have := abs_norm_sub_norm_le (1 : ℂ) (-(τ * u τ))
        rw [norm_one, norm_neg] at this
        linarith [le_abs_self (1 - ‖τ * u τ‖)]
      linarith [hτu_le, h5]
    have h4 : ‖1 + τ * u τ‖ - ‖σ * u τ‖ ≤ ‖1 + τ * u τ - σ * u τ‖ := by
      have := abs_norm_sub_norm_le (1 + τ * u τ) (σ * u τ)
      linarith [le_abs_self (‖1 + τ * u τ‖ - ‖σ * u τ‖)]
    have h5 : (8 * Real.pi * ‖α‖) * 2 ≤ 1 / 8 := by
      have h8 : ‖α‖ ≤ ρmin / 10 ^ 6 := hαs
      have h9 : ρmin / 10 ^ 6 ≤ 1 / 10 ^ 6 := div_const_le_of_le_one (by norm_num) hρmin1
      have hpi : Real.pi ≤ 3.1416 := le_of_lt Real.pi_lt_d4
      nlinarith [h8, h9, hpi, Real.pi_pos, hρmin1, le_of_lt hρmin, norm_nonneg α]
    have h6 : ‖τ‖ * 2 ≤ 1 / 8 := by
      nlinarith [hτb2, hρmin1, le_of_lt hρmin, norm_nonneg τ]
    have h7 : (1 : ℝ) / 4 ≤ ‖1 + τ * u τ - σ * u τ‖ := by linarith [h2, h3, h4, h5, h6]
    intro h
    rw [h, norm_zero] at h7
    norm_num at h7
  -- ## the normalisation `A`, the error `E`, and `1 - s = A(1+E)`
  set A : ℂ := Complex.exp (2 * Real.pi * I * α) with hA
  have hAe : (1 : ℂ) - σ * u 0 = A := by rw [hA]; exact hnorm
  have hAsmall : ‖A - 1‖ ≤ 1 / 2 := by
    have h1 : ‖A - 1‖ = ‖1 - A‖ := norm_sub_rev _ _
    rw [h1, ← hAe]
    have h2 : (1 : ℂ) - (1 - σ * u 0) = σ * u 0 := by ring
    rw [h2]
    calc ‖σ * u 0‖ ≤ ‖σ‖ * 2 := by
          rw [norm_mul]; exact mul_le_mul_of_nonneg_left hu0b.2 (norm_nonneg σ)
      _ ≤ (8 * Real.pi * ‖α‖) * 2 := by
          exact mul_le_mul_of_nonneg_right hσ8 (by norm_num)
      _ ≤ 1 / 2 := by
          have hp : Real.pi ≤ 3.1416 := le_of_lt Real.pi_lt_d4
          nlinarith [hαs, hp, Real.pi_pos, hρmin1, le_of_lt hρmin, norm_nonneg α]
  have hAre : 1 / 2 ≤ A.re := by
    have h1 : |(A - 1).re| ≤ ‖A - 1‖ := Complex.abs_re_le_norm (A - 1)
    have h2 : (A - 1).re = A.re - 1 := by simp
    rw [h2] at h1
    have h3 := neg_le_abs (A.re - 1)
    linarith
  have hAne : A ≠ 0 := by
    intro h
    rw [h] at hAre
    norm_num at hAre
  set sfunw : ℂ := σ * u τ / (1 + τ * u τ) with hsfun
  have hsfun_eq : sfun u σ α w = sfunw := by rw [sfun, hτc, hsfun]
  set E : ℂ := σ * (u 0 - u τ + u 0 * (τ * u τ)) / (A * (1 + τ * u τ)) with hEdef
  have hEid : 1 - sfunw = A * (1 + E) := by
    have hA0 : (1 : ℂ) - σ * u 0 ≠ 0 := by rw [hAe]; exact hAne
    have hcomm : (1 : ℂ) + u τ * τ ≠ 0 := by rw [mul_comm]; exact h1pu
    rw [hEdef, hsfun, ← hAe]
    field_simp [hcomm]
    ring
  have hEbound : ‖E‖ ≤ 4 * ‖σ‖ * ((8 / ρmin + 4) * ‖τ‖) := by
    have hnum : ‖σ * (u 0 - u τ + u 0 * (τ * u τ))‖ ≤ ‖σ‖ * ((8 / ρmin + 4) * ‖τ‖) := by
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg σ)
      have h3 : ‖u 0 * (τ * u τ)‖ ≤ 4 * ‖τ‖ := by
        rw [norm_mul]
        calc ‖u 0‖ * ‖τ * u τ‖ ≤ 2 * (2 * ‖τ‖) :=
              mul_le_mul hu0b.2 hτu_le (norm_nonneg (τ * u τ)) (by norm_num)
          _ = 4 * ‖τ‖ := by ring
      calc ‖u 0 - u τ + u 0 * (τ * u τ)‖ ≤ ‖u 0 - u τ‖ + ‖u 0 * (τ * u τ)‖ :=
            norm_add_le _ _
        _ ≤ (8 / ρmin) * ‖τ‖ + 4 * ‖τ‖ := by linarith [hmvt, h3]
        _ = (8 / ρmin + 4) * ‖τ‖ := by ring
    have hden : (1 : ℝ) / 4 ≤ ‖A * (1 + τ * u τ)‖ := by
      rw [norm_mul]
      have h2 : 1 / 2 ≤ ‖A‖ := by
        have h1 : |‖A‖ - 1| ≤ ‖A - 1‖ := by
          have := abs_norm_sub_norm_le A 1
          rwa [norm_one] at this
        linarith [hAsmall, neg_le_abs (‖A‖ - 1)]
      have h3 : 1 / 2 ≤ ‖1 + τ * u τ‖ := by
        have h5 : ‖(1 : ℂ) + τ * u τ‖ = ‖1 - (-(τ * u τ))‖ := by ring_nf
        rw [h5]
        have h6 : 1 - ‖τ * u τ‖ ≤ ‖1 - (-(τ * u τ))‖ := by
          have := abs_norm_sub_norm_le (1 : ℂ) (-(τ * u τ))
          rw [norm_one, norm_neg] at this
          linarith [le_abs_self (1 - ‖τ * u τ‖)]
        have h7 : 2 * ‖τ‖ ≤ 1 / 2 := by
          nlinarith [hτb2, hρmin1, le_of_lt hρmin, norm_nonneg τ]
        linarith [hτu_le, h6, h7]
      nlinarith [h2, h3]
    calc ‖E‖ = ‖σ * (u 0 - u τ + u 0 * (τ * u τ))‖ / ‖A * (1 + τ * u τ)‖ := by
          rw [hEdef, norm_div]
      _ ≤ (‖σ‖ * ((8 / ρmin + 4) * ‖τ‖)) / ‖A * (1 + τ * u τ)‖ :=
          div_le_div_of_nonneg_right hnum (norm_nonneg _)
      _ ≤ (‖σ‖ * ((8 / ρmin + 4) * ‖τ‖)) / (1 / 4) :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
      _ = 4 * ‖σ‖ * ((8 / ρmin + 4) * ‖τ‖) := by ring
  have hEhalf : ‖E‖ ≤ 1 / 2 := by
    have h1 : 4 * ‖σ‖ * ((8 / ρmin + 4) * ‖τ‖) ≤ 4 * (8 * Real.pi * ‖α‖) * (3 / 2500) :=
      mul_le_mul (by linarith [hσ8]) hkey (by positivity) (by positivity)
    have h5 : 4 * (8 * Real.pi * ‖α‖) * (3 / 2500) ≤ 1 / 2 := by
      have hp : Real.pi ≤ 3.1416 := le_of_lt Real.pi_lt_d4
      nlinarith [hαs, hp, Real.pi_pos, hρmin1, le_of_lt hρmin, norm_nonneg α]
    linarith [hEbound, h1, h5]
  have h1Ere : 0 < (1 + E).re := by
    have h1 : E.re ≥ -‖E‖ := by
      have := neg_abs_le E.re
      linarith [Complex.abs_re_le_norm E]
    have h2 : (1 + E).re = 1 + E.re := by simp
    rw [h2]; linarith
  have h1Ene : (1 : ℂ) + E ≠ 0 := by
    intro h; rw [h] at h1Ere; norm_num at h1Ere
  -- ## the logarithm
  have hlogmul : Complex.log (1 - sfun u σ α w) = Complex.log A + Complex.log (1 + E) := by
    rw [hsfun_eq, hEid]
    refine Complex.log_mul hAne h1Ene ?_
    have h1 : A.arg < Real.pi / 2 :=
      Complex.arg_lt_pi_div_two_iff.mpr (Or.inl (by linarith [hAre]))
    have h2 : -(Real.pi / 2) < A.arg :=
      Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl (by linarith [hAre]))
    have h3 : (1 + E).arg < Real.pi / 2 :=
      Complex.arg_lt_pi_div_two_iff.mpr (Or.inl h1Ere)
    have h4 : -(Real.pi / 2) < (1 + E).arg :=
      Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl h1Ere)
    refine ⟨?_, ?_⟩ <;> linarith
  have hlogA : Complex.log A = 2 * Real.pi * I * α := by
    rw [hA]
    refine Complex.log_exp ?_ ?_
    · have hIm : (2 * Real.pi * I * α).im = 2 * Real.pi * α.re := by
        simp [Complex.mul_im, Complex.mul_re]
      rw [hIm]; nlinarith [Real.pi_pos, hαre]
    · have hIm : (2 * Real.pi * I * α).im = 2 * Real.pi * α.re := by
        simp [Complex.mul_im, Complex.mul_re]
      rw [hIm]
      have h1 : α.re ≤ ‖α‖ := Complex.re_le_norm α
      nlinarith [Real.pi_pos, h1, hαs1]
  have hlift_eq : liftF u σ α w = w + 1 + (1 / (2 * Real.pi * I * α)) * Complex.log (1 + E) := by
    rw [liftF, hlogmul, hlogA]
    field_simp
    ring
  have hval : ‖liftF u σ α w - (w + 1)‖ ≤ 1 / 32 := by
    have h1 : liftF u σ α w - (w + 1)
        = (1 / (2 * Real.pi * I * α)) * Complex.log (1 + E) := by
      rw [hlift_eq]; ring
    have hlogb : ‖Complex.log (1 + E)‖ ≤ 3 / 2 * ‖E‖ :=
      Complex.norm_log_one_add_half_le_self hEhalf
    have hfac : ‖((1 : ℂ) / (2 * Real.pi * I * α))‖ = 1 / (2 * Real.pi * ‖α‖) := by
      rw [norm_div, norm_one, norm_two_pi_I_mul_s α]
    rw [h1, norm_mul, hfac]
    have hpos : (0 : ℝ) < 1 / (2 * Real.pi * ‖α‖) := by positivity
    have h2 : ‖E‖ ≤ 4 * ‖σ‖ * (3 / 2500) := by
      have h3 : 4 * ‖σ‖ * ((8 / ρmin + 4) * ‖τ‖) ≤ 4 * ‖σ‖ * (3 / 2500) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
      linarith [hEbound, h3]
    have hratio : ‖σ‖ / (2 * Real.pi * ‖α‖) ≤ 4 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi * ‖α‖)]
      nlinarith [hσ8]
    calc (1 / (2 * Real.pi * ‖α‖)) * ‖Complex.log (1 + E)‖
        ≤ (1 / (2 * Real.pi * ‖α‖)) * (3 / 2 * ‖E‖) :=
          mul_le_mul_of_nonneg_left hlogb (le_of_lt hpos)
      _ ≤ (1 / (2 * Real.pi * ‖α‖)) * (3 / 2 * (4 * ‖σ‖ * (3 / 2500))) :=
          mul_le_mul_of_nonneg_left (by linarith [h2]) (le_of_lt hpos)
      _ = (‖σ‖ / (2 * Real.pi * ‖α‖)) * 6 * (3 / 2500) := by ring
      _ ≤ 4 * 6 * (3 / 2500) := by
          have h7 : (0 : ℝ) ≤ ‖σ‖ / (2 * Real.pi * ‖α‖) := by positivity
          nlinarith [hratio]
      _ ≤ 1 / 32 := by norm_num
  -- ## the derivative: Shishikura (A.1.7)(ii) via `gate_derivF`
  have hAre2 : ‖A‖ ≤ 2 := by
    have h1 : ‖A‖ ≤ ‖A - 1‖ + 1 := by
      calc ‖A‖ = ‖(A - 1) + 1‖ := by ring_nf
        _ ≤ ‖A - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
        _ = ‖A - 1‖ + 1 := by rw [norm_one]
    linarith [hAsmall]
  have hEtiny : ‖E‖ ≤ 1 / 8 := by
    have h3 : 4 * ‖σ‖ * ((8 / ρmin + 4) * ‖τ‖) ≤ 4 * (8 * Real.pi * ‖α‖) * (3 / 2500) :=
      mul_le_mul (by linarith [hσ8]) hkey (by positivity) (by positivity)
    have h5 : 4 * (8 * Real.pi * ‖α‖) * (3 / 2500) ≤ 1 / 8 := by
      have hp : Real.pi ≤ 3.1416 := le_of_lt Real.pi_lt_d4
      nlinarith [hαs, hp, Real.pi_pos, hρmin1, le_of_lt hρmin, norm_nonneg α]
    linarith [hEbound, h3, h5]
  have hslit : 1 - sfun u σ α w ∈ Complex.slitPlane := by
    refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    rw [hsfun_eq, hEid, mul_add, mul_one, Complex.add_re]
    have h1 : -(‖A * E‖) ≤ (A * E).re := by
      have := neg_abs_le (A * E).re
      linarith [Complex.abs_re_le_norm (A * E)]
    have h2 : ‖A * E‖ ≤ 2 * (1 / 8) := by
      rw [norm_mul]
      exact mul_le_mul hAre2 hEtiny (norm_nonneg E) (by norm_num)
    linarith [h1, h2, hAre]
  have hEne : Complex.exp (-(2 * Real.pi * I * α * w)) ≠ 1 := by
    intro h
    exact hζne (by rw [h]; ring)
  have huτ' : DifferentiableAt ℂ u (tauC σ α w) := by rw [hτc]; exact huτ
  have hz : tauC σ α w ≠ 0 := by
    rw [hτc, hτ]
    exact div_ne_zero hσne hζne
  have hderivF := gate_derivF hαne hσne hz huτ' hslit hEne h1pu hks
  have hderiv_bound : ‖deriv (liftF u σ α) w - 1‖ ≤ 1 / 32 := by
    rw [hderivF.deriv]
    set X : ℂ := tauC σ α w * (tauC σ α w - σ)
      * (deriv u (tauC σ α w) - u (tauC σ α w) ^ 2) with hXdef
    set D : ℂ := (1 + tauC σ α w * u (tauC σ α w) - σ * u (tauC σ α w))
      * (1 + tauC σ α w * u (tauC σ α w)) with hDdef
    have hX : ‖X‖ ≤ 1 / 1024 := by
      rw [hXdef, norm_mul, norm_mul, hτc]
      have h2 : ‖τ - σ‖ ≤ 24 * Real.pi * ρmin / 10 ^ 6 := by
        have hp : 8 * Real.pi * ‖α‖ ≤ 8 * Real.pi * (ρmin / 10 ^ 6) :=
          mul_le_mul_of_nonneg_left hαs (by positivity)
        calc ‖τ - σ‖ ≤ ‖τ‖ + ‖σ‖ := norm_sub_le _ _
          _ ≤ 16 * Real.pi * ρmin / 10 ^ 6 + 8 * Real.pi * (ρmin / 10 ^ 6) := by linarith [hτb, hσ8, hp]
          _ = 24 * Real.pi * ρmin / 10 ^ 6 := by ring
      have h3 : ‖deriv u τ - u τ ^ 2‖ ≤ 8 / ρmin + 4 := by
        have h4 : ‖deriv u τ‖ ≤ 8 / ρmin := hderiv_le τ hτ2
        have h5 : ‖u τ ^ 2‖ ≤ 4 := by
          rw [norm_pow]
          nlinarith [huτb.2, norm_nonneg (u τ)]
        calc ‖deriv u τ - u τ ^ 2‖ ≤ ‖deriv u τ‖ + ‖u τ ^ 2‖ := norm_sub_le _ _
          _ ≤ 8 / ρmin + 4 := by linarith
      have h6 : ‖τ‖ * (8 / ρmin + 4) ≤ 3 / 2500 := by
        rw [mul_comm]; exact hkey
      have h7 : (24 * Real.pi * ρmin / 10 ^ 6) * (3 / 2500) ≤ 1 / 1024 := by
        have hp : Real.pi ≤ 3.1416 := le_of_lt Real.pi_lt_d4
        nlinarith [hp, hρmin1, le_of_lt hρmin]
      calc ‖τ‖ * ‖τ - σ‖ * ‖deriv u τ - u τ ^ 2‖
          ≤ ‖τ‖ * (24 * Real.pi * ρmin / 10 ^ 6) * (8 / ρmin + 4) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h2 (norm_nonneg τ)) h3
              (norm_nonneg _) (by positivity)
        _ = (24 * Real.pi * ρmin / 10 ^ 6) * (‖τ‖ * (8 / ρmin + 4)) := by ring
        _ ≤ (24 * Real.pi * ρmin / 10 ^ 6) * (3 / 2500) :=
            mul_le_mul_of_nonneg_left h6 (by positivity)
        _ ≤ 1 / 1024 := h7
    have hD : (1 : ℝ) / 4 ≤ ‖D‖ := by
      have hDτ : ‖D‖ = ‖1 + τ * u τ - σ * u τ‖ * ‖1 + τ * u τ‖ := by
        simp only [hDdef, norm_mul, hτc]
      rw [hDτ]
      have h2 : 1 - ‖τ‖ * 2 ≤ ‖1 + τ * u τ‖ := by
        have h5 : ‖(1 : ℂ) + τ * u τ‖ = ‖1 - (-(τ * u τ))‖ := by ring_nf
        rw [h5]
        have h6 : 1 - ‖τ * u τ‖ ≤ ‖1 - (-(τ * u τ))‖ := by
          have := abs_norm_sub_norm_le (1 : ℂ) (-(τ * u τ))
          rw [norm_one, norm_neg] at this
          linarith [le_abs_self (1 - ‖τ * u τ‖)]
        linarith [hτu_le, h6]
      have h3 : 1 - (‖τ * u τ‖ + ‖σ * u τ‖) ≤ ‖1 + τ * u τ - σ * u τ‖ := by
        have h4 : ‖1 + τ * u τ - σ * u τ‖ = ‖1 - (σ * u τ - τ * u τ)‖ := by ring_nf
        rw [h4]
        have h5 : |(1 : ℝ) - ‖σ * u τ - τ * u τ‖| ≤ ‖1 - (σ * u τ - τ * u τ)‖ := by
          simpa using abs_norm_sub_norm_le (1 : ℂ) (σ * u τ - τ * u τ)
        have h6 : ‖σ * u τ - τ * u τ‖ ≤ ‖τ * u τ‖ + ‖σ * u τ‖ := by
          have := norm_sub_le (σ * u τ) (τ * u τ); linarith
        linarith [h5, h6, le_abs_self (1 - ‖σ * u τ - τ * u τ‖)]
      have h4 : ‖τ * u τ‖ ≤ 2 * (ρmin / 10 ^ 4) := by
        rw [norm_mul]
        have hh := mul_le_mul huτb.2 hτb2 (norm_nonneg τ) (by positivity)
        linarith [hh]
      have h5 : ‖σ * u τ‖ ≤ 16 * Real.pi * ρmin / 10 ^ 6 := by
        rw [norm_mul]
        calc ‖σ‖ * ‖u τ‖ ≤ (8 * Real.pi * (ρmin / 10 ^ 6)) * 2 :=
              mul_le_mul (le_trans hσ8 (mul_le_mul_of_nonneg_left hαs (by positivity)))
                huτb.2 (norm_nonneg _) (by positivity)
          _ = 16 * Real.pi * ρmin / 10 ^ 6 := by ring
      have hp : Real.pi ≤ 4 := le_of_lt Real.pi_lt_four
      have h8 : (1 : ℝ) / 2 ≤ ‖1 + τ * u τ - σ * u τ‖ := by
        nlinarith [h3, h4, h5, hp, hρmin1, le_of_lt hρmin]
      have h9 : (1 : ℝ) / 2 ≤ ‖1 + τ * u τ‖ := by
        nlinarith [h2, hτb2, hρmin1, le_of_lt hρmin]
      nlinarith [h8, h9]
    have heq : 1 + X / D - 1 = X / D := by ring
    rw [heq, norm_div]
    calc ‖X‖ / ‖D‖ ≤ (1 / 1024) / ‖D‖ := div_le_div_of_nonneg_right hX (norm_nonneg D)
      _ ≤ (1 / 1024) / (1 / 4) :=
          div_le_div_of_nonneg_left (by norm_num) (by norm_num) hD
      _ ≤ 1 / 32 := by norm_num
  exact ⟨hderivF.differentiableAt, hval, hderiv_bound⟩

end

end Work.Pert

namespace Work.Pert

open MandelDim Complex

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

/-- **Shishikura (A.1.7)(ii)**, scale-dependent form: for every `ρmin > 0` there are `ξ₁, ε₀ > 0`
(namely `ξ₁ = 10^6/min ρmin 1` and `ε₀ = min ρmin 1/10^6`) such that whenever `u` is holomorphic
and `1/2 ≤ ‖u‖ ≤ 2` on `ball 0 ρ` with `ρ ≥ ρmin`, and `1 - σ u 0 = exp(2πiα)` with
`‖σ‖, ‖α‖ ≤ ε₀`, `α ≠ 0`, `α ∈ 𝓕₁`, the lift `F_f = liftF u σ α` is a near-translation (`1/32`
form) on both gate regions `Qreg (some ξ₁) (some (-ξ₁ + 1/α))` and
`Qreg (some (ξ₁ - 1/α)) (some (-ξ₁))`.

The witnesses are produced by `Work.Pert.gate_point_scale` applied to `m := min ρmin 1`, whose
Cauchy data live on `ball 0 ρ ⊇ ball 0 m`, together with `Work.Pert.scale_lattice`, which turns
membership in the two gate regions into the lattice gap hypothesis `‖w - k/α‖ ≥ ξ₁/2`. -/
theorem gate_scale (ρmin : ℝ) (hρmin : 0 < ρmin) :
    ∃ ξ₁ ε₀ : ℝ, 0 < ξ₁ ∧ 0 < ε₀ ∧
    ∀ {u : ℂ → ℂ} {σ α : ℂ} {ρ : ℝ}, ρmin ≤ ρ →
      DifferentiableOn ℂ u (Metric.ball (0 : ℂ) ρ) →
      (∀ z ∈ Metric.ball (0 : ℂ) ρ, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
      1 - σ * u 0 = Complex.exp (2 * Real.pi * I * α) →
      ‖σ‖ ≤ ε₀ → ‖α‖ ≤ ε₀ → α ≠ 0 → MandelDim.InF1 α →
      MandelDim.NearTranslationOn (Work.Pert.liftF u σ α)
        (MandelDim.Qreg (some (ξ₁ : ℂ)) (some (-(ξ₁ : ℂ) + 1 / α))) ∧
      MandelDim.NearTranslationOn (Work.Pert.liftF u σ α)
        (MandelDim.Qreg (some ((ξ₁ : ℂ) - 1 / α)) (some (-(ξ₁ : ℂ)))) := by
  refine ⟨10 ^ 6 / min ρmin 1, min ρmin 1 / 10 ^ 6, ?_, ?_, ?_⟩
  · positivity
  · positivity
  · intro u σ α ρ hρ hu hub hnorm hσs hαs hαne hinf
    have hm0 : (0 : ℝ) < min ρmin 1 := lt_min hρmin zero_lt_one
    have hm1 : min ρmin 1 ≤ 1 := min_le_right _ _
    have hmρ : min ρmin 1 ≤ ρ := le_trans (min_le_left _ _) hρ
    have hξ : (0 : ℝ) < 10 ^ 6 / min ρmin 1 := by positivity
    have hlat := scale_lattice hξ hinf
    constructor
    · refine ⟨fun w hw => (gate_point_scale hm0 hm1 hmρ hu hub hnorm hσs hαs hαne hinf
          (fun k => hlat.1 hw k)).1.differentiableWithinAt, ?_⟩
      exact fun w hw => (gate_point_scale hm0 hm1 hmρ hu hub hnorm hσs hαs hαne hinf
        (fun k => hlat.1 hw k)).2
    · refine ⟨fun w hw => (gate_point_scale hm0 hm1 hmρ hu hub hnorm hσs hαs hαne hinf
          (fun k => hlat.2 hw k)).1.differentiableWithinAt, ?_⟩
      exact fun w hw => (gate_point_scale hm0 hm1 hmρ hu hub hnorm hσs hαs hαne hinf
        (fun k => hlat.2 hw k)).2

end

end Work.Pert
