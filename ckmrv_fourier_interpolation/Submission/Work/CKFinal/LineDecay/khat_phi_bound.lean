import Mathlib
import Submission.Work.CKFinal.LineDecay.ContourPoint
import Submission.Work.CKFinal.LineDecay.PhiAxis
import Submission.Work.CKFinal.LineDecay.Phi_axis_norm_eight
import Submission.Work.CKFinal.LineDecay.Phi_axis_norm_twentyfour
import Submission.Work.Asymptotics.KPlus_slash_bound_half
import Submission.Work.CKFinal.LineDecay.KMinus_slash_bound_half_clean
import Submission.Work.CKFinal.LineDecay.slash_qtau_twentyfour

namespace Work.CKFinal.LineDecay

open UpperHalfPlane

/-- A point `τ` with `Re τ = ±1/2` and `Im τ ≥ 1` lies in the CKMRV domain `𝒟`. -/
private lemma mem_DomainD_of_re_half {τ : UpperHalfPlane}
    (hre : τ.re = 1 / 2 ∨ τ.re = - 1 / 2) (him : (1 : ℝ) ≤ τ.im) :
    τ ∈ Work.Asymptotics.DomainD := by
  have hre1 : -1 < τ.re ∧ τ.re < 1 := by
    rcases hre with h | h <;> (rw [h]; norm_num)
  refine ⟨hre1.1, hre1.2, ?_, ?_⟩
  · have h1 : |τ.im| ≤ ‖((τ : ℂ) - (1 / 2 : ℂ))‖ := by
      have h := Complex.abs_im_le_norm ((τ : ℂ) - (1 / 2 : ℂ))
      have him' : ((τ : ℂ) - (1 / 2 : ℂ)).im = τ.im := by simp
      rwa [him'] at h
    have h2 : |τ.im| = τ.im := abs_of_pos τ.im_pos
    linarith [abs_nonneg τ.im]
  · have h1 : |τ.im| ≤ ‖((τ : ℂ) + (1 / 2 : ℂ))‖ := by
      have h := Complex.abs_im_le_norm ((τ : ℂ) + (1 / 2 : ℂ))
      have him' : ((τ : ℂ) + (1 / 2 : ℂ)).im = τ.im := by simp
      rwa [him'] at h
    have h2 : |τ.im| = τ.im := abs_of_pos τ.im_pos
    linarith [abs_nonneg τ.im]

/-- **Pointwise bound for the second difference `Φ` of the hatted kernel on the two lines.**

Let `τ` lie on `Re τ = ±1/2` with `Im τ ≥ 12`, and suppose that on the positive imaginary axis the
divisor is bounded below,
`c ≤ ‖Δ(zcb u) * (j τ - j (zcb u))‖` for all `u ≥ 1/3` (`hdiv`; this holds because
`Δ(z) j(z) = E₄(z)³` with `‖E₄(z)‖ ≥ 1/2` for `Im z ≥ 3`, plus compactness on the imaginary axis,
which is pole-free here).  Then `‖Φ(K̂^{(d)}, τ, t)‖ ≤ C (1+t)^N e^{-π t}` for all `t ≥ 1`.

Route: `Work.CKFinal.PhiHat_axis_eq` identifies
`Φ(K̂)(τ,t) = -(i t)^{d/2-2} (K_+(τ, i/t) + K_-(τ, i/t))`, so
`‖Φ‖ ≤ t^{d/2-2} (‖K_+(τ, zcb (1/t))‖ + ‖K_-(τ, zcb (1/t))‖)` (note `S • zcb t = zcb (1/t)`,
`Submission.Work.CKFinal.LineDecay.ContourPoint.S_smul_zcb`).  The CKMRV quotient bounds
(`Work.Asymptotics.KPlus_slash_bound_half 8` and
`Work.CKFinal.LineDecay.KMinus_slash_bound_half_clean` for `d = 8`,
`Work.CKFinal.LineDecay.slash_qtau_twentyfour` for `d = 24`, applied at `z = zcb t`, where
`Im z = t ≥ 1/3`) give
`t^{d/2-2} ‖K_±(τ, zcb (1/t))‖ ≤ C (1+‖τ‖)^A (1+t)^A e^{-π t} / ‖Δ(zcb t) (j τ - j (zcb t))‖`,
and `hdiv` bounds the denominator below by `c`. -/
theorem khat_phi_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (hre : τ.re = 1 / 2 ∨ τ.re = - 1 / 2) (hy : 12 ≤ τ.im)
    (hdiv : ∃ c : ℝ, 0 < c ∧ ∀ u : ℝ, 1 / 3 ≤ u →
      c ≤ ‖Work.Kernels.DeltaFun (zcb u)
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun (zcb u))‖) :
    ∃ C N : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ici (1 : ℝ),
      ‖Work.CKFinal.Phi (Work.Kernels.Khat ℓ d) τ t‖ ≤ C * (1 + t) ^ N * Real.exp (-(Real.pi * t)) := by
  obtain ⟨c, hc, hdivb⟩ := hdiv
  have hτD : τ ∈ Work.Asymptotics.DomainD := mem_DomainD_of_re_half hre (by linarith)
  have hτhalf : (1 : ℝ) / 2 ≤ τ.im := by linarith
  rcases hd with rfl | rfl
  · -- dimension 8
    obtain ⟨Cp, Ap, hCp, hAp, hKpb⟩ := Work.Asymptotics.KPlus_slash_bound_half 8 (Or.inl rfl)
    obtain ⟨Cm, Am, hCm, hAm, hKmb⟩ := Work.CKFinal.LineDecay.KMinus_slash_bound_half_clean ℓ
    refine ⟨(Cp * (1 + ‖(τ : ℂ)‖) ^ Ap + Cm * (1 + ‖(τ : ℂ)‖) ^ Am) / c,
      max Am 0, by positivity, ?_⟩
    intro t ht1
    have ht1' : (1 : ℝ) ≤ t := ht1
    have ht : (0 : ℝ) < t := by linarith
    have hzim : (zcb t).im = t := zcb_im ht
    have hz3 : (1 : ℝ) / 3 ≤ (zcb t).im := by rw [hzim]; linarith
    have hzn : ‖(zcb t : ℂ)‖ = t := by
      rw [zcb_coe ht, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg ht.le]
    set D : ℝ := ‖Work.Kernels.DeltaFun (zcb t)
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun (zcb t))‖ with hDdef
    have hden : c ≤ D := by rw [hDdef]; exact hdivb t (by linarith)
    have hDpos : 0 < D := lt_of_lt_of_le hc hden
    have hJne : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (zcb t) := by
      intro hh
      have h0 : D = 0 := by rw [hDdef, hh, sub_self, mul_zero, norm_zero]
      rw [h0] at hden; linarith
    have hp := hKpb τ (zcb t) hτD hτhalf hz3 hJne
    rw [show (((8 : ℕ) : ℤ) / 2 - 2) = (2 : ℤ) by norm_num, zpow_ofNat] at hp
    rw [hzim] at hp
    rw [← hDdef] at hp
    have hm := hKmb τ (zcb t) hτD hτhalf hz3 hJne
    rw [hzim] at hm
    rw [hzn] at hm
    rw [← hDdef] at hm
    have hΦ : ‖Work.CKFinal.Phi (Work.Kernels.Khat ℓ 8) τ t‖
        ≤ t ^ 2 * (‖Work.Kernels.KPlus 8 τ (ModularGroup.S • zcb t)‖
              + ‖Work.Kernels.KMinus ℓ 8 τ (ModularGroup.S • zcb t)‖) := by
      have h := (Phi_axis_norm_eight ℓ τ ht).2
      rw [← zcb_eq_imagAxis ht] at h
      exact h
    have hcP : t ^ 2 * ‖Work.Kernels.KPlus 8 τ (ModularGroup.S • zcb t)‖
        = ‖(zcb t : ℂ) ^ 2 * Work.Kernels.KPlus 8 τ (ModularGroup.S • zcb t)‖ := by
      rw [norm_mul, norm_pow, hzn]
    have hcM : t ^ 2 * ‖Work.Kernels.KMinus ℓ 8 τ (ModularGroup.S • zcb t)‖
        = ‖(zcb t : ℂ) ^ 2 * Work.Kernels.KMinus ℓ 8 τ (ModularGroup.S • zcb t)‖ := by
      rw [norm_mul, norm_pow, hzn]
    have he0 : 0 ≤ Real.exp (-(Real.pi * t)) := (Real.exp_pos _).le
    have h1t : (1 : ℝ) ≤ 1 + t := by linarith
    have hNge : Am ≤ max Am 0 := le_max_left Am 0
    have hNnn : 0 ≤ max Am 0 := le_max_right Am 0
    have hpAmN : (1 + t) ^ Am ≤ (1 + t) ^ (max Am 0) :=
      Real.rpow_le_rpow_of_exponent_le h1t hNge
    have h1N : (1 : ℝ) ≤ (1 + t) ^ (max Am 0) := Real.one_le_rpow h1t hNnn
    have hA1 : (0 : ℝ) ≤ Cp * (1 + ‖(τ : ℂ)‖) ^ Ap := by positivity
    have hA2 : (0 : ℝ) ≤ Cm * (1 + ‖(τ : ℂ)‖) ^ Am := by positivity
    have hterm : Cp * (1 + ‖(τ : ℂ)‖) ^ Ap
          + Cm * (1 + ‖(τ : ℂ)‖) ^ Am * (1 + t) ^ Am
        ≤ (Cp * (1 + ‖(τ : ℂ)‖) ^ Ap + Cm * (1 + ‖(τ : ℂ)‖) ^ Am)
            * (1 + t) ^ (max Am 0) := by
      have h1 := le_mul_of_one_le_right hA1 h1N
      have h2 := mul_le_mul_of_nonneg_left hpAmN hA2
      calc Cp * (1 + ‖(τ : ℂ)‖) ^ Ap + Cm * (1 + ‖(τ : ℂ)‖) ^ Am * (1 + t) ^ Am
          ≤ Cp * (1 + ‖(τ : ℂ)‖) ^ Ap * (1 + t) ^ (max Am 0)
            + Cm * (1 + ‖(τ : ℂ)‖) ^ Am * (1 + t) ^ (max Am 0) := add_le_add h1 h2
        _ = (Cp * (1 + ‖(τ : ℂ)‖) ^ Ap + Cm * (1 + ‖(τ : ℂ)‖) ^ Am)
              * (1 + t) ^ (max Am 0) := by ring
    have hdiv' : Real.exp (-(Real.pi * t)) / D ≤ Real.exp (-(Real.pi * t)) / c :=
      div_le_div_of_nonneg_left he0 hc hden
    have hstep1 : (Cp * (1 + ‖(τ : ℂ)‖) ^ Ap
          + Cm * (1 + ‖(τ : ℂ)‖) ^ Am * (1 + t) ^ Am) * (Real.exp (-(Real.pi * t)) / D)
        ≤ (Cp * (1 + ‖(τ : ℂ)‖) ^ Ap + Cm * (1 + ‖(τ : ℂ)‖) ^ Am)
            * (1 + t) ^ (max Am 0) * (Real.exp (-(Real.pi * t)) / c) :=
      mul_le_mul hterm hdiv' (by positivity) (by positivity)
    have hfin : (Cp * (1 + ‖(τ : ℂ)‖) ^ Ap + Cm * (1 + ‖(τ : ℂ)‖) ^ Am)
            * (1 + t) ^ (max Am 0) * (Real.exp (-(Real.pi * t)) / c)
        = (Cp * (1 + ‖(τ : ℂ)‖) ^ Ap + Cm * (1 + ‖(τ : ℂ)‖) ^ Am) / c
            * (1 + t) ^ (max Am 0) * Real.exp (-(Real.pi * t)) := by
      rw [div_eq_mul_inv]; ring
    calc ‖Work.CKFinal.Phi (Work.Kernels.Khat ℓ 8) τ t‖
        ≤ t ^ 2 * (‖Work.Kernels.KPlus 8 τ (ModularGroup.S • zcb t)‖
              + ‖Work.Kernels.KMinus ℓ 8 τ (ModularGroup.S • zcb t)‖) := hΦ
      _ = t ^ 2 * ‖Work.Kernels.KPlus 8 τ (ModularGroup.S • zcb t)‖
            + t ^ 2 * ‖Work.Kernels.KMinus ℓ 8 τ (ModularGroup.S • zcb t)‖ := by ring
      _ = ‖(zcb t : ℂ) ^ 2 * Work.Kernels.KPlus 8 τ (ModularGroup.S • zcb t)‖
            + ‖(zcb t : ℂ) ^ 2 * Work.Kernels.KMinus ℓ 8 τ (ModularGroup.S • zcb t)‖ := by
          rw [hcP, hcM]
      _ ≤ Cp * (1 + ‖(τ : ℂ)‖) ^ Ap * Real.exp (-(Real.pi * t)) / D
            + Cm * (1 + ‖(τ : ℂ)‖) ^ Am * (1 + t) ^ Am
                * Real.exp (-(Real.pi * t)) / D := add_le_add hp hm
      _ = (Cp * (1 + ‖(τ : ℂ)‖) ^ Ap
            + Cm * (1 + ‖(τ : ℂ)‖) ^ Am * (1 + t) ^ Am)
              * (Real.exp (-(Real.pi * t)) / D) := by
          rw [div_eq_mul_inv]; ring
      _ ≤ (Cp * (1 + ‖(τ : ℂ)‖) ^ Ap + Cm * (1 + ‖(τ : ℂ)‖) ^ Am)
            * (1 + t) ^ (max Am 0) * (Real.exp (-(Real.pi * t)) / c) := hstep1
      _ = (Cp * (1 + ‖(τ : ℂ)‖) ^ Ap + Cm * (1 + ‖(τ : ℂ)‖) ^ Am) / c
            * (1 + t) ^ (max Am 0) * Real.exp (-(Real.pi * t)) := hfin
  · -- dimension 24
    obtain ⟨C24, A24, hC24, hA24, hK24⟩ := Work.CKFinal.LineDecay.slash_qtau_twentyfour ℓ
    refine ⟨2 * C24 * (1 + ‖(τ : ℂ)‖) ^ A24 / c, 0, by positivity, ?_⟩
    intro t ht1
    have ht1' : (1 : ℝ) ≤ t := ht1
    have ht : (0 : ℝ) < t := by linarith
    have hzim : (zcb t).im = t := zcb_im ht
    have hz3 : (1 : ℝ) / 3 ≤ (zcb t).im := by rw [hzim]; linarith
    have hzn : ‖(zcb t : ℂ)‖ = t := by
      rw [zcb_coe ht, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg ht.le]
    set D : ℝ := ‖Work.Kernels.DeltaFun (zcb t)
        * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun (zcb t))‖ with hDdef
    have hden : c ≤ D := by rw [hDdef]; exact hdivb t (by linarith)
    have hDpos : 0 < D := lt_of_lt_of_le hc hden
    have hJne : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (zcb t) := by
      intro hh
      have h0 : D = 0 := by rw [hDdef, hh, sub_self, mul_zero, norm_zero]
      rw [h0] at hden; linarith
    have hp := (hK24 τ (zcb t) hτD (by linarith) hz3 hJne).1
    have hm := (hK24 τ (zcb t) hτD (by linarith) hz3 hJne).2
    rw [show ((24 : ℤ) / 2 - 2) = (10 : ℤ) by norm_num, zpow_ofNat] at hp hm
    rw [hzim] at hp hm
    rw [← hDdef] at hp hm
    have hq : ‖Work.Kernels.qParamFun τ‖ ≤ 1 := by
      rw [Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
      nlinarith [Real.pi_pos, hy]
    have hΦ : ‖Work.CKFinal.Phi (Work.Kernels.Khat ℓ 24) τ t‖
        ≤ t ^ 10 * (‖Work.Kernels.KPlus 24 τ (ModularGroup.S • zcb t)‖
              + ‖Work.Kernels.KMinus ℓ 24 τ (ModularGroup.S • zcb t)‖) := by
      have h := (Phi_axis_norm_twentyfour ℓ τ ht).2
      rw [← zcb_eq_imagAxis ht] at h
      exact h
    have hcP : t ^ 10 * ‖Work.Kernels.KPlus 24 τ (ModularGroup.S • zcb t)‖
        = ‖(zcb t : ℂ) ^ 10 * Work.Kernels.KPlus 24 τ (ModularGroup.S • zcb t)‖ := by
      rw [norm_mul, norm_pow, hzn]
    have hcM : t ^ 10 * ‖Work.Kernels.KMinus ℓ 24 τ (ModularGroup.S • zcb t)‖
        = ‖(zcb t : ℂ) ^ 10 * Work.Kernels.KMinus ℓ 24 τ (ModularGroup.S • zcb t)‖ := by
      rw [norm_mul, norm_pow, hzn]
    have he0 : 0 ≤ Real.exp (-(Real.pi * t)) := (Real.exp_pos _).le
    have hA1 : (0 : ℝ) ≤ C24 * (1 + ‖(τ : ℂ)‖) ^ A24 := by positivity
    -- the two slashed terms
    have hsum : C24 * (1 + ‖(τ : ℂ)‖) ^ A24 * ‖Work.Kernels.qParamFun τ‖
            * Real.exp (-(Real.pi * t)) / D
          + C24 * (1 + ‖(τ : ℂ)‖) ^ A24 * ‖Work.Kernels.qParamFun τ‖
            * Real.exp (-(Real.pi * t)) / D
        = 2 * (C24 * (1 + ‖(τ : ℂ)‖) ^ A24 * ‖Work.Kernels.qParamFun τ‖
            * Real.exp (-(Real.pi * t)) / D) := by ring
    have hstep1 : 2 * (C24 * (1 + ‖(τ : ℂ)‖) ^ A24 * ‖Work.Kernels.qParamFun τ‖
            * Real.exp (-(Real.pi * t)) / D)
        ≤ 2 * ((C24 * (1 + ‖(τ : ℂ)‖) ^ A24) / c * Real.exp (-(Real.pi * t))) := by
      have hnum : C24 * (1 + ‖(τ : ℂ)‖) ^ A24 * ‖Work.Kernels.qParamFun τ‖
            * Real.exp (-(Real.pi * t))
          ≤ C24 * (1 + ‖(τ : ℂ)‖) ^ A24 * Real.exp (-(Real.pi * t)) := by
        have h1 : C24 * (1 + ‖(τ : ℂ)‖) ^ A24 * ‖Work.Kernels.qParamFun τ‖
            ≤ C24 * (1 + ‖(τ : ℂ)‖) ^ A24 * 1 :=
          mul_le_mul_of_nonneg_left hq hA1
        exact mul_le_mul_of_nonneg_right (by simpa using h1) he0
      have hd1 : C24 * (1 + ‖(τ : ℂ)‖) ^ A24 * ‖Work.Kernels.qParamFun τ‖
            * Real.exp (-(Real.pi * t)) / D
          ≤ C24 * (1 + ‖(τ : ℂ)‖) ^ A24 * Real.exp (-(Real.pi * t)) / D :=
        div_le_div_of_nonneg_right hnum hDpos.le
      have hd2 : C24 * (1 + ‖(τ : ℂ)‖) ^ A24 * Real.exp (-(Real.pi * t)) / D
          ≤ (C24 * (1 + ‖(τ : ℂ)‖) ^ A24) / c * Real.exp (-(Real.pi * t)) := by
        have h := div_le_div_of_nonneg_left
          (show (0 : ℝ) ≤ C24 * (1 + ‖(τ : ℂ)‖) ^ A24 * Real.exp (-(Real.pi * t)) by positivity)
          hc hden
        calc C24 * (1 + ‖(τ : ℂ)‖) ^ A24 * Real.exp (-(Real.pi * t)) / D
            ≤ C24 * (1 + ‖(τ : ℂ)‖) ^ A24 * Real.exp (-(Real.pi * t)) / c := h
          _ = (C24 * (1 + ‖(τ : ℂ)‖) ^ A24) / c * Real.exp (-(Real.pi * t)) := by
              rw [div_eq_mul_inv]; ring
      calc 2 * (C24 * (1 + ‖(τ : ℂ)‖) ^ A24 * ‖Work.Kernels.qParamFun τ‖
            * Real.exp (-(Real.pi * t)) / D)
          ≤ 2 * (C24 * (1 + ‖(τ : ℂ)‖) ^ A24 * Real.exp (-(Real.pi * t)) / D) :=
            mul_le_mul_of_nonneg_left hd1 (by norm_num)
        _ ≤ 2 * ((C24 * (1 + ‖(τ : ℂ)‖) ^ A24) / c * Real.exp (-(Real.pi * t))) :=
            mul_le_mul_of_nonneg_left hd2 (by norm_num)
    have hfin : 2 * ((C24 * (1 + ‖(τ : ℂ)‖) ^ A24) / c * Real.exp (-(Real.pi * t)))
        = 2 * C24 * (1 + ‖(τ : ℂ)‖) ^ A24 / c * (1 + t) ^ (0 : ℝ)
            * Real.exp (-(Real.pi * t)) := by
      rw [Real.rpow_zero, div_eq_mul_inv]; ring
    calc ‖Work.CKFinal.Phi (Work.Kernels.Khat ℓ 24) τ t‖
        ≤ t ^ 10 * (‖Work.Kernels.KPlus 24 τ (ModularGroup.S • zcb t)‖
              + ‖Work.Kernels.KMinus ℓ 24 τ (ModularGroup.S • zcb t)‖) := hΦ
      _ = t ^ 10 * ‖Work.Kernels.KPlus 24 τ (ModularGroup.S • zcb t)‖
            + t ^ 10 * ‖Work.Kernels.KMinus ℓ 24 τ (ModularGroup.S • zcb t)‖ := by ring
      _ = ‖(zcb t : ℂ) ^ 10 * Work.Kernels.KPlus 24 τ (ModularGroup.S • zcb t)‖
            + ‖(zcb t : ℂ) ^ 10 * Work.Kernels.KMinus ℓ 24 τ (ModularGroup.S • zcb t)‖ := by
          rw [hcP, hcM]
      _ ≤ C24 * (1 + ‖(τ : ℂ)‖) ^ A24 * ‖Work.Kernels.qParamFun τ‖
              * Real.exp (-(Real.pi * t)) / D
            + C24 * (1 + ‖(τ : ℂ)‖) ^ A24 * ‖Work.Kernels.qParamFun τ‖
              * Real.exp (-(Real.pi * t)) / D := add_le_add hp hm
      _ = 2 * (C24 * (1 + ‖(τ : ℂ)‖) ^ A24 * ‖Work.Kernels.qParamFun τ‖
              * Real.exp (-(Real.pi * t)) / D) := hsum
      _ ≤ 2 * ((C24 * (1 + ‖(τ : ℂ)‖) ^ A24) / c * Real.exp (-(Real.pi * t))) := hstep1
      _ = 2 * C24 * (1 + ‖(τ : ℂ)‖) ^ A24 / c * (1 + t) ^ (0 : ℝ)
            * Real.exp (-(Real.pi * t)) := hfin

end Work.CKFinal.LineDecay
