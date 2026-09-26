import Mathlib
import Submission.Work.Asymptotics.KhatE1.EptSmallDefs
import Submission.Work.Rigidity.decay_of_qExpansion_coeff_zero

/-!
# Upgrading `O(Ept^m)` to `O(q^{⌈m/2⌉})` for periodic holomorphic functions
-/

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane Filter
open scoped Topology

noncomputable section

/-- `t ↦ t^K e^{-ct} → 0` at `+∞` for `c > 0`. -/
lemma tendsto_pow_mul_exp_neg_mul_atTop_nhds_zero (K : ℕ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => t ^ K * Real.exp (-(c * t))) atTop (nhds 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero K).comp
    (Filter.tendsto_id.const_mul_atTop hc)
  have h2 : Tendsto (fun t : ℝ => (c * t) ^ K * Real.exp (-(c * t))) atTop (nhds 0) := by
    simpa only [Function.comp_def, id_eq] using h
  have h3 := h2.const_mul ((c ^ K)⁻¹)
  have h4 : (fun t : ℝ => (c ^ K)⁻¹ * ((c * t) ^ K * Real.exp (-(c * t))))
      = fun t : ℝ => t ^ K * Real.exp (-(c * t)) := by
    funext t
    rw [mul_pow]
    field_simp
  rw [h4] at h3
  simpa using h3

/-- **Vanishing of the low `q`-coefficients from `Ept`-order decay.** -/
theorem coeff_zero_of_ept_decay {F : UpperHalfPlane → ℂ} {m : ℕ} {C N : ℝ} (hC : 0 ≤ C)
    (hN : 0 ≤ N)
    (hper : Function.Periodic (fun w : ℂ => F (UpperHalfPlane.ofComplex w)) 1)
    (hP : Work.Kernels.InP F) (hbdd : UpperHalfPlane.IsBoundedAtImInfty F)
    (hdec : ∀ τ : UpperHalfPlane, 1 ≤ τ.im →
      ‖F τ‖ ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Residues.Ept τ‖ ^ m) :
    ∀ j : ℕ, 2 * j < m → (UpperHalfPlane.qExpansion 1 F).coeff j = 0 := by
  intro j hj
  set n : ℕ := Nat.ceil N with hn
  have hNn' : N ≤ (n : ℝ) := by rw [hn]; exact Nat.le_ceil N
  have hmj : (0:ℝ) < (m : ℝ) - 2 * j := by
    have h : (2 * j : ℝ) < (m : ℝ) := by exact_mod_cast hj
    linarith
  have hcol : ∀ t : ℝ, 1 ≤ t →
      ‖(UpperHalfPlane.qExpansion 1 F).coeff j‖
        ≤ (C * 4 ^ n) * (t ^ n * Real.exp (-(Real.pi * ((m : ℝ) - 2 * j) * t))) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
    have hmain := UpperHalfPlane.qExpansion_coeff_eq_intervalIntegral (h := 1) one_pos hper
      hP.1 hbdd j ht0
    rw [hmain]
    simp only [one_div, Complex.ofReal_one, inv_one, one_mul]
    refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := (C * 4 ^ n) * (t ^ n * Real.exp (-(Real.pi * ((m : ℝ) - 2 * j) * t)))) ?_) ?_
    · intro u hu
      have hzim : ((u : ℂ) + (t : ℂ) * ((UpperHalfPlane.I : UpperHalfPlane) : ℂ)).im = t := by
        simp [Complex.add_im, Complex.mul_im]
      set τ : ℍ := ⟨(u : ℂ) + (t : ℂ) * ((UpperHalfPlane.I : UpperHalfPlane) : ℂ),
        by rw [hzim]; exact ht0⟩ with hτdef
      have hτim : τ.im = t := by rw [hτdef]; exact hzim
      have hτre : (τ : ℂ).re = u := by rw [hτdef]; simp [Complex.add_re, Complex.mul_re]
      have hqpow : ‖Function.Periodic.qParam 1 ((u : ℂ) + (t : ℂ) *
            ((UpperHalfPlane.I : UpperHalfPlane) : ℂ)) ^ j‖
          = Real.exp (-(2 * Real.pi * (j : ℝ) * t)) := by
        rw [norm_pow, Function.Periodic.norm_qParam, hzim, div_one, ← Real.exp_nat_mul]
        congr 1; ring
      have hqnorm : ‖(Function.Periodic.qParam 1 ((u : ℂ) + (t : ℂ) *
            ((UpperHalfPlane.I : UpperHalfPlane) : ℂ)) ^ j)⁻¹‖
          = Real.exp (2 * Real.pi * (j : ℝ) * t) := by
        rw [norm_inv, hqpow, ← Real.exp_neg]
        congr 1; ring
      have hscale : (Work.Kernels.scale τ) ^ N ≤ 4 ^ n * t ^ n := by
        have h1 : (1:ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
        have h2 : Work.Kernels.scale τ ≤ 3 + t := by
          rw [Work.Kernels.scale]
          have h3 : ‖(τ : ℂ)‖ ≤ |u| + t := by
            refine le_trans (Complex.norm_le_abs_re_add_abs_im _) ?_
            have him : (τ : ℂ).im = t := hτim
            rw [hτre, him, abs_of_pos ht0]
          have h4 : τ.im⁻¹ ≤ 1 := by
            rw [hτim]; exact inv_le_one_of_one_le₀ ht
          have huI : u ∈ Set.Ioc (0:ℝ) 1 := by
            simpa only [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hu
          have h5 : |u| ≤ 1 := by
            rw [abs_le]; exact ⟨by linarith [huI.1], huI.2⟩
          linarith [h3, h4, h5]
        have h6 : Work.Kernels.scale τ ≤ 4 * t := by linarith
        calc (Work.Kernels.scale τ) ^ N ≤ (Work.Kernels.scale τ) ^ ((n:ℕ) : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le h1 hNn'
          _ = (Work.Kernels.scale τ) ^ n := Real.rpow_natCast _ _
          _ ≤ (4 * t) ^ n := pow_le_pow_left₀ (Work.Kernels.scale_pos τ).le h6 n
          _ = 4 ^ n * t ^ n := mul_pow 4 t n
      have hExp : ‖Work.Residues.Ept τ‖ ^ m = Real.exp (-(Real.pi * (m : ℝ) * t)) := by
        rw [Work.Residues.norm_Ept, hτim, ← Real.exp_nat_mul]
        congr 1; ring
      rw [norm_mul, hqnorm]
      have hF := hdec τ (by rw [hτim]; exact ht)
      rw [hExp] at hF
      refine le_trans (mul_le_mul_of_nonneg_left hF (Real.exp_nonneg _)) ?_
      have hexp2 : Real.exp (2 * Real.pi * (j : ℝ) * t)
            * Real.exp (-(Real.pi * (m : ℝ) * t))
          = Real.exp (-(Real.pi * ((m : ℝ) - 2 * j) * t)) := by
        rw [← Real.exp_add]
        congr 1; ring
      calc Real.exp (2 * Real.pi * (j : ℝ) * t)
            * (C * (Work.Kernels.scale τ) ^ N * Real.exp (-(Real.pi * (m : ℝ) * t)))
          = C * (Work.Kernels.scale τ) ^ N
              * (Real.exp (2 * Real.pi * (j : ℝ) * t)
                  * Real.exp (-(Real.pi * (m : ℝ) * t))) := by ring
        _ = C * (Work.Kernels.scale τ) ^ N * Real.exp (-(Real.pi * ((m : ℝ) - 2 * j) * t)) := by
              rw [hexp2]
        _ ≤ C * (4 ^ n * t ^ n) * Real.exp (-(Real.pi * ((m : ℝ) - 2 * j) * t)) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale hC) (Real.exp_nonneg _)
        _ = (C * 4 ^ n) * (t ^ n * Real.exp (-(Real.pi * ((m : ℝ) - 2 * j) * t))) := by ring
    · simp
  have hlim : Tendsto (fun t : ℝ =>
      (C * 4 ^ n) * (t ^ n * Real.exp (-(Real.pi * ((m : ℝ) - 2 * j) * t))))
      atTop (nhds 0) := by
    have h := tendsto_pow_mul_exp_neg_mul_atTop_nhds_zero n
      (c := Real.pi * ((m : ℝ) - 2 * j)) (by positivity)
    simpa using h.const_mul (C * 4 ^ n)
  have hle : ‖(UpperHalfPlane.qExpansion 1 F).coeff j‖ ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim
      (eventually_atTop.mpr ⟨1, fun t ht => hcol t ht⟩)
  exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg _))

/-- **The periodic upgrade**: a `1`-periodic holomorphic function that is `O(Ept^m)` is
`O(q^{(m+1)/2})`. -/
theorem IsSmall.periodic_decay {F : UpperHalfPlane → ℂ} {m : ℕ}
    (hper : Function.Periodic (fun w : ℂ => F (UpperHalfPlane.ofComplex w)) 1)
    (hP : Work.Kernels.InP F) (hbdd : UpperHalfPlane.IsBoundedAtImInfty F)
    (h : IsSmall F m) :
    ∃ A B : ℝ, 0 ≤ B ∧ ∀ τ : UpperHalfPlane, A ≤ τ.im →
      ‖F τ‖ ≤ B * ‖Work.Kernels.qParamFun τ‖ ^ ((m + 1) / 2) := by
  obtain ⟨C, N, hC, hN, hdec⟩ := h
  have hcoeff : ∀ j : ℕ, j < (m + 1) / 2 → (UpperHalfPlane.qExpansion 1 F).coeff j = 0 := by
    intro j hj
    refine coeff_zero_of_ept_decay hC.le hN hper hP hbdd hdec j ?_
    omega
  obtain ⟨A, B, hB, hbd⟩ :=
    Work.Rigidity.decay_of_qExpansion_coeff_zero hper hP.1 hbdd hcoeff
  refine ⟨A, B, hB, fun τ hτ => ?_⟩
  have h1 := hbd τ hτ
  have h2 : Real.exp (-(2 * Real.pi * (((m + 1) / 2 : ℕ) : ℝ) * τ.im))
      = ‖Work.Kernels.qParamFun τ‖ ^ ((m + 1) / 2) := by
    rw [Work.Asymptotics.norm_qParamFun, ← Real.exp_nat_mul]
    congr 1; ring
  rwa [h2] at h1

end

end Work.Asymptotics.KhatE1
