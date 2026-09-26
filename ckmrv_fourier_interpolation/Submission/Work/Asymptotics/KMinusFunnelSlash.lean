import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.KMinusCuspBallDefs
import Submission.Work.Asymptotics.KMinusFunnelJAtoms
import Submission.Work.Asymptotics.KPlus_slash_bound_funnel
import Submission.Work.Asymptotics.mdiff_eta
import Submission.Work.Asymptotics.KMinusCuspBallLimit
import Submission.Work.Asymptotics.KMinusFunnelZBounds
import Submission.Work.Asymptotics.KMinusFunnelZBoundsLS

set_option maxHeartbeats 2000000

namespace Work.Asymptotics

open UpperHalfPlane
open scoped Manifold

noncomputable section

/-! ## The cancelled forms of `T₈` and `T₂₄` -/

theorem T8_cancelled (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) :
    T8 ℓ τ z =
      (-3456 : ℂ) * Work.Kernels.E4Fun τ * Work.Kernels.E10Fun z * ℓ.L_S z
      + (Work.Kernels.E8Fun z * Work.Kernels.VFun z
            + Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2))
          * (Work.Kernels.E4Fun τ
              * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                  - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
              / Work.Kernels.DeltaFun τ)
      + (-1728 : ℂ) * Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun z * Work.Kernels.VFun z := by
  rw [T8]
  simp (config := { decide := true }) only [Alpha, Work.Kernels.psiVec, vlen, ulen,
    Work.Kernels.fk, Work.Kernels.E8Fun, Work.Kernels.E10Fun, Work.Kernels.E14Fun,
    Work.Kernels.jInvariantFun, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, ite_true, Matrix.of_apply]
  norm_num
  ring_nf

theorem T24_cancelled (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane) :
    T24 ℓ τ z =
      (-3456 : ℂ) * Work.Kernels.DeltaFun τ * (Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z)
          * ℓ.L_S z
      + (3456 * Work.Kernels.DeltaFun τ
            + 2 * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ))
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)
          * Work.Kernels.VFun z
      + (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
            - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
          * Work.Kernels.jInvariantFun τ * Work.Kernels.VFun z
      + (-1728 : ℂ) * Work.Kernels.psi4 ℓ τ * (Work.Kernels.E8Fun τ * Work.Kernels.VFun z)
      + (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
            - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
          * (Work.Kernels.E10Fun z / Work.Kernels.DeltaFun z)
          * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2) := by
  rw [T24]
  simp (config := { decide := true }) only [Alpha, Work.Kernels.psiVec, vlen, ulen,
    Work.Kernels.fk, Work.Kernels.E8Fun, Work.Kernels.E10Fun, Work.Kernels.E14Fun,
    Work.Kernels.jInvariantFun, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, ite_true, Matrix.of_apply]
  norm_num
  ring_nf

/-! ## Elementary norm helpers -/

private lemma nmul2 {a b : ℂ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) : ‖a * b‖ ≤ A * B := by
  rw [norm_mul]
  exact mul_le_mul ha hb (norm_nonneg _) hA

private lemma nmul3 {a b c : ℂ} {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ C) : ‖a * b * c‖ ≤ A * B * C := by
  rw [norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul ha hb (norm_nonneg _) hA) hc (norm_nonneg _) (by positivity)

private lemma nmul4 {a b c d : ℂ} {A B C D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hD : 0 ≤ D) (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) (hc : ‖c‖ ≤ C) (hd : ‖d‖ ≤ D) :
    ‖a * b * c * d‖ ≤ A * B * C * D := by
  have h3 : ‖a * b * c‖ ≤ A * B * C := nmul3 hA hB hC ha hb hc
  rw [norm_mul]
  exact mul_le_mul h3 hd (norm_nonneg _) (by positivity)

private lemma norm_neg_natCast (n : ℕ) : ‖(-(n : ℂ))‖ = n := by
  rw [norm_neg, Complex.norm_natCast]

private lemma norm_add4_le (a b c d : ℂ) :
    ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  have e1 := norm_add_le (a + b + c) d
  have e2 := norm_add_le (a + b) c
  have e3 := norm_add_le a b
  linarith [e1, e2, e3, norm_nonneg (a + b + c), norm_nonneg (a + b), norm_nonneg a, norm_nonneg b,
    norm_nonneg c, norm_nonneg d]

private lemma norm_add5_le (a b c d e : ℂ) :
    ‖a + b + c + d + e‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ := by
  have e1 := norm_add_le (a + b + c + d) e
  have e2 := norm_add4_le a b c d
  linarith [e1, e2, norm_nonneg (a + b + c + d), norm_nonneg a, norm_nonneg b, norm_nonneg c,
    norm_nonneg d, norm_nonneg e]


/-- `scale τ ≤ 3 (1 + ‖τ‖)` for `Im τ ≥ 1/2`. -/
lemma scale_le_three (τ : UpperHalfPlane) (h : (1 : ℝ) / 2 ≤ τ.im) :
    Work.Kernels.scale τ ≤ 3 * (1 + ‖(τ : ℂ)‖) := by
  have hinv : (τ.im)⁻¹ ≤ 2 := by
    have := inv_anti₀ (show (0:ℝ) < 1/2 by norm_num) h
    norm_num at this
    exact this
  have h0 : (0 : ℝ) ≤ ‖(τ : ℂ)‖ := norm_nonneg _
  rw [Work.Kernels.scale]
  linarith


/-! ## The crude funnel bound on `Ncusp` -/

set_option maxHeartbeats 8000000 in
theorem Ncusp_funnel_crude (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧ ∀ (τ z : UpperHalfPlane), Funnel τ → 1 / 3 ≤ z.im →
      ‖Ncusp ℓ d τ z‖ ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (Real.pi * z.im) := by
  obtain ⟨Cz1, hCz1, hz1⟩ := KMinusFunnelZBounds
  obtain ⟨Cz2, hCz2, hz2⟩ := KMinusFunnelZBoundsLS ℓ
  obtain ⟨CΔ, hCΔ, hΔlow⟩ := exists_Delta_Funnel_lower
  obtain ⟨CD, ND, hCD, hND, hD⟩ := psi4E8_sub_psi2E10_funnel ℓ
  obtain ⟨Cψ, Nψ, hCψ, hNψ, hψ⟩ := psi_scale_funnel ℓ
  have hE4f : ∀ τ : UpperHalfPlane, Funnel τ → ‖Work.Kernels.E4Fun τ‖ ≤ 3 / 2 :=
    fun τ hτ => (Work.FunnelNumerics.E4_funnel_bounds).1 τ hτ
  have hjf : ∀ τ : UpperHalfPlane, Funnel τ →
      ‖Work.Kernels.jInvariantFun τ‖ ≤ (27 / 4) * Real.exp (2 * Real.pi * τ.im) :=
    fun τ hτ => KF24.norm_j_funnel τ hτ
  have hΔuf : ∀ τ : UpperHalfPlane, Funnel τ →
      ‖Work.Kernels.DeltaFun τ‖ ≤ 2 * ‖Work.Kernels.qParamFun τ‖ :=
    fun τ hτ => DeltaFun_funnel_le τ hτ
  have hE8f : ∀ τ : UpperHalfPlane, Funnel τ → ‖Work.Kernels.E8Fun τ‖ ≤ 9 / 4 := by
    intro τ hτ
    have h := hE4f τ hτ
    rw [show Work.Kernels.E8Fun τ = Work.Kernels.E4Fun τ ^ 2 from rfl, norm_pow]
    nlinarith [h, norm_nonneg (Work.Kernels.E4Fun τ)]
  rcases hd with rfl | rfl
  · -- ## `d = 8`
    set A : ℝ := max ND Nψ with hAdef
    have hA0 : 0 ≤ A := by rw [hAdef]; exact le_trans hND (le_max_left _ _)
    refine ⟨‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ *
        (3456 * (3 / 2) * Cz2 + (Cz1 * (3 / 2) * (CD / CΔ) + 1728 * Cψ * Cz1)) * 3 ^ A + 1,
      A, ?_, hA0, ?_⟩
    · have h1 : (0:ℝ) < 3456 * (3 / 2) * Cz2 + (Cz1 * (3 / 2) * (CD / CΔ) + 1728 * Cψ * Cz1) := by
        positivity
      have h2 : (0:ℝ) < (3:ℝ) ^ A := Real.rpow_pos_of_pos (by norm_num) _
      have h3 : (0:ℝ) ≤ ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ := norm_nonneg _
      have h4 : (0:ℝ) ≤ ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖
          * (3456 * (3 / 2) * Cz2 + (Cz1 * (3 / 2) * (CD / CΔ) + 1728 * Cψ * Cz1)) * 3 ^ A :=
        mul_nonneg (mul_nonneg h3 h1.le) h2.le
      linarith
    · intro τ z hτ hz
      have hτhalf : (1:ℝ)/2 ≤ τ.im := by linarith [hτ.2]
      have hX0 : (0:ℝ) ≤ ‖(τ : ℂ)‖ := norm_nonneg _
      have hsc1 : (1:ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
      have hscpos : 0 < Work.Kernels.scale τ := Work.Kernels.scale_pos τ
      have hexp1 : (1:ℝ) ≤ Real.exp (Real.pi * z.im) := by
        rw [Real.one_le_exp_iff]; positivity
      have hexppos : 0 < Real.exp (Real.pi * z.im) := Real.exp_pos _
      have hexpnn : (0:ℝ) ≤ Real.exp (Real.pi * z.im) := hexppos.le
      have hq : ‖Work.Kernels.qParamFun τ‖ = Real.exp (-(2 * Real.pi * τ.im)) := norm_qParamFun τ
      have hqpos : 0 < ‖Work.Kernels.qParamFun τ‖ := by rw [hq]; exact Real.exp_pos _
      -- z-side estimates
      have hJ' : ‖Work.Kernels.E8Fun z * Work.Kernels.VFun z
            + Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)‖
          ≤ Cz1 * Real.exp (Real.pi * z.im) :=
        le_trans (hz1 z hz).1 (le_mul_of_one_le_right hCz1.le hexp1)
      have hE8V' : ‖Work.Kernels.E8Fun z * Work.Kernels.VFun z‖
          ≤ Cz1 * Real.exp (Real.pi * z.im) :=
        le_trans (hz1 z hz).2.1 (le_mul_of_one_le_right hCz1.le hexp1)
      have hE10LS' : ‖Work.Kernels.E10Fun z * ℓ.L_S z‖ ≤ Cz2 * Real.exp (Real.pi * z.im) :=
        le_trans (hz2 z hz).1 (le_mul_of_one_le_right hCz2.le hexp1)
      -- τ-side estimates
      have hE4τ : ‖Work.Kernels.E4Fun τ‖ ≤ 3 / 2 := hE4f τ hτ
      have hDτ : ‖Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
            - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ‖
          ≤ CD * Work.Kernels.scale τ ^ ND * ‖Work.Kernels.qParamFun τ‖ := hD τ hτ
      have hψ4 : ‖Work.Kernels.psi4 ℓ τ‖ ≤ Cψ * Work.Kernels.scale τ ^ Nψ := (hψ τ hτ).2
      have hΔden : CΔ * ‖Work.Kernels.qParamFun τ‖ ≤ ‖Work.Kernels.DeltaFun τ‖ := by
        rw [hq]; exact hΔlow τ hτ
      -- piece `A`
      have htA : ‖(-3456 : ℂ) * Work.Kernels.E4Fun τ * Work.Kernels.E10Fun z * ℓ.L_S z‖
          ≤ (3456 * (3 / 2) * Cz2) * Real.exp (Real.pi * z.im) := by
        rw [show (-3456 : ℂ) * Work.Kernels.E4Fun τ * Work.Kernels.E10Fun z * ℓ.L_S z
            = (-3456 : ℂ) * Work.Kernels.E4Fun τ * (Work.Kernels.E10Fun z * ℓ.L_S z) by ring]
        have h := nmul3 (a := (-3456 : ℂ)) (b := Work.Kernels.E4Fun τ)
          (c := Work.Kernels.E10Fun z * ℓ.L_S z) (A := (3456:ℝ)) (B := (3/2:ℝ))
          (C := Cz2 * Real.exp (Real.pi * z.im)) (by norm_num) (by norm_num) (by positivity)
          (by simp) hE4τ hE10LS'
        calc ‖(-3456 : ℂ) * Work.Kernels.E4Fun τ * (Work.Kernels.E10Fun z * ℓ.L_S z)‖
            ≤ 3456 * (3 / 2) * (Cz2 * Real.exp (Real.pi * z.im)) := h
          _ = (3456 * (3 / 2) * Cz2) * Real.exp (Real.pi * z.im) := by ring
      -- piece `B`
      have hfrac : ‖Work.Kernels.E4Fun τ
            * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
            / Work.Kernels.DeltaFun τ‖
          ≤ (3 / 2) * (CD / CΔ) * Work.Kernels.scale τ ^ ND := by
        rw [norm_div, norm_mul]
        have hdenpos : 0 < CΔ * ‖Work.Kernels.qParamFun τ‖ := mul_pos hCΔ hqpos
        have hΔpos : 0 < ‖Work.Kernels.DeltaFun τ‖ := lt_of_lt_of_le hdenpos hΔden
        have hnum : ‖Work.Kernels.E4Fun τ‖
            * ‖Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ‖
            ≤ (3 / 2) * (CD * Work.Kernels.scale τ ^ ND * ‖Work.Kernels.qParamFun τ‖) :=
          mul_le_mul hE4τ hDτ (norm_nonneg _) (by norm_num)
        have hinv : (‖Work.Kernels.DeltaFun τ‖)⁻¹ ≤ (CΔ * ‖Work.Kernels.qParamFun τ‖)⁻¹ :=
          inv_anti₀ hdenpos hΔden
        calc ‖Work.Kernels.E4Fun τ‖
              * ‖Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                  - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ‖ / ‖Work.Kernels.DeltaFun τ‖
            = (‖Work.Kernels.E4Fun τ‖
                * ‖Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                    - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ‖)
                * (‖Work.Kernels.DeltaFun τ‖)⁻¹ := by rw [div_eq_mul_inv]
          _ ≤ ((3 / 2) * (CD * Work.Kernels.scale τ ^ ND * ‖Work.Kernels.qParamFun τ‖))
                * (CΔ * ‖Work.Kernels.qParamFun τ‖)⁻¹ :=
              mul_le_mul hnum hinv (inv_nonneg.mpr hΔpos.le) (by positivity)
          _ = (3 / 2) * (CD / CΔ) * Work.Kernels.scale τ ^ ND := by
              field_simp
      have htB : ‖(Work.Kernels.E8Fun z * Work.Kernels.VFun z
              + Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2))
            * (Work.Kernels.E4Fun τ
                * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                    - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ) / Work.Kernels.DeltaFun τ)‖
          ≤ (Cz1 * (3 / 2) * (CD / CΔ)) * Work.Kernels.scale τ ^ ND
              * Real.exp (Real.pi * z.im) := by
        have h := nmul2 (a := Work.Kernels.E8Fun z * Work.Kernels.VFun z
              + Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2))
          (b := Work.Kernels.E4Fun τ
              * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                  - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ) / Work.Kernels.DeltaFun τ)
          (A := Cz1 * Real.exp (Real.pi * z.im))
          (B := (3 / 2) * (CD / CΔ) * Work.Kernels.scale τ ^ ND)
          (by positivity) (by positivity) hJ' hfrac
        calc ‖(Work.Kernels.E8Fun z * Work.Kernels.VFun z
                + Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2))
              * (Work.Kernels.E4Fun τ
                  * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                      - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ) / Work.Kernels.DeltaFun τ)‖
            ≤ (Cz1 * Real.exp (Real.pi * z.im))
                * ((3 / 2) * (CD / CΔ) * Work.Kernels.scale τ ^ ND) := h
          _ = (Cz1 * (3 / 2) * (CD / CΔ)) * Work.Kernels.scale τ ^ ND
                * Real.exp (Real.pi * z.im) := by ring
      -- piece `C`
      have htC : ‖(-1728 : ℂ) * Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun z * Work.Kernels.VFun z‖
          ≤ (1728 * Cψ * Cz1) * Work.Kernels.scale τ ^ Nψ * Real.exp (Real.pi * z.im) := by
        rw [show (-1728 : ℂ) * Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun z * Work.Kernels.VFun z
            = (-1728 : ℂ) * Work.Kernels.psi4 ℓ τ
                * (Work.Kernels.E8Fun z * Work.Kernels.VFun z) by ring]
        have h := nmul3 (a := (-1728 : ℂ)) (b := Work.Kernels.psi4 ℓ τ)
          (c := Work.Kernels.E8Fun z * Work.Kernels.VFun z) (A := (1728:ℝ))
          (B := Cψ * Work.Kernels.scale τ ^ Nψ) (C := Cz1 * Real.exp (Real.pi * z.im))
          (by norm_num) (by positivity) (by positivity) (by simp) hψ4 hE8V'
        calc ‖(-1728 : ℂ) * Work.Kernels.psi4 ℓ τ * (Work.Kernels.E8Fun z * Work.Kernels.VFun z)‖
            ≤ 1728 * (Cψ * Work.Kernels.scale τ ^ Nψ) * (Cz1 * Real.exp (Real.pi * z.im)) := h
          _ = (1728 * Cψ * Cz1) * Work.Kernels.scale τ ^ Nψ * Real.exp (Real.pi * z.im) := by ring
      -- assemble
      have hT8 : ‖T8 ℓ τ z‖
          ≤ (3456 * (3 / 2) * Cz2 + (Cz1 * (3 / 2) * (CD / CΔ) + 1728 * Cψ * Cz1))
              * Work.Kernels.scale τ ^ A * Real.exp (Real.pi * z.im) := by
        rw [T8_cancelled ℓ τ z]
        have hscND : Work.Kernels.scale τ ^ ND ≤ Work.Kernels.scale τ ^ A :=
          Real.rpow_le_rpow_of_exponent_le hsc1 (by rw [hAdef]; exact le_max_left _ _)
        have hscNψ : Work.Kernels.scale τ ^ Nψ ≤ Work.Kernels.scale τ ^ A :=
          Real.rpow_le_rpow_of_exponent_le hsc1 (by rw [hAdef]; exact le_max_right _ _)
        have htA' : ‖(-3456 : ℂ) * Work.Kernels.E4Fun τ * Work.Kernels.E10Fun z * ℓ.L_S z‖
            ≤ (3456 * (3 / 2) * Cz2) * Work.Kernels.scale τ ^ A * Real.exp (Real.pi * z.im) := by
          have h1 : (1:ℝ) ≤ Work.Kernels.scale τ ^ A := Real.one_le_rpow hsc1 hA0
          have h2 : (3456 * (3 / 2) * Cz2) * Real.exp (Real.pi * z.im)
              ≤ (3456 * (3 / 2) * Cz2) * Work.Kernels.scale τ ^ A
                * Real.exp (Real.pi * z.im) := by
            apply mul_le_mul_of_nonneg_right _ hexpnn
            exact le_mul_of_one_le_right (by positivity) h1
          linarith [htA, h2]
        have htB' : ‖(Work.Kernels.E8Fun z * Work.Kernels.VFun z
              + Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2))
            * (Work.Kernels.E4Fun τ
                * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                    - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ) / Work.Kernels.DeltaFun τ)‖
            ≤ (Cz1 * (3 / 2) * (CD / CΔ)) * Work.Kernels.scale τ ^ A
                * Real.exp (Real.pi * z.im) := by
          have h1 : (0:ℝ) ≤ Cz1 * (3 / 2) * (CD / CΔ) := by positivity
          have h2 : (Cz1 * (3 / 2) * (CD / CΔ)) * Work.Kernels.scale τ ^ ND
                * Real.exp (Real.pi * z.im)
              ≤ (Cz1 * (3 / 2) * (CD / CΔ)) * Work.Kernels.scale τ ^ A
                * Real.exp (Real.pi * z.im) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscND h1) hexpnn
          linarith [htB, h2]
        have htC' : ‖(-1728 : ℂ) * Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun z
              * Work.Kernels.VFun z‖
            ≤ (1728 * Cψ * Cz1) * Work.Kernels.scale τ ^ A * Real.exp (Real.pi * z.im) := by
          have h1 : (0:ℝ) ≤ 1728 * Cψ * Cz1 := by positivity
          have h2 : (1728 * Cψ * Cz1) * Work.Kernels.scale τ ^ Nψ * Real.exp (Real.pi * z.im)
              ≤ (1728 * Cψ * Cz1) * Work.Kernels.scale τ ^ A * Real.exp (Real.pi * z.im) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscNψ h1) hexpnn
          linarith [htC, h2]
        have htri : ‖(-3456 : ℂ) * Work.Kernels.E4Fun τ * Work.Kernels.E10Fun z * ℓ.L_S z
              + (Work.Kernels.E8Fun z * Work.Kernels.VFun z
                  + Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2))
                * (Work.Kernels.E4Fun τ
                    * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                        - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ) / Work.Kernels.DeltaFun τ)
              + (-1728 : ℂ) * Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun z * Work.Kernels.VFun z‖
            ≤ ‖(-3456 : ℂ) * Work.Kernels.E4Fun τ * Work.Kernels.E10Fun z * ℓ.L_S z‖
              + ‖(Work.Kernels.E8Fun z * Work.Kernels.VFun z
                  + Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2))
                * (Work.Kernels.E4Fun τ
                    * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                        - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ) / Work.Kernels.DeltaFun τ)‖
              + ‖(-1728 : ℂ) * Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun z * Work.Kernels.VFun z‖ := by
          have e1 := norm_add_le ((-3456 : ℂ) * Work.Kernels.E4Fun τ * Work.Kernels.E10Fun z * ℓ.L_S z
                + (Work.Kernels.E8Fun z * Work.Kernels.VFun z
                    + Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2))
                  * (Work.Kernels.E4Fun τ
                      * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                          - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ) / Work.Kernels.DeltaFun τ))
            ((-1728 : ℂ) * Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun z * Work.Kernels.VFun z)
          have e2 := norm_add_le ((-3456 : ℂ) * Work.Kernels.E4Fun τ * Work.Kernels.E10Fun z * ℓ.L_S z)
            ((Work.Kernels.E8Fun z * Work.Kernels.VFun z
                + Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2))
              * (Work.Kernels.E4Fun τ
                  * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                      - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ) / Work.Kernels.DeltaFun τ))
          linarith [e1, e2]
        have hsum : (3456 * (3 / 2) * Cz2) * Work.Kernels.scale τ ^ A * Real.exp (Real.pi * z.im)
              + (Cz1 * (3 / 2) * (CD / CΔ)) * Work.Kernels.scale τ ^ A * Real.exp (Real.pi * z.im)
              + (1728 * Cψ * Cz1) * Work.Kernels.scale τ ^ A * Real.exp (Real.pi * z.im)
            = (3456 * (3 / 2) * Cz2 + (Cz1 * (3 / 2) * (CD / CΔ) + 1728 * Cψ * Cz1))
                * Work.Kernels.scale τ ^ A * Real.exp (Real.pi * z.im) := by ring
        have hfin : ‖(-3456 : ℂ) * Work.Kernels.E4Fun τ * Work.Kernels.E10Fun z * ℓ.L_S z
              + (Work.Kernels.E8Fun z * Work.Kernels.VFun z
                  + Work.Kernels.E6Fun z * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2))
                * (Work.Kernels.E4Fun τ
                    * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                        - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ) / Work.Kernels.DeltaFun τ)
              + (-1728 : ℂ) * Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun z * Work.Kernels.VFun z‖
            ≤ (3456 * (3 / 2) * Cz2) * Work.Kernels.scale τ ^ A * Real.exp (Real.pi * z.im)
              + (Cz1 * (3 / 2) * (CD / CΔ)) * Work.Kernels.scale τ ^ A * Real.exp (Real.pi * z.im)
              + (1728 * Cψ * Cz1) * Work.Kernels.scale τ ^ A * Real.exp (Real.pi * z.im) := by
          linarith [htri, htA', htB', htC']
        linarith [hfin, hsum]
      calc ‖Ncusp ℓ 8 τ z‖
          = ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹ * T8 ℓ τ z‖ := by
            rw [Ncusp_eight_expansion ℓ τ z]
        _ ≤ ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * ‖T8 ℓ τ z‖ :=
            norm_mul_le _ _
        _ ≤ ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖
              * ((3456 * (3 / 2) * Cz2 + (Cz1 * (3 / 2) * (CD / CΔ) + 1728 * Cψ * Cz1))
                  * Work.Kernels.scale τ ^ A * Real.exp (Real.pi * z.im)) :=
            mul_le_mul_of_nonneg_left hT8 (norm_nonneg _)
        _ ≤ ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖
              * ((3456 * (3 / 2) * Cz2 + (Cz1 * (3 / 2) * (CD / CΔ) + 1728 * Cψ * Cz1))
                  * ((3:ℝ) ^ A * (1 + ‖(τ : ℂ)‖) ^ A) * Real.exp (Real.pi * z.im)) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            have hK : 0 < 3456 * (3 / 2) * Cz2 + (Cz1 * (3 / 2) * (CD / CΔ) + 1728 * Cψ * Cz1) := by
              positivity
            have hle : Work.Kernels.scale τ ^ A ≤ (3:ℝ) ^ A * (1 + ‖(τ : ℂ)‖) ^ A := by
              rw [← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) (by positivity : (0:ℝ) ≤ 1 + ‖(τ : ℂ)‖)]
              exact Real.rpow_le_rpow hscpos.le (scale_le_three τ hτhalf) hA0
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hK.le) hexpnn
        _ = ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖
              * (3456 * (3 / 2) * Cz2 + (Cz1 * (3 / 2) * (CD / CΔ) + 1728 * Cψ * Cz1))
              * (3:ℝ) ^ A * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (Real.pi * z.im) := by ring
        _ ≤ (‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖
              * (3456 * (3 / 2) * Cz2 + (Cz1 * (3 / 2) * (CD / CΔ) + 1728 * Cψ * Cz1))
              * (3:ℝ) ^ A + 1) * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (Real.pi * z.im) := by
            have h1 : (1:ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ A := Real.one_le_rpow (by linarith) hA0
            have h0 : (0:ℝ) ≤ ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖
                * (3456 * (3 / 2) * Cz2 + (Cz1 * (3 / 2) * (CD / CΔ) + 1728 * Cψ * Cz1))
                * (3:ℝ) ^ A := by positivity
            have h2 : (0:ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ A := Real.rpow_nonneg (by linarith) A
            nlinarith [h1, h0, h2, hexpnn,
              mul_nonneg h0 (mul_nonneg h2 hexpnn)]
  · -- ## `d = 24`
    set A : ℝ := max ND Nψ with hAdef
    have hA0 : 0 ≤ A := by rw [hAdef]; exact le_trans hND (le_max_left _ _)
    refine ⟨‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ *
        (3456 * 2 * Cz2 + (3456 * (27 / 8) * Cz1 + 3456 * 2 * Cz1
            + 2 * CD * (27 / 4) * Cz1 + 2 * CD * Cz1) + CD * (27 / 4) * Cz1
          + 1728 * (9 / 4) * Cψ * Cz1 + CD * Cz1) * 3 ^ A + 1,
      A, ?_, hA0, ?_⟩
    · have h1 : (0:ℝ) < 3456 * 2 * Cz2 + (3456 * (27 / 8) * Cz1 + 3456 * 2 * Cz1
            + 2 * CD * (27 / 4) * Cz1 + 2 * CD * Cz1) + CD * (27 / 4) * Cz1
          + 1728 * (9 / 4) * Cψ * Cz1 + CD * Cz1 := by positivity
      have h2 : (0:ℝ) < (3:ℝ) ^ A := Real.rpow_pos_of_pos (by norm_num) _
      have h3 : (0:ℝ) ≤ ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ := norm_nonneg _
      have h4 : (0:ℝ) ≤ ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖
          * (3456 * 2 * Cz2 + (3456 * (27 / 8) * Cz1 + 3456 * 2 * Cz1
              + 2 * CD * (27 / 4) * Cz1 + 2 * CD * Cz1) + CD * (27 / 4) * Cz1
            + 1728 * (9 / 4) * Cψ * Cz1 + CD * Cz1) * 3 ^ A :=
        mul_nonneg (mul_nonneg h3 h1.le) h2.le
      linarith
    · intro τ z hτ hz
      have hsc1 : (1:ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
      have hscpos : 0 < Work.Kernels.scale τ := Work.Kernels.scale_pos τ
      have hexp1 : (1:ℝ) ≤ Real.exp (Real.pi * z.im) := by
        rw [Real.one_le_exp_iff]; positivity
      have hexppos : 0 < Real.exp (Real.pi * z.im) := Real.exp_pos _
      have hexpnn : (0:ℝ) ≤ Real.exp (Real.pi * z.im) := hexppos.le
      have hq : ‖Work.Kernels.qParamFun τ‖ = Real.exp (-(2 * Real.pi * τ.im)) := norm_qParamFun τ
      have hq1 : ‖Work.Kernels.qParamFun τ‖ ≤ 1 := by
        rw [hq, Real.exp_le_one_iff]; nlinarith [Real.pi_pos, τ.im_pos]
      have hqexp : ‖Work.Kernels.qParamFun τ‖ * Real.exp (2 * Real.pi * τ.im) = 1 := by
        rw [hq, ← Real.exp_add, show -(2 * Real.pi * τ.im) + 2 * Real.pi * τ.im = 0 by ring,
          Real.exp_zero]
      -- z-side estimates
      have hV' : ‖Work.Kernels.VFun z‖ ≤ Cz1 * Real.exp (Real.pi * z.im) :=
        le_trans (hz1 z hz).2.2.1 (le_mul_of_one_le_right hCz1.le hexp1)
      have hjV' : ‖Work.Kernels.jInvariantFun z * Work.Kernels.VFun z‖
          ≤ Cz1 * Real.exp (Real.pi * z.im) := (hz1 z hz).2.2.2.1
      have hE10D2' : ‖Work.Kernels.E10Fun z / Work.Kernels.DeltaFun z
            * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)‖
          ≤ Cz1 * Real.exp (Real.pi * z.im) := (hz1 z hz).2.2.2.2
      have hLS2' : ‖Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z * ℓ.L_S z‖
          ≤ Cz2 * Real.exp (Real.pi * z.im) := (hz2 z hz).2
      -- τ-side estimates
      have hΔ2 : ‖Work.Kernels.DeltaFun τ‖ ≤ 2 := by
        have h := hΔuf τ hτ
        have hqnn : (0:ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
        nlinarith [h, hq1, hqnn]
      have hE4τ : ‖Work.Kernels.E4Fun τ‖ ≤ 3 / 2 := hE4f τ hτ
      have hE8τ : ‖Work.Kernels.E8Fun τ‖ ≤ 9 / 4 := hE8f τ hτ
      have hjτ : ‖Work.Kernels.jInvariantFun τ‖ ≤ (27 / 4) * Real.exp (2 * Real.pi * τ.im) := hjf τ hτ
      have hDτ : ‖Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
            - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ‖
          ≤ CD * Work.Kernels.scale τ ^ ND * ‖Work.Kernels.qParamFun τ‖ := hD τ hτ
      have hψ4 : ‖Work.Kernels.psi4 ℓ τ‖ ≤ Cψ * Work.Kernels.scale τ ^ Nψ := (hψ τ hτ).2
      have hDτ' : ‖Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
            - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ‖
          ≤ CD * Work.Kernels.scale τ ^ ND :=
        le_trans hDτ (mul_le_of_le_one_right (by positivity) hq1)
      have hΔj : ‖Work.Kernels.DeltaFun τ * Work.Kernels.jInvariantFun τ‖ ≤ 27 / 8 := by
        rw [Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun, norm_pow]
        calc ‖Work.Kernels.E4Fun τ‖ ^ 3 ≤ ((3:ℝ) / 2) ^ 3 :=
              pow_le_pow_left₀ (norm_nonneg _) hE4τ 3
          _ = 27 / 8 := by norm_num
      have hDj : ‖(Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
            - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
            * Work.Kernels.jInvariantFun τ‖ ≤ CD * (27 / 4) * Work.Kernels.scale τ ^ ND := by
        rw [norm_mul]
        have h1 : ‖Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
              - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ‖
              * ‖Work.Kernels.jInvariantFun τ‖
            ≤ (CD * Work.Kernels.scale τ ^ ND * ‖Work.Kernels.qParamFun τ‖)
              * ((27 / 4) * Real.exp (2 * Real.pi * τ.im)) :=
          mul_le_mul hDτ hjτ (norm_nonneg _) (by positivity)
        refine le_trans h1 (le_of_eq ?_)
        rw [show CD * Work.Kernels.scale τ ^ ND * ‖Work.Kernels.qParamFun τ‖
              * ((27 / 4) * Real.exp (2 * Real.pi * τ.im))
            = CD * (27 / 4) * Work.Kernels.scale τ ^ ND
              * (‖Work.Kernels.qParamFun τ‖ * Real.exp (2 * Real.pi * τ.im)) by ring,
          hqexp, mul_one]
      have hE8τV : ‖Work.Kernels.E8Fun τ * Work.Kernels.VFun z‖
          ≤ (9 / 4) * (Cz1 * Real.exp (Real.pi * z.im)) :=
        nmul2 (by norm_num) (by positivity) hE8τ hV'
      -- the eight pieces
      have hsA : ‖(-3456 : ℂ) * Work.Kernels.DeltaFun τ
            * (Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z) * ℓ.L_S z‖
          ≤ (3456 * 2 * Cz2) * Real.exp (Real.pi * z.im) := by
        rw [show (-3456 : ℂ) * Work.Kernels.DeltaFun τ
              * (Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z) * ℓ.L_S z
            = (-3456 : ℂ) * Work.Kernels.DeltaFun τ
              * ((Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z) * ℓ.L_S z) by ring]
        refine le_trans (nmul3 (a := (-3456 : ℂ)) (b := Work.Kernels.DeltaFun τ)
          (c := (Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z) * ℓ.L_S z)
          (A := (3456:ℝ)) (B := (2:ℝ)) (C := Cz2 * Real.exp (Real.pi * z.im))
          (by norm_num) (by norm_num) (by positivity) (by simp) hΔ2 hLS2') ?_
        exact le_of_eq (by ring)
      have ht1 : ‖(3456 : ℂ) * (Work.Kernels.DeltaFun τ * Work.Kernels.jInvariantFun τ)
            * Work.Kernels.VFun z‖ ≤ (3456 * (27 / 8) * Cz1) * Real.exp (Real.pi * z.im) := by
        refine le_trans (nmul3 (a := (3456 : ℂ))
          (b := Work.Kernels.DeltaFun τ * Work.Kernels.jInvariantFun τ)
          (c := Work.Kernels.VFun z) (A := (3456:ℝ)) (B := (27/8:ℝ))
          (C := Cz1 * Real.exp (Real.pi * z.im)) (by norm_num) (by norm_num) (by positivity)
          (by simp) hΔj hV') ?_
        exact le_of_eq (by ring)
      have ht2 : ‖(-3456 : ℂ) * Work.Kernels.DeltaFun τ
            * (Work.Kernels.jInvariantFun z * Work.Kernels.VFun z)‖
          ≤ (3456 * 2 * Cz1) * Real.exp (Real.pi * z.im) := by
        refine le_trans (nmul3 (a := (-3456 : ℂ)) (b := Work.Kernels.DeltaFun τ)
          (c := Work.Kernels.jInvariantFun z * Work.Kernels.VFun z) (A := (3456:ℝ))
          (B := (2:ℝ)) (C := Cz1 * Real.exp (Real.pi * z.im)) (by norm_num) (by norm_num)
          (by positivity) (by simp) hΔ2 hjV') ?_
        exact le_of_eq (by ring)
      have ht3 : ‖(2 : ℂ) * ((Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
              - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
            * Work.Kernels.jInvariantFun τ) * Work.Kernels.VFun z‖
          ≤ (2 * CD * (27 / 4) * Cz1) * Work.Kernels.scale τ ^ ND
            * Real.exp (Real.pi * z.im) := by
        refine le_trans (nmul3 (a := (2 : ℂ)) (b := (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
              - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
            * Work.Kernels.jInvariantFun τ) (c := Work.Kernels.VFun z) (A := (2:ℝ))
          (B := CD * (27 / 4) * Work.Kernels.scale τ ^ ND)
          (C := Cz1 * Real.exp (Real.pi * z.im)) (by norm_num) (by positivity) (by positivity)
          (by simp) hDj hV') ?_
        exact le_of_eq (by ring)
      have ht4 : ‖(-2 : ℂ) * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
              - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
            * (Work.Kernels.jInvariantFun z * Work.Kernels.VFun z)‖
          ≤ (2 * CD * Cz1) * Work.Kernels.scale τ ^ ND * Real.exp (Real.pi * z.im) := by
        refine le_trans (nmul3 (a := (-2 : ℂ)) (b := (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
              - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ))
          (c := Work.Kernels.jInvariantFun z * Work.Kernels.VFun z) (A := (2:ℝ))
          (B := CD * Work.Kernels.scale τ ^ ND) (C := Cz1 * Real.exp (Real.pi * z.im))
          (by norm_num) (by positivity) (by positivity) (by simp) hDτ' hjV') ?_
        exact le_of_eq (by ring)
      have hsC : ‖(Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
              - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
            * Work.Kernels.jInvariantFun τ * Work.Kernels.VFun z‖
          ≤ (CD * (27 / 4) * Cz1) * Work.Kernels.scale τ ^ ND * Real.exp (Real.pi * z.im) := by
        refine le_trans (nmul2 (a := (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
              - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ) * Work.Kernels.jInvariantFun τ)
          (b := Work.Kernels.VFun z) (A := CD * (27 / 4) * Work.Kernels.scale τ ^ ND)
          (B := Cz1 * Real.exp (Real.pi * z.im)) (by positivity) (by positivity) hDj hV') ?_
        exact le_of_eq (by ring)
      have hsD : ‖(-1728 : ℂ) * Work.Kernels.psi4 ℓ τ
            * (Work.Kernels.E8Fun τ * Work.Kernels.VFun z)‖
          ≤ (1728 * (9 / 4) * Cψ * Cz1) * Work.Kernels.scale τ ^ Nψ
            * Real.exp (Real.pi * z.im) := by
        refine le_trans (nmul3 (a := (-1728 : ℂ)) (b := Work.Kernels.psi4 ℓ τ)
          (c := Work.Kernels.E8Fun τ * Work.Kernels.VFun z) (A := (1728:ℝ))
          (B := Cψ * Work.Kernels.scale τ ^ Nψ)
          (C := (9 / 4) * (Cz1 * Real.exp (Real.pi * z.im))) (by norm_num) (by positivity)
          (by positivity) (by simp) hψ4 hE8τV) ?_
        exact le_of_eq (by ring)
      have hsE : ‖(Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
              - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
            * (Work.Kernels.E10Fun z / Work.Kernels.DeltaFun z)
            * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)‖
          ≤ (CD * Cz1) * Work.Kernels.scale τ ^ ND * Real.exp (Real.pi * z.im) := by
        rw [show (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
              - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
            * (Work.Kernels.E10Fun z / Work.Kernels.DeltaFun z)
            * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)
            = (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
              - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
              * ((Work.Kernels.E10Fun z / Work.Kernels.DeltaFun z)
                * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)) by ring]
        refine le_trans (nmul2 (a := Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
              - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
          (b := (Work.Kernels.E10Fun z / Work.Kernels.DeltaFun z)
              * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2))
          (A := CD * Work.Kernels.scale τ ^ ND) (B := Cz1 * Real.exp (Real.pi * z.im))
          (by positivity) (by positivity) hDτ' hE10D2') ?_
        exact le_of_eq (by ring)
      -- assemble
      have hT24 : ‖T24 ℓ τ z‖
          ≤ (3456 * 2 * Cz2 + (3456 * (27 / 8) * Cz1 + 3456 * 2 * Cz1
              + 2 * CD * (27 / 4) * Cz1 + 2 * CD * Cz1) + CD * (27 / 4) * Cz1
            + 1728 * (9 / 4) * Cψ * Cz1 + CD * Cz1)
              * Work.Kernels.scale τ ^ A * Real.exp (Real.pi * z.im) := by
        rw [T24_cancelled ℓ τ z]
        have hscND : Work.Kernels.scale τ ^ ND ≤ Work.Kernels.scale τ ^ A :=
          Real.rpow_le_rpow_of_exponent_le hsc1 (by rw [hAdef]; exact le_max_left _ _)
        have hscNψ : Work.Kernels.scale τ ^ Nψ ≤ Work.Kernels.scale τ ^ A :=
          Real.rpow_le_rpow_of_exponent_le hsc1 (by rw [hAdef]; exact le_max_right _ _)
        have hsBexp : (3456 * Work.Kernels.DeltaFun τ
              + 2 * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                  - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ))
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) * Work.Kernels.VFun z
            = (3456 : ℂ) * (Work.Kernels.DeltaFun τ * Work.Kernels.jInvariantFun τ)
                * Work.Kernels.VFun z
              + (-3456 : ℂ) * Work.Kernels.DeltaFun τ
                * (Work.Kernels.jInvariantFun z * Work.Kernels.VFun z)
              + (2 : ℂ) * ((Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                  - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
                * Work.Kernels.jInvariantFun τ) * Work.Kernels.VFun z
              + (-2 : ℂ) * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                  - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
                * (Work.Kernels.jInvariantFun z * Work.Kernels.VFun z) := by ring
        rw [hsBexp]
        -- upgrade the scale powers to `A`
        have hsA' : ‖(-3456 : ℂ) * Work.Kernels.DeltaFun τ
              * (Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z) * ℓ.L_S z‖
            ≤ (3456 * 2 * Cz2) * Work.Kernels.scale τ ^ A * Real.exp (Real.pi * z.im) := by
          have h1 : (1:ℝ) ≤ Work.Kernels.scale τ ^ A := Real.one_le_rpow hsc1 hA0
          have h2 : (3456 * 2 * Cz2) * Real.exp (Real.pi * z.im)
              ≤ (3456 * 2 * Cz2) * Work.Kernels.scale τ ^ A * Real.exp (Real.pi * z.im) := by
            apply mul_le_mul_of_nonneg_right _ hexpnn
            exact le_mul_of_one_le_right (by positivity) h1
          linarith [hsA, h2]
        have ht1' : ‖(3456 : ℂ) * (Work.Kernels.DeltaFun τ * Work.Kernels.jInvariantFun τ)
              * Work.Kernels.VFun z‖
            ≤ (3456 * (27 / 8) * Cz1) * Work.Kernels.scale τ ^ A * Real.exp (Real.pi * z.im) := by
          have h1 : (1:ℝ) ≤ Work.Kernels.scale τ ^ A := Real.one_le_rpow hsc1 hA0
          have h2 : (3456 * (27 / 8) * Cz1) * Real.exp (Real.pi * z.im)
              ≤ (3456 * (27 / 8) * Cz1) * Work.Kernels.scale τ ^ A * Real.exp (Real.pi * z.im) := by
            apply mul_le_mul_of_nonneg_right _ hexpnn
            exact le_mul_of_one_le_right (by positivity) h1
          linarith [ht1, h2]
        have ht2' : ‖(-3456 : ℂ) * Work.Kernels.DeltaFun τ
              * (Work.Kernels.jInvariantFun z * Work.Kernels.VFun z)‖
            ≤ (3456 * 2 * Cz1) * Work.Kernels.scale τ ^ A * Real.exp (Real.pi * z.im) := by
          have h1 : (1:ℝ) ≤ Work.Kernels.scale τ ^ A := Real.one_le_rpow hsc1 hA0
          have h2 : (3456 * 2 * Cz1) * Real.exp (Real.pi * z.im)
              ≤ (3456 * 2 * Cz1) * Work.Kernels.scale τ ^ A * Real.exp (Real.pi * z.im) := by
            apply mul_le_mul_of_nonneg_right _ hexpnn
            exact le_mul_of_one_le_right (by positivity) h1
          linarith [ht2, h2]
        have ht3' : ‖(2 : ℂ) * ((Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
              * Work.Kernels.jInvariantFun τ) * Work.Kernels.VFun z‖
            ≤ (2 * CD * (27 / 4) * Cz1) * Work.Kernels.scale τ ^ A
              * Real.exp (Real.pi * z.im) := by
          have h1 : (0:ℝ) ≤ 2 * CD * (27 / 4) * Cz1 := by positivity
          have h2 : (2 * CD * (27 / 4) * Cz1) * Work.Kernels.scale τ ^ ND
                * Real.exp (Real.pi * z.im)
              ≤ (2 * CD * (27 / 4) * Cz1) * Work.Kernels.scale τ ^ A
                * Real.exp (Real.pi * z.im) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscND h1) hexpnn
          linarith [ht3, h2]
        have ht4' : ‖(-2 : ℂ) * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
              * (Work.Kernels.jInvariantFun z * Work.Kernels.VFun z)‖
            ≤ (2 * CD * Cz1) * Work.Kernels.scale τ ^ A * Real.exp (Real.pi * z.im) := by
          have h1 : (0:ℝ) ≤ 2 * CD * Cz1 := by positivity
          have h2 : (2 * CD * Cz1) * Work.Kernels.scale τ ^ ND * Real.exp (Real.pi * z.im)
              ≤ (2 * CD * Cz1) * Work.Kernels.scale τ ^ A * Real.exp (Real.pi * z.im) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscND h1) hexpnn
          linarith [ht4, h2]
        have hsC' : ‖(Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
              * Work.Kernels.jInvariantFun τ * Work.Kernels.VFun z‖
            ≤ (CD * (27 / 4) * Cz1) * Work.Kernels.scale τ ^ A * Real.exp (Real.pi * z.im) := by
          have h1 : (0:ℝ) ≤ CD * (27 / 4) * Cz1 := by positivity
          have h2 : (CD * (27 / 4) * Cz1) * Work.Kernels.scale τ ^ ND * Real.exp (Real.pi * z.im)
              ≤ (CD * (27 / 4) * Cz1) * Work.Kernels.scale τ ^ A * Real.exp (Real.pi * z.im) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscND h1) hexpnn
          linarith [hsC, h2]
        have hsD' : ‖(-1728 : ℂ) * Work.Kernels.psi4 ℓ τ
              * (Work.Kernels.E8Fun τ * Work.Kernels.VFun z)‖
            ≤ (1728 * (9 / 4) * Cψ * Cz1) * Work.Kernels.scale τ ^ A
              * Real.exp (Real.pi * z.im) := by
          have h1 : (0:ℝ) ≤ 1728 * (9 / 4) * Cψ * Cz1 := by positivity
          have h2 : (1728 * (9 / 4) * Cψ * Cz1) * Work.Kernels.scale τ ^ Nψ
                * Real.exp (Real.pi * z.im)
              ≤ (1728 * (9 / 4) * Cψ * Cz1) * Work.Kernels.scale τ ^ A
                * Real.exp (Real.pi * z.im) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscNψ h1) hexpnn
          linarith [hsD, h2]
        have hsE' : ‖(Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
              * (Work.Kernels.E10Fun z / Work.Kernels.DeltaFun z)
              * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2)‖
            ≤ (CD * Cz1) * Work.Kernels.scale τ ^ A * Real.exp (Real.pi * z.im) := by
          have h1 : (0:ℝ) ≤ CD * Cz1 := by positivity
          have h2 : (CD * Cz1) * Work.Kernels.scale τ ^ ND * Real.exp (Real.pi * z.im)
              ≤ (CD * Cz1) * Work.Kernels.scale τ ^ A * Real.exp (Real.pi * z.im) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscND h1) hexpnn
          linarith [hsE, h2]
        -- triangle inequalities
        have houter := norm_add5_le
          ((-3456 : ℂ) * Work.Kernels.DeltaFun τ
            * (Work.Kernels.E14Fun z / Work.Kernels.DeltaFun z) * ℓ.L_S z)
          ((3456 : ℂ) * (Work.Kernels.DeltaFun τ * Work.Kernels.jInvariantFun τ)
              * Work.Kernels.VFun z
            + (-3456 : ℂ) * Work.Kernels.DeltaFun τ
              * (Work.Kernels.jInvariantFun z * Work.Kernels.VFun z)
            + (2 : ℂ) * ((Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
              * Work.Kernels.jInvariantFun τ) * Work.Kernels.VFun z
            + (-2 : ℂ) * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
              * (Work.Kernels.jInvariantFun z * Work.Kernels.VFun z))
          ((Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
              - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
            * Work.Kernels.jInvariantFun τ * Work.Kernels.VFun z)
          ((-1728 : ℂ) * Work.Kernels.psi4 ℓ τ
            * (Work.Kernels.E8Fun τ * Work.Kernels.VFun z))
          ((Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
              - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
            * (Work.Kernels.E10Fun z / Work.Kernels.DeltaFun z)
            * (Work.Kernels.UFun z ^ 2 - Work.Kernels.WFun z ^ 2))
        have hinner := norm_add4_le
          ((3456 : ℂ) * (Work.Kernels.DeltaFun τ * Work.Kernels.jInvariantFun τ)
              * Work.Kernels.VFun z)
          ((-3456 : ℂ) * Work.Kernels.DeltaFun τ
            * (Work.Kernels.jInvariantFun z * Work.Kernels.VFun z))
          ((2 : ℂ) * ((Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
              - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
            * Work.Kernels.jInvariantFun τ) * Work.Kernels.VFun z)
          ((-2 : ℂ) * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
              - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
            * (Work.Kernels.jInvariantFun z * Work.Kernels.VFun z))
        have hsum : (3456 * 2 * Cz2) * Work.Kernels.scale τ ^ A * Real.exp (Real.pi * z.im)
              + ((3456 * (27 / 8) * Cz1) * Work.Kernels.scale τ ^ A
                  * Real.exp (Real.pi * z.im)
                + (3456 * 2 * Cz1) * Work.Kernels.scale τ ^ A * Real.exp (Real.pi * z.im)
                + (2 * CD * (27 / 4) * Cz1) * Work.Kernels.scale τ ^ A
                  * Real.exp (Real.pi * z.im)
                + (2 * CD * Cz1) * Work.Kernels.scale τ ^ A * Real.exp (Real.pi * z.im))
              + (CD * (27 / 4) * Cz1) * Work.Kernels.scale τ ^ A * Real.exp (Real.pi * z.im)
              + (1728 * (9 / 4) * Cψ * Cz1) * Work.Kernels.scale τ ^ A * Real.exp (Real.pi * z.im)
              + (CD * Cz1) * Work.Kernels.scale τ ^ A * Real.exp (Real.pi * z.im)
            = (3456 * 2 * Cz2 + (3456 * (27 / 8) * Cz1 + 3456 * 2 * Cz1
                + 2 * CD * (27 / 4) * Cz1 + 2 * CD * Cz1) + CD * (27 / 4) * Cz1
              + 1728 * (9 / 4) * Cψ * Cz1 + CD * Cz1)
                * Work.Kernels.scale τ ^ A * Real.exp (Real.pi * z.im) := by ring
        have hB : ‖(3456 : ℂ) * (Work.Kernels.DeltaFun τ * Work.Kernels.jInvariantFun τ)
              * Work.Kernels.VFun z
            + (-3456 : ℂ) * Work.Kernels.DeltaFun τ
              * (Work.Kernels.jInvariantFun z * Work.Kernels.VFun z)
            + (2 : ℂ) * ((Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
              * Work.Kernels.jInvariantFun τ) * Work.Kernels.VFun z
            + (-2 : ℂ) * (Work.Kernels.psi4 ℓ τ * Work.Kernels.E8Fun τ
                - Work.Kernels.psi2 ℓ τ * Work.Kernels.E10Fun τ)
              * (Work.Kernels.jInvariantFun z * Work.Kernels.VFun z)‖
            ≤ (3456 * (27 / 8) * Cz1) * Work.Kernels.scale τ ^ A * Real.exp (Real.pi * z.im)
              + (3456 * 2 * Cz1) * Work.Kernels.scale τ ^ A * Real.exp (Real.pi * z.im)
              + (2 * CD * (27 / 4) * Cz1) * Work.Kernels.scale τ ^ A
                * Real.exp (Real.pi * z.im)
              + (2 * CD * Cz1) * Work.Kernels.scale τ ^ A * Real.exp (Real.pi * z.im) :=
          le_trans hinner (add_le_add (add_le_add (add_le_add ht1' ht2') ht3') ht4')
        have hmain := le_trans houter
          (add_le_add (add_le_add (add_le_add (add_le_add hsA' hB) hsC') hsD') hsE')
        rw [← hsum]
        exact hmain
      calc ‖Ncusp ℓ 24 τ z‖
          = ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹ * T24 ℓ τ z‖ := by
            rw [Ncusp_twentyfour_expansion ℓ τ z]
        _ ≤ ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖ * ‖T24 ℓ τ z‖ :=
            norm_mul_le _ _
        _ ≤ ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖
              * ((3456 * 2 * Cz2 + (3456 * (27 / 8) * Cz1 + 3456 * 2 * Cz1
                  + 2 * CD * (27 / 4) * Cz1 + 2 * CD * Cz1) + CD * (27 / 4) * Cz1
                + 1728 * (9 / 4) * Cψ * Cz1 + CD * Cz1)
                  * Work.Kernels.scale τ ^ A * Real.exp (Real.pi * z.im)) :=
            mul_le_mul_of_nonneg_left hT24 (norm_nonneg _)
        _ ≤ ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖
              * ((3456 * 2 * Cz2 + (3456 * (27 / 8) * Cz1 + 3456 * 2 * Cz1
                  + 2 * CD * (27 / 4) * Cz1 + 2 * CD * Cz1) + CD * (27 / 4) * Cz1
                + 1728 * (9 / 4) * Cψ * Cz1 + CD * Cz1)
                  * ((3:ℝ) ^ A * (1 + ‖(τ : ℂ)‖) ^ A) * Real.exp (Real.pi * z.im)) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            have hK : 0 < 3456 * 2 * Cz2 + (3456 * (27 / 8) * Cz1 + 3456 * 2 * Cz1
                + 2 * CD * (27 / 4) * Cz1 + 2 * CD * Cz1) + CD * (27 / 4) * Cz1
                + 1728 * (9 / 4) * Cψ * Cz1 + CD * Cz1 := by positivity
            have hle : Work.Kernels.scale τ ^ A ≤ (3:ℝ) ^ A * (1 + ‖(τ : ℂ)‖) ^ A := by
              rw [← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) (by positivity : (0:ℝ) ≤ 1 + ‖(τ : ℂ)‖)]
              exact Real.rpow_le_rpow hscpos.le (scale_le_three τ (by linarith [hτ.2])) hA0
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hK.le) hexpnn
        _ = ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖
              * (3456 * 2 * Cz2 + (3456 * (27 / 8) * Cz1 + 3456 * 2 * Cz1
                  + 2 * CD * (27 / 4) * Cz1 + 2 * CD * Cz1) + CD * (27 / 4) * Cz1
                + 1728 * (9 / 4) * Cψ * Cz1 + CD * Cz1)
              * (3:ℝ) ^ A * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (Real.pi * z.im) := by ring
        _ ≤ (‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖
              * (3456 * 2 * Cz2 + (3456 * (27 / 8) * Cz1 + 3456 * 2 * Cz1
                  + 2 * CD * (27 / 4) * Cz1 + 2 * CD * Cz1) + CD * (27 / 4) * Cz1
                + 1728 * (9 / 4) * Cψ * Cz1 + CD * Cz1)
              * (3:ℝ) ^ A + 1) * (1 + ‖(τ : ℂ)‖) ^ A * Real.exp (Real.pi * z.im) := by
            have h1 : (1:ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ A := Real.one_le_rpow (by linarith [norm_nonneg (τ : ℂ)]) hA0
            have h0 : (0:ℝ) ≤ ‖((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))⁻¹‖
                * (3456 * 2 * Cz2 + (3456 * (27 / 8) * Cz1 + 3456 * 2 * Cz1
                    + 2 * CD * (27 / 4) * Cz1 + 2 * CD * Cz1) + CD * (27 / 4) * Cz1
                  + 1728 * (9 / 4) * Cψ * Cz1 + CD * Cz1)
                * (3:ℝ) ^ A := by positivity
            have h2 : (0:ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ A := Real.rpow_nonneg (by positivity) A
            nlinarith [h1, h0, h2, hexpnn, mul_nonneg h0 (mul_nonneg h2 hexpnn)]

set_option maxHeartbeats 4000000 in
theorem KMinusFunnelSlash (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧
      ∀ (τ z : UpperHalfPlane), τ ∈ Work.Asymptotics.DomainD → 2 ≤ τ.im → 1 / 3 ≤ z.im →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z →
        ‖(z : ℂ) ^ ((d : ℤ) / 2 - 2) * Work.Kernels.KMinus ℓ d τ (ModularGroup.S • z)‖
          ≤ C * (1 + ‖(τ : ℂ)‖) ^ A * (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) * Real.exp (-(Real.pi * z.im))
            / ‖Work.Kernels.DeltaFun z * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)‖ := by
  obtain ⟨C0, A0, hC0, hA0, hcrude⟩ := Ncusp_funnel_crude ℓ d hd
  refine ⟨C0 * Real.exp (2 * Real.pi) + 1, A0, by positivity, hA0, fun τ z hD hτ2 hz hne => ?_⟩
  have hF : Funnel τ := ⟨hD, hτ2⟩
  have hzX : (1 : ℝ) ≤ (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) := by
    have := norm_nonneg (z : ℂ); nlinarith
  -- sharp decay of `Ncusp` on `Im z ≥ 1`
  have hsharp : ∀ z' : UpperHalfPlane, 1 ≤ z'.im →
      ‖Ncusp ℓ d τ z'‖ ≤ (C0 * (1 + ‖(τ : ℂ)‖) ^ A0 * Real.exp (2 * Real.pi))
        * Real.exp (-(Real.pi * z'.im)) := by
    intro z' hz'
    set B : ℝ := C0 * (1 + ‖(τ : ℂ)‖) ^ A0 with hB
    have hB0 : 0 ≤ B := by rw [hB]; positivity
    set g : UpperHalfPlane → ℂ := fun w => Ecusp w * Ncusp ℓ d τ w with hg
    have hperp : ∀ w : UpperHalfPlane, g ((1 : ℝ) +ᵥ w) = g w := by
      intro w; simp only [hg, Ecusp_vadd_one, Ncusp_vadd_one]; ring
    have hmd : MDiff g := by
      rw [hg]; exact (UpperHalfPlane.mdifferentiable_iff).mpr (mdiff_eta ℓ d τ)
    have hBg : ∀ w : UpperHalfPlane, 1 ≤ w.im → ‖g w‖ ≤ B := by
      intro w hw
      rw [hg, norm_mul, norm_Ecusp, hB]
      have h1 : ‖Ncusp ℓ d τ w‖ ≤ C0 * (1 + ‖(τ : ℂ)‖) ^ A0 * Real.exp (Real.pi * w.im) :=
        hcrude τ w hF (le_trans (by norm_num) hw)
      have h2 : Real.exp (-(Real.pi * w.im))
            * (C0 * (1 + ‖(τ : ℂ)‖) ^ A0 * Real.exp (Real.pi * w.im))
          = C0 * (1 + ‖(τ : ℂ)‖) ^ A0 := by
        rw [show Real.exp (-(Real.pi * w.im))
              * (C0 * (1 + ‖(τ : ℂ)‖) ^ A0 * Real.exp (Real.pi * w.im))
            = C0 * (1 + ‖(τ : ℂ)‖) ^ A0
              * (Real.exp (-(Real.pi * w.im)) * Real.exp (Real.pi * w.im)) by ring,
          ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
      calc Real.exp (-(Real.pi * w.im)) * ‖Ncusp ℓ d τ w‖
          ≤ Real.exp (-(Real.pi * w.im))
              * (C0 * (1 + ‖(τ : ℂ)‖) ^ A0 * Real.exp (Real.pi * w.im)) :=
            mul_le_mul_of_nonneg_left h1 (Real.exp_nonneg _)
        _ = C0 * (1 + ‖(τ : ℂ)‖) ^ A0 := h2
    have h := periodic_zero_cusp_decay_uhp hB0 hperp hmd hBg (KMinusCuspBallLimit ℓ d hd τ) z' hz'
    rw [hg, norm_mul, norm_Ecusp] at h
    have h1 : ‖Ncusp ℓ d τ z'‖ ≤ Real.exp (Real.pi * z'.im)
        * (B * Real.exp (2 * Real.pi) * Real.exp (-(2 * Real.pi * z'.im))) := by
      calc ‖Ncusp ℓ d τ z'‖
          = Real.exp (Real.pi * z'.im)
              * (Real.exp (-(Real.pi * z'.im)) * ‖Ncusp ℓ d τ z'‖) := by
            rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
        _ ≤ Real.exp (Real.pi * z'.im)
              * (B * Real.exp (2 * Real.pi) * Real.exp (-(2 * Real.pi * z'.im))) :=
            mul_le_mul_of_nonneg_left h (Real.exp_nonneg _)
    rw [hB] at h1
    calc ‖Ncusp ℓ d τ z'‖
        ≤ Real.exp (Real.pi * z'.im)
            * ((C0 * (1 + ‖(τ : ℂ)‖) ^ A0) * Real.exp (2 * Real.pi)
              * Real.exp (-(2 * Real.pi * z'.im))) := h1
      _ = (C0 * (1 + ‖(τ : ℂ)‖) ^ A0 * Real.exp (2 * Real.pi))
            * Real.exp (-(Real.pi * z'.im)) := by
          rw [show Real.exp (Real.pi * z'.im)
                * ((C0 * (1 + ‖(τ : ℂ)‖) ^ A0) * Real.exp (2 * Real.pi)
                  * Real.exp (-(2 * Real.pi * z'.im)))
              = C0 * (1 + ‖(τ : ℂ)‖) ^ A0 * Real.exp (2 * Real.pi)
                * (Real.exp (Real.pi * z'.im) * Real.exp (-(2 * Real.pi * z'.im))) by ring,
            ← Real.exp_add, show Real.pi * z'.im + -(2 * Real.pi * z'.im) = -(Real.pi * z'.im) by ring]
  -- the `Ncusp` bound with the `(1+‖z‖)^2` factor
  have hmain : ‖Ncusp ℓ d τ z‖ ≤ (C0 * Real.exp (2 * Real.pi) + 1)
      * (1 + ‖(τ : ℂ)‖) ^ A0 * (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) * Real.exp (-(Real.pi * z.im)) := by
    by_cases hz1 : (1:ℝ) ≤ z.im
    · have h := hsharp z hz1
      have hs : (0:ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ A0 := Real.rpow_nonneg (by positivity) A0
      calc ‖Ncusp ℓ d τ z‖
          ≤ (C0 * (1 + ‖(τ : ℂ)‖) ^ A0 * Real.exp (2 * Real.pi))
              * Real.exp (-(Real.pi * z.im)) := h
        _ = (C0 * Real.exp (2 * Real.pi) * (1 + ‖(τ : ℂ)‖) ^ A0)
              * Real.exp (-(Real.pi * z.im)) := by ring
        _ ≤ (C0 * Real.exp (2 * Real.pi) * (1 + ‖(τ : ℂ)‖) ^ A0)
              * ((1 + ‖(z : ℂ)‖) ^ (2 : ℕ)) * Real.exp (-(Real.pi * z.im)) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
            exact le_mul_of_one_le_right (by positivity) hzX
        _ ≤ ((C0 * Real.exp (2 * Real.pi) + 1) * (1 + ‖(τ : ℂ)‖) ^ A0)
              * (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) * Real.exp (-(Real.pi * z.im)) := by
            refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
            have h1 : C0 * Real.exp (2 * Real.pi) * (1 + ‖(τ : ℂ)‖) ^ A0
                ≤ (C0 * Real.exp (2 * Real.pi) + 1) * (1 + ‖(τ : ℂ)‖) ^ A0 :=
              mul_le_mul_of_nonneg_right (by linarith) hs
            exact mul_le_mul_of_nonneg_right h1 (by positivity)
        _ = (C0 * Real.exp (2 * Real.pi) + 1) * (1 + ‖(τ : ℂ)‖) ^ A0
              * (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) * Real.exp (-(Real.pi * z.im)) := by ring
    · have h := hcrude τ z hF hz
      have him : z.im ≤ 1 := le_of_lt (not_le.mp hz1)
      have he : Real.exp (Real.pi * z.im) ≤ Real.exp Real.pi :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, him])
      have he2 : Real.exp Real.pi ≤ Real.exp (2 * Real.pi) :=
        Real.exp_le_exp.mpr (by linarith [Real.pi_pos])
      have he3 : Real.exp (-Real.pi) ≤ Real.exp (-(Real.pi * z.im)) := by
        rw [Real.exp_le_exp]; nlinarith [Real.pi_pos, hz, him]
      have hs : (0:ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ A0 := Real.rpow_nonneg (by positivity) A0
      have h1 : ‖Ncusp ℓ d τ z‖ ≤ C0 * (1 + ‖(τ : ℂ)‖) ^ A0 * Real.exp Real.pi := by
        calc ‖Ncusp ℓ d τ z‖ ≤ C0 * (1 + ‖(τ : ℂ)‖) ^ A0 * Real.exp (Real.pi * z.im) := h
          _ ≤ C0 * (1 + ‖(τ : ℂ)‖) ^ A0 * Real.exp Real.pi :=
              mul_le_mul_of_nonneg_left he (by positivity)
      have hee : Real.exp Real.pi = Real.exp (2 * Real.pi) * Real.exp (-Real.pi) := by
        rw [← Real.exp_add, show 2 * Real.pi + -Real.pi = Real.pi by ring]
      refine le_trans h1 ?_
      calc C0 * (1 + ‖(τ : ℂ)‖) ^ A0 * Real.exp Real.pi
          = (C0 * Real.exp (2 * Real.pi) * (1 + ‖(τ : ℂ)‖) ^ A0)
              * Real.exp (-Real.pi) := by rw [hee]; ring
        _ ≤ (C0 * Real.exp (2 * Real.pi) * (1 + ‖(τ : ℂ)‖) ^ A0)
              * Real.exp (-(Real.pi * z.im)) :=
            mul_le_mul_of_nonneg_left he3 (by positivity)
        _ ≤ ((C0 * Real.exp (2 * Real.pi) + 1) * (1 + ‖(τ : ℂ)‖) ^ A0)
              * Real.exp (-(Real.pi * z.im)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hs)
              (Real.exp_nonneg _)
        _ ≤ ((C0 * Real.exp (2 * Real.pi) + 1) * (1 + ‖(τ : ℂ)‖) ^ A0)
              * (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) * Real.exp (-(Real.pi * z.im)) := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
            exact le_mul_of_one_le_right (by positivity) hzX
        _ = (C0 * Real.exp (2 * Real.pi) + 1) * (1 + ‖(τ : ℂ)‖) ^ A0
              * (1 + ‖(z : ℂ)‖) ^ (2 : ℕ) * Real.exp (-(Real.pi * z.im)) := by ring
  -- convert `Ncusp` to the slashed kernel
  have hDne : Work.Kernels.DeltaFun z
      * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) ≠ 0 :=
    mul_ne_zero (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z) (sub_ne_zero.mpr hne)
  have hkey : (z : ℂ) ^ ((d : ℤ) / 2 - 2) * Work.Kernels.KMinus ℓ d τ (ModularGroup.S • z)
      = Ncusp ℓ d τ z
        / (Work.Kernels.DeltaFun z
            * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)) := by
    rw [show ((d : ℤ) / 2 - 2) = -(2 - (d : ℤ) / 2) by ring, Ncusp_ident ℓ d hd τ z hne]
    exact (mul_div_cancel_left₀ _ hDne).symm
  rw [hkey, norm_div]
  exact div_le_div_of_nonneg_right hmain (norm_nonneg _)

end

end Work.Asymptotics
