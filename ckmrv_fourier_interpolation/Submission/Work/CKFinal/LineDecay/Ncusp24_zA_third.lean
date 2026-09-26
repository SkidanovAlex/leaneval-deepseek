import Mathlib
import Submission.Work.Asymptotics.KMinusFunnelZBounds
import Submission.Work.Asymptotics.KMinusFunnelZBoundsLS
import Submission.Work.Asymptotics.KPlusFunnel.ZFacts
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.ZAtomsThird.first_order
import Submission.Work.Residues.KMinusCuspDefs
import Submission.Work.Residues.ThetaEpt
import Submission.Work.Kernels.Kernels
import Submission.Work.CKFinal.LineDecay.Ncz24zA_high
import Submission.Work.CKFinal.LineDecay.VFun_bdd_third

/-!
# The `z`-atom `A(z) = E₁₄(z)𝓛_S(z) + E₄(z)³V(z)` vanishes to third order at the cusp

This file proves `Work.CKFinal.LineDecay.Ncusp24_zA_third` (the `z`-atom bound of CKMRV
Lemma 4.11 for `d = 24`, in the form consumed by
`Work.CKFinal.LineDecay.Ncusp24_delta_funnel_zfree`):

  `‖E₁₄(z)·𝓛_S(z) + E₄(z)³·V(z)‖ ≤ C e^{-3π Im z}`  for `Im z ≥ 1/3`.

## The two regimes

* `Im z ≥ 1` (**third-order cancellation**, `Ncz24zA_high`): writing `E = e^{πiz}`
  (`‖E‖ = e^{-π Im z}`), the two summands are individually of size `‖E‖` at the cusp —
  `𝓛_S = -16E + O(‖E‖³)` and `V = 16E + O(‖E‖³)` — with the *same* linear term, so the
  combination is `O(‖E‖³) = O(e^{-3π Im z})`.
* `1/3 ≤ Im z ≤ 1` (**boundedness**, `Ncz24zA_bdd`): each of the four factors is bounded on
  the whole funnel `{Im z ≥ 1/3}` (`E₄, E₆` and hence `E₁₄` by
  `ZAtomsThird.first_order`, `𝓛_S` by `LS_exp_bound_third`, `V` by `VFun_bdd_third`), so the
  atom is bounded there; the exponential loss `e^{3π}` turns the bound into `C e^{-3π Im z}`.
-/

namespace Work.CKFinal.LineDecay

open UpperHalfPlane

noncomputable section

/-! ## Boundedness of the atom on the whole funnel -/

private lemma Ncz24zA_bdd (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, (1 : ℝ) / 3 ≤ z.im →
      ‖Work.Kernels.E14Fun z * ℓ.L_S z + Work.Kernels.E4Fun z ^ 3 * Work.Kernels.VFun z‖
        ≤ C := by
  obtain ⟨CLS, hCLS, hLS⟩ := Work.Asymptotics.LS_exp_bound_third ℓ
  obtain ⟨Cfo, hCfo, -, hE4, hE6, -⟩ := Work.Asymptotics.ZAtomsThird.first_order
  obtain ⟨CV, hCV, hV⟩ := VFun_bdd_third
  set K : ℝ := 1 + Cfo with hK
  have hKpos : 0 < K := by rw [hK]; linarith
  have hqle : ∀ z : UpperHalfPlane, (1 : ℝ) / 3 ≤ z.im → ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
    intro z hz
    rw [Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
    nlinarith [Real.pi_pos, hz]
  have hE4b : ∀ z : UpperHalfPlane, (1 : ℝ) / 3 ≤ z.im → ‖Work.Kernels.E4Fun z‖ ≤ K := by
    intro z hz
    have hq := hqle z hz
    have h := hE4 z hz
    have h1 : Cfo * ‖Work.Kernels.qParamFun z‖ ≤ Cfo := by
      nlinarith [hCfo.le, hq, norm_nonneg (Work.Kernels.qParamFun z)]
    have hsplit : Work.Kernels.E4Fun z = (Work.Kernels.E4Fun z - 1) + 1 := by ring
    rw [hsplit]
    have h2 := norm_add_le (Work.Kernels.E4Fun z - 1) (1 : ℂ)
    rw [norm_one] at h2
    rw [hK]
    linarith
  have hE6b : ∀ z : UpperHalfPlane, (1 : ℝ) / 3 ≤ z.im → ‖Work.Kernels.E6Fun z‖ ≤ K := by
    intro z hz
    have hq := hqle z hz
    have h := hE6 z hz
    have h1 : Cfo * ‖Work.Kernels.qParamFun z‖ ≤ Cfo := by
      nlinarith [hCfo.le, hq, norm_nonneg (Work.Kernels.qParamFun z)]
    have hsplit : Work.Kernels.E6Fun z = (Work.Kernels.E6Fun z - 1) + 1 := by ring
    rw [hsplit]
    have h2 := norm_add_le (Work.Kernels.E6Fun z - 1) (1 : ℂ)
    rw [norm_one] at h2
    rw [hK]
    linarith
  refine ⟨K ^ 3 * CLS + K ^ 3 * CV + 1, by positivity, fun z hz => ?_⟩
  have hLSz : ‖ℓ.L_S z‖ ≤ CLS := by
    have h := hLS z hz
    have hexp1 : Real.exp (-(Real.pi * z.im)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, z.im_pos]
    nlinarith [h, hCLS.le, hexp1, Real.exp_pos (-(Real.pi * z.im))]
  have hVz : ‖Work.Kernels.VFun z‖ ≤ CV := hV z hz
  have hE4z := hE4b z hz
  have hE6z := hE6b z hz
  have hE14z : ‖Work.Kernels.E14Fun z‖ ≤ K ^ 3 := by
    rw [show Work.Kernels.E14Fun z = Work.Kernels.E4Fun z ^ 2 * Work.Kernels.E6Fun z from rfl,
      norm_mul, norm_pow]
    have h2 : ‖Work.Kernels.E4Fun z‖ ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hE4z 2
    calc ‖Work.Kernels.E4Fun z‖ ^ 2 * ‖Work.Kernels.E6Fun z‖
        ≤ K ^ 2 * K := mul_le_mul h2 hE6z (norm_nonneg _) (pow_nonneg hKpos.le 2)
      _ = K ^ 3 := by ring
  have hE4c : ‖Work.Kernels.E4Fun z ^ 3‖ ≤ K ^ 3 := by
    rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hE4z 3
  calc ‖Work.Kernels.E14Fun z * ℓ.L_S z + Work.Kernels.E4Fun z ^ 3 * Work.Kernels.VFun z‖
      ≤ ‖Work.Kernels.E14Fun z * ℓ.L_S z‖ + ‖Work.Kernels.E4Fun z ^ 3 * Work.Kernels.VFun z‖ :=
        norm_add_le _ _
    _ = ‖Work.Kernels.E14Fun z‖ * ‖ℓ.L_S z‖ + ‖Work.Kernels.E4Fun z ^ 3‖ * ‖Work.Kernels.VFun z‖ := by
        simp only [norm_mul]
    _ ≤ K ^ 3 * CLS + K ^ 3 * CV := by
        have h1 : ‖Work.Kernels.E14Fun z‖ * ‖ℓ.L_S z‖ ≤ K ^ 3 * CLS :=
          mul_le_mul hE14z hLSz (norm_nonneg _) (pow_nonneg hKpos.le 3)
        have h2 : ‖Work.Kernels.E4Fun z ^ 3‖ * ‖Work.Kernels.VFun z‖ ≤ K ^ 3 * CV :=
          mul_le_mul hE4c hVz (norm_nonneg _) (pow_nonneg hKpos.le 3)
        linarith
    _ ≤ K ^ 3 * CLS + K ^ 3 * CV + 1 := by linarith

/-! ## The target -/

theorem Ncusp24_zA_third (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : UpperHalfPlane, (1 : ℝ) / 3 ≤ z.im →
      ‖Work.Kernels.E14Fun z * ℓ.L_S z + Work.Kernels.E4Fun z ^ 3 * Work.Kernels.VFun z‖
        ≤ C * Real.exp (-(Real.pi * z.im)) ^ 3 := by
  obtain ⟨C1, hC1, h1⟩ := Ncz24zA_high ℓ
  obtain ⟨C2, hC2, h2⟩ := Ncz24zA_bdd ℓ
  refine ⟨max C1 (C2 * Real.exp (3 * Real.pi)) + 1, by positivity, fun z hz => ?_⟩
  have hCbig : C1 ≤ max C1 (C2 * Real.exp (3 * Real.pi)) + 1 := by
    linarith [le_max_left C1 (C2 * Real.exp (3 * Real.pi))]
  rcases le_total (1 : ℝ) z.im with hy | hy
  · have h := h1 z hy
    rw [Work.Residues.norm_Ept] at h
    calc ‖Work.Kernels.E14Fun z * ℓ.L_S z + Work.Kernels.E4Fun z ^ 3 * Work.Kernels.VFun z‖
        ≤ C1 * Real.exp (-(Real.pi * z.im)) ^ 3 := h
      _ ≤ (max C1 (C2 * Real.exp (3 * Real.pi)) + 1) * Real.exp (-(Real.pi * z.im)) ^ 3 :=
          mul_le_mul_of_nonneg_right hCbig (by positivity)
  · have h := h2 z hz
    have hexp3 : Real.exp (-Real.pi) ^ 3 = Real.exp (-(3 * Real.pi)) := by
      rw [← Real.exp_nat_mul (-Real.pi) 3]
      congr 1
      ring
    have hprod : Real.exp (3 * Real.pi) * Real.exp (-(3 * Real.pi)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hexp_ge : Real.exp (-Real.pi) ≤ Real.exp (-(Real.pi * z.im)) := by
      rw [Real.exp_le_exp]; nlinarith [Real.pi_pos, hy]
    have h3ge : Real.exp (-Real.pi) ^ 3 ≤ Real.exp (-(Real.pi * z.im)) ^ 3 :=
      pow_le_pow_left₀ (Real.exp_pos _).le hexp_ge 3
    have hC2le : C2 * Real.exp (3 * Real.pi) ≤ max C1 (C2 * Real.exp (3 * Real.pi)) + 1 := by
      linarith [le_max_right C1 (C2 * Real.exp (3 * Real.pi))]
    have hstep : C2 ≤ (max C1 (C2 * Real.exp (3 * Real.pi)) + 1)
        * Real.exp (-(Real.pi * z.im)) ^ 3 := by
      have h2' : C2 * Real.exp (3 * Real.pi) * Real.exp (-Real.pi) ^ 3
          ≤ (max C1 (C2 * Real.exp (3 * Real.pi)) + 1)
            * Real.exp (-(Real.pi * z.im)) ^ 3 :=
        mul_le_mul hC2le h3ge (by positivity) (by positivity)
      have h3 : C2 * (Real.exp (3 * Real.pi) * Real.exp (-Real.pi) ^ 3) = C2 := by
        rw [hexp3, hprod, mul_one]
      nlinarith [h2', hC2.le, Real.exp_pos (3 * Real.pi), pow_pos (Real.exp_pos (-Real.pi)) 3,
        pow_pos (Real.exp_pos (-(Real.pi * z.im))) 3, hC2le, h3ge, h3]
    linarith [h, hstep]

end

end Work.CKFinal.LineDecay
