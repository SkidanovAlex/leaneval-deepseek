import Mathlib
import Submission.Work.Asymptotics.TSasm.AexpGcusp24T2
import Submission.Work.Asymptotics.TSasm.layerSemi_Tregion
import Submission.Work.Asymptotics.TSasm.ShiftFlatTail

namespace Work.Asymptotics

open MeasureTheory UpperHalfPlane
open scoped Topology

noncomputable section

set_option maxHeartbeats 1000000

/-!
# The `T`-ladder of the layer `paperLayer (Gcusp ℓ 24)` on the half tile `Tregion`

This file proves

`paperLayer (Gcusp ℓ 24) ℓ 24 (1 +ᵥ u) r = 2 * paperLayer (Gcusp ℓ 24) ℓ 24 u r
    - paperLayer (Gcusp ℓ 24) ℓ 24 (-1 +ᵥ u) r`

for `u ∈ Tregion` with `Re u ≥ 1/4` and every `r : ℝ`.

The proof is *exact and elementary*: `paperLayer = layerLow + layerTrunc + highPart`, each piece
is a (`τ`-independent) multiple of an integral of a kernel which is *pointwise* an exact
`(T - I)²`-ladder, and the pointwise identities integrate because the integrands are dominated by
the flatness of the kernel at `t → 0⁺` (`flat_vadd_one`, `Kaxis_local_flat`) and by the cusp
`i∞` expansion at `t → ∞` (`tail_vadd_one`, `cusp_expansion_of_kernel`).  No non-coincidence
hypothesis is needed: on the half tile the two ends of the ladder never meet the poles of the
kernel along the contour; at worst the coincidence is *removable* and the flatness/expansion
estimates already hold (this is the content of `MFix.Kaxis_local_flat` / `cusp_expansion_of_kernel`).
The `highPart` is an explicit linear combination of the cusp coefficients, whose ladder is the
`(T-I)²`-annihilation `T2aux.Gcusp24_T2_all`.
-/

/-! ## Elementary norm and tail estimates -/

lemma norm_exp_contourE (r t : ℝ) :
    ‖Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))‖ = Real.exp (-(Real.pi * r ^ 2 * t)) := by
  rw [Complex.norm_exp]
  congr 1
  have hr2 : ((r : ℂ) ^ 2).re = r ^ 2 := by
    have h : ((r : ℂ) ^ 2) = ((r ^ 2 : ℝ) : ℂ) := (Complex.ofReal_pow r 2).symm
    rw [h, Complex.ofReal_re]
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero]
  rw [hr2]
  ring

/-- The elementary decay comparison used to dominate the cusp-`i∞` tail by an integrable
exponential. -/
lemma tail_exp_bound {C M T₀ r t : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) (ht : 1 ≤ t) :
    C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀))) * Real.exp (-(Real.pi * r ^ 2 * t))
      ≤ (C * Real.exp (Real.pi * T₀) * 2 ^ M)
          * (t ^ M * Real.exp (-((Real.pi * (1 + r ^ 2)) * t))) := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have h1t : (1 + t) ^ M ≤ 2 ^ M * t ^ M := by
    calc (1 + t) ^ M ≤ (2 * t) ^ M := Real.rpow_le_rpow (by linarith) (by linarith) hM
      _ = 2 ^ M * t ^ M := Real.mul_rpow (by norm_num) (by linarith)
  have hX : (0 : ℝ) ≤ Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * r ^ 2 * t)) := by
    positivity
  have hCE : (0 : ℝ) ≤ C * Real.exp (Real.pi * T₀) := mul_nonneg hC (Real.exp_nonneg _)
  calc C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀))) * Real.exp (-(Real.pi * r ^ 2 * t))
      = (C * Real.exp (Real.pi * T₀))
          * ((1 + t) ^ M
              * (Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * r ^ 2 * t)))) := by
        rw [show -(Real.pi * (t - T₀)) = Real.pi * T₀ + -(Real.pi * t) by ring, Real.exp_add]
        ring
    _ ≤ (C * Real.exp (Real.pi * T₀))
          * ((2 ^ M * t ^ M)
              * (Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * r ^ 2 * t)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1t hX) hCE
    _ = (C * Real.exp (Real.pi * T₀) * 2 ^ M)
          * (t ^ M * Real.exp (-((Real.pi * (1 + r ^ 2)) * t))) := by
        rw [show Real.exp (-((Real.pi * (1 + r ^ 2)) * t))
            = Real.exp (-(Real.pi * t)) * Real.exp (-(Real.pi * r ^ 2 * t)) by
          rw [← Real.exp_add]; congr 1; ring]
        ring

/-! ## Integrability of the two integrands, from flatness and from the cusp expansion -/

/-- Integrability on `(0,1]` of the low contour integrand, from a uniform bound on the kernel. -/
lemma integrableOn_low_of_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ : ℍ} {c : ℝ}
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ c) (r : ℝ) :
    MeasureTheory.IntegrableOn (fun t : ℝ =>
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioc 0 1) := by
  have hc : 0 ≤ c := le_trans (norm_nonneg _) (h (1 / 2) (by norm_num) (by norm_num))
  refine MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top ?_ c ?_
  · exact ((Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd τ).mul
      (by fun_prop)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 < t := ht.1
    have hb := h t ht0 ht.2
    rw [norm_mul, norm_exp_contourE]
    calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ * Real.exp (-(Real.pi * r ^ 2 * t))
        ≤ c * 1 := by
          refine mul_le_mul hb ?_ (Real.exp_nonneg _) hc
          rw [Real.exp_le_one_iff]
          have hpos : 0 ≤ Real.pi * r ^ 2 * t :=
            mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg r)) ht0.le
          linarith
      _ = c := mul_one c

/-- Integrability on `(0,1]` of the low contour integrand at a point of `𝒟`. -/
lemma integrableOn_low_of_mem (ℓ : Work.Kernels.LogLambdaData) {τ : ℍ}
    (hτ : τ ∈ Work.Asymptotics.DomainD) (r : ℝ) :
    MeasureTheory.IntegrableOn (fun t : ℝ =>
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) τ t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioc 0 1) := by
  obtain ⟨c, -, hb⟩ := Work.Asymptotics.MFix.Kaxis_local_flat ℓ 24 (Or.inr rfl)
    (K := {τ}) isCompact_singleton (by rintro x rfl; exact hτ) 0 le_rfl
  exact integrableOn_low_of_bound ℓ 24 (Or.inr rfl)
    (fun t ht0 ht1 => by simpa [Real.rpow_zero] using hb τ t (by simp) ht0 ht1) r

/-- Integrability on `(0,1]` of the low contour integrand at the `T`-translate `1 +ᵥ u`. -/
lemma integrableOn_low_vadd_one (ℓ : Work.Kernels.LogLambdaData) (u : ℍ)
    (hu : u ∈ Work.Asymptotics.Tregion) (hx : (1 : ℝ) / 4 ≤ u.re) (r : ℝ) :
    MeasureTheory.IntegrableOn (fun t : ℝ =>
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) ((1 : ℝ) +ᵥ u) t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioc 0 1) := by
  obtain ⟨c, -, hb⟩ := Work.Asymptotics.flat_vadd_one ℓ u hu hx 0 le_rfl
  exact integrableOn_low_of_bound ℓ 24 (Or.inr rfl)
    (fun t ht0 ht1 => by simpa [Real.rpow_zero] using hb t ht0 ht1) r

/-- Integrability on `[1,∞)` of the truncated contour integrand, from a polynomial/exponential
bound on `K - Aexp`. -/
lemma integrableOn_trunc_of_tail (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (G : Fin 2 → Fin 2 → ℍ → ℂ) {τ : ℍ} {C M T₀ : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (h : ∀ t : ℝ, 1 ≤ t →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp G τ t‖
        ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀)))) (r : ℝ) :
    MeasureTheory.IntegrableOn (fun t : ℝ =>
      (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp G τ t)
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ici 1) := by
  have hcpos : 0 < Real.pi * (1 + r ^ 2) := by positivity
  have hdomIoi : MeasureTheory.Integrable (fun t : ℝ =>
      (C * Real.exp (Real.pi * T₀) * 2 ^ M)
        * (t ^ M * Real.exp (-((Real.pi * (1 + r ^ 2)) * t)))) (volume.restrict (Set.Ioi (1 : ℝ))) :=
    (Work.Asymptotics.integrableOn_rpow_mul_exp_neg_mul_Ioi M (Real.pi * (1 + r ^ 2)) hcpos).const_mul _
  have hdom : MeasureTheory.Integrable (fun t : ℝ =>
      (C * Real.exp (Real.pi * T₀) * 2 ^ M)
        * (t ^ M * Real.exp (-((Real.pi * (1 + r ^ 2)) * t)))) (volume.restrict (Set.Ici (1 : ℝ))) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (b := (1 : ℝ))).mpr hdomIoi
  refine MeasureTheory.Integrable.mono' hdom ?_ ?_
  · exact (((Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd τ).sub
      (by unfold Work.Asymptotics.Aexp; fun_prop)).mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    have ht1 : (1 : ℝ) ≤ t := ht
    have hb := h t ht1
    rw [norm_mul, norm_exp_contourE]
    exact le_trans (mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _))
      (tail_exp_bound hC hM ht1)

/-- Integrability on `[1,∞)` of the truncated contour integrand at a point of `𝒟`. -/
lemma integrableOn_trunc_of_mem (ℓ : Work.Kernels.LogLambdaData) {τ : ℍ}
    (hτ : τ ∈ Work.Asymptotics.DomainD) (r : ℝ) :
    MeasureTheory.IntegrableOn (fun t : ℝ =>
      (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) τ t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 24) τ t)
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ici 1) := by
  obtain ⟨C, M, T₀, hC, hM, -, hb⟩ := Work.HFN.cusp_expansion_of_kernel ℓ 24 (Or.inr rfl)
    (K := {τ}) isCompact_singleton (by rintro x rfl; exact hτ)
  exact integrableOn_trunc_of_tail ℓ 24 (Or.inr rfl) (Work.Asymptotics.Gcusp ℓ 24)
    hC.le hM (fun t ht1 => hb τ t (by simp) ht1) r

/-- Integrability on `[1,∞)` of the truncated contour integrand at the `T`-translate `1 +ᵥ u`. -/
lemma integrableOn_trunc_vadd_one (ℓ : Work.Kernels.LogLambdaData) (u : ℍ)
    (hu : u ∈ Work.Asymptotics.Tregion) (hx : (1 : ℝ) / 4 ≤ u.re) (r : ℝ) :
    MeasureTheory.IntegrableOn (fun t : ℝ =>
      (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) ((1 : ℝ) +ᵥ u) t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 24) ((1 : ℝ) +ᵥ u) t)
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ici 1) := by
  obtain ⟨C, M, T₀, hC, hM, -, hb⟩ := Work.Asymptotics.tail_vadd_one ℓ u hu hx
  exact integrableOn_trunc_of_tail ℓ 24 (Or.inr rfl) (Work.Asymptotics.Gcusp ℓ 24)
    hC.le hM hb r

/-! ## The `T`-ladder of the cusp coefficients `Gcusp ℓ 24` and of `highPart` -/

lemma Gcusp_24_T2 (ℓ : Work.Kernels.LogLambdaData) (i j : Fin 2) :
    Work.Kernels.T2op (fun τ : ℍ => Work.Asymptotics.Gcusp ℓ 24 i j τ) = 0 :=
  Work.Asymptotics.T2aux.Gcusp24_T2_all ℓ i j

lemma Gcusp24_vadd_ladder (ℓ : Work.Kernels.LogLambdaData) (i j : Fin 2) (τ : ℍ) :
    Work.Asymptotics.Gcusp ℓ 24 i j ((1 : ℝ) +ᵥ τ)
      = 2 * Work.Asymptotics.Gcusp ℓ 24 i j τ
        - Work.Asymptotics.Gcusp ℓ 24 i j ((-1 : ℝ) +ᵥ τ) := by
  have h := congr_fun (Gcusp_24_T2 ℓ i j) ((-1 : ℝ) +ᵥ τ)
  simp only [Work.Kernels.T2op, Pi.zero_apply] at h
  rw [show (2 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ τ) = (1 : ℝ) +ᵥ τ from by rw [← add_vadd]; norm_num,
      show (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ τ) = τ from by rw [← add_vadd]; norm_num] at h
  linear_combination h

lemma Aexp_vadd_ladder24 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) (t : ℝ) :
    Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 24) ((1 : ℝ) +ᵥ τ) t
      = 2 * Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 24) τ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 24) ((-1 : ℝ) +ᵥ τ) t := by
  simp only [Work.Asymptotics.Aexp]
  rw [Gcusp24_vadd_ladder ℓ 0 0 τ, Gcusp24_vadd_ladder ℓ 0 1 τ,
    Gcusp24_vadd_ladder ℓ 1 0 τ, Gcusp24_vadd_ladder ℓ 1 1 τ]
  ring

lemma highPart_vadd_ladder24 (ℓ : Work.Kernels.LogLambdaData) (τ : ℍ) (r : ℝ) :
    Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ 24) ((1 : ℝ) +ᵥ τ) r
      = 2 * Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ 24) τ r
        - Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ 24) ((-1 : ℝ) +ᵥ τ) r := by
  simp only [Work.Asymptotics.highPart]
  rw [Gcusp24_vadd_ladder ℓ 0 0 τ, Gcusp24_vadd_ladder ℓ 0 1 τ,
    Gcusp24_vadd_ladder ℓ 1 0 τ, Gcusp24_vadd_ladder ℓ 1 1 τ]
  ring

/-! ## The pointwise ladder of the kernel on the contour -/

lemma Kaxis_vadd_ladder24 (ℓ : Work.Kernels.LogLambdaData) (u : ℍ) (t : ℝ) :
    Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) ((1 : ℝ) +ᵥ u) t
      = 2 * Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) u t
        - Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) ((-1 : ℝ) +ᵥ u) t := by
  have h := Work.Asymptotics.Kaxis_T2_Kfun_s ℓ 24 (Or.inr rfl) ((-1 : ℝ) +ᵥ u) t
  rw [show (2 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ u) = (1 : ℝ) +ᵥ u from by rw [← add_vadd]; norm_num,
      show (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ u) = u from by rw [← add_vadd]; norm_num] at h
  linear_combination h

/-! ## The ladders of the three pieces of the layer -/

lemma layerLow_vadd_ladder24 (ℓ : Work.Kernels.LogLambdaData) (u : ℍ)
    (hu : u ∈ Work.Asymptotics.Tregion) (hx : (1 : ℝ) / 4 ≤ u.re) (r : ℝ) :
    Work.Asymptotics.layerLow ℓ 24 ((1 : ℝ) +ᵥ u) r
      = 2 * Work.Asymptotics.layerLow ℓ 24 u r
        - Work.Asymptotics.layerLow ℓ 24 ((-1 : ℝ) +ᵥ u) r := by
  have huD : u ∈ Work.Asymptotics.DomainD := hu.1
  have hx0 : 0 < u.re := by linarith
  have hu1D : ((-1 : ℝ) +ᵥ u) ∈ Work.Asymptotics.DomainD :=
    Work.Asymptotics.ts_vadd_neg_one_mem_DomainD_of_pos huD hx0
  have hint1 := integrableOn_low_vadd_one ℓ u hu hx r
  have hint0 := integrableOn_low_of_mem ℓ huD r
  have hintm := integrableOn_low_of_mem ℓ hu1D r
  have hpoint : ∀ t : ℝ,
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) ((1 : ℝ) +ᵥ u) t
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))
        = 2 * (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) u t
            * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
          - Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) ((-1 : ℝ) +ᵥ u) t
            * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) := by
    intro t
    linear_combination (Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
      * Kaxis_vadd_ladder24 ℓ u t
  have hkey : (∫ t in (0 : ℝ)..1, Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) ((1 : ℝ) +ᵥ u) t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
      = 2 * (∫ t in (0 : ℝ)..1, Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) u t
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
        - ∫ t in (0 : ℝ)..1, Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) ((-1 : ℝ) +ᵥ u) t
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t _ => hpoint t),
      MeasureTheory.integral_sub (hint0.const_mul 2) hintm,
      MeasureTheory.integral_const_mul]
  simp only [Work.Asymptotics.layerLow]
  rw [hkey]
  ring

lemma layerTrunc_vadd_ladder24 (ℓ : Work.Kernels.LogLambdaData) (u : ℍ)
    (hu : u ∈ Work.Asymptotics.Tregion) (hx : (1 : ℝ) / 4 ≤ u.re) (r : ℝ) :
    Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 ((1 : ℝ) +ᵥ u) r
      = 2 * Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 u r
        - Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 ((-1 : ℝ) +ᵥ u) r := by
  have huD : u ∈ Work.Asymptotics.DomainD := hu.1
  have hx0 : 0 < u.re := by linarith
  have hu1D : ((-1 : ℝ) +ᵥ u) ∈ Work.Asymptotics.DomainD :=
    Work.Asymptotics.ts_vadd_neg_one_mem_DomainD_of_pos huD hx0
  have hint1 := integrableOn_trunc_vadd_one ℓ u hu hx r
  have hint0 := integrableOn_trunc_of_mem ℓ huD r
  have hintm := integrableOn_trunc_of_mem ℓ hu1D r
  have hpoint : ∀ t : ℝ,
      (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) ((1 : ℝ) +ᵥ u) t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 24) ((1 : ℝ) +ᵥ u) t)
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))
        = 2 * ((Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) u t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 24) u t)
            * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
          - (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ 24) ((-1 : ℝ) +ᵥ u) t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ 24) ((-1 : ℝ) +ᵥ u) t)
            * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) := by
    intro t
    linear_combination (Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
        * Kaxis_vadd_ladder24 ℓ u t
      - (Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) * Aexp_vadd_ladder24 ℓ u t
  simp only [Work.Asymptotics.layerTrunc]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun t _ => hpoint t),
    MeasureTheory.integral_sub (hint0.const_mul 2) hintm,
    MeasureTheory.integral_const_mul]
  ring

theorem paperLayer_vadd_shift (ℓ : Work.Kernels.LogLambdaData) (u : UpperHalfPlane)
    (hu : u ∈ Work.Asymptotics.Tregion) (hx : (1 : ℝ) / 4 ≤ u.re) (r : ℝ) :
    Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 ((1 : ℝ) +ᵥ u) r
      = 2 * Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 u r
        - Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ 24) ℓ 24 ((-1 : ℝ) +ᵥ u) r := by
  have hlow := layerLow_vadd_ladder24 ℓ u hu hx r
  have htrunc := layerTrunc_vadd_ladder24 ℓ u hu hx r
  have hhigh := highPart_vadd_ladder24 ℓ u r
  simp only [Work.Asymptotics.paperLayer]
  rw [hlow, htrunc, hhigh]
  ring

end

end Work.Asymptotics
