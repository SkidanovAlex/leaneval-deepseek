/-
# The `T`-ladder of the CKMRV layer at the translate `1 +ᵥ u`

For `u ∈ 𝒟` with `Re u > 0` (so that `u - 1 ∈ 𝒟`, while `1 + u ∉ 𝒟`) the layer of the paper
satisfies the `T`-ladder identity

  `layer(1 + u) = 2 layer(u) - layer(u - 1)`,

a pointwise identity in `r`.  This is the branch-clean, `d`-general version of
`Submission/Work/Asymptotics/paperLayer_vadd_shift.lean` (which is `d = 24` only and lives on the
`kernelTransform_seminorm_cuspHalf_TS` branch).

## Main results

* `Work.Asymptotics.lh_paperLayer_vadd_ladder`;
* `Work.Asymptotics.lh_layer_vadd_ladder`.
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.MFix.Cusp0Flat
import Submission.Work.HFN.Kaxis_local_tail
import Submission.Work.Asymptotics.CuspLadderTS
import Submission.Work.Asymptotics.FlatTailVaddOneTS
import Submission.Work.Asymptotics.measurable_Kaxis_Kfun
import Submission.Work.Asymptotics.paperLayer_agreement

noncomputable section

open UpperHalfPlane MeasureTheory Filter
open scoped Topology

namespace Work.Asymptotics

lemma lh_norm_exp_contour (r t : ℝ) :
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
lemma lh_tail_exp_bound {C M T₀ r t : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) (ht : 1 ≤ t) :
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
lemma lh_integrableOn_low_of_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {τ : ℍ} {c : ℝ}
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
    rw [norm_mul, lh_norm_exp_contour]
    calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ * Real.exp (-(Real.pi * r ^ 2 * t))
        ≤ c * 1 := by
          refine mul_le_mul hb ?_ (Real.exp_nonneg _) hc
          rw [Real.exp_le_one_iff]
          have hpos : 0 ≤ Real.pi * r ^ 2 * t :=
            mul_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg r)) ht0.le
          linarith
      _ = c := mul_one c

/-- Integrability on `(0,1]` of the low contour integrand at a point of `𝒟`. -/
lemma lh_integrableOn_low_of_mem (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ : ℍ} (hτ : τ ∈ Work.Asymptotics.DomainD) (r : ℝ) :
    MeasureTheory.IntegrableOn (fun t : ℝ =>
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioc 0 1) := by
  obtain ⟨c, -, hb⟩ := Work.Asymptotics.MFix.Kaxis_local_flat ℓ d hd
    (K := {τ}) isCompact_singleton (by rintro x rfl; exact hτ) 0 le_rfl
  exact lh_integrableOn_low_of_bound ℓ d hd
    (fun t ht0 ht1 => by simpa [Real.rpow_zero] using hb τ t (by simp) ht0 ht1) r

/-- Integrability on `(0,1]` of the low contour integrand at the `T`-translate `1 +ᵥ u`. -/
lemma lh_integrableOn_low_vadd_one (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (u : ℍ) (hu : u ∈ Work.Asymptotics.DomainD) (hre : 0 < u.re)
    (r : ℝ) :
    MeasureTheory.IntegrableOn (fun t : ℝ =>
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ u) t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioc 0 1) := by
  obtain ⟨c, -, hb⟩ := lh_flat_vadd_one ℓ d hd u hu hre 0 le_rfl
  exact lh_integrableOn_low_of_bound ℓ d hd
    (fun t ht0 ht1 => by simpa [Real.rpow_zero] using hb t ht0 ht1) r

/-- Integrability on `[1,∞)` of the truncated contour integrand, from a polynomial/exponential
bound on `K - Aexp`. -/
lemma lh_integrableOn_trunc_of_tail (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (G : Fin 2 → Fin 2 → ℍ → ℂ) {τ : ℍ} {C M T₀ : ℝ} (hC : 0 ≤ C)
    (hM : 0 ≤ M)
    (h : ∀ t : ℝ, 1 ≤ t →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp G τ t‖
        ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀)))) (r : ℝ) :
    MeasureTheory.IntegrableOn (fun t : ℝ =>
      (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp G τ t)
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ici 1) := by
  have hcpos : 0 < Real.pi * (1 + r ^ 2) := by positivity
  have hdomIoi : MeasureTheory.Integrable (fun t : ℝ =>
      (C * Real.exp (Real.pi * T₀) * 2 ^ M)
        * (t ^ M * Real.exp (-((Real.pi * (1 + r ^ 2)) * t))))
      (volume.restrict (Set.Ioi (1 : ℝ))) :=
    (Work.Asymptotics.integrableOn_rpow_mul_exp_neg_mul_Ioi M (Real.pi * (1 + r ^ 2))
      hcpos).const_mul _
  have hdom : MeasureTheory.Integrable (fun t : ℝ =>
      (C * Real.exp (Real.pi * T₀) * 2 ^ M)
        * (t ^ M * Real.exp (-((Real.pi * (1 + r ^ 2)) * t))))
      (volume.restrict (Set.Ici (1 : ℝ))) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (b := (1 : ℝ))).mpr hdomIoi
  refine MeasureTheory.Integrable.mono' hdom ?_ ?_
  · exact (((Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd τ).sub
      (by unfold Work.Asymptotics.Aexp; fun_prop)).mul (by fun_prop)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    have ht1 : (1 : ℝ) ≤ t := ht
    have hb := h t ht1
    rw [norm_mul, lh_norm_exp_contour]
    exact le_trans (mul_le_mul_of_nonneg_right hb (Real.exp_nonneg _))
      (lh_tail_exp_bound hC hM ht1)

/-- Integrability on `[1,∞)` of the truncated contour integrand at a point of `𝒟`. -/
lemma lh_integrableOn_trunc_of_mem (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ : ℍ} (hτ : τ ∈ Work.Asymptotics.DomainD) (r : ℝ) :
    MeasureTheory.IntegrableOn (fun t : ℝ =>
      (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ici 1) := by
  obtain ⟨C, M, T₀, hC, hM, -, hb⟩ := Work.HFN.cusp_expansion_of_kernel ℓ d hd
    (K := {τ}) isCompact_singleton (by rintro x rfl; exact hτ)
  exact lh_integrableOn_trunc_of_tail ℓ d hd (Work.Asymptotics.Gcusp ℓ d)
    hC.le hM (fun t ht1 => hb τ t (by simp) ht1) r

/-- Integrability on `[1,∞)` of the truncated contour integrand at the `T`-translate `1 +ᵥ u`. -/
lemma lh_integrableOn_trunc_vadd_one (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (u : ℍ) (hu : u ∈ Work.Asymptotics.DomainD) (hre : 0 < u.re)
    (r : ℝ) :
    MeasureTheory.IntegrableOn (fun t : ℝ =>
      (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ u) t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((1 : ℝ) +ᵥ u) t)
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ici 1) := by
  obtain ⟨C, M, T₀, hC, hM, -, hb⟩ := lh_tail_vadd_one ℓ d hd u hu hre
  exact lh_integrableOn_trunc_of_tail ℓ d hd (Work.Asymptotics.Gcusp ℓ d)
    hC.le hM hb r

/-! ## The `T`-ladders of the pieces of the layer -/

/-- The `T`-ladder of `highPart`. -/
lemma lh_highPart_vadd_ladder (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (u : ℍ) (r : ℝ) :
    Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) ((1 : ℝ) +ᵥ u) r
      = 2 * Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) u r
        - Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) ((-1 : ℝ) +ᵥ u) r := by
  simp only [Work.Asymptotics.highPart]
  rw [Gcusp_vadd_ladderTS ℓ d hd 0 0 u, Gcusp_vadd_ladderTS ℓ d hd 0 1 u,
    Gcusp_vadd_ladderTS ℓ d hd 1 0 u, Gcusp_vadd_ladderTS ℓ d hd 1 1 u]
  ring

/-- **The ladder of the `low` piece.** -/
lemma lh_layerLow_vadd_ladder (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (u : ℍ) (hu : u ∈ Work.Asymptotics.DomainD) (hre : 0 < u.re) (r : ℝ) :
    Work.Asymptotics.layerLow ℓ d ((1 : ℝ) +ᵥ u) r
      = 2 * Work.Asymptotics.layerLow ℓ d u r
        - Work.Asymptotics.layerLow ℓ d ((-1 : ℝ) +ᵥ u) r := by
  have hu1D : ((-1 : ℝ) +ᵥ u) ∈ Work.Asymptotics.DomainD :=
    lh_vadd_neg_one_mem_DomainD_of_pos hu hre
  have hint1 := lh_integrableOn_low_vadd_one ℓ d hd u hu hre r
  have hint0 := lh_integrableOn_low_of_mem ℓ d hd hu r
  have hintm := lh_integrableOn_low_of_mem ℓ d hd hu1D r
  have hpoint : ∀ t : ℝ,
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ u) t
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))
        = 2 * (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) u t
            * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
          - Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((-1 : ℝ) +ᵥ u) t
            * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) := by
    intro t
    linear_combination (Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
      * lh_Kaxis_vadd ℓ d hd u t
  have hkey : (∫ t in (0 : ℝ)..1, Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ u) t
        * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
      = 2 * (∫ t in (0 : ℝ)..1, Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) u t
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
        - ∫ t in (0 : ℝ)..1, Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((-1 : ℝ) +ᵥ u) t
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

/-- **The ladder of the `trunc` piece.** -/
lemma lh_layerTrunc_vadd_ladder (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (u : ℍ) (hu : u ∈ Work.Asymptotics.DomainD) (hre : 0 < u.re) (r : ℝ) :
    Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ u) r
      = 2 * Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d u r
        - Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d ((-1 : ℝ) +ᵥ u) r := by
  have hu1D : ((-1 : ℝ) +ᵥ u) ∈ Work.Asymptotics.DomainD :=
    lh_vadd_neg_one_mem_DomainD_of_pos hu hre
  have hint1 := lh_integrableOn_trunc_vadd_one ℓ d hd u hu hre r
  have hint0 := lh_integrableOn_trunc_of_mem ℓ d hd hu r
  have hintm := lh_integrableOn_trunc_of_mem ℓ d hd hu1D r
  have hpoint : ∀ t : ℝ,
      (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ u) t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((1 : ℝ) +ᵥ u) t)
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))
        = 2 * ((Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) u t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) u t)
            * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
          - (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((-1 : ℝ) +ᵥ u) t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((-1 : ℝ) +ᵥ u) t)
            * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) := by
    intro t
    linear_combination (Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
        * lh_Kaxis_vadd ℓ d hd u t
      - (Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) * Aexp_vadd_ladderTS ℓ d hd u t
  simp only [Work.Asymptotics.layerTrunc]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun t _ => hpoint t),
    MeasureTheory.integral_sub (hint0.const_mul 2) hintm,
    MeasureTheory.integral_const_mul]
  ring

/-- **The `T`-ladder of `paperLayer` at the translate `1 +ᵥ u`.** -/
theorem lh_paperLayer_vadd_ladder (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (u : ℍ) (hu : u ∈ Work.Asymptotics.DomainD) (hre : 0 < u.re) (r : ℝ) :
    Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ u) r
      = 2 * Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d u r
        - Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((-1 : ℝ) +ᵥ u) r := by
  have hlow := lh_layerLow_vadd_ladder ℓ d hd u hu hre r
  have htrunc := lh_layerTrunc_vadd_ladder ℓ d hd u hu hre r
  have hhigh := lh_highPart_vadd_ladder ℓ d hd u r
  simp only [Work.Asymptotics.paperLayer]
  rw [hlow, htrunc, hhigh]
  ring

/-- **The `T`-ladder of the layer at the translate `1 +ᵥ u`.** -/
theorem lh_layer_vadd_ladder (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (u : ℍ) (hu : u ∈ Work.Asymptotics.DomainD) (hre : 0 < u.re) (r : ℝ) :
    Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((1 : ℝ) +ᵥ u) r
      = 2 * Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d u r
        - Work.Asymptotics.layer (Work.Asymptotics.Gcusp ℓ d) ℓ d ((-1 : ℝ) +ᵥ u) r := by
  by_cases hr : r = 0
  · subst hr
    simp [Work.Asymptotics.layer]
  · rw [Work.Asymptotics.layer, if_neg hr, Work.Asymptotics.layer, if_neg hr,
      Work.Asymptotics.layer, if_neg hr]
    exact lh_paperLayer_vadd_ladder ℓ d hd u hu hre r

end Work.Asymptotics
