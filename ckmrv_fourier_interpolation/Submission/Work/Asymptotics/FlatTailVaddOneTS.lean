/-
# Flatness and the cusp-`i∞` tail at the `T`-translate `1 +ᵥ u`

For `u ∈ 𝒟` with `Re u > 0` the point `1 + u` lies outside `𝒟`, but the kernel and the cusp model
at `1 + u` are `T`-ladder combinations of their values at `u` and at `u - 1` (both in `𝒟`), so the
flatness at the cusp `0` and the expansion at the cusp `i∞` transfer to `1 + u`.

## Main results

* `Work.Asymptotics.lh_flat_vadd_one`;
* `Work.Asymptotics.lh_tail_vadd_one`.
-/
import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.MFix.Cusp0Flat
import Submission.Work.HFN.Kaxis_local_tail
import Submission.Work.Asymptotics.T2op_kernelTransform
import Submission.Work.Asymptotics.CuspLadderTS

noncomputable section

open UpperHalfPlane MeasureTheory Filter
open scoped Topology

namespace Work.Asymptotics

/-! ## Elementary geometry -/

/-- The `𝒟` arc conditions say `|Re u| < (Re u)² + (Im u)²`. -/
lemma lh_abs_re_lt_normSq_of_mem_DomainD {u : ℍ} (hu : u ∈ DomainD) :
    |u.re| < u.re ^ 2 + u.im ^ 2 := by
  have h1 : (1 / 2 : ℝ) < ‖(u : ℂ) - (1 / 2 : ℂ)‖ := hu.2.2.1
  have h2 : (1 / 2 : ℝ) < ‖(u : ℂ) + (1 / 2 : ℂ)‖ := hu.2.2.2
  have e1 : ‖(u : ℂ) - (1 / 2 : ℂ)‖ ^ 2 = (u.re - 1 / 2) ^ 2 + u.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    norm_num
    ring
  have e2 : ‖(u : ℂ) + (1 / 2 : ℂ)‖ ^ 2 = (u.re + 1 / 2) ^ 2 + u.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    norm_num
    ring
  have k1 : (1 / 4 : ℝ) < (u.re - 1 / 2) ^ 2 + u.im ^ 2 := by
    rw [← e1]; nlinarith [norm_nonneg ((u : ℂ) - (1 / 2 : ℂ)), h1]
  have k2 : (1 / 4 : ℝ) < (u.re + 1 / 2) ^ 2 + u.im ^ 2 := by
    rw [← e2]; nlinarith [norm_nonneg ((u : ℂ) + (1 / 2 : ℂ)), h2]
  rw [abs_lt]
  constructor <;> nlinarith [k1, k2]

/-- `‖(u : ℂ) - (3/2 : ℂ)‖ ^ 2 = (Re u - 3/2)^2 + (Im u)^2`. -/
private lemma lh_normSq_sub_threehalf (u : ℍ) :
    ‖(u : ℂ) - (3 / 2 : ℂ)‖ ^ 2 = (u.re - 3 / 2) ^ 2 + u.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  norm_num
  ring

/-- `u - 1 ∈ 𝒟` for `u ∈ 𝒟` with `0 < Re u`. -/
lemma lh_vadd_neg_one_mem_DomainD_of_pos {u : ℍ} (hu : u ∈ DomainD) (hre : 0 < u.re) :
    ((-1 : ℝ) +ᵥ u) ∈ DomainD := by
  have harc := lh_abs_re_lt_normSq_of_mem_DomainD hu
  obtain ⟨harc1, harc2⟩ := abs_lt.mp harc
  have hcoe : ((((-1 : ℝ) +ᵥ u : ℍ)) : ℂ) = (u : ℂ) - 1 := by
    rw [UpperHalfPlane.coe_vadd]
    simp only [Complex.ofReal_neg, Complex.ofReal_one]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [UpperHalfPlane.vadd_re]; linarith [hu.1]
  · rw [UpperHalfPlane.vadd_re]; linarith [hu.2.1]
  · -- `|(u-1) - 1/2| > 1/2`, i.e. `(Re u - 3/2)^2 + (Im u)^2 > 1/4`
    have hnorm : ‖((((-1 : ℝ) +ᵥ u : ℍ)) : ℂ) - (1 / 2 : ℂ)‖ = ‖(u : ℂ) - (3 / 2 : ℂ)‖ := by
      rw [hcoe]; congr 1; ring
    rw [hnorm]
    have hsq := lh_normSq_sub_threehalf u
    have hkey : (1 / 4 : ℝ) < (u.re - 3 / 2) ^ 2 + u.im ^ 2 := by
      nlinarith [harc2, hu.2.1]
    nlinarith [norm_nonneg ((u : ℂ) - (3 / 2 : ℂ)), hsq, hkey]
  · -- `|(u-1) + 1/2| > 1/2` is exactly the condition `|u - 1/2| > 1/2`
    have hnorm : ‖((((-1 : ℝ) +ᵥ u : ℍ)) : ℂ) + (1 / 2 : ℂ)‖ = ‖(u : ℂ) - (1 / 2 : ℂ)‖ := by
      rw [hcoe]; congr 1; ring
    rw [hnorm]
    exact hu.2.2.1

/-! ## Flatness at `1 +ᵥ u` -/

/-- The pointwise `T`-identity for the kernel on the contour. -/
lemma lh_Kaxis_vadd (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) (u : ℍ)
    (t : ℝ) :
    Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ u) t
      = 2 * Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) u t
        - Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((-1 : ℝ) +ᵥ u) t := by
  have h := congr_fun (Work.Asymptotics.Kaxis_Kfun_T2 ℓ d hd t) ((-1 : ℝ) +ᵥ u)
  simp only [Work.Kernels.T2op, Pi.zero_apply] at h
  rw [show (2 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ u) = (1 : ℝ) +ᵥ u from by rw [← add_vadd]; norm_num,
    show (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ u) = u from by rw [← add_vadd]; norm_num] at h
  linear_combination h

/-- **Flatness of the kernel at `1 +ᵥ u`** for `u ∈ 𝒟` with `Re u > 0`. -/
theorem lh_flat_vadd_one (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (u : ℍ) (hu : u ∈ DomainD) (hre : 0 < u.re) :
    ∀ N : ℝ, 0 ≤ N → ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ u) t‖ ≤ c * t ^ N := by
  intro N hN
  have hu1D : ((-1 : ℝ) +ᵥ u) ∈ DomainD := lh_vadd_neg_one_mem_DomainD_of_pos hu hre
  obtain ⟨c1, hc1, h1⟩ := Work.Asymptotics.MFix.Kaxis_local_flat ℓ d hd
    (K := ({u} : Set ℍ)) isCompact_singleton (by rintro x rfl; exact hu) N hN
  obtain ⟨c2, hc2, h2⟩ := Work.Asymptotics.MFix.Kaxis_local_flat ℓ d hd
    (K := ({((-1 : ℝ) +ᵥ u)} : Set ℍ)) isCompact_singleton
    (by rintro x rfl; exact hu1D) N hN
  refine ⟨2 * c1 + c2, by positivity, fun t ht ht1 => ?_⟩
  have b1 := h1 u t (by simp) ht ht1
  have b2 := h2 ((-1 : ℝ) +ᵥ u) t (by simp) ht ht1
  rw [lh_Kaxis_vadd ℓ d hd u t]
  calc ‖2 * Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) u t
        - Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((-1 : ℝ) +ᵥ u) t‖
      ≤ ‖2 * Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) u t‖
        + ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((-1 : ℝ) +ᵥ u) t‖ := norm_sub_le _ _
    _ = 2 * ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) u t‖
        + ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((-1 : ℝ) +ᵥ u) t‖ := by
        rw [norm_mul]; norm_num
    _ ≤ 2 * (c1 * t ^ N) + c2 * t ^ N := by linarith
    _ = (2 * c1 + c2) * t ^ N := by ring

/-! ## The cusp-`i∞` tail at `1 +ᵥ u` -/

/-- **The cusp-`i∞` tail estimate at `1 +ᵥ u`** for `u ∈ 𝒟` with `Re u > 0`. -/
theorem lh_tail_vadd_one (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (u : ℍ) (hu : u ∈ DomainD) (hre : 0 < u.re) :
    ∃ C M T₀ : ℝ, 0 < C ∧ 0 ≤ M ∧ 0 ≤ T₀ ∧ ∀ t : ℝ, 1 ≤ t →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ u) t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((1 : ℝ) +ᵥ u) t‖
        ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀))) := by
  have hu1D : ((-1 : ℝ) +ᵥ u) ∈ DomainD := lh_vadd_neg_one_mem_DomainD_of_pos hu hre
  obtain ⟨C1, M1, T1, hC1, hM1, hT1, hb1⟩ := Work.HFN.cusp_expansion_of_kernel ℓ d hd
    (K := ({u} : Set ℍ)) isCompact_singleton (by rintro x rfl; exact hu)
  obtain ⟨C2, M2, T2, hC2, hM2, hT2, hb2⟩ := Work.HFN.cusp_expansion_of_kernel ℓ d hd
    (K := ({((-1 : ℝ) +ᵥ u)} : Set ℍ)) isCompact_singleton (by rintro x rfl; exact hu1D)
  refine ⟨2 * (C1 * Real.exp (Real.pi * T1)) + C2 * Real.exp (Real.pi * T2), max M1 M2, 0,
    by positivity, le_trans hM1 (le_max_left _ _), le_rfl, fun t ht => ?_⟩
  simp only [sub_zero]
  have b1 := hb1 u t (by simp) ht
  have b2 := hb2 ((-1 : ℝ) +ᵥ u) t (by simp) ht
  have hA := Aexp_vadd_ladderTS ℓ d hd u t
  have hval : Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ u) t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((1 : ℝ) +ᵥ u) t
      = 2 * (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) u t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) u t)
        - (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((-1 : ℝ) +ᵥ u) t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((-1 : ℝ) +ᵥ u) t) := by
    rw [lh_Kaxis_vadd ℓ d hd u t, hA]
    ring
  set A : ℝ := ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) u t
    - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) u t‖ with hAdef
  set B : ℝ := ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((-1 : ℝ) +ᵥ u) t
    - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((-1 : ℝ) +ᵥ u) t‖ with hBdef
  have hA1 : A ≤ C1 * (1 + t) ^ M1 * Real.exp (-(Real.pi * (t - T1))) := by
    rw [hAdef]; exact b1
  have hB1 : B ≤ C2 * (1 + t) ^ M2 * Real.exp (-(Real.pi * (t - T2))) := by
    rw [hBdef]; exact b2
  have hnorm : ‖2 * (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) u t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) u t)
      - (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((-1 : ℝ) +ᵥ u) t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((-1 : ℝ) +ᵥ u) t)‖
      ≤ 2 * (C1 * (1 + t) ^ M1 * Real.exp (-(Real.pi * (t - T1))))
        + C2 * (1 + t) ^ M2 * Real.exp (-(Real.pi * (t - T2))) := by
    have h1 : ‖2 * (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) u t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) u t)
        - (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((-1 : ℝ) +ᵥ u) t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((-1 : ℝ) +ᵥ u) t)‖
        ≤ 2 * A + B := by
      calc ‖2 * (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) u t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) u t)
          - (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((-1 : ℝ) +ᵥ u) t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((-1 : ℝ) +ᵥ u) t)‖
          ≤ ‖2 * (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) u t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) u t)‖
            + ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((-1 : ℝ) +ᵥ u) t
              - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) ((-1 : ℝ) +ᵥ u) t‖ :=
            norm_sub_le _ _
        _ = 2 * A + B := by rw [norm_mul, hAdef, hBdef]; norm_num
    linarith [h1, hA1, hB1]
  rw [hval]
  refine le_trans hnorm ?_
  have hM1' : (1 + t) ^ M1 ≤ (1 + t) ^ max M1 M2 :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
  have hM2' : (1 + t) ^ M2 ≤ (1 + t) ^ max M1 M2 :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_right _ _)
  have heq1 : Real.exp (-(Real.pi * (t - T1)))
      = Real.exp (Real.pi * T1) * Real.exp (-(Real.pi * t)) := by
    rw [← Real.exp_add]; congr 1; ring
  have heq2 : Real.exp (-(Real.pi * (t - T2)))
      = Real.exp (Real.pi * T2) * Real.exp (-(Real.pi * t)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hE1 : C1 * (1 + t) ^ M1 * Real.exp (-(Real.pi * (t - T1)))
      ≤ (C1 * Real.exp (Real.pi * T1)) * (1 + t) ^ max M1 M2 * Real.exp (-(Real.pi * t)) := by
    rw [heq1]
    calc C1 * (1 + t) ^ M1 * (Real.exp (Real.pi * T1) * Real.exp (-(Real.pi * t)))
        = (C1 * Real.exp (Real.pi * T1)) * ((1 + t) ^ M1 * Real.exp (-(Real.pi * t))) := by ring
      _ ≤ (C1 * Real.exp (Real.pi * T1)) * ((1 + t) ^ max M1 M2 * Real.exp (-(Real.pi * t))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hM1' (Real.exp_nonneg _)) (by positivity)
      _ = (C1 * Real.exp (Real.pi * T1)) * (1 + t) ^ max M1 M2 * Real.exp (-(Real.pi * t)) := by ring
  have hE2 : C2 * (1 + t) ^ M2 * Real.exp (-(Real.pi * (t - T2)))
      ≤ (C2 * Real.exp (Real.pi * T2)) * (1 + t) ^ max M1 M2 * Real.exp (-(Real.pi * t)) := by
    rw [heq2]
    calc C2 * (1 + t) ^ M2 * (Real.exp (Real.pi * T2) * Real.exp (-(Real.pi * t)))
        = (C2 * Real.exp (Real.pi * T2)) * ((1 + t) ^ M2 * Real.exp (-(Real.pi * t))) := by ring
      _ ≤ (C2 * Real.exp (Real.pi * T2)) * ((1 + t) ^ max M1 M2 * Real.exp (-(Real.pi * t))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hM2' (Real.exp_nonneg _)) (by positivity)
      _ = (C2 * Real.exp (Real.pi * T2)) * (1 + t) ^ max M1 M2 * Real.exp (-(Real.pi * t)) := by ring
  calc 2 * (C1 * (1 + t) ^ M1 * Real.exp (-(Real.pi * (t - T1))))
        + C2 * (1 + t) ^ M2 * Real.exp (-(Real.pi * (t - T2)))
      ≤ 2 * ((C1 * Real.exp (Real.pi * T1)) * (1 + t) ^ max M1 M2 * Real.exp (-(Real.pi * t)))
        + (C2 * Real.exp (Real.pi * T2)) * (1 + t) ^ max M1 M2 * Real.exp (-(Real.pi * t)) := by
        linarith
    _ = (2 * (C1 * Real.exp (Real.pi * T1)) + C2 * Real.exp (Real.pi * T2))
          * (1 + t) ^ max M1 M2 * Real.exp (-(Real.pi * t)) := by ring

end Work.Asymptotics
