import Mathlib
import Submission.Work.CKFinal.LineDecay.Defs
import Submission.Work.CKFinal.LineDecay.PhiAxis
import Submission.Work.CKFinal.LineDecay.slash_qtau_twentyfour
import Submission.Work.CKFinal.LineDecay.DenomLower_lines
import Submission.Work.CKFinal.LineDecay.Phi_axis_norm_twentyfour
import Submission.Work.CKFinal.LineDecay.KPlus_tail_lines_twentyfour
import Submission.Work.CKFinal.LineDecay.KMinus_tail_lines_twentyfour
import Submission.Work.CKFinal.LineDecay.Tail_integral_twentyfour

/-!
# The tail bound for `Φ` on the lines `Re τ = ±1/2`, in dimension `24`

This file proves `Work.CKFinal.LineDecay.Phi_tail_bound_twentyfour`: for `Re τ = ±1/2` and
`Im τ` large, both tail integrals `∫_{t ≥ 1} ‖Φ(K^{(24)}, τ, t)‖ dt` and
`∫_{t ≥ 1} ‖Φ(K̂^{(24)}, τ, t)‖ dt` decay like `e^{-3π Im τ}` up to a power of `Im τ`.

The three ingredients are

* `Work.CKFinal.LineDecay.Phi_axis_norm_twentyfour`: on the imaginary axis the second difference of
  the kernel is the `z`-slash of the two slashed kernels at the inverse point,
  `‖Φ(τ,t)‖ ≤ t^{10}(‖K₊(τ,S·(it))‖ + ‖K₋(τ,S·(it))‖)` (and the same for `K̂`);
* the CKMRV `z`-cusp bounds for the two slashed kernels on these lines
  (`KPlus_tail_lines_twentyfour`, `KMinus_tail_lines_twentyfour`, whose input is the divisor lower
  bound `Work.CKFinal.LineDecay.DenomLower_lines`): for `Re τ = ±1/2`, `Im τ ≥ 2`, `t ≥ 1`,
  `t^{10}‖K_±(τ,S·(i t))‖ ≤ C_± (1+‖τ‖)^{A_±} e^{-2π Im τ} e^{-πt}/(1 + e^{2π(Im τ - t)})`;
* the elementary tail integral `Work.CKFinal.LineDecay.Tail_integral_twentyfour`
  (`∫_{t ≥ 1} e^{-2πy} e^{-πt}/(1+e^{2π(y-t)}) dt ≤ C e^{-3πy}`, from the bump
  `1/(1+e^{2π(y-t)})` of width `O(1)` at `t = y`).

The factor `e^{-2π Im τ}` (which is `‖q(τ)‖`, present in the `n̂ = 4` cusp bound of dimension 24 but
absent in dimension 8) is what shifts the exponent from `π` to `3π`.
-/

namespace Work.CKFinal.LineDecay

open MeasureTheory UpperHalfPlane
open scoped Topology

noncomputable section

/-- **Assembly of the dimension-24 tail bound** from the two slashed-kernel bounds, the pointwise
axis reduction and the elementary integral bound.

The two slashed-kernel bounds carry the cusp factor
`Ecusp y t = e^{-2πy} e^{-πt}/(1 + e^{2π(y-t)})`, which is dominated by
`e^{-3πy} e^{-π|t-y|}`; integrating in `t` leaves `e^{-3πy}` up to the polynomial
`(1 + ‖τ‖)^A ≤ 2^{2A} (Im τ)^A`. -/
private lemma tail_assembly_twentyfour (ℓ : Work.Kernels.LogLambdaData) (Y0 : ℝ) (hY : 2 ≤ Y0)
    (haxis : ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t),
      (‖Work.CKFinal.Phi (Work.Kernels.Kfun ℓ 24) τ t‖
          ≤ t ^ 10 * (‖Work.Kernels.KPlus 24 τ (ModularGroup.S • Work.Kernels.imagAxis t ht)‖
                + ‖Work.Kernels.KMinus ℓ 24 τ (ModularGroup.S • Work.Kernels.imagAxis t ht)‖)) ∧
      (‖Work.CKFinal.Phi (Work.Kernels.Khat ℓ 24) τ t‖
          ≤ t ^ 10 * (‖Work.Kernels.KPlus 24 τ (ModularGroup.S • Work.Kernels.imagAxis t ht)‖
                + ‖Work.Kernels.KMinus ℓ 24 τ (ModularGroup.S • Work.Kernels.imagAxis t ht)‖)))
    (Cp Ap : ℝ) (hCp : 0 ≤ Cp) (hAp : 0 ≤ Ap)
    (hKp : ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t),
        (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y0 ≤ τ.im → 1 ≤ t →
        t ^ 10 * ‖Work.Kernels.KPlus 24 τ (ModularGroup.S • Work.Kernels.imagAxis t ht)‖
          ≤ Cp * (1 + ‖(τ : ℂ)‖) ^ Ap *
              (Real.exp (-(2 * Real.pi * τ.im)) *
                (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t))))))
    (Cm Am : ℝ) (hCm : 0 ≤ Cm) (hAm : 0 ≤ Am)
    (hKm : ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t),
        (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y0 ≤ τ.im → 1 ≤ t →
        t ^ 10 * ‖Work.Kernels.KMinus ℓ 24 τ (ModularGroup.S • Work.Kernels.imagAxis t ht)‖
          ≤ Cm * (1 + ‖(τ : ℂ)‖) ^ Am *
              (Real.exp (-(2 * Real.pi * τ.im)) *
                (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t))))))
    (CI : ℝ) (hCI : 0 < CI)
    (hI : ∀ y : ℝ, 1 ≤ y →
        MeasureTheory.IntegrableOn (fun t : ℝ => Real.exp (-(2 * Real.pi * y)) *
            (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (y - t))))) (Set.Ici 1) ∧
        ∫ t in Set.Ici (1 : ℝ), Real.exp (-(2 * Real.pi * y)) *
            (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (y - t))))
          ≤ CI * Real.exp (-(3 * Real.pi * y))) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (τ : UpperHalfPlane), (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y0 ≤ τ.im →
        (∫ t in Set.Ici 1, ‖Work.CKFinal.Phi (Work.Kernels.Kfun ℓ 24) τ t‖
            ≤ C * τ.im ^ N * Real.exp (-(3 * Real.pi * τ.im))) ∧
        (∫ t in Set.Ici 1, ‖Work.CKFinal.Phi (Work.Kernels.Khat ℓ 24) τ t‖
            ≤ C * τ.im ^ N * Real.exp (-(3 * Real.pi * τ.im))) := by
  set A : ℝ := max Ap Am with hAdef
  have hA0 : 0 ≤ A := by rw [hAdef]; exact le_trans hAp (le_max_left Ap Am)
  have hApA : Ap ≤ A := by rw [hAdef]; exact le_max_left Ap Am
  have hAmA : Am ≤ A := by rw [hAdef]; exact le_max_right Ap Am
  refine ⟨2 * (Cp + Cm) * CI * (2 : ℝ) ^ (2 * A) + 1, A, by positivity, hA0, ?_⟩
  intro τ hre hYτ
  have hy1 : 1 ≤ τ.im := by linarith
  have hy0 : 0 < τ.im := by linarith
  have hsτ1 : (1 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by have := norm_nonneg (τ : ℂ); linarith
  have hsτ0 : (0 : ℝ) ≤ 1 + ‖(τ : ℂ)‖ := by linarith
  have hτn_le : 1 + ‖(τ : ℂ)‖ ≤ 2 * (1 + τ.im) := by
    have h1 := Complex.norm_le_abs_re_add_abs_im (τ : ℂ)
    rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, abs_of_pos hy0] at h1
    have h2 : |τ.re| = 1 / 2 := by rcases hre with h | h <;> rw [h] <;> norm_num
    rw [h2] at h1
    linarith
  set B : ℝ := 2 * (Cp + Cm) * (1 + ‖(τ : ℂ)‖) ^ A with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  set Ecusp : ℝ → ℝ := fun t => Real.exp (-(2 * Real.pi * τ.im)) *
      (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t)))) with hEdef
  have hEcusp0 : ∀ t, 0 ≤ Ecusp t := fun t => by rw [hEdef]; positivity
  have hEint : MeasureTheory.Integrable (Ecusp) (MeasureTheory.volume.restrict (Set.Ici 1)) := by
    have h := (hI τ.im hy1).1
    rw [hEdef]; exact h
  have hEval : ∫ t in Set.Ici (1 : ℝ), Ecusp t ≤ CI * Real.exp (-(3 * Real.pi * τ.im)) := by
    rw [hEdef]; exact (hI τ.im hy1).2
  have hXA : (1 + ‖(τ : ℂ)‖) ^ A ≤ (2 : ℝ) ^ (2 * A) * τ.im ^ A := by
    have h2 : (1 + ‖(τ:ℂ)‖) ^ A ≤ (2 * (1 + τ.im)) ^ A :=
      Real.rpow_le_rpow (by positivity) hτn_le hA0
    have h3 : (2 * (1 + τ.im)) ^ A = (2:ℝ)^A * (1 + τ.im)^A :=
      Real.mul_rpow (by norm_num) (by linarith)
    have h4 : (1 + τ.im) ^ A ≤ (2 * τ.im) ^ A :=
      Real.rpow_le_rpow (by linarith) (by linarith) hA0
    have h5 : (2 * τ.im) ^ A = (2:ℝ)^A * τ.im^A := Real.mul_rpow (by norm_num) (by linarith)
    have h6 : (2:ℝ)^A * (2:ℝ)^A = (2:ℝ)^(2*A) := by
      rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      congr 1; ring
    calc (1 + ‖(τ:ℂ)‖)^A ≤ (2*(1+τ.im))^A := h2
      _ = (2:ℝ)^A * (1+τ.im)^A := h3
      _ ≤ (2:ℝ)^A * ((2:ℝ)^A * τ.im^A) :=
          mul_le_mul_of_nonneg_left (le_trans h4 (le_of_eq h5)) (Real.rpow_nonneg (by norm_num) A)
      _ = (2:ℝ)^(2*A) * τ.im^A := by rw [← mul_assoc, h6]
  have arith : B * (CI * Real.exp (-(3 * Real.pi * τ.im))) ≤
      (2 * (Cp + Cm) * CI * (2 : ℝ) ^ (2 * A) + 1) * τ.im ^ A *
        Real.exp (-(3 * Real.pi * τ.im)) := by
    have hyA0 : 0 ≤ τ.im ^ A := Real.rpow_nonneg (by linarith) A
    have he0 : 0 ≤ Real.exp (-(3 * Real.pi * τ.im)) := (Real.exp_pos _).le
    have hXe : (1 + ‖(τ:ℂ)‖)^A * Real.exp (-(3*Real.pi*τ.im))
        ≤ ((2:ℝ)^(2*A) * τ.im^A) * Real.exp (-(3*Real.pi*τ.im)) :=
      mul_le_mul_of_nonneg_right hXA he0
    have hk0 : 0 ≤ 2 * (Cp + Cm) * CI := by positivity
    calc B * (CI * Real.exp (-(3*Real.pi*τ.im)))
        = (2 * (Cp + Cm) * CI) * ((1+‖(τ:ℂ)‖)^A * Real.exp (-(3*Real.pi*τ.im))) := by
            rw [hBdef]; ring
      _ ≤ (2 * (Cp + Cm) * CI) * (((2:ℝ)^(2*A) * τ.im^A) * Real.exp (-(3*Real.pi*τ.im))) :=
            mul_le_mul_of_nonneg_left hXe hk0
      _ = (2 * (Cp + Cm) * CI * (2:ℝ)^(2*A)) * (τ.im^A * Real.exp (-(3*Real.pi*τ.im))) := by ring
      _ ≤ (2 * (Cp + Cm) * CI * (2:ℝ)^(2*A) + 1) * (τ.im^A * Real.exp (-(3*Real.pi*τ.im))) :=
            mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hyA0 he0)
      _ = (2 * (Cp + Cm) * CI * (2:ℝ)^(2*A) + 1) * τ.im ^ A *
            Real.exp (-(3 * Real.pi * τ.im)) := by ring
  have key : ∀ (K : UpperHalfPlane → UpperHalfPlane → ℂ)
      (hK : ∀ (s : ℝ) (hs : 0 < s),
        ‖Work.CKFinal.Phi K τ s‖ ≤ s ^ 10 *
          (‖Work.Kernels.KPlus 24 τ (ModularGroup.S • Work.Kernels.imagAxis s hs)‖
           + ‖Work.Kernels.KMinus ℓ 24 τ (ModularGroup.S • Work.Kernels.imagAxis s hs)‖)),
      ∫ t in Set.Ici 1, ‖Work.CKFinal.Phi K τ t‖ ≤ B * (CI * Real.exp (-(3 * Real.pi * τ.im))) := by
    intro K hK
    have hle : ∀ t : ℝ, 1 ≤ t → ‖Work.CKFinal.Phi K τ t‖ ≤ B * Ecusp t := by
      intro t ht1
      have ht0 : 0 < t := by linarith
      have hEp0 : 0 ≤ Ecusp t := hEcusp0 t
      have hXA0 : (0:ℝ) ≤ (1 + ‖(τ : ℂ)‖) ^ A := Real.rpow_nonneg hsτ0 A
      have hbp : t ^ 10 * ‖Work.Kernels.KPlus 24 τ (ModularGroup.S • Work.Kernels.imagAxis t ht0)‖
          ≤ (Cp + Cm) * (1 + ‖(τ : ℂ)‖) ^ A * Ecusp t := by
        have hp := hKp τ t ht0 hre hYτ ht1
        rw [hEdef]
        calc t ^ 10 * ‖Work.Kernels.KPlus 24 τ (ModularGroup.S • Work.Kernels.imagAxis t ht0)‖
            ≤ Cp * (1 + ‖(τ : ℂ)‖) ^ Ap * (Real.exp (-(2 * Real.pi * τ.im)) *
                (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t))))) := hp
          _ ≤ (Cp + Cm) * (1 + ‖(τ : ℂ)‖) ^ A * (Real.exp (-(2 * Real.pi * τ.im)) *
                (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t))))) := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              calc Cp * (1 + ‖(τ : ℂ)‖) ^ Ap ≤ Cp * (1 + ‖(τ : ℂ)‖) ^ A :=
                    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hsτ1 hApA) hCp
                _ ≤ (Cp + Cm) * (1 + ‖(τ : ℂ)‖) ^ A :=
                    mul_le_mul_of_nonneg_right (by linarith) hXA0
      have hbm : t ^ 10 * ‖Work.Kernels.KMinus ℓ 24 τ (ModularGroup.S • Work.Kernels.imagAxis t ht0)‖
          ≤ (Cp + Cm) * (1 + ‖(τ : ℂ)‖) ^ A * Ecusp t := by
        have hm := hKm τ t ht0 hre hYτ ht1
        rw [hEdef]
        calc t ^ 10 * ‖Work.Kernels.KMinus ℓ 24 τ (ModularGroup.S • Work.Kernels.imagAxis t ht0)‖
            ≤ Cm * (1 + ‖(τ : ℂ)‖) ^ Am * (Real.exp (-(2 * Real.pi * τ.im)) *
                (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t))))) := hm
          _ ≤ (Cp + Cm) * (1 + ‖(τ : ℂ)‖) ^ A * (Real.exp (-(2 * Real.pi * τ.im)) *
                (Real.exp (-(Real.pi * t)) / (1 + Real.exp (2 * Real.pi * (τ.im - t))))) := by
              refine mul_le_mul_of_nonneg_right ?_ (by positivity)
              calc Cm * (1 + ‖(τ : ℂ)‖) ^ Am ≤ Cm * (1 + ‖(τ : ℂ)‖) ^ A :=
                    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hsτ1 hAmA) hCm
                _ ≤ (Cp + Cm) * (1 + ‖(τ : ℂ)‖) ^ A :=
                    mul_le_mul_of_nonneg_right (by linarith) hXA0
      have hsum : t ^ 10 * (‖Work.Kernels.KPlus 24 τ (ModularGroup.S • Work.Kernels.imagAxis t ht0)‖
            + ‖Work.Kernels.KMinus ℓ 24 τ (ModularGroup.S • Work.Kernels.imagAxis t ht0)‖)
          ≤ B * Ecusp t := by
        have e : t ^ 10 * (‖Work.Kernels.KPlus 24 τ (ModularGroup.S • Work.Kernels.imagAxis t ht0)‖
              + ‖Work.Kernels.KMinus ℓ 24 τ (ModularGroup.S • Work.Kernels.imagAxis t ht0)‖)
            = t ^ 10 * ‖Work.Kernels.KPlus 24 τ (ModularGroup.S • Work.Kernels.imagAxis t ht0)‖
              + t ^ 10 * ‖Work.Kernels.KMinus ℓ 24 τ
                  (ModularGroup.S • Work.Kernels.imagAxis t ht0)‖ := by
          ring
        rw [e]
        calc t ^ 10 * ‖Work.Kernels.KPlus 24 τ (ModularGroup.S • Work.Kernels.imagAxis t ht0)‖
              + t ^ 10 * ‖Work.Kernels.KMinus ℓ 24 τ (ModularGroup.S • Work.Kernels.imagAxis t ht0)‖
            ≤ (Cp + Cm) * (1 + ‖(τ : ℂ)‖) ^ A * Ecusp t
              + (Cp + Cm) * (1 + ‖(τ : ℂ)‖) ^ A * Ecusp t := add_le_add hbp hbm
          _ = B * Ecusp t := by rw [hBdef]; ring
      exact le_trans (hK t ht0) hsum
    have hIntB : MeasureTheory.Integrable (fun t => B * Ecusp t)
        (MeasureTheory.volume.restrict (Set.Ici 1)) := hEint.const_mul B
    calc ∫ t in Set.Ici 1, ‖Work.CKFinal.Phi K τ t‖
        ≤ ∫ t in Set.Ici 1, B * Ecusp t := by
          refine MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun t => norm_nonneg _)) hIntB ?_
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with t ht
          exact hle t ht
      _ = B * ∫ t in Set.Ici 1, Ecusp t := MeasureTheory.integral_const_mul B _
      _ ≤ B * (CI * Real.exp (-(3 * Real.pi * τ.im))) := mul_le_mul_of_nonneg_left hEval hB0
  exact ⟨(key (Work.Kernels.Kfun ℓ 24) (fun s hs => (haxis τ s hs).1)).trans arith,
         (key (Work.Kernels.Khat ℓ 24) (fun s hs => (haxis τ s hs).2)).trans arith⟩

/-- **The tail bound for `Φ` on the lines `Re τ = ±1/2` in dimension `24`.**

For `Re τ = ±1/2` and `Im τ` large, both tail integrals `∫_{t ≥ 1} ‖Φ(K^{(24)}, τ, t)‖ dt` and
`∫_{t ≥ 1} ‖Φ(K̂^{(24)}, τ, t)‖ dt` decay like `e^{-3π Im τ}` up to a power of `Im τ`.  The proof
combines the axis reduction `Phi_axis_norm_twentyfour`, the two slashed-kernel cusp bounds
`KPlus_tail_lines_twentyfour`/`KMinus_tail_lines_twentyfour` (whose divisor input is
`DenomLower_lines`) and the elementary tail integral `Tail_integral_twentyfour`. -/
theorem Phi_tail_bound_twentyfour (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N Y₀ : ℝ, 0 ≤ C ∧ 0 ≤ N ∧ 1 ≤ Y₀ ∧
      ∀ (τ : UpperHalfPlane), (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y₀ ≤ τ.im →
        (∫ t in Set.Ici 1, ‖Work.CKFinal.Phi (Work.Kernels.Kfun ℓ 24) τ t‖
            ≤ C * τ.im ^ N * Real.exp (-(3 * Real.pi * τ.im))
          ∧ ∫ t in Set.Ici 1, ‖Work.CKFinal.Phi (Work.Kernels.Khat ℓ 24) τ t‖
            ≤ C * τ.im ^ N * Real.exp (-(3 * Real.pi * τ.im))) := by
  obtain ⟨c, Yc, hc, hYc, hD⟩ := DenomLower_lines
  set Y : ℝ := max Yc 2 with hYdef
  have hY1 : 1 ≤ Y := by rw [hYdef]; exact le_trans hYc (le_max_left Yc 2)
  have hY2 : 2 ≤ Y := by rw [hYdef]; exact le_max_right Yc 2
  have hD' : ∀ (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t),
      (τ.re = 1 / 2 ∨ τ.re = -1 / 2) → Y ≤ τ.im → 1 ≤ t →
      c * (Real.exp (-(2 * Real.pi * t)) + Real.exp (-(2 * Real.pi * τ.im)))
        ≤ ‖Work.Kernels.DeltaFun τ * Work.Kernels.DeltaFun (Work.Kernels.imagAxis t ht) *
            (Work.Kernels.jInvariantFun τ
              - Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht))‖ :=
    fun τ t ht hre hYτ ht1 =>
      hD τ t ht hre (le_trans (le_max_left Yc 2) hYτ) ht1
  obtain ⟨Cp, Ap, hCp, hAp, hKp⟩ := KPlus_tail_lines_twentyfour ℓ c Y hc hY2 hD'
  obtain ⟨Cm, Am, hCm, hAm, hKm⟩ := KMinus_tail_lines_twentyfour ℓ c Y hc hY2 hD'
  obtain ⟨CI, hCI, hI⟩ := Tail_integral_twentyfour
  obtain ⟨C, N, hC, hN, hmain⟩ :=
    tail_assembly_twentyfour ℓ Y hY2 (Phi_axis_norm_twentyfour ℓ)
      Cp Ap hCp hAp hKp Cm Am hCm hAm hKm CI hCI hI
  exact ⟨C, N, Y, hC, hN, hY1, fun τ hre hYτ => hmain τ hre hYτ⟩

end

end Work.CKFinal.LineDecay
