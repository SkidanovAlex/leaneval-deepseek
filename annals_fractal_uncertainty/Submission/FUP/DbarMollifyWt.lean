import Submission.FUP.DbarLocalize
import Submission.Commons.Analysis.Calculus.fderiv_fderiv_swap
import Submission.Commons.MeasureTheory.integrable_mul_shift_sub_prod

open MeasureTheory Metric Filter Function
open scoped ENNReal BigOperators ContDiff

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Mollifying the weight: transferring the distributional positivity `∂∂̄φ ≥ κ`

`DbarDbarPos φ κ` (`Submission/FUP/Dbar.lean`) is the distributional form of `∂∂̄φ ≥ κ`.  This
module proves that it is preserved by mollifying the *weight*:

* `dbarDbarTest_comp_add` — translation invariance of the test functional;
* `DbarDbarPos.convolution` — from `DbarDbarPos φ κ` deduce
  `DbarDbarPos (φ * K) (κ * K)` for a smooth nonnegative kernel `K` with `∫K = 1`.

This is the analytic input of the Fatou/Montel approximation argument (gap (H) of the Hörmander
project) which removes the smoothness hypothesis on the weight.
-/

namespace Submission.FUP

variable {d : ℕ}
local notation "ℂᵈ" => (Fin d → ℂ)

section Trans

/-- Translation invariance of the real quadratic functions attached to a test form. -/
lemma formTest_comp_add (α : ℂᵈ → (Fin d → ℂ)) (c : ℂᵈ) (j k : Fin d) :
    formTest (fun z => α (z + c)) j k = fun z => formTest α j k (z + c) := rfl

lemma formImag_comp_add (α : ℂᵈ → (Fin d → ℂ)) (c : ℂᵈ) (j k : Fin d) :
    formImag (fun z => α (z + c)) j k = fun z => formImag α j k (z + c) := rfl

lemma dxx_comp_add (ψ : ℂᵈ → ℝ) (c : ℂᵈ) (j k : Fin d) :
    dxx j k (fun z => ψ (z + c)) = fun z => dxx j k ψ (z + c) := by
  funext z
  simp only [dxx, iteratedFDeriv_comp_add_right]

lemma dyy_comp_add (ψ : ℂᵈ → ℝ) (c : ℂᵈ) (j k : Fin d) :
    dyy j k (fun z => ψ (z + c)) = fun z => dyy j k ψ (z + c) := by
  funext z
  simp only [dyy, iteratedFDeriv_comp_add_right]

lemma dxy_comp_add (ψ : ℂᵈ → ℝ) (c : ℂᵈ) (j k : Fin d) :
    dxy j k (fun z => ψ (z + c)) = fun z => dxy j k ψ (z + c) := by
  funext z
  simp only [dxy, iteratedFDeriv_comp_add_right]

lemma dyx_comp_add (ψ : ℂᵈ → ℝ) (c : ℂᵈ) (j k : Fin d) :
    dyx j k (fun z => ψ (z + c)) = fun z => dyx j k ψ (z + c) := by
  funext z
  simp only [dyx, iteratedFDeriv_comp_add_right]

/-- **Translation invariance of the test functional** `dbarDbarTest`:
`dbarDbarTest (α(·+c)) z = dbarDbarTest α (z+c)`. -/
lemma dbarDbarTest_comp_add (α : ℂᵈ → (Fin d → ℂ)) (c : ℂᵈ) :
    dbarDbarTest (fun z => α (z + c)) = fun z => dbarDbarTest α (z + c) := by
  funext z
  simp only [dbarDbarTest]
  congr 1
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [formTest_comp_add, formImag_comp_add, dxx_comp_add, dyy_comp_add, dxy_comp_add,
    dyx_comp_add]

end Trans

section Mollify

open scoped Convolution

/-- The mollification of a weight `φ` against a kernel `K`, in the kernel-derivative form
`z ↦ ∫ s, K (z - s) * φ s` (equal to `∫ t, K t * φ (z - t)`). -/
noncomputable def mollWt (K φ : ℂᵈ → ℝ) (z : ℂᵈ) : ℝ := ∫ s, K (z - s) * φ s

lemma mollWt_apply (K φ : ℂᵈ → ℝ) (z : ℂᵈ) : mollWt K φ z = ∫ s, K (z - s) * φ s := rfl

/-- The two forms of the mollification agree. -/
lemma mollWt_eq (K φ : ℂᵈ → ℝ) (z : ℂᵈ) :
    mollWt K φ z = ∫ t, K t * φ (z - t) := by
  rw [mollWt]
  simpa using integral_sub_left_eq_self (fun t => K t * φ (z - t)) volume z

lemma mollWt_eq_fun (K φ : ℂᵈ → ℝ) :
    mollWt K φ = fun z => ∫ t, K t * φ (z - t) := funext (mollWt_eq K φ)

/-- A mollification against a smooth compactly supported kernel is smooth. -/
lemma contDiff_mollWt {K φ : ℂᵈ → ℝ} (hKc : ContDiff ℝ ∞ K) (hKs : HasCompactSupport K)
    (hφm : LocallyIntegrable φ (volume : Measure (ℂᵈ))) : ContDiff ℝ ∞ (mollWt K φ) := by
  have h : ContDiff ℝ ∞ (fun z => ∫ s, K (z - s) * φ s) := by
    have h' := hKs.contDiff_convolution_right (L := ContinuousLinearMap.mul ℝ ℝ)
      (μ := volume) hφm hKc
    have hfun : (φ ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] K) = fun z => ∫ s, K (z - s) * φ s := by
      funext z
      rw [convolution_def]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      change (φ t) * (K (z - t)) = K (z - t) * φ t
      ring
    rwa [hfun] at h'
  exact h

/-- **The Fubini/substitution identity for mollifications.**
`∫ (K * φ) · T = ∫ t, K t · (∫ z, φ z · T (z + t))`. -/
theorem integral_mollWt_mul {K T φ : ℂᵈ → ℝ} (hKc : Continuous K) (hKs : HasCompactSupport K)
    (hTc : Continuous T) (hTs : HasCompactSupport T)
    (hφm : LocallyIntegrable φ (volume : Measure (ℂᵈ))) :
    ∫ z, (∫ t, K t * φ (z - t)) * T z
      = ∫ t, K t * (∫ z, φ z * T (z + t)) := by
  have hInt := Commons.MeasureTheory.integrable_mul_shift_sub_prod (d := d) hKc hKs hTc hTs hφm
  have hz : ∀ z : ℂᵈ, (∫ t, K t * φ (z - t)) * T z = ∫ t, K t * φ (z - t) * T z := by
    intro z
    rw [show (∫ t, K t * φ (z - t)) * T z = T z * ∫ t, K t * φ (z - t) from mul_comm _ _,
      ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    ring
  rw [show (∫ z, (∫ t, K t * φ (z - t)) * T z) = ∫ z, ∫ t, K t * φ (z - t) * T z from
    integral_congr_ae (Eventually.of_forall hz)]
  rw [show (∫ z, ∫ t, K t * φ (z - t) * T z) = ∫ t, ∫ z, K t * φ (z - t) * T z from
    (integral_integral_swap hInt).symm]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  show (∫ z, K t * φ (z - t) * T z) = K t * ∫ z, φ z * T (z + t)
  rw [show (∫ z, K t * φ (z - t) * T z) = ∫ z, K t * (φ (z - t) * T z) from
    integral_congr_ae (Eventually.of_forall fun z => by ring)]
  rw [integral_const_mul]
  congr 1
  rw [← integral_add_right_eq_self (fun z => φ (z - t) * T z) t]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  show φ (z + t - t) * T (z + t) = φ z * T (z + t)
  rw [add_sub_cancel_right]

end Mollify

section Transfer

open scoped Convolution

/-- **`DbarDbarPos` is preserved by mollifying the weight against a smooth nonnegative kernel.**

This is the analytic input of the Fatou/Montel approximation argument that removes the smoothness
hypothesis on the plurisubharmonic weight in Hörmander's theorem. -/
theorem DbarDbarPos.mollify {φ κ : ℂᵈ → ℝ} {K : ℂᵈ → ℝ}
    (hKc : ContDiff ℝ ∞ K) (hKs : HasCompactSupport K) (hKnn : ∀ t, 0 ≤ K t)
    (hφm : LocallyIntegrable φ (volume : Measure (ℂᵈ)))
    (hκm : LocallyIntegrable κ (volume : Measure (ℂᵈ)))
    (h : DbarDbarPos φ κ) :
    DbarDbarPos (mollWt K φ) (mollWt K κ) := by
  intro α hα hαs
  set W : ℂᵈ → ℝ := fun z => formNormSq α z with hW
  set T : ℂᵈ → ℝ := fun z => dbarDbarTest α z with hT
  have hWc : Continuous W := continuous_formNormSq hα.continuous
  have hWs : HasCompactSupport W := hasCompactSupport_formNormSq hαs
  have hTc : Continuous T := continuous_dbarDbarTest hα
  have hTs : HasCompactSupport T := hasCompactSupport_dbarDbarTest hαs
  have hKcon : Continuous K := hKc.continuous
  -- the pointwise-in-`t` inequality, from `h` applied to the translated test form
  have hstep : ∀ t : ℂᵈ, (∫ z, κ z * W (z + t)) ≤ ∫ z, φ z * T (z + t) := by
    intro t
    have hαt : ContDiff ℝ ∞ (fun z => α (z + t)) := hα.comp (contDiff_id.add contDiff_const)
    have hαts : HasCompactSupport (fun z => α (z + t)) :=
      hαs.comp_homeomorph (Homeomorph.addRight t)
    obtain ⟨-, -, hineq⟩ := h (fun z => α (z + t)) hαt hαts
    have e1 : (∫ z, κ z * formNormSq (fun z => α (z + t)) z) = ∫ z, κ z * W (z + t) := by
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [hW, formNormSq]
    have e2 : (∫ z, φ z * dbarDbarTest (fun z => α (z + t)) z) = ∫ z, φ z * T (z + t) := by
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      have hh := congrFun (dbarDbarTest_comp_add α t) z
      simp only [hT]
      rw [hh]
    rw [e1, e2] at hineq
    exact hineq
  -- integrability of the two `t`-level functions, from joint integrability and Fubini
  have hIntκ : Integrable (fun p : ℂᵈ × ℂᵈ => K p.1 * κ (p.2 - p.1) * W p.2)
      (volume.prod volume) :=
    Commons.MeasureTheory.integrable_mul_shift_sub_prod hKcon hKs hWc hWs hκm
  have hIntφ : Integrable (fun p : ℂᵈ × ℂᵈ => K p.1 * φ (p.2 - p.1) * T p.2)
      (volume.prod volume) :=
    Commons.MeasureTheory.integrable_mul_shift_sub_prod hKcon hKs hTc hTs hφm
  have hshift : ∀ t : ℂᵈ, (∫ z, K t * κ (z - t) * W z) = K t * ∫ z, κ z * W (z + t) := by
    intro t
    show (∫ z, K t * κ (z - t) * W z) = K t * ∫ z, κ z * W (z + t)
    rw [show (∫ z, K t * κ (z - t) * W z) = ∫ z, K t * (κ (z - t) * W z) from
      integral_congr_ae (Eventually.of_forall fun z => by ring)]
    rw [integral_const_mul]
    congr 1
    rw [← integral_add_right_eq_self (fun z => κ (z - t) * W z) t]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    show κ (z + t - t) * W (z + t) = κ z * W (z + t)
    rw [add_sub_cancel_right]
  have hshift' : ∀ t : ℂᵈ, (∫ z, K t * φ (z - t) * T z) = K t * ∫ z, φ z * T (z + t) := by
    intro t
    show (∫ z, K t * φ (z - t) * T z) = K t * ∫ z, φ z * T (z + t)
    rw [show (∫ z, K t * φ (z - t) * T z) = ∫ z, K t * (φ (z - t) * T z) from
      integral_congr_ae (Eventually.of_forall fun z => by ring)]
    rw [integral_const_mul]
    congr 1
    rw [← integral_add_right_eq_self (fun z => φ (z - t) * T z) t]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    show φ (z + t - t) * T (z + t) = φ z * T (z + t)
    rw [add_sub_cancel_right]
  have hIntA : Integrable (fun t => K t * (∫ z, κ z * W (z + t))) volume :=
    (hIntκ.integral_prod_left).congr (Eventually.of_forall fun t => by
      simpa only [] using hshift t)
  have hIntB : Integrable (fun t => K t * (∫ z, φ z * T (z + t))) volume :=
    (hIntφ.integral_prod_left).congr (Eventually.of_forall fun t => by
      simpa only [] using hshift' t)
  have hmono : (∫ t, K t * (∫ z, κ z * W (z + t)))
      ≤ ∫ t, K t * (∫ z, φ z * T (z + t)) :=
    integral_mono_ae hIntA hIntB (Eventually.of_forall fun t =>
      mul_le_mul_of_nonneg_left (hstep t) (hKnn t))
  -- assembly
  have hmollκ : Continuous (mollWt K κ) := (contDiff_mollWt hKc hKs hκm).continuous
  have hmollφ : Continuous (mollWt K φ) := (contDiff_mollWt hKc hKs hφm).continuous
  have hcsκ : HasCompactSupport (fun z => mollWt K κ z * W z) := hWs.mul_left
  have hcsφ : HasCompactSupport (fun z => mollWt K φ z * T z) := hTs.mul_left
  refine ⟨?_, ?_, ?_⟩
  · exact (hmollκ.mul hWc).integrable_of_hasCompactSupport hcsκ
  · exact (hmollφ.mul hTc).integrable_of_hasCompactSupport hcsφ
  · calc (∫ z, mollWt K κ z * W z)
        = ∫ z, (∫ t, K t * κ (z - t)) * W z := by rw [mollWt_eq_fun]
      _ = ∫ t, K t * (∫ z, κ z * W (z + t)) := integral_mollWt_mul hKcon hKs hWc hWs hκm
      _ ≤ ∫ t, K t * (∫ z, φ z * T (z + t)) := hmono
      _ = ∫ z, (∫ t, K t * φ (z - t)) * T z := (integral_mollWt_mul hKcon hKs hTc hTs hφm).symm
      _ = ∫ z, mollWt K φ z * T z := by rw [mollWt_eq_fun]

end Transfer

end Submission.FUP
