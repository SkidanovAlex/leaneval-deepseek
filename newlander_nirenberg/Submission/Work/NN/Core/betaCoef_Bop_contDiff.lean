import Mathlib
import Submission.Work.NN.Core.DbarCnPertAux

/-!
# Smoothness of the Beltrami coefficients `β`, `Bop` and `BopBar`

For a smooth family `A : ℂⁿ → (ℂⁿ →L[ℝ] ℂⁿ)` of perturbations of the standard complex
structure, this file proves that the Beltrami coefficients

`betaCoef A k j z = -(I/2) · (A z e_k)_j`

are `C^∞` in `z`, and hence also the matrix-valued maps `z ↦ Bop A z` and `z ↦ BopBar A z`
of the (implicit) Beltrami system `dbarCoord_eq_beltrami_implicit`.

The only non-trivial point is that the scalar argument of `ContinuousLinearMap.smulRight`
may live in a *larger* scalar ring than the base field (here `ℝ ⊆ ℂ`), for which Mathlib's
`ContDiff.smulRight` (restricted to `StrongDual`) does not apply. We therefore build the
curried map `c ↦ f.smulRight c` as an explicit continuous linear map.
-/

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Core

variable {n : ℕ}

/-- The continuous linear map `c ↦ f.smulRight c`, for a fixed `f : ℂⁿ →L[ℝ] ℂ`. -/
private noncomputable def smulRightCLM (f : Cn n →L[ℝ] ℂ) : ℂ →L[ℝ] (Cn n →L[ℝ] ℂ) :=
  LinearMap.mkContinuous (f.smulRightₗ) ‖f‖ (fun c => by
    rw [ContinuousLinearMap.coe_smulRightₗ]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
    rw [ContinuousLinearMap.smulRight_apply, norm_smul]
    calc ‖f v‖ * ‖c‖ ≤ (‖f‖ * ‖v‖) * ‖c‖ := by gcongr; exact f.le_opNorm v
      _ = ‖f‖ * ‖c‖ * ‖v‖ := by ring)

private lemma smulRightCLM_apply (f : Cn n →L[ℝ] ℂ) (c : ℂ) :
    smulRightCLM f c = f.smulRight c := by
  simp only [smulRightCLM, LinearMap.mkContinuous_apply, ContinuousLinearMap.coe_smulRightₗ]

/-- Each Beltrami coefficient `z ↦ betaCoef A k j z` is `C^∞`. -/
theorem betaCoef_contDiff (A : Cn n → Cn n →L[ℝ] Cn n)
    (hA : ∀ m, ContDiff ℝ m A) (k j : Fin n) :
    ContDiff ℝ ⊤ (fun z => betaCoef A k j z) := by
  unfold betaCoef
  fun_prop

/-- General form of the smoothness of `Bop`/`BopBar`: for any `C^∞` map `φ : ℂ → ℂ`, the
family `z ↦ pi (fun k => ∑ j, smulRight (proj j) (φ (betaCoef A k j z)))` is `C^∞`. -/
theorem contDiff_pi_smulRight_betaCoef (A : Cn n → Cn n →L[ℝ] Cn n)
    (hA : ∀ m, ContDiff ℝ m A) {φ : ℂ → ℂ} (hφ : ContDiff ℝ ⊤ φ) :
    ContDiff ℝ ⊤ (fun z => ContinuousLinearMap.pi (fun k : Fin n => ∑ j : Fin n,
      ContinuousLinearMap.smulRight (ContinuousLinearMap.proj j : Cn n →L[ℝ] ℂ)
        (φ (betaCoef A k j z)))) := by
  have hβ : ∀ k j : Fin n, ContDiff ℝ ⊤ (fun z => betaCoef A k j z) :=
    fun k j => betaCoef_contDiff A hA k j
  -- the componentwise family is `C^∞`, as a function into the Pi type
  have hg : ContDiff ℝ ⊤ (fun z : Cn n => fun k : Fin n => ∑ j : Fin n,
      ContinuousLinearMap.smulRight (ContinuousLinearMap.proj j : Cn n →L[ℝ] ℂ)
        (φ (betaCoef A k j z))) := by
    refine contDiff_pi.mpr (fun k => ?_)
    have hsum : ContDiff ℝ ⊤ (fun z : Cn n => ∑ j : Fin n,
        ContinuousLinearMap.smulRight (ContinuousLinearMap.proj j : Cn n →L[ℝ] ℂ)
          (φ (betaCoef A k j z))) := by
      refine ContDiff.sum (s := Finset.univ) (f := fun (j : Fin n) (z : Cn n) =>
        ContinuousLinearMap.smulRight (ContinuousLinearMap.proj j : Cn n →L[ℝ] ℂ)
          (φ (betaCoef A k j z))) (fun j _ => ?_)
      have h1 : ContDiff ℝ ⊤ (fun z => φ (betaCoef A k j z)) := hφ.comp (hβ k j)
      have h2 := (smulRightCLM (ContinuousLinearMap.proj j : Cn n →L[ℝ] ℂ)).contDiff.comp h1
      convert h2 using 1
      funext z
      rw [Function.comp_apply, smulRightCLM_apply]
    simpa using hsum
  -- transport along `ContinuousLinearMap.piEquivL`
  have h3 := (ContinuousLinearEquiv.comp_contDiff_iff
      (ContinuousLinearMap.piEquivL ℝ (Cn n) (fun _ : Fin n => ℂ))).mpr hg
  convert h3 using 1
  funext z
  rw [Function.comp_apply, ContinuousLinearMap.piEquivL_apply]

theorem betaCoef_Bop_contDiff {n : ℕ} (A : Cn n → Cn n →L[ℝ] Cn n)
    (hA : ∀ m, ContDiff ℝ m A) :
    (∀ k j, ContDiff ℝ ⊤ (fun z => betaCoef A k j z)) ∧
    ContDiff ℝ ⊤ (fun z => Bop A z) ∧ ContDiff ℝ ⊤ (fun z => BopBar A z) := by
  have hconj : ContDiff ℝ ⊤ (starRingEnd ℂ : ℂ → ℂ) := by
    have h : ContDiff ℝ ⊤ (⇑Complex.conjCLE) := Complex.conjCLE.contDiff (n := ⊤)
    rwa [funext Complex.conjCLE_apply] at h
  refine ⟨fun k j => betaCoef_contDiff A hA k j, ?_, ?_⟩
  · simpa only [Bop, id_eq] using contDiff_pi_smulRight_betaCoef A hA contDiff_id
  · simpa only [BopBar] using contDiff_pi_smulRight_betaCoef A hA hconj

end Work.NN.Core
