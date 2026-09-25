import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.DbarCnPertAux
import Submission.Work.NN.Core.dbarCn_implicit_form
import Submission.Work.NN.Core.exists_contDiff_bump_of_isCompact_subset
import Submission.Work.CR.Flat.Cauchy.holderNorm_univ_le_holderNorm_polydisc_of_vanishing
import Submission.Work.NN.Core.norm_inverse_one_add_sub_le
import Submission.Work.NN.Core.jholoBeltramiCoefSmall
import Submission.Work.NN.Core.beltramiCoefSmallZero
import Submission.Work.NN.Core.isInvertible_one_add_and_inverse_norm_le
import Submission.Work.NN.Core.dbarCoord_eq_beltramiCoeff_pointwise
import Submission.Work.NN.Core.jholoFrame_pre

namespace Work.NN.Core

noncomputable section
open scoped NNReal ENNReal ContDiff
open Set

/-!
# The Beltrami form of the perturbed `∂̄`-equation with a smooth compactly supported coefficient

The main result is `Work.NN.Core.exists_beltramiCoef_small_smooth`.  It is proved by cutting off
the perturbation with a smooth `[0,1]`-valued bump `χ` (equal to `1` near `polydisc 0 ρ₁`,
supported in `polydisc 0 ρ`) and taking `c := beltramiCoef (χ • A)`.  Two facts are needed:
the pointwise decoupled Beltrami form `dbarCoord_eq_beltramiCoeff_pointwise`, and the `C^{0,α}`
bound for the cut-off coefficient (`beltramiCoefSmallZero_c1`).  The latter is the classical
statement `beltramiCoefSmallZero` with the (unnecessarily strong) analytic hypothesis on `χ`
replaced by `C¹`; the smoothness of `beltramiCoef` is proved here in the finite-order form
`beltramiCoef_contDiff_infty`, since the classical statement `dbarCoord_eq_beltramiCoeff` uses the
analytic order `⊤`, which a compactly supported bump cannot satisfy.
-/

/-- `‖(a : ℂ) * b‖ = |a| * ‖b‖`. -/
private lemma norm_coe_mul_nn (a : ℝ) (b : ℂ) : ‖(a : ℂ) * b‖ = |a| * ‖b‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]

/-- Norm bound on `-(i/2)`. -/
private lemma norm_neg_I_half_nn : ‖(-(Complex.I / 2) : ℂ)‖ = 1 / 2 := by
  rw [norm_neg, norm_div, Complex.norm_I]
  norm_num

/-- The continuous linear map `c ↦ f.smulRight c`, for a fixed `f : ℂⁿ →L[ℝ] ℂ`. -/
private noncomputable def smulRightCLM_nn {n : ℕ} (f : Cn n →L[ℝ] ℂ) :
    ℂ →L[ℝ] (Cn n →L[ℝ] ℂ) :=
  LinearMap.mkContinuous (f.smulRightₗ) ‖f‖ (fun c => by
    rw [ContinuousLinearMap.coe_smulRightₗ]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
    rw [ContinuousLinearMap.smulRight_apply, norm_smul]
    calc ‖f v‖ * ‖c‖ ≤ (‖f‖ * ‖v‖) * ‖c‖ := by gcongr; exact f.le_opNorm v
      _ = ‖f‖ * ‖c‖ * ‖v‖ := by ring)

private lemma smulRightCLM_nn_apply {n : ℕ} (f : Cn n →L[ℝ] ℂ) (c : ℂ) :
    smulRightCLM_nn f c = f.smulRight c := by
  simp only [smulRightCLM_nn, LinearMap.mkContinuous_apply, ContinuousLinearMap.coe_smulRightₗ]

/-- Each Beltrami coefficient `z ↦ betaCoef A k j z` is `C^∞` (finite order) for a `C^∞` family
`A`. -/
private theorem betaCoef_contDiff_infty_aux {n : ℕ} (A : Cn n → Cn n →L[ℝ] Cn n)
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A) (k j : Fin n) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => betaCoef A k j z) := by
  unfold betaCoef
  fun_prop

/-- General form of the `C^∞` smoothness of `Bop`/`BopBar`: for any `C^∞` map `φ : ℂ → ℂ`, the
family `z ↦ pi (fun k => ∑ j, smulRight (proj j) (φ (betaCoef A k j z)))` is `C^∞`. -/
private theorem contDiff_pi_smulRight_betaCoef_infty {n : ℕ} (A : Cn n → Cn n →L[ℝ] Cn n)
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A) {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => ContinuousLinearMap.pi (fun k : Fin n => ∑ j : Fin n,
        ContinuousLinearMap.smulRight (ContinuousLinearMap.proj j : Cn n →L[ℝ] ℂ)
          (φ (betaCoef A k j z)))) := by
  have hβ : ∀ k j : Fin n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => betaCoef A k j z) :=
    fun k j => betaCoef_contDiff_infty_aux A hA k j
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Cn n => fun k : Fin n => ∑ j : Fin n,
      ContinuousLinearMap.smulRight (ContinuousLinearMap.proj j : Cn n →L[ℝ] ℂ)
        (φ (betaCoef A k j z))) := by
    refine contDiff_pi.mpr (fun k => ?_)
    have hsum : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Cn n => ∑ j : Fin n,
        ContinuousLinearMap.smulRight (ContinuousLinearMap.proj j : Cn n →L[ℝ] ℂ)
          (φ (betaCoef A k j z))) := by
      refine ContDiff.sum (s := Finset.univ) (f := fun (j : Fin n) (z : Cn n) =>
        ContinuousLinearMap.smulRight (ContinuousLinearMap.proj j : Cn n →L[ℝ] ℂ)
          (φ (betaCoef A k j z))) (fun j _ => ?_)
      have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => φ (betaCoef A k j z)) :=
        hφ.comp (hβ k j)
      have h2 := (smulRightCLM_nn (ContinuousLinearMap.proj j : Cn n →L[ℝ] ℂ)).contDiff.comp h1
      convert h2 using 1
      funext z
      rw [Function.comp_apply, smulRightCLM_nn_apply]
    simpa using hsum
  have h3 := (ContinuousLinearEquiv.comp_contDiff_iff
      (ContinuousLinearMap.piEquivL ℝ (Cn n) (fun _ : Fin n => ℂ))).mpr hg
  convert h3 using 1
  funext z
  rw [Function.comp_apply, ContinuousLinearMap.piEquivL_apply]

/-- `Bop` and `BopBar` of a `C^∞` (finite-order) family `A` are `C^∞`. -/
private theorem betaCoef_Bop_contDiff_infty {n : ℕ} (A : Cn n → Cn n →L[ℝ] Cn n)
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A) :
    (∀ k j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => betaCoef A k j z)) ∧
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => Bop A z) ∧
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => BopBar A z) := by
  have hconj : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (starRingEnd ℂ : ℂ → ℂ) := by
    have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑Complex.conjCLE) :=
      Complex.conjCLE.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
    rwa [funext Complex.conjCLE_apply] at h
  refine ⟨fun k j => betaCoef_contDiff_infty_aux A hA k j, ?_, ?_⟩
  · simpa only [Bop, id_eq] using contDiff_pi_smulRight_betaCoef_infty A hA contDiff_id
  · simpa only [BopBar] using contDiff_pi_smulRight_betaCoef_infty A hA hconj

/-- **Smoothness of the decoupled Beltrami coefficient, finite-order form.**  If `A` is `C^∞`
(finite order) and `‖BopBar A z‖ ≤ 1/4` everywhere, then every entry `z ↦ beltramiCoef A k j z`
is `C^∞`. -/
theorem beltramiCoef_contDiff_infty {n : ℕ}
    (A : Cn n → Cn n →L[ℝ] Cn n)
    (hA : ∀ m : ℕ, ContDiff ℝ m A)
    (hq : ∀ z, ‖BopBar A z‖ ≤ 1 / 4) (k j : Fin n) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (beltramiCoef A k j) := by
  have hA' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A := contDiff_infty.mpr hA
  obtain ⟨_, hBop, hBopBar⟩ := betaCoef_Bop_contDiff_infty A hA'
  have hInv : ∀ z, (1 + BopBar A z).IsInvertible := fun z =>
    (isInvertible_one_add_and_inverse_norm_le (hq z)).1
  have hY : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => ContinuousLinearMap.inverse (1 + BopBar A z)) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    have hz : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w => (1 : Cn n →L[ℝ] Cn n) + BopBar A w) z :=
      ((contDiff_const (c := (1 : Cn n →L[ℝ] Cn n))).add hBopBar).contDiffAt
    have h := (ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse (hInv z)).comp z hz
    simpa only [Function.comp_def] using h
  have hY' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Cn n =>
      (ContinuousLinearMap.inverse (1 + BopBar A z) : Cn n →L[ℝ] Cn n)) := hY
  have hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Cn n =>
      (ContinuousLinearMap.inverse (1 + BopBar A z) : Cn n →L[ℝ] Cn n) ∘SL Bop A z) :=
    hY'.clm_comp hBop
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Cn n =>
      ((ContinuousLinearMap.inverse (1 + BopBar A z) : Cn n →L[ℝ] Cn n) ∘SL Bop A z)
        (Pi.single j (1 : ℂ) : Cn n)) :=
    hΨ.clm_apply (contDiff_const : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun _ : Cn n => (Pi.single j (1 : ℂ) : Cn n)))
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Cn n =>
      (ContinuousLinearMap.proj k : Cn n →L[ℝ] ℂ)
        (((ContinuousLinearMap.inverse (1 + BopBar A z) : Cn n →L[ℝ] Cn n) ∘SL Bop A z)
          (Pi.single j (1 : ℂ) : Cn n))) :=
    ((ContinuousLinearMap.proj k : Cn n →L[ℝ] ℂ).contDiff).comp h1
  convert h2 using 1
  ext z
  simp only [beltramiCoef, beltramiCoeff, mul_apply_eq_comp, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.comp_apply]


theorem beltramiCoefSmallZero_c1 {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
        (hA : ∀ m : ℕ, ContDiff ℝ m A) (χ : Work.NN.Core.Cn n → ℝ),
        ContDiff ℝ 1 χ → HasCompactSupport χ →
        (∀ z, χ z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ) →
        (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) →
        (∀ z, ‖fderiv ℝ χ z‖ ≤ M) →
        ∀ {ε : ℝ}, 0 ≤ ε → ε ≤ 1 / (2 * (n : ℝ)) →
        (∀ i j : Fin n, Work.CR.Flat.holderNorm 0 α
          (fun z => A z (Pi.single i 1) j) (Work.CR.Flat.polydisc 0 ρ)
          ≤ ENNReal.ofReal ε) →
        ∀ k j : Fin n,
          Work.CR.Flat.holderNorm 0 α
            (fun z => Work.NN.Core.beltramiCoef (fun z => χ z • A z) k j z) Set.univ
            ≤ ENNReal.ofReal (C * ε * (1 + M)) := by
  refine ⟨7 * (n : ℝ) + 1, by positivity, ?_⟩
  intro A hA χ hχsmooth hχcpt hχsupp hχ01 hχgrad ε hε hεsmall hεH k j
  set D : Cn n → Cn n →L[ℝ] Cn n := fun w => χ w • A w with hDdef
  -- (1) pointwise bounds on the entries of `A` on the polydisc
  have hentry : ∀ (i j : Fin n) (z : Cn n), z ∈ Work.CR.Flat.polydisc 0 ρ →
      ‖A z (Pi.single i 1) j‖ ≤ ε := by
    intro i j z hz
    have h1 := Work.CR.Flat.norm_apply_le_holderNorm 0 α (fun z => A z (Pi.single i 1) j)
      (Work.CR.Flat.polydisc 0 ρ) hz
    exact (ENNReal.ofReal_le_ofReal_iff hε).mp (le_trans h1 (hεH i j))
  -- (2) smoothness of the entries
  have hsmooth : ∀ i j : Fin n, ContDiff ℝ 1 (fun z : Cn n => A z (Pi.single i 1) j) := by
    intro i j
    have h1 : ContDiff ℝ 1 (fun z : Cn n => A z (Pi.single i 1)) :=
      (hA 1).clm_apply contDiff_const
    exact ((ContinuousLinearMap.proj j : Cn n →L[ℝ] ℂ).contDiff (n := 1)).comp h1
  -- (3) the `C^{0,α}` bound for the cut-offed entries
  have hG : ∀ i j : Fin n,
      (∀ z, ‖χ z * (A z (Pi.single i 1) j)‖ ≤ ε) ∧
      (∀ x y, ‖χ x * (A x (Pi.single i 1) j) - χ y * (A y (Pi.single i 1) j)‖
        ≤ 3 * ε * (1 + M) * ‖x - y‖ ^ α) := fun i j =>
    chiMulEntry_zero hα0 hα1 hρ hM hχsmooth hχ01 hχgrad hχsupp
      (hsmooth i j) hε (hεH i j)
  -- (4) `|χ z| ≤ 1`
  have hchiabs : ∀ z, |χ z| ≤ 1 := by
    intro z
    rw [abs_of_nonneg (hχ01 z).1]
    exact (hχ01 z).2
  -- (5) bounds on the Beltrami coefficients of `D`
  have hbetasup : ∀ (k' j' : Fin n) (z : Cn n), ‖betaCoef D k' j' z‖ ≤ ε / 2 := by
    intro k' j' z
    rw [betaCoef_smul]
    have h : |χ z| * ‖A z (Pi.single k' 1) j'‖ ≤ ε := by
      by_cases hz : χ z = 0
      · simp only [hz, abs_zero, zero_mul]
        exact hε
      · calc |χ z| * ‖A z (Pi.single k' 1) j'‖ ≤ 1 * ε :=
            mul_le_mul (hchiabs z) (hentry k' j' z (hχsupp z hz)) (norm_nonneg _) zero_le_one
          _ = ε := one_mul ε
    calc ‖-(Complex.I / 2) * (χ z * A z (Pi.single k' 1) j')‖
        = ‖(Complex.I / 2 : ℂ)‖ * ‖χ z * A z (Pi.single k' 1) j'‖ := by
          rw [norm_mul, norm_neg]
      _ = (1 / 2) * (|χ z| * ‖A z (Pi.single k' 1) j'‖) := by
          rw [norm_div, Complex.norm_I, norm_mul, Complex.norm_real, Real.norm_eq_abs]
          norm_num
      _ ≤ (1 / 2) * ε := by linarith
      _ = ε / 2 := by ring
  have hbetaquarter : ∀ (k' j' : Fin n) (z : Cn n),
      ‖betaCoef D k' j' z‖ ≤ 1 / (4 * (n : ℝ)) := by
    intro k' j' z
    refine le_trans (hbetasup k' j' z) ?_
    have heq : (1 / (2 * (n : ℝ))) / 2 = 1 / (4 * (n : ℝ)) := by
      rw [div_div]
      congr 1
      ring
    linarith [hεsmall, heq]
  -- (6) norm bounds for `Bop D z`
  have hBopsup : ∀ z, ‖Bop D z‖ ≤ (n : ℝ) * (ε / 2) := by
    intro z
    rw [Bop_eq_BopCoef]
    exact norm_BopCoef_le _ (by positivity) fun k' j' => hbetasup k' j' z
  have hnne : (n : ℝ) ≠ 0 := by
    simp only [Nat.cast_ne_zero]
    exact ne_of_gt hn
  have hnquarter : (n : ℝ) * (1 / (4 * (n : ℝ))) = 1 / 4 := by
    rw [mul_one_div]; field_simp
  have hquarter : ∀ z, ‖BopBar D z‖ ≤ 1 / 4 := by
    intro z
    rw [BopBar_eq_BopBarCoef]
    refine le_trans (norm_BopBarCoef_le _ (by positivity) fun k' j' => hbetaquarter k' j' z) ?_
    rw [hnquarter]
  have hBopquarter : ∀ z, ‖Bop D z‖ ≤ 1 / 4 := by
    intro z
    rw [Bop_eq_BopCoef]
    refine le_trans (norm_BopCoef_le _ (by positivity) fun k' j' => hbetaquarter k' j' z) ?_
    rw [hnquarter]
  have hBopej : ∀ z, ‖Bop D z (Pi.single j 1)‖ ≤ 1 / 4 := by
    intro z
    have h := ContinuousLinearMap.le_opNorm (Bop D z) (Pi.single j 1)
    rw [Pi.norm_single, norm_one, mul_one] at h
    exact le_trans h (hBopquarter z)
  -- (7) the sup bound for the coefficient
  have hsup : ∀ z, ‖beltramiCoef D k j z‖ ≤ (n : ℝ) * ε := by
    intro z
    by_cases hz : χ z = 0
    · have hz0 : beltramiCoeff D z = 0 := by
        refine beltramiCoeff_eq_zero_of_betaCoef_eq_zero D z fun k' j' => ?_
        rw [betaCoef_smul]
        simp [hz]
      rw [beltramiCoef, hz0]
      simp only [ContinuousLinearMap.zero_apply, Pi.zero_apply, norm_zero]
      positivity
    · calc ‖beltramiCoef D k j z‖ = ‖(beltramiCoeff D z (Pi.single j 1)) k‖ := rfl
        _ ≤ ‖beltramiCoeff D z (Pi.single j 1)‖ := norm_le_pi_norm _ k
        _ ≤ ‖beltramiCoeff D z‖ := by
            have h := ContinuousLinearMap.le_opNorm (beltramiCoeff D z) (Pi.single j 1)
            rwa [Pi.norm_single, norm_one, mul_one] at h
        _ ≤ 2 * ‖Bop D z‖ := by
            have hinv : ‖ContinuousLinearMap.inverse (1 + BopBar D z)‖ ≤ 2 :=
              (isInvertible_one_add_and_inverse_norm_le (hquarter z)).2
            rw [beltramiCoeff]
            exact le_trans (norm_mul_le _ _) (mul_le_mul_of_nonneg_right hinv (norm_nonneg _))
        _ ≤ 2 * ((n : ℝ) * (ε / 2)) := mul_le_mul_of_nonneg_left (hBopsup z) (by norm_num)
        _ = (n : ℝ) * ε := by ring
  -- (8) the difference bounds for `Bop`, `BopBar`
  have hBopDiff : ∀ x y, ‖Bop D x - Bop D y‖ ≤ (n : ℝ) * (2 * (ε * (1 + M) * ‖x - y‖ ^ α)) := by
    intro x y
    rw [Bop_eq_BopCoef, Bop_eq_BopCoef, BopCoef_sub]
    refine norm_BopCoef_le _ (by positivity) fun k' i' => ?_
    rw [betaCoef_smul, betaCoef_smul]
    have h := (hG k' i').2 x y
    have hr : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
    have hc : 0 ≤ 3 * ε * (1 + M) * ‖x - y‖ ^ α :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hε) (by linarith)) hr
    calc ‖-(Complex.I / 2) * (χ x * A x (Pi.single k' 1) i')
          - -(Complex.I / 2) * (χ y * A y (Pi.single k' 1) i')‖
        = ‖(-(Complex.I / 2) : ℂ)‖
            * ‖χ x * A x (Pi.single k' 1) i' - χ y * A y (Pi.single k' 1) i'‖ := by
          rw [← mul_sub, norm_mul]
      _ = (1 / 2) * ‖χ x * A x (Pi.single k' 1) i' - χ y * A y (Pi.single k' 1) i'‖ := by
          rw [norm_neg_I_half_nn]
      _ ≤ (1 / 2) * (3 * ε * (1 + M) * ‖x - y‖ ^ α) := by linarith
      _ ≤ 2 * (ε * (1 + M) * ‖x - y‖ ^ α) := by linarith
  have hBopBarDiff : ∀ x y,
      ‖BopBar D x - BopBar D y‖ ≤ (n : ℝ) * (2 * (ε * (1 + M) * ‖x - y‖ ^ α)) := by
    intro x y
    rw [BopBar_eq_BopBarCoef, BopBar_eq_BopBarCoef, BopBarCoef_sub]
    refine norm_BopBarCoef_le _ (by positivity) fun k' i' => ?_
    rw [betaCoef_smul, betaCoef_smul]
    have h := (hG k' i').2 x y
    have hr : 0 ≤ ‖x - y‖ ^ α := Real.rpow_nonneg (norm_nonneg _) α
    have hc : 0 ≤ 3 * ε * (1 + M) * ‖x - y‖ ^ α :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hε) (by linarith)) hr
    calc ‖-(Complex.I / 2) * (χ x * A x (Pi.single k' 1) i')
          - -(Complex.I / 2) * (χ y * A y (Pi.single k' 1) i')‖
        = ‖(-(Complex.I / 2) : ℂ)‖
            * ‖χ x * A x (Pi.single k' 1) i' - χ y * A y (Pi.single k' 1) i'‖ := by
          rw [← mul_sub, norm_mul]
      _ = (1 / 2) * ‖χ x * A x (Pi.single k' 1) i' - χ y * A y (Pi.single k' 1) i'‖ := by
          rw [norm_neg_I_half_nn]
      _ ≤ (1 / 2) * (3 * ε * (1 + M) * ‖x - y‖ ^ α) := by linarith
      _ ≤ 2 * (ε * (1 + M) * ‖x - y‖ ^ α) := by linarith
  -- (9) the difference bound for the coefficient
  have hdiff : ∀ x y, ‖beltramiCoef D k j x - beltramiCoef D k j y‖
      ≤ 6 * (n : ℝ) * ε * (1 + M) * ‖x - y‖ ^ α := by
    intro x y
    set ux : Cn n := Bop D x (Pi.single j 1) with huxdef
    set uy : Cn n := Bop D y (Pi.single j 1) with huydef
    set invX : Cn n →L[ℝ] Cn n := ContinuousLinearMap.inverse (1 + BopBar D x) with hinvXdef
    set invY : Cn n →L[ℝ] Cn n := ContinuousLinearMap.inverse (1 + BopBar D y) with hinvYdef
    have hkey : beltramiCoeff D x (Pi.single j 1) - beltramiCoeff D y (Pi.single j 1)
        = invX (ux - uy) + (invX - invY) uy := by
      rw [beltramiCoeff, beltramiCoeff, mul_apply_eq_comp, mul_apply_eq_comp,
        ← huxdef, ← huydef, ← hinvXdef, ← hinvYdef, map_sub, sub_apply]
      abel
    have hres : ‖invX - invY‖ ≤ 4 * ‖BopBar D x - BopBar D y‖ := by
      rw [hinvXdef, hinvYdef]
      exact norm_inverse_one_add_sub_le (hquarter x) (hquarter y)
    have hinvXn : ‖invX‖ ≤ 2 := by
      rw [hinvXdef]
      exact (isInvertible_one_add_and_inverse_norm_le (hquarter x)).2
    have huxy : ‖ux - uy‖ ≤ ‖Bop D x - Bop D y‖ := by
      have h := ContinuousLinearMap.le_opNorm (Bop D x - Bop D y) (Pi.single j 1)
      rw [Pi.norm_single, norm_one, mul_one] at h
      rwa [sub_apply, ← huxdef, ← huydef] at h
    have huyq : ‖uy‖ ≤ 1 / 4 := by
      rw [huydef]
      exact hBopej y
    calc ‖beltramiCoef D k j x - beltramiCoef D k j y‖
        = ‖(beltramiCoeff D x (Pi.single j 1) - beltramiCoeff D y (Pi.single j 1)) k‖ := by
          simp only [beltramiCoef, Pi.sub_apply]
      _ ≤ ‖beltramiCoeff D x (Pi.single j 1) - beltramiCoeff D y (Pi.single j 1)‖ :=
          norm_le_pi_norm _ k
      _ = ‖invX (ux - uy) + (invX - invY) uy‖ := by rw [hkey]
      _ ≤ ‖invX (ux - uy)‖ + ‖(invX - invY) uy‖ := norm_add_le _ _
      _ ≤ 2 * ‖Bop D x - Bop D y‖ + (4 * ‖BopBar D x - BopBar D y‖) * (1 / 4) := by
          refine add_le_add ?_ ?_
          · calc ‖invX (ux - uy)‖ ≤ ‖invX‖ * ‖ux - uy‖ := ContinuousLinearMap.le_opNorm _ _
              _ ≤ 2 * ‖Bop D x - Bop D y‖ :=
                  mul_le_mul hinvXn huxy (norm_nonneg _) (by norm_num)
          · calc ‖(invX - invY) uy‖ ≤ ‖invX - invY‖ * ‖uy‖ := ContinuousLinearMap.le_opNorm _ _
              _ ≤ (4 * ‖BopBar D x - BopBar D y‖) * (1 / 4) :=
                  mul_le_mul hres huyq (norm_nonneg _) (by positivity)
      _ ≤ 6 * (n : ℝ) * ε * (1 + M) * ‖x - y‖ ^ α := by
          have hA' := mul_le_mul_of_nonneg_left (hBopDiff x y) (by norm_num : (0:ℝ) ≤ 2)
          have hB := mul_le_mul_of_nonneg_left (hBopBarDiff x y) (by norm_num : (0:ℝ) ≤ 4)
          have hB' := mul_le_mul_of_nonneg_right hB (by norm_num : (0:ℝ) ≤ 1 / 4)
          have hsum := add_le_add hA' hB'
          calc 2 * ‖Bop D x - Bop D y‖ + (4 * ‖BopBar D x - BopBar D y‖) * (1 / 4)
              ≤ 2 * ((n : ℝ) * (2 * (ε * (1 + M) * ‖x - y‖ ^ α)))
                + (4 * ((n : ℝ) * (2 * (ε * (1 + M) * ‖x - y‖ ^ α)))) * (1 / 4) := hsum
            _ = 6 * (n : ℝ) * ε * (1 + M) * ‖x - y‖ ^ α := by ring
  -- (10) assembly
  have hmain := holderNorm_zero_le_ofReal (f := fun z => beltramiCoef D k j z)
    (B1 := (n : ℝ) * ε) (B2 := 6 * (n : ℝ) * ε * (1 + M))
    (mul_nonneg (Nat.cast_nonneg n) hε)
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) hε) (by linarith))
    hsup hdiff
  have hfin : (n : ℝ) * ε + 6 * (n : ℝ) * ε * (1 + M) ≤ (7 * (n : ℝ) + 1) * ε * (1 + M) := by
    have hprod : 0 ≤ ε * (1 + M) := mul_nonneg hε (by linarith)
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h1 : 0 ≤ (n : ℝ) * ε * M := mul_nonneg (mul_nonneg hn0 hε) hM
    nlinarith [h1, hprod]
  have hgoal : (fun z => beltramiCoef (fun z => χ z • A z) k j z)
      = fun z => beltramiCoef D k j z := by
    rw [hDdef]
  rw [hgoal]
  calc Work.CR.Flat.holderNorm 0 α (fun z => beltramiCoef D k j z) Set.univ
      ≤ ENNReal.ofReal ((n : ℝ) * ε + 6 * (n : ℝ) * ε * (1 + M)) := hmain
    _ ≤ ENNReal.ofReal ((7 * (n : ℝ) + 1) * ε * (1 + M)) := ENNReal.ofReal_le_ofReal hfin

/-- A `C^∞` (finite-order) compactly supported real function has a bounded Fréchet derivative. -/
private lemma nn_fderiv_bound_of_contDiff_hasCompactSupport {n : ℕ} {φ : Cn n → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hc : HasCompactSupport φ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z, ‖fderiv ℝ φ z‖ ≤ M := by
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by simp)
  have hcont : Continuous (fderiv ℝ φ) := hφ1.continuous_fderiv (by norm_num)
  obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support (hc.fderiv ℝ)
  exact ⟨max C 0, le_max_right _ _, fun z => le_trans (hC z) (le_max_left _ _)⟩

/-- **The Beltrami form of the perturbed `∂̄`-equation, with `C^{0,α}`-small compactly supported
coefficient — finite-smoothness form.**

Same as `Work.NN.Core.exists_beltramiCoef_small` but with the coefficient required only to be
`C^∞` in the *finite-order* sense `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)` (written `∞` in the
`ContDiff` scope), not analytic (`ContDiff ℝ ⊤`, i.e. `ω`).  This matters: a compactly supported
`ω`-function is zero, so the analytic form of the statement forces `c ≡ 0` and is false, whereas
the coefficient built from a cutoff `φ • A` is smooth but not analytic. -/
theorem exists_beltramiCoef_small_smooth {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) {ρ ρ₁ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hρ₁ : ∀ j, 0 < ρ₁ j)
    (hρ₁ρ : ∀ j, ρ₁ j < ρ j) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n) (ε : ℝ),
        0 ≤ ε → ε ≤ ε₀ →
        (∀ m : ℕ, ContDiff ℝ m A) →
        (∀ i j : Fin n, Work.CR.Flat.holderNorm 0 α (fun z => A z (Pi.single i 1) j)
          (Work.CR.Flat.polydisc 0 ρ) ≤ ENNReal.ofReal ε) →
        ∃ c : Fin n → Fin n → Work.NN.Core.Cn n → ℂ,
          (∀ k j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (c k j)) ∧
          (∀ k j, HasCompactSupport (c k j)) ∧
          (∀ k j z, c k j z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ) ∧
          (∀ k j, Work.CR.Flat.holderNorm 0 α (c k j) Set.univ ≤ ENNReal.ofReal (C * ε)) ∧
          ∀ (u : Work.NN.Core.Cn n → ℂ) (z : Work.NN.Core.Cn n),
            z ∈ Work.CR.Flat.polydisc 0 ρ₁ →
            (∀ k : Fin n, Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z
              (Pi.single k 1) = 0) →
            ∀ k, Work.CR.Flat.dbarCoord k u z
              = ∑ j, c k j z * Work.CR.Flat.dCoord j u z := by
  classical
  -- ## A smooth cut-off of the perturbation
  obtain ⟨χ, V, hχsm, hχcs, hχtsupp, hVopen, hKV, hχone, hχ01⟩ :=
    JFPre.jf_exists_cutoff_polydisc (n := n) (σ := ρ₁) (ρ := ρ) hρ₁ρ
  obtain ⟨M, hM0, hMbd⟩ := nn_fderiv_bound_of_contDiff_hasCompactSupport hχsm hχcs
  -- ## The Hölder constant for the cut-off coefficient
  obtain ⟨C₀, hC₀pos, hC₀⟩ := beltramiCoefSmallZero_c1 (n := n) hn hα0 hα1 hρ M hM0
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  refine ⟨1 / (2 * (n : ℝ)), ?_, C₀ * (1 + M), ?_, ?_⟩
  · positivity
  · have h1 : (0 : ℝ) < 1 + M := by linarith
    exact mul_pos hC₀pos h1
  intro A ε hε0 hεε₀ hA hsmall
  -- ## The cut-off function is supported in the polydisc
  have hχsupp : ∀ z, χ z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ :=
    fun z hz => hχtsupp (subset_closure (by simpa [Function.mem_support] using hz))
  -- ## Pointwise bounds on the entries of `A` on the polydisc
  have hentry : ∀ (i j : Fin n) (z : Cn n), z ∈ Work.CR.Flat.polydisc 0 ρ →
      ‖A z (Pi.single i 1) j‖ ≤ ε := by
    intro i j z hz
    have h1 := Work.CR.Flat.norm_apply_le_holderNorm 0 α (fun z => A z (Pi.single i 1) j)
      (Work.CR.Flat.polydisc 0 ρ) hz
    exact (ENNReal.ofReal_le_ofReal_iff hε0).mp (le_trans h1 (hsmall i j))
  -- ## The cut-off perturbation and its decoupled Beltrami coefficient
  set D : Cn n → Cn n →L[ℝ] Cn n := fun z => χ z • A z with hDdef
  have hDsm : ∀ m : ℕ, ContDiff ℝ m D := by
    intro m
    have hχm : ContDiff ℝ m χ := hχsm.of_le (by simp)
    rw [hDdef]
    exact hχm.smul (hA m)
  have hchiabs : ∀ z, |χ z| ≤ 1 := by
    intro z; rw [abs_of_nonneg (hχ01 z).1]; exact (hχ01 z).2
  have hbetaD : ∀ (k j : Fin n) (z : Cn n), ‖betaCoef D k j z‖ ≤ ε / 2 := by
    intro k j z
    rw [hDdef, betaCoef_smul]
    have h : ‖χ z * A z (Pi.single k 1) j‖ ≤ ε := by
      rw [norm_coe_mul_nn]
      by_cases hz : χ z = 0
      · rw [hz]; simp only [abs_zero, zero_mul]; exact hε0
      · calc |χ z| * ‖A z (Pi.single k 1) j‖ ≤ 1 * ε :=
            mul_le_mul (hchiabs z) (hentry k j z (hχsupp z hz)) (norm_nonneg _) (by norm_num)
          _ = ε := one_mul ε
    calc ‖-(Complex.I / 2) * (χ z * A z (Pi.single k 1) j)‖
        = ‖(-(Complex.I / 2) : ℂ)‖ * ‖χ z * A z (Pi.single k 1) j‖ := by rw [norm_mul]
      _ = (1 / 2) * ‖χ z * A z (Pi.single k 1) j‖ := by rw [norm_neg_I_half_nn]
      _ ≤ (1 / 2) * ε := by linarith
      _ = ε / 2 := by ring
  have hnε : (n : ℝ) * (ε / 2) ≤ 1 / 4 := by
    have h2 : (n : ℝ) * (1 / (2 * (n : ℝ))) = 1 / 2 := by
      rw [mul_one_div]; field_simp
    have h3 : (n : ℝ) * ε ≤ 1 / 2 :=
      calc (n : ℝ) * ε ≤ (n : ℝ) * (1 / (2 * (n : ℝ))) :=
            mul_le_mul_of_nonneg_left hεε₀ (le_of_lt hnpos)
        _ = 1 / 2 := h2
    have h4 : (n : ℝ) * (ε / 2) = ((n : ℝ) * ε) / 2 := by ring
    rw [h4]; linarith
  have hqD : ∀ z, ‖BopBar D z‖ ≤ 1 / 4 := by
    intro z
    rw [BopBar_eq_BopBarCoef]
    exact le_trans (norm_BopBarCoef_le (fun k j => betaCoef D k j z) (by positivity)
      (fun k j => hbetaD k j z)) hnε
  have hbetasm : ∀ k j : Fin n,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => beltramiCoef D k j z) :=
    fun k j => beltramiCoef_contDiff_infty D hDsm hqD k j
  -- ## The coefficient vanishes off the topological support of the cut-off
  have hsupp_c : ∀ (k j : Fin n) (z : Cn n),
      z ∉ tsupport χ → beltramiCoef D k j z = 0 := by
    intro k j z hz
    have hχz0 : χ z = 0 := by
      by_contra hne
      exact hz (subset_closure (by simpa [Function.mem_support] using hne))
    have hDz0 : D z = 0 := by
      change χ z • A z = 0
      rw [hχz0]
      exact zero_smul ℝ (A z)
    have hbeta0 : ∀ k' j', betaCoef D k' j' z = 0 := by
      intro k' j'; rw [betaCoef, hDz0]; simp
    have hb := beltramiCoeff_eq_zero_of_betaCoef_eq_zero D z hbeta0
    rw [beltramiCoef, hb]; simp
  refine ⟨fun k j z => beltramiCoef D k j z, hbetasm, ?_, ?_, ?_, ?_⟩
  · -- compact support
    intro k j
    rw [HasCompactSupport]
    refine IsCompact.of_isClosed_subset hχcs (isClosed_tsupport _) ?_
    rw [tsupport, tsupport]
    refine closure_minimal (fun z hz => ?_) (isClosed_tsupport χ)
    simp only [Function.mem_support] at hz
    by_contra hc
    exact hz (hsupp_c k j z hc)
  · -- support inside the polydisc
    intro k j z hz
    by_contra hc
    exact hz (hsupp_c k j z (fun hmem => hc (hχtsupp hmem)))
  · -- the `C^{0,α}` bound
    intro k j
    have h := hC₀ (A := A) hA χ (hχsm.of_le (by simp)) hχcs hχsupp hχ01 hMbd hε0 hεε₀ hsmall k j
    change Work.CR.Flat.holderNorm 0 α (fun z => beltramiCoef D k j z) Set.univ
        ≤ ENNReal.ofReal (C₀ * (1 + M) * ε)
    have hgoal : (fun z => beltramiCoef D k j z)
        = (fun z => beltramiCoef (fun z => χ z • A z) k j z) := by rw [hDdef]
    rw [hgoal]
    refine h.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    ring
  · -- the pointwise Beltrami form
    intro u z hz hdbar k
    have hχz : χ z = 1 := hχone z (hKV (fun j => le_of_lt (by simpa using hz j)))
    have hmemρ : z ∈ Work.CR.Flat.polydisc 0 ρ :=
      Work.CR.Flat.polydisc_mono (fun j => le_of_lt (hρ₁ρ j)) hz
    have hentryA : ∀ k j : Fin n, ‖betaCoef A k j z‖ ≤ ε / 2 := by
      intro k j
      rw [betaCoef]
      have h1 := hentry k j z hmemρ
      calc ‖-(Complex.I / 2) * (A z (Pi.single k 1)) j‖
          = (1 / 2) * ‖(A z (Pi.single k 1)) j‖ := by rw [norm_mul, norm_neg_I_half_nn]
        _ ≤ (1 / 2) * ε := by linarith
        _ = ε / 2 := by ring
    have hqA : ‖BopBar A z‖ ≤ 1 / 4 := by
      rw [BopBar_eq_BopBarCoef]
      exact le_trans (norm_BopBarCoef_le (fun k j => betaCoef A k j z) (by positivity)
        (fun k j => hentryA k j)) hnε
    have hpt := dbarCoord_eq_beltramiCoeff_pointwise A u z hqA hdbar k
    have hcoef : ∀ k j, beltramiCoef D k j z = beltramiCoef A k j z := by
      intro k j
      have hDz : D z = A z := by rw [hDdef]; simp [hχz]
      have hbeta_eq : ∀ k' j', betaCoef D k' j' z = betaCoef A k' j' z := by
        intro k' j'; rw [betaCoef, betaCoef, hDz]
      have hfamily : (fun k' j' => betaCoef D k' j' z) = (fun k' j' => betaCoef A k' j' z) :=
        funext fun k' => funext fun j' => hbeta_eq k' j'
      have hBop : Bop D z = Bop A z := by rw [Bop_eq_BopCoef, Bop_eq_BopCoef, hfamily]
      have hBopBar : BopBar D z = BopBar A z := by
        rw [BopBar_eq_BopBarCoef, BopBar_eq_BopBarCoef, hfamily]
      have hb : beltramiCoeff D z = beltramiCoeff A z := by
        rw [beltramiCoeff, beltramiCoeff, hBop, hBopBar]
      rw [beltramiCoef, beltramiCoef, hb]
    rw [hpt]
    refine Finset.sum_congr rfl fun j _ => ?_
    change beltramiCoef A k j z * Work.CR.Flat.dCoord j u z
        = beltramiCoef D k j z * Work.CR.Flat.dCoord j u z
    rw [hcoef k j]

end
end Work.NN.Core
