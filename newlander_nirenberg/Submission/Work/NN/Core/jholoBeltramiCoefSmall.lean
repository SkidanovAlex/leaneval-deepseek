import Mathlib
import Submission.Work.NN.Core.dbarCoord_eq_beltramiCoeff
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Holder.Bilinear
import Submission.Work.NN.Core.norm_inverse_one_add_sub_le
import Submission.Work.NN.Core.chiMulEntry

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Core

variable {n : ℕ}

/-! ## The linear operator attached to a coefficient matrix

`Bop A z` and `BopBar A z` are the `ℝ`-linear operators of `ℂⁿ` whose matrices are
`(β k j z)` and `(conj (β k j z))`.  The estimates below are all obtained by writing these
operators as functions of the *coefficient family* alone, which makes the difference of two of
them a function of the differences of the coefficients. -/

/-- The `ℝ`-linear operator on `ℂⁿ` with coefficient matrix `c`: `v ↦ (k ↦ Σ_j v_j * c k j)`. -/
def BopCoef (c : Fin n → Fin n → ℂ) : Cn n →L[ℝ] Cn n :=
  ContinuousLinearMap.pi (fun k : Fin n => ∑ j : Fin n,
    ContinuousLinearMap.smulRight (ContinuousLinearMap.proj j : Cn n →L[ℝ] ℂ) (c k j))

/-- Same, with conjugated coefficients. -/
def BopBarCoef (c : Fin n → Fin n → ℂ) : Cn n →L[ℝ] Cn n :=
  ContinuousLinearMap.pi (fun k : Fin n => ∑ j : Fin n,
    ContinuousLinearMap.smulRight (ContinuousLinearMap.proj j : Cn n →L[ℝ] ℂ)
      (starRingEnd ℂ (c k j)))

lemma Bop_eq_BopCoef (A : Cn n → Cn n →L[ℝ] Cn n) (z : Cn n) :
    Bop A z = BopCoef (fun k j => betaCoef A k j z) := rfl

lemma BopBar_eq_BopBarCoef (A : Cn n → Cn n →L[ℝ] Cn n) (z : Cn n) :
    BopBar A z = BopBarCoef (fun k j => betaCoef A k j z) := rfl

lemma BopCoef_sub (c c' : Fin n → Fin n → ℂ) :
    BopCoef c - BopCoef c' = BopCoef (fun k j => c k j - c' k j) := by
  ext v k
  simp only [BopCoef, Pi.sub_apply, sub_apply, ContinuousLinearMap.pi_apply, sum_apply,
    ContinuousLinearMap.smulRight_apply, Pi.sub_apply, smul_eq_mul]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma BopBarCoef_sub (c c' : Fin n → Fin n → ℂ) :
    BopBarCoef c - BopBarCoef c' = BopBarCoef (fun k j => c k j - c' k j) := by
  ext v k
  simp only [BopBarCoef, Pi.sub_apply, sub_apply, ContinuousLinearMap.pi_apply, sum_apply,
    ContinuousLinearMap.smulRight_apply, Pi.sub_apply, smul_eq_mul, map_sub]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma norm_BopCoef_le (c : Fin n → Fin n → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ k j, ‖c k j‖ ≤ M) : ‖BopCoef c‖ ≤ (n : ℝ) * M :=
  opNorm_pi_sum_smulRight_le c hM h

lemma norm_BopBarCoef_le (c : Fin n → Fin n → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ k j, ‖c k j‖ ≤ M) : ‖BopBarCoef c‖ ≤ (n : ℝ) * M := by
  refine opNorm_pi_sum_smulRight_le (fun k j => starRingEnd ℂ (c k j)) hM (fun k j => ?_)
  rw [starRingEnd_apply, norm_star]
  exact h k j

/-! ## The coefficient of a pointwise scalar multiple -/

/-- The Beltrami coefficient of `χ • A` at `z`: `β = -(i/2) χ(z) A z e_k`. -/
lemma betaCoef_smul (A : Cn n → Cn n →L[ℝ] Cn n) (χ : Cn n → ℝ) (k j : Fin n) (z : Cn n) :
    betaCoef (fun w => χ w • A w) k j z = -(Complex.I / 2) * (χ z * A z (Pi.single k 1) j) := by
  simp only [betaCoef, smul_apply, Pi.smul_apply, Complex.real_smul]

/-- If all the Beltrami coefficients of `D` at `z` vanish then so does the decoupled coefficient
`(1 + BopBar D z)⁻¹ Bop D z`. -/
lemma beltramiCoeff_eq_zero_of_betaCoef_eq_zero (D : Cn n → Cn n →L[ℝ] Cn n) (z : Cn n)
    (h : ∀ k j, betaCoef D k j z = 0) : beltramiCoeff D z = 0 := by
  have hc : (fun k j => betaCoef D k j z) = (0 : Fin n → Fin n → ℂ) :=
    funext fun k => funext fun j => h k j
  have hB : Bop D z = 0 := by rw [Bop_eq_BopCoef, hc]; simp [BopCoef, ContinuousLinearMap.pi_zero]
  have hBb : BopBar D z = 0 := by
    rw [BopBar_eq_BopBarCoef, hc]; simp [BopBarCoef, ContinuousLinearMap.pi_zero]
  rw [beltramiCoeff, hB, hBb]
  simp

/-! ## The `C^{0,α}` norm from a sup bound and an `α`-Hölder bound -/

lemma holderNorm_zero_le_ofReal {α : ℝ} {f : Cn n → ℂ} {B1 B2 : ℝ} (hB1 : 0 ≤ B1)
    (hB2 : 0 ≤ B2) (h1 : ∀ z, ‖f z‖ ≤ B1)
    (h2 : ∀ x y, ‖f x - f y‖ ≤ B2 * ‖x - y‖ ^ α) :
    Work.CR.Flat.holderNorm 0 α f Set.univ ≤ ENNReal.ofReal (B1 + B2) := by
  have h1' : Work.CR.Flat.iterDerivNorm 0 f Set.univ ≤ ENNReal.ofReal B1 := by
    rw [Work.CR.Flat.iterDerivNorm_zero]
    exact iSup₂_le fun z _ => ENNReal.ofReal_le_ofReal (h1 z)
  have h2' : Work.CR.Flat.holderSeminorm 0 α f Set.univ ≤ ENNReal.ofReal B2 := by
    refine iSup₂_le fun x _ => iSup₂_le fun y _ => iSup_le fun hxy => ?_
    rw [Work.CR.Flat.Holder.norm_iteratedFDerivWithin_zero_sub,
      ENNReal.ofReal_le_ofReal_iff hB2,
      div_le_iff₀ (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α)]
    exact h2 x y
  rw [Work.CR.Flat.holderNorm, Finset.sum_range_one]
  exact le_trans (add_le_add h1' h2') (le_of_eq (ENNReal.ofReal_add hB1 hB2).symm)

/-! ## The main estimate -/

/-- Norm bound on `-(i/2)`. -/
private lemma norm_neg_I_half : ‖(-(Complex.I / 2) : ℂ)‖ = 1 / 2 := by
  rw [norm_neg, norm_div, Complex.norm_I]
  norm_num


theorem jholoBeltramiCoefSmall {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
        (hA : ∀ m : ℕ, ContDiff ℝ m A) (χ : Work.NN.Core.Cn n → ℝ),
        ContDiff ℝ ⊤ χ → HasCompactSupport χ →
        (∀ z, χ z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ) →
        (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) →
        (∀ z, ‖fderiv ℝ χ z‖ ≤ M) →
        (∀ z, ‖A z‖ ≤ 1 / (2 * (n : ℝ))) →
        ∀ {ε : ℝ}, 0 ≤ ε →
        (∀ i j : Fin n, Work.CR.Flat.holderNorm 1 α (fun z => A z (Pi.single i 1) j)
          (Work.CR.Flat.polydisc 0 ρ) ≤ ENNReal.ofReal ε) →
        ∀ k j : Fin n,
          Work.CR.Flat.holderNorm 0 α
            (fun z => Work.NN.Core.beltramiCoef (fun z => χ z • A z) k j z) Set.univ
            ≤ ENNReal.ofReal (C * ε * (1 + M)) := by
  refine ⟨7 * (n : ℝ) + 1, by positivity, ?_⟩
  intro A hA χ hχsmooth hχcpt hχsupp hχ01 hχgrad hAsmall ε hε hεH k j
  set D : Cn n → Cn n →L[ℝ] Cn n := fun w => χ w • A w with hDdef
  -- (1) pointwise bounds on the entries of `A` on the polydisc
  have hentry : ∀ (i j : Fin n) (z : Cn n), z ∈ Work.CR.Flat.polydisc 0 ρ →
      ‖A z (Pi.single i 1) j‖ ≤ ε := by
    intro i j z hz
    have h1 := Work.CR.Flat.le_iterDerivNorm 0 (fun z => A z (Pi.single i 1) j)
      (Work.CR.Flat.polydisc 0 ρ) hz
    rw [norm_iteratedFDerivWithin_zero] at h1
    refine (ENNReal.ofReal_le_ofReal_iff hε).mp (le_trans h1 ?_)
    exact le_trans (Work.CR.Flat.iterDerivNorm_le_holderNorm 1 α _ _ (Nat.zero_le 1)) (hεH i j)
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
    chiMulEntry hα0 hα1 hρ hM (hχsmooth.of_le le_top) hχ01 hχgrad hχsupp
      (hsmooth i j) hε (hεH i j)
  -- (4) `|χ z| ≤ 1`
  have hchiabs : ∀ z, |χ z| ≤ 1 := by
    intro z
    rw [abs_of_nonneg (hχ01 z).1]
    exact (hχ01 z).2
  have hnne : (n : ℝ) ≠ 0 := by
    simp only [Nat.cast_ne_zero]
    exact ne_of_gt hn
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
  have hbetaquarter : ∀ (k' j' : Fin n) (z : Cn n), ‖betaCoef D k' j' z‖ ≤ 1 / (4 * (n : ℝ)) := by
    intro k' j' z
    have hDsmall : ‖D z‖ ≤ 1 / (2 * (n : ℝ)) := by
      have h : ‖χ z • A z‖ = |χ z| * ‖A z‖ := by rw [norm_smul, Real.norm_eq_abs]
      rw [hDdef, h]
      calc |χ z| * ‖A z‖ ≤ 1 * (1 / (2 * (n : ℝ))) :=
            mul_le_mul (hchiabs z) (hAsmall z) (norm_nonneg _) zero_le_one
        _ = 1 / (2 * (n : ℝ)) := one_mul _
    refine le_trans (norm_betaCoef_le (ε := 1 / (2 * (n : ℝ))) hDsmall k' j') ?_
    have heq : (1 / (2 * (n : ℝ))) / 2 = 1 / (4 * (n : ℝ)) := by ring_nf
    rw [heq]
  -- (6) norm bounds for `Bop D z` and `BopBar D z`
  have hBopsup : ∀ z, ‖Bop D z‖ ≤ (n : ℝ) * (ε / 2) := by
    intro z
    rw [Bop_eq_BopCoef]
    exact norm_BopCoef_le _ (by positivity) fun k' j' => hbetasup k' j' z
  have hBopBarsup : ∀ z, ‖BopBar D z‖ ≤ (n : ℝ) * (ε / 2) := by
    intro z
    rw [BopBar_eq_BopBarCoef]
    exact norm_BopBarCoef_le _ (by positivity) fun k' j' => hbetasup k' j' z
  have hnquarter : (n : ℝ) * (1 / (4 * (n : ℝ))) = 1 / 4 := by
    rw [mul_one_div]; field_simp
  have hnhalf : (n : ℝ) * (1 / (2 * (n : ℝ))) = 1 / 2 := by
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
          rw [norm_neg_I_half]
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
          rw [norm_neg_I_half]
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
          have hA := mul_le_mul_of_nonneg_left (hBopDiff x y) (by norm_num : (0:ℝ) ≤ 2)
          have hB := mul_le_mul_of_nonneg_left (hBopBarDiff x y) (by norm_num : (0:ℝ) ≤ 4)
          have hB' := mul_le_mul_of_nonneg_right hB (by norm_num : (0:ℝ) ≤ 1 / 4)
          have hsum := add_le_add hA hB'
          calc 2 * ‖Bop D x - Bop D y‖ + (4 * ‖BopBar D x - BopBar D y‖) * (1 / 4)
              ≤ 2 * ((n : ℝ) * (2 * (ε * (1 + M) * ‖x - y‖ ^ α)))
                + (4 * ((n : ℝ) * (2 * (ε * (1 + M) * ‖x - y‖ ^ α)))) * (1 / 4) := hsum
            _ = 6 * (n : ℝ) * ε * (1 + M) * ‖x - y‖ ^ α := by ring
  -- (10) assembly
  have hmain := holderNorm_zero_le_ofReal (f := fun z => beltramiCoef D k j z)
    (B1 := (n : ℝ) * ε) (B2 := 6 * (n : ℝ) * ε * (1 + M))
    (by positivity) (by positivity) hsup hdiff
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

end Work.NN.Core
