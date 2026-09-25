import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.DbarCnPertAux
import Submission.Work.NN.Core.jholoBeltramiCoefSmall
import Submission.Work.NN.Core.chiMulEntry

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Core

/-!
# The Beltrami coefficient of a cut-off times a `C^{0,α}`-small perturbation

This file proves `Work.NN.Core.beltramiCoefSmallZero`: the decoupled Beltrami coefficient
`beltramiCoef (χ • A)` of a compactly supported cut-off of a perturbation `A` whose entries are
`C^{0,α}`-small (rather than `C^{1,α}`-small, as in `jholoBeltramiCoefSmall`) is again `C^{0,α}`
with a bound proportional to `ε * (1 + M)`.

The only ingredient that differs from `jholoBeltramiCoefSmall` is the product estimate
`chiMulEntry_zero`: a cut-off of Lipschitz constant `M` times a function that is merely
`C^{0,α}`-bounded is `C^{0,α}` with constant `3 ε (1 + M)` (instead of the `C^{1,α}` hypothesis
used in `chiMulEntry`).
-/

/-! ## The `C^{0,α}` product estimate for a cut-off times a `C^{0,α}` function -/

private lemma min_one_mul_le_rpow_z {M d α : ℝ} (hM : 0 ≤ M) (hd : 0 < d) (hα0 : 0 < α)
    (hα1 : α < 1) :
    min 1 (M * d) ≤ (1 + M) * d ^ α := by
  have hdα : 0 < d ^ α := Real.rpow_pos_of_pos hd α
  rcases le_or_gt d 1 with h1 | h1
  · have hle : d ≤ d ^ α := by
      have h := Real.rpow_le_rpow_of_exponent_ge hd h1 hα1.le
      rwa [Real.rpow_one] at h
    calc min 1 (M * d) ≤ M * d := min_le_right _ _
      _ ≤ M * d ^ α := mul_le_mul_of_nonneg_left hle hM
      _ ≤ (1 + M) * d ^ α := by nlinarith [hdα]
  · have h2 : 1 ≤ d ^ α := Real.one_le_rpow h1.le hα0.le
    calc min 1 (M * d) ≤ 1 := min_le_left _ _
      _ ≤ d ^ α := h2
      _ ≤ (1 + M) * d ^ α := by nlinarith [hdα, hM]

private lemma three_mul_nonneg_z {M ε D : ℝ} (hε : 0 ≤ ε) (hM : 0 ≤ M) (hD : 0 ≤ D) :
    0 ≤ 3 * ε * (1 + M) * D :=
  mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hε) (by linarith)) hD

private lemma norm_mul_reals_z {n : ℕ} (χ : Cn n → ℝ) (g : Cn n → ℂ) (z : Cn n) :
    ‖χ z * g z‖ = |χ z| * ‖g z‖ := by
  rw [show χ z * g z = (χ z : ℂ) * g z from rfl, norm_mul]
  congr 1
  simp only [Complex.norm_real, Real.norm_eq_abs]

private lemma norm_mul_reals_left_z {n : ℕ} (χ : Cn n → ℝ) (g : Cn n → ℂ) (x y : Cn n) :
    ‖(χ x : ℂ) * (g x - g y)‖ = |χ x| * ‖g x - g y‖ := by
  rw [norm_mul]
  congr 1
  simp only [Complex.norm_real, Real.norm_eq_abs]

private lemma norm_sub_reals_z {n : ℕ} (χ : Cn n → ℝ) (g : Cn n → ℂ) (x y : Cn n) :
    ‖((χ x : ℂ) - (χ y : ℂ)) * g y‖ = |χ x - χ y| * ‖g y‖ := by
  rw [norm_mul]
  congr 1
  rw [← Complex.ofReal_sub]
  simp only [Complex.norm_real, Real.norm_eq_abs]

/-- **`C^{0,α}` product estimate.**  If `χ` is a `[0,1]`-valued cut-off with Lipschitz constant
`M` supported in the polydisc `polydisc 0 ρ`, and `g` satisfies `holderNorm 0 α g (polydisc 0 ρ)
≤ ε`, then `χ • g` is bounded by `ε` and is `α`-Hölder with constant `3 ε (1 + M)` on all of
`ℂⁿ`.  This is the level-`0` analogue of `chiMulEntry`. -/
theorem chiMulEntry_zero {n : ℕ} {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {ρ : Fin n → ℝ}
    (hρ : ∀ j, 0 < ρ j) {M : ℝ} (hM : 0 ≤ M) {χ : Cn n → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hχ01 : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1) (hχgrad : ∀ z, ‖fderiv ℝ χ z‖ ≤ M)
    (hχsupp : ∀ z, χ z ≠ 0 → z ∈ Work.CR.Flat.polydisc 0 ρ)
    {g : Cn n → ℂ} (hg : ContDiff ℝ 1 g) {ε : ℝ} (hε : 0 ≤ ε)
    (hgε : Work.CR.Flat.holderNorm 0 α g (Work.CR.Flat.polydisc 0 ρ) ≤ ENNReal.ofReal ε) :
    (∀ z, ‖χ z * g z‖ ≤ ε) ∧
      (∀ x y, ‖χ x * g x - χ y * g y‖ ≤ 3 * ε * (1 + M) * ‖x - y‖ ^ α) := by
  have _ := hρ
  have _ := hg
  have hdiff : ∀ z : Cn n, DifferentiableAt ℝ χ z :=
    fun z => (hχ.differentiable (by norm_num)).differentiableAt
  have hlip : ∀ x y : Cn n, |χ x - χ y| ≤ M * ‖x - y‖ := fun x y => by
    have h := convex_univ.norm_image_sub_le_of_norm_fderiv_le (f := χ) (C := M) (s := Set.univ)
      (fun z _ => hdiff z) (fun z _ => hχgrad z) (Set.mem_univ x) (Set.mem_univ y)
    rw [Real.norm_eq_abs, abs_sub_comm, norm_sub_rev] at h
    exact h
  have hgΩ : ∀ z, z ∈ Work.CR.Flat.polydisc 0 ρ → ‖g z‖ ≤ ε := fun z hz =>
    (ENNReal.ofReal_le_ofReal_iff hε).mp
      (le_trans (Work.CR.Flat.norm_apply_le_holderNorm 0 α g _ hz) hgε)
  have hghold : ∀ x, x ∈ Work.CR.Flat.polydisc 0 ρ → ∀ y, y ∈ Work.CR.Flat.polydisc 0 ρ →
      x ≠ y → ‖g x - g y‖ ≤ ε * ‖x - y‖ ^ α := by
    intro x hx y hy hxy
    have hη : ‖iteratedFDerivWithin ℝ 0 g (Work.CR.Flat.polydisc 0 ρ) x
        - iteratedFDerivWithin ℝ 0 g (Work.CR.Flat.polydisc 0 ρ) y‖ = ‖g x - g y‖ := by
      rw [← dist_eq_norm, dist_iteratedFDerivWithin_zero, dist_eq_norm]
    have hmain : ENNReal.ofReal (‖g x - g y‖ / ‖x - y‖ ^ α) ≤ ENNReal.ofReal ε := by
      refine le_trans ?_ hgε
      have h := Work.CR.Flat.le_holderSeminorm 0 α g (Work.CR.Flat.polydisc 0 ρ) hx hy hxy
      rw [hη] at h
      exact le_trans h (Work.CR.Flat.holderSeminorm_le_holderNorm 0 α g
        (Work.CR.Flat.polydisc 0 ρ) le_rfl)
    have hle := (ENNReal.ofReal_le_ofReal_iff hε).mp hmain
    have hp : (0 : ℝ) < ‖x - y‖ ^ α :=
      Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
    rwa [div_le_iff₀ hp] at hle
  refine ⟨?_, ?_⟩
  · intro z
    rcases eq_or_ne (χ z) 0 with hz0 | hz0
    · rw [hz0]
      simp only [Complex.ofReal_zero, zero_mul, norm_zero]
      exact hε
    · have hgz : ‖g z‖ ≤ ε := hgΩ z (hχsupp z hz0)
      have habs : |χ z| ≤ 1 := abs_le.mpr ⟨by linarith [(hχ01 z).1], (hχ01 z).2⟩
      rw [norm_mul_reals_z χ g z]
      calc |χ z| * ‖g z‖ ≤ 1 * ε := mul_le_mul habs hgz (norm_nonneg _) (by norm_num)
        _ = ε := one_mul ε
  · intro x y
    by_cases hxy : x = y
    · rw [hxy]
      simp [sub_self, Real.zero_rpow (ne_of_gt hα0)]
    · have hd : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
      have hdα : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos hd α
      have hmin0 : (0 : ℝ) ≤ min 1 (M * ‖x - y‖) :=
        le_min (by norm_num) (mul_nonneg hM (norm_nonneg _))
      have hmin_le : min 1 (M * ‖x - y‖) ≤ (1 + M) * ‖x - y‖ ^ α :=
        min_one_mul_le_rpow_z hM hd hα0 hα1
      have hfin : min 1 (M * ‖x - y‖) * ε ≤ 3 * ε * (1 + M) * ‖x - y‖ ^ α := by
        calc min 1 (M * ‖x - y‖) * ε ≤ ((1 + M) * ‖x - y‖ ^ α) * ε :=
              mul_le_mul_of_nonneg_right hmin_le hε
          _ ≤ 3 * (((1 + M) * ‖x - y‖ ^ α) * ε) := by
              have hx0 : (0 : ℝ) ≤ ((1 + M) * ‖x - y‖ ^ α) * ε :=
                mul_nonneg (mul_nonneg (by linarith) hdα.le) hε
              linarith
          _ = 3 * ε * (1 + M) * ‖x - y‖ ^ α := by ring
      by_cases hx0 : χ x = 0
      · have hL : ‖χ x * g x - χ y * g y‖ = ‖χ y * g y‖ := by rw [hx0]; simp
        rw [hL]
        by_cases hy0 : χ y = 0
        · rw [hy0]
          simp only [Complex.ofReal_zero, zero_mul, norm_zero]
          exact three_mul_nonneg_z hε hM hdα.le
        · have hyΩ : y ∈ Work.CR.Flat.polydisc 0 ρ := hχsupp y hy0
          have hgy : ‖g y‖ ≤ ε := hgΩ y hyΩ
          have habs1 : |χ y| ≤ 1 := abs_le.mpr ⟨by linarith [(hχ01 y).1], (hχ01 y).2⟩
          have habs2 : |χ y| ≤ M * ‖x - y‖ := by
            have h := hlip y x
            have hx' : χ y - χ x = χ y := by rw [hx0, sub_zero]
            rw [hx', norm_sub_rev] at h
            exact h
          rw [norm_mul_reals_z χ g y]
          calc |χ y| * ‖g y‖ ≤ (min 1 (M * ‖x - y‖)) * ε :=
                mul_le_mul (le_min habs1 habs2) hgy (norm_nonneg _) hmin0
            _ ≤ 3 * ε * (1 + M) * ‖x - y‖ ^ α := hfin
      · by_cases hy0 : χ y = 0
        · have hL : ‖χ x * g x - χ y * g y‖ = ‖χ x * g x‖ := by rw [hy0]; simp
          rw [hL]
          have hxΩ : x ∈ Work.CR.Flat.polydisc 0 ρ := hχsupp x hx0
          have hgx : ‖g x‖ ≤ ε := hgΩ x hxΩ
          have habs1 : |χ x| ≤ 1 := abs_le.mpr ⟨by linarith [(hχ01 x).1], (hχ01 x).2⟩
          have habs2 : |χ x| ≤ M * ‖x - y‖ := by
            have h := hlip x y
            have hy' : χ x - χ y = χ x := by rw [hy0, sub_zero]
            rwa [hy'] at h
          rw [norm_mul_reals_z χ g x]
          calc |χ x| * ‖g x‖ ≤ (min 1 (M * ‖x - y‖)) * ε :=
                mul_le_mul (le_min habs1 habs2) hgx (norm_nonneg _) hmin0
            _ ≤ 3 * ε * (1 + M) * ‖x - y‖ ^ α := hfin
        · have hxΩ : x ∈ Work.CR.Flat.polydisc 0 ρ := hχsupp x hx0
          have hyΩ : y ∈ Work.CR.Flat.polydisc 0 ρ := hχsupp y hy0
          have hgy : ‖g y‖ ≤ ε := hgΩ y hyΩ
          have hgh : ‖g x - g y‖ ≤ ε * ‖x - y‖ ^ α := hghold x hxΩ y hyΩ hxy
          have habsx : |χ x| ≤ 1 := abs_le.mpr ⟨by linarith [(hχ01 x).1], (hχ01 x).2⟩
          have habs1 : |χ x - χ y| ≤ 1 :=
            abs_le.mpr ⟨by linarith [(hχ01 x).1, (hχ01 y).2],
              by linarith [(hχ01 x).2, (hχ01 y).1]⟩
          have hmin : |χ x - χ y| ≤ min 1 (M * ‖x - y‖) := le_min habs1 (hlip x y)
          have hdecomp : χ x * g x - χ y * g y
              = (χ x : ℂ) * (g x - g y) + ((χ x : ℂ) - (χ y : ℂ)) * g y := by ring
          rw [hdecomp]
          refine le_trans (norm_add_le _ _) ?_
          rw [norm_mul_reals_left_z χ g x y, norm_sub_reals_z χ g x y]
          have hfin'' : min 1 (M * ‖x - y‖) * ε ≤ ((1 + M) * ‖x - y‖ ^ α) * ε :=
            mul_le_mul_of_nonneg_right hmin_le hε
          calc |χ x| * ‖g x - g y‖ + |χ x - χ y| * ‖g y‖
              ≤ 1 * (ε * ‖x - y‖ ^ α) + (min 1 (M * ‖x - y‖)) * ε :=
                add_le_add (mul_le_mul habsx hgh (norm_nonneg _) (by norm_num))
                  (mul_le_mul hmin hgy (norm_nonneg _) hmin0)
            _ ≤ 3 * ε * (1 + M) * ‖x - y‖ ^ α := by
                rw [one_mul]
                calc ε * ‖x - y‖ ^ α + (min 1 (M * ‖x - y‖)) * ε
                    ≤ ε * ‖x - y‖ ^ α + ((1 + M) * ‖x - y‖ ^ α) * ε :=
                      add_le_add le_rfl hfin''
                  _ = ε * ‖x - y‖ ^ α * (2 + M) := by ring
                  _ ≤ ε * ‖x - y‖ ^ α * (3 * (1 + M)) :=
                      mul_le_mul_of_nonneg_left (by linarith [hM]) (mul_nonneg hε hdα.le)
                  _ = 3 * ε * (1 + M) * ‖x - y‖ ^ α := by ring

/-! ## The main estimate -/

/-- Norm bound on `-(i/2)`. -/
private lemma norm_neg_I_half_z : ‖(-(Complex.I / 2) : ℂ)‖ = 1 / 2 := by
  rw [norm_neg, norm_div, Complex.norm_I]
  norm_num

theorem beltramiCoefSmallZero {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (M : ℝ) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n}
        (hA : ∀ m : ℕ, ContDiff ℝ m A) (χ : Work.NN.Core.Cn n → ℝ),
        ContDiff ℝ ⊤ χ → HasCompactSupport χ →
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
    chiMulEntry_zero hα0 hα1 hρ hM (hχsmooth.of_le le_top) hχ01 hχgrad hχsupp
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
          rw [norm_neg_I_half_z]
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
          rw [norm_neg_I_half_z]
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

end Work.NN.Core
