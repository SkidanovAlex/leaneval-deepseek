/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The level-`0` estimate for the perturbation coefficients `L_A w`

`Work.NN.Core.Lcoef A w j z = (i/2) · (dw_z (A z e_j))` is the difference between the `j`-th
coefficient of `∂̄_{Jstd+A} w` and the flat `∂̄_j w`.  In the Newlander--Nirenberg fixed-point
argument the perturbation is small in the sense that the columns `z ↦ A z e_j` of `A` are
`C^{0,α}`-small, with a constant `ε`, on the polydisc `pd n ρ 4` (the predicate `VecHolder`).

This file records the resulting `C^{0,α}` estimate for `L_A w` against the `C^{1,α}`-norm of `w`:

`‖L_A w‖_{C^{0,α}(pd n ρ 4)} ≤ C ε ‖w‖_{C^{1,α}(pd n ρ 4)}`

for `0 < α < 1` and a constant `C > 0` depending only on `n` and `α`.  The proof is the product
rule for the first order operator `L_A`: the derivative `dw` is controlled by `‖w‖_{C^{1,α}}` and
the vector field `A` by `ε`.
-/
import Mathlib
import Submission.Work.NN.Final.Defs
import Submission.Work.CR.Flat.Holder.Bilinear
import Submission.Work.CR.Flat.Holder.holderNorm_smul
import Submission.Work.NN.Core.holderNorm_fderiv_apply_le

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Final

/-! ## Auxiliary lemmas about the Hölder norm and the `VecHolder` predicate -/

/-- The `C^{k,α}`-norm only depends on the values of the function on `Ω`. -/
private lemma holderNorm_congrOn {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {k : ℕ} {α : ℝ} {Ω : Set X} {f g : X → ℂ} (h : ∀ x ∈ Ω, f x = g x) :
    Work.CR.Flat.holderNorm k α f Ω = Work.CR.Flat.holderNorm k α g Ω := by
  unfold Work.CR.Flat.holderNorm
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [← Work.CR.Flat.Holder.iDN_complex_eq, ← Work.CR.Flat.Holder.hSN_complex_eq,
    Work.CR.Flat.Holder.iDN_congr h, Work.CR.Flat.Holder.hSN_congr h]

/-- A field which is bounded by `ε` and `α`-Hölder with constant `ε` on `Ω` is continuous on
`Ω` (for `0 < α` and `0 ≤ ε`). -/
private lemma VecHolder.continuousOn {n : ℕ} {φ : (Fin n → ℂ) → (Fin n → ℂ)} {α ε : ℝ}
    {Ω : Set (Fin n → ℂ)} (h : VecHolder φ α ε Ω) (hα : 0 < α) (hε : 0 ≤ ε) :
    ContinuousOn φ Ω := by
  have hhd : ∀ z ∈ Ω, ∀ z' ∈ Ω, ‖φ z - φ z'‖ ≤ ε * ‖z - z'‖ ^ α := h.2
  intro x hx
  rw [Metric.continuousWithinAt_iff]
  intro e he
  rcases eq_or_lt_of_le hε with hε0 | hεpos
  · refine ⟨1, one_pos, fun y hy _ => ?_⟩
    have h1 : ‖φ y - φ x‖ = 0 := by
      have h2 := hhd y hy x hx
      rw [← hε0, zero_mul] at h2
      exact le_antisymm h2 (norm_nonneg _)
    rw [dist_eq_norm, h1]
    exact he
  · refine ⟨(e / ε) ^ (1 / α), Real.rpow_pos_of_pos (div_pos he hεpos) _, fun y hy hxy => ?_⟩
    rw [dist_eq_norm] at hxy ⊢
    have hpos : 0 < e / ε := div_pos he hεpos
    have h3 : ((e / ε) ^ (1 / α)) ^ α = e / ε := by
      rw [← Real.rpow_mul hpos.le, one_div_mul_cancel (ne_of_gt hα), Real.rpow_one]
    have hpow : ‖y - x‖ ^ α < e / ε := by
      have h4 := Real.rpow_lt_rpow (norm_nonneg (y - x)) hxy hα
      rwa [h3] at h4
    calc ‖φ y - φ x‖ ≤ ε * ‖y - x‖ ^ α := hhd y hy x hx
      _ < ε * (e / ε) := mul_lt_mul_of_pos_left hpow hεpos
      _ = e := by rw [mul_div_cancel₀ e (ne_of_gt hεpos)]

/-- Each coordinate of a `VecHolder` field is again `C^{0,α}`-bounded by `2 ε` (in the sense of
the Hölder norm, which is the sum of its sup-norm and its Hölder part). -/
private lemma VecHolder.component_holderNorm_le {n : ℕ} {φ : (Fin n → ℂ) → (Fin n → ℂ)}
    {α ε : ℝ} {Ω : Set (Fin n → ℂ)} (h : VecHolder φ α ε Ω) (hα : 0 < α) (hε : 0 ≤ ε)
    (j : Fin n) :
    Work.CR.Flat.holderNorm 0 α (fun z => φ z j) Ω ≤ ENNReal.ofReal (2 * ε) := by
  have h1 : Work.CR.Flat.Holder.iDN 0 (fun z => φ z j) Ω ≤ ENNReal.ofReal ε := by
    rw [Work.CR.Flat.Holder.iDN_zero_deriv]
    exact iSup₂_le fun z hz =>
      ENNReal.ofReal_le_ofReal (le_trans (norm_le_pi_norm (φ z) j) (h.1 z hz))
  have h2 : Work.CR.Flat.Holder.hSN 0 α (fun z => φ z j) Ω ≤ ENNReal.ofReal ε := by
    rw [Work.CR.Flat.Holder.hSN_zero_deriv]
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy =>
      ENNReal.ofReal_le_ofReal ?_
    have hd : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have hdα : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos hd α
    rw [div_le_iff₀ hdα]
    calc ‖φ x j - φ y j‖ = ‖(φ x - φ y) j‖ := by rw [Pi.sub_apply]
      _ ≤ ‖φ x - φ y‖ := norm_le_pi_norm (φ x - φ y) j
      _ ≤ ε * ‖x - y‖ ^ α := h.2 x hx y hy
  rw [Work.CR.Flat.holderNorm, Finset.sum_range_one]
  calc Work.CR.Flat.Holder.iDN 0 (fun z => φ z j) Ω
        + Work.CR.Flat.Holder.hSN 0 α (fun z => φ z j) Ω
      ≤ ENNReal.ofReal ε + ENNReal.ofReal ε := add_le_add h1 h2
    _ = ENNReal.ofReal (2 * ε) := by
        rw [← ENNReal.ofReal_add hε hε]
        congr 1
        ring

/-! ## The `ℝ≥0∞` bookkeeping -/

/-- The arithmetic behind the estimate: pulling the two constants out of the product
`(1/2) · C · (2ε) · A = (C ε) · A`. -/
private lemma ofReal_half_mul (C ε : ℝ) (hC : 0 ≤ C) (A : ℝ≥0∞) :
    ENNReal.ofReal (1 / 2) * (ENNReal.ofReal C * (ENNReal.ofReal (2 * ε) * A))
      = ENNReal.ofReal (C * ε) * A := by
  calc ENNReal.ofReal (1 / 2) * (ENNReal.ofReal C * (ENNReal.ofReal (2 * ε) * A))
      = (ENNReal.ofReal (1 / 2) * ENNReal.ofReal C) * (ENNReal.ofReal (2 * ε) * A) := by
        rw [← mul_assoc (ENNReal.ofReal (1 / 2)) (ENNReal.ofReal C)
          (ENNReal.ofReal (2 * ε) * A)]
    _ = ENNReal.ofReal (1 / 2 * C) * (ENNReal.ofReal (2 * ε) * A) := by
        rw [show ENNReal.ofReal (1 / 2) * ENNReal.ofReal C = ENNReal.ofReal (1 / 2 * C) from
          (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)).symm]
    _ = (ENNReal.ofReal (1 / 2 * C) * ENNReal.ofReal (2 * ε)) * A := by
        rw [← mul_assoc]
    _ = ENNReal.ofReal (1 / 2 * C * (2 * ε)) * A := by
        rw [show ENNReal.ofReal (1 / 2 * C) * ENNReal.ofReal (2 * ε)
              = ENNReal.ofReal (1 / 2 * C * (2 * ε)) from
          (ENNReal.ofReal_mul (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hC)).symm]
    _ = ENNReal.ofReal (C * ε) * A := by
        rw [show (1 / 2 : ℝ) * C * (2 * ε) = C * ε from by ring]

/-! ## The estimate -/

/-- **The level-`0` a priori estimate for the perturbation coefficients `L_A w`**: for
`0 < α < 1` there is a constant `C > 0` such that whenever the columns `z ↦ A z e_j` of `A` are
`C^{0,α}`-bounded and `α`-Hölder with constant `ε` on the polydisc `pd n ρ 4`, the coefficients
`z ↦ L_A w j z` obey
`‖L_A w j‖_{C^{0,α}(pd n ρ 4)} ≤ C ε ‖w‖_{C^{1,α}(pd n ρ 4)}`
for every `w` of class `C¹` on `pd n ρ 4`. -/
theorem Lcoef_holderNorm_zero {n : ℕ} {α : ℝ} {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) (hα0 : 0 < α) (hα1 : α < 1) : ∃ C : ℝ, 0 < C ∧ ∀ (A : (Fin n → ℂ) → (Fin n → ℂ) →L[ℝ] (Fin n → ℂ)) (ε : ℝ), 0 ≤ ε → (∀ j : Fin n, Work.NN.Final.VecHolder (fun z => A z (Pi.single j 1)) α ε (Work.NN.Final.pd n ρ 4)) → ∀ (w : (Fin n → ℂ) → ℂ), ContDiffOn ℝ 1 w (Work.NN.Final.pd n ρ 4) → ∀ j : Fin n, Work.CR.Flat.holderNorm 0 α (fun z => Work.NN.Core.Lcoef A w j z) (Work.NN.Final.pd n ρ 4) ≤ ENNReal.ofReal (C * ε) * Work.CR.Flat.holderNorm 1 α w (Work.NN.Final.pd n ρ 4) := by
  obtain ⟨C, hCpos, hC⟩ := Work.NN.Core.holderNorm_fderiv_apply_le (n := n) (α := α) hα0
    (Ω := pd n ρ 4) (isOpen_pd ρ 4) (k := 1) le_rfl
  refine ⟨C, hCpos, ?_⟩
  intro A ε hε hVec w hw j
  have hΩopen : IsOpen (pd n ρ 4) := isOpen_pd ρ 4
  have hΩ : UniqueDiffOn ℝ (pd n ρ 4) := hΩopen.uniqueDiffOn
  -- the smallness of the vector field `z ↦ A z e_j`, coordinate by coordinate
  have hWcont : ContinuousOn (fun z => A z (Pi.single j 1)) (pd n ρ 4) :=
    (hVec j).continuousOn hα0 hε
  have hWcd : ContDiffOn ℝ ((0 : ℕ) : WithTop ℕ∞)
      (fun z => A z (Pi.single j 1)) (pd n ρ 4) :=
    contDiffOn_zero.mpr hWcont
  have hcomp : ∀ j' : Fin n, ContDiffOn ℝ (((1 - 1 : ℕ)) : WithTop ℕ∞)
      (fun z => (A z (Pi.single j 1)) j') (pd n ρ 4) := by
    intro j'
    exact contDiffOn_zero.mpr ((continuous_apply j').comp_continuousOn' hWcont)
  have hb : ∀ j' : Fin n, Work.CR.Flat.holderNorm 0 α
      (fun z => (A z (Pi.single j 1)) j') (pd n ρ 4) ≤ ENNReal.ofReal (2 * ε) :=
    fun j' => (hVec j).component_holderNorm_le hα0 hε j'
  -- the product-rule estimate for the pairing `z ↦ dw_z (A z e_j)`
  have hpair := hC (hu := hw) (W := fun z => A z (Pi.single j 1)) (hW := hcomp)
    (hε := by linarith) (hb := hb)
  -- the factor `i/2`
  have hG : ContDiffOn ℝ ((0 : ℕ) : ℕ∞)
      (fun z => fderiv ℝ w z (A z (Pi.single j 1))) (pd n ρ 4) :=
    (hw.fderiv_of_isOpen hΩopen (m := 0) (by simp)).clm_apply hWcd
  have hsmul := Work.CR.Flat.Holder.holderNorm_smul (k := 0) (α := α) (Complex.I / 2) hG hΩ
  have hcongr : Work.CR.Flat.holderNorm 0 α (fun z => Work.NN.Core.Lcoef A w j z)
        (pd n ρ 4)
      = Work.CR.Flat.holderNorm 0 α ((Complex.I / 2) •
          (fun z => fderiv ℝ w z (A z (Pi.single j 1)))) (pd n ρ 4) :=
    holderNorm_congrOn fun z _ => by
      rw [Work.NN.Core.Lcoef, Pi.smul_apply, smul_eq_mul]
  have hc : ‖(Complex.I / 2 : ℂ)‖ = 1 / 2 := by
    rw [Complex.norm_div, Complex.norm_I, Complex.norm_ofNat]
  calc Work.CR.Flat.holderNorm 0 α (fun z => Work.NN.Core.Lcoef A w j z) (pd n ρ 4)
      = ENNReal.ofReal ‖(Complex.I / 2 : ℂ)‖ * Work.CR.Flat.holderNorm 0 α
          (fun z => fderiv ℝ w z (A z (Pi.single j 1))) (pd n ρ 4) := by
        rw [hcongr, hsmul]
    _ = ENNReal.ofReal (1 / 2) * Work.CR.Flat.holderNorm 0 α
          (fun z => fderiv ℝ w z (A z (Pi.single j 1))) (pd n ρ 4) := by
        rw [hc]
    _ ≤ ENNReal.ofReal (1 / 2) * (ENNReal.ofReal C * (ENNReal.ofReal (2 * ε) *
          Work.CR.Flat.holderNorm 1 α w (pd n ρ 4))) := mul_le_mul' le_rfl hpair
    _ = ENNReal.ofReal (C * ε) * Work.CR.Flat.holderNorm 1 α w (pd n ρ 4) :=
        ofReal_half_mul C ε hCpos.le _

end Work.NN.Final
