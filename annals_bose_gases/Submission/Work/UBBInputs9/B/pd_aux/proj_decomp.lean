import Mathlib.Tactic.Have
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Submission.Work.SmallBoxA0.kwPhi_props
import Submission.Work.UBBInputs9.B.integrable_fderiv_chiBPhi_sq
import Submission.Work.UBBInputs9.B.pd_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs9.B.pd_aux.proj_decomp` — the pointwise decomposition of the projection defect

The whole content of `proj_prod_lower` is the completion of squares
`χ_B Φ = χ_B Q_B Φ + c_u χ_B` (`c_u = boxMean ℓ d u Φ`), i.e. the pointwise inequality

    `(1-δ)·Σ_k(∂_k(χ_BΦ))² - ((1-δ)/δ)·c_u²·Σ_k(∂_kχ_B)² ≤ Σ_k(∂_k(χ_B(Φ-c_u)))²`

whose difference is `δ·Σ_k(∂_k(χ_BΦ) - ((1-δ)/δ)c_u ∂_kχ_B)² ≥ 0`.

This module provides the pointwise layer (no measure theory): the derivative decomposition,
the explicit Leibniz forms of the three integrands `kinInt = Σ(∂_k(χ_BΦ))²`,
`kinIntD = Σ(∂_kχ_B)²`, `kinIntPrj = Σ(∂_k(χ_B(Φ-c_u)))²`, and the pointwise inequality
together with the crude bound `kinIntPrj ≤ 2·kinInt + 2M²·kinIntD`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.UBBInputs9.B.pd_aux

open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "X1" => Submission.BoseGases.X 1

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The derivative decomposition `∂(χ_B Φ) = ∂(χ_B(Φ-m)) + m·∂χ_B` -/

/-- Splitting off the box mean: for a smooth state `Φ` the directional derivative of
`χ_{B(u)}·Φ` is the derivative of `χ_{B(u)}·(Φ - m)` plus `m` times the derivative of
`χ_{B(u)}`, with `m = boxMean ℓ d u Φ`. -/
lemma fderiv_chiB_mul_sub {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : ℝ³)
    {Φ : X1 → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (x : X1) (k : Fin 3) :
    fderiv ℝ (fun y : X1 => chiB ℓ d u (y 0) * Φ y) x (kcDir 1 0 k)
      = fderiv ℝ (fun y : X1 => chiB ℓ d u (y 0) * (Φ y - boxMean ℓ d u Φ)) x
          (kcDir 1 0 k)
        + boxMean ℓ d u Φ
            * fderiv ℝ (fun y : X1 => chiB ℓ d u (y 0)) x (kcDir 1 0 k) := by
  set m : ℝ := boxMean ℓ d u Φ with hm
  have hχ : ContDiff ℝ (⊤ : ENat) (fun y : X1 => chiB ℓ d u (y 0)) :=
    (Work.SmallBoxTBWord.contDiff_chiB hℓ hd u).comp
      (ContinuousLinearMap.contDiff Work.UBBInputs9.B.projX1)
  have hχd : DifferentiableAt ℝ (fun y : X1 => chiB ℓ d u (y 0)) x :=
    hχ.differentiable (by simp) x
  have hQ : DifferentiableAt ℝ
      (fun y : X1 => chiB ℓ d u (y 0) * (Φ y - m)) x :=
    hχd.mul ((hΦ.differentiable (by simp) x).sub (differentiableAt_const m))
  have hM : DifferentiableAt ℝ (fun y : X1 => m * chiB ℓ d u (y 0)) x :=
    (differentiableAt_const m).mul hχd
  have hfun : (fun y : X1 => chiB ℓ d u (y 0) * Φ y)
      = (fun y : X1 => chiB ℓ d u (y 0) * (Φ y - m))
        + (fun y : X1 => m * chiB ℓ d u (y 0)) := by
    funext y; simp only [Pi.add_apply]; ring
  rw [hfun, fderiv_add hQ hM, add_apply, fderiv_const_mul hχd m, smul_apply, smul_eq_mul]

/-! ## 2. The Leibniz forms of the three integrands -/

/-- Leibniz form of `∂_k χ_{B(u)}` at `z` (the product `χ(z/ℓ)·χ(z/(ℓd) − u)` split). -/
lemma fderiv_chiB_apply {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u z : ℝ³) (k : Fin 3) :
    fderiv ℝ (chiB ℓ d u) z (kcStdBasis k)
      = fderiv ℝ (chiScale ℓ) z (kcStdBasis k)
          * chiScale (ℓ * d) (z - (ℓ * d) • u)
        + chiScale ℓ z
          * fderiv ℝ (chiScale (ℓ * d)) (z - (ℓ * d) • u) (kcStdBasis k) := by
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  have h := Work.UBBInputs9.B.fderiv_chiBPhi_eq ℓ d
    (Φ := fun _ : X1 => (1 : ℝ)) contDiff_const u (fun _ : Fin 1 => z) k
  simp only [mul_one] at h
  rw [Work.UBBInputs9.B.fderiv_liftX_apply (chiScale ℓ) (fun _ : Fin 1 => z)
      ((chiScale_contDiff hℓne).differentiable (by simp) z) k] at h
  rw [← Work.UBBInputs9.B.fderiv_liftX_apply (chiB ℓ d u) (fun _ : Fin 1 => z)
      ((Work.SmallBoxTBWord.contDiff_chiB hℓ hd u).differentiable (by simp) z) k]
  exact h

/-- The Leibniz expression for `∂_k χ_B`, as a function of `p = (u,x)`. -/
noncomputable def chiBLb (ℓ d : ℝ) (k : Fin 3) (p : ℝ³ × X1) : ℝ :=
  fderiv ℝ (chiScale ℓ) (p.2 0) (kcStdBasis k) * chiScale (ℓ * d) (p.2 0 - (ℓ * d) • p.1)
    + chiScale ℓ (p.2 0)
      * fderiv ℝ (chiScale (ℓ * d)) (p.2 0 - (ℓ * d) • p.1) (kcStdBasis k)

/-- The Leibniz expression for `∂_k (χ_B Φ)`, as a function of `p = (u,x)`. -/
noncomputable def chiBLc (ℓ d : ℝ) (Φ : X1 → ℝ) (k : Fin 3) (p : ℝ³ × X1) : ℝ :=
  fderiv ℝ (fun y : X1 => chiScale ℓ (y 0) * Φ y) p.2 (kcDir 1 0 k)
      * chiScale (ℓ * d) (p.2 0 - (ℓ * d) • p.1)
    + chiScale ℓ (p.2 0) * Φ p.2
      * fderiv ℝ (chiScale (ℓ * d)) (p.2 0 - (ℓ * d) • p.1) (kcStdBasis k)

lemma chiBLb_apply {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : ℝ³) (x : X1) (k : Fin 3) :
    fderiv ℝ (fun y : X1 => chiB ℓ d u (y 0)) x (kcDir 1 0 k) = chiBLb ℓ d k (u, x) := by
  rw [Work.UBBInputs9.B.fderiv_liftX_apply (chiB ℓ d u) x
      ((Work.SmallBoxTBWord.contDiff_chiB hℓ hd u).differentiable (by simp) (x 0)) k]
  exact fderiv_chiB_apply hℓ hd u (x 0) k

lemma chiBLc_apply {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : ℝ³) {Φ : X1 → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (x : X1) (k : Fin 3) :
    fderiv ℝ (fun y : X1 => chiB ℓ d u (y 0) * Φ y) x (kcDir 1 0 k) = chiBLc ℓ d Φ k (u, x) := by
  rw [Work.UBBInputs9.B.fderiv_chiBPhi_eq ℓ d hΦ u x k]
  rfl

lemma continuous_chiBLb {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (k : Fin 3) :
    Continuous (chiBLb ℓ d k) := by
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  have hld : ℓ * d ≠ 0 := mul_ne_zero hℓne (ne_of_gt hd)
  have h1 : Continuous (fun p : ℝ³ × X1 => fderiv ℝ (chiScale ℓ) (p.2 0) (kcStdBasis k)) :=
    ((chiScale_contDiff hℓne).continuous_fderiv (by simp)).clm_apply continuous_const
      |>.comp ((continuous_apply 0).comp continuous_snd)
  have h2 : Continuous (fun p : ℝ³ × X1 => chiScale (ℓ * d) (p.2 0 - (ℓ * d) • p.1)) :=
    (chiScale_contDiff hld).continuous.comp
      (((continuous_apply 0).comp continuous_snd).sub (continuous_fst.const_smul (ℓ * d)))
  have h3 : Continuous (fun p : ℝ³ × X1 => chiScale ℓ (p.2 0)) :=
    (chiScale_contDiff hℓne).continuous.comp ((continuous_apply 0).comp continuous_snd)
  have h4 : Continuous (fun p : ℝ³ × X1 =>
      fderiv ℝ (chiScale (ℓ * d)) (p.2 0 - (ℓ * d) • p.1) (kcStdBasis k)) :=
    ((chiScale_contDiff hld).continuous_fderiv (by simp)).clm_apply continuous_const
      |>.comp (((continuous_apply 0).comp continuous_snd).sub
        (continuous_fst.const_smul (ℓ * d)))
  unfold chiBLb
  exact (h1.mul h2).add (h3.mul h4)

lemma continuous_chiBLc {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (Φ : X1 → ℝ)
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (k : Fin 3) :
    Continuous (chiBLc ℓ d Φ k) := by
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  have hld : ℓ * d ≠ 0 := mul_ne_zero hℓne (ne_of_gt hd)
  have hcd : ContDiff ℝ (⊤ : ENat) (fun y : X1 => chiScale ℓ (y 0) * Φ y) :=
    ((chiScale_contDiff hℓne).comp (ContinuousLinearMap.contDiff Work.UBBInputs9.B.projX1)).mul hΦ
  have h1 : Continuous (fun p : ℝ³ × X1 =>
      fderiv ℝ (fun y : X1 => chiScale ℓ (y 0) * Φ y) p.2 (kcDir 1 0 k)) :=
    (hcd.continuous_fderiv (by simp)).clm_apply continuous_const |>.comp continuous_snd
  have h2 : Continuous (fun p : ℝ³ × X1 => chiScale (ℓ * d) (p.2 0 - (ℓ * d) • p.1)) :=
    (chiScale_contDiff hld).continuous.comp
      (((continuous_apply 0).comp continuous_snd).sub (continuous_fst.const_smul (ℓ * d)))
  have h3 : Continuous (fun p : ℝ³ × X1 => chiScale ℓ (p.2 0)) :=
    (chiScale_contDiff hℓne).continuous.comp ((continuous_apply 0).comp continuous_snd)
  have h4 : Continuous (fun p : ℝ³ × X1 => Φ p.2) := hΦ.continuous.comp continuous_snd
  have h5 : Continuous (fun p : ℝ³ × X1 =>
      fderiv ℝ (chiScale (ℓ * d)) (p.2 0 - (ℓ * d) • p.1) (kcStdBasis k)) :=
    ((chiScale_contDiff hld).continuous_fderiv (by simp)).clm_apply continuous_const
      |>.comp (((continuous_apply 0).comp continuous_snd).sub
        (continuous_fst.const_smul (ℓ * d)))
  unfold chiBLc
  exact (h1.mul h2).add ((h3.mul h4).mul h5)

/-! ## 3. The three integrands in Leibniz form -/

lemma kinInt_eq {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : ℝ³) {Φ : X1 → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (x : X1) :
    kinInt ℓ d Φ u x = ∑ k : Fin 3, (chiBLc ℓ d Φ k (u, x)) ^ 2 := by
  unfold kinInt
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [chiBLc_apply hℓ hd u hΦ x k]

lemma kinIntD_eq {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : ℝ³) (x : X1) :
    kinIntD ℓ d u x = ∑ k : Fin 3, (chiBLb ℓ d k (u, x)) ^ 2 := by
  unfold kinIntD
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [chiBLb_apply hℓ hd u x k]

lemma kinIntPrj_eq {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : ℝ³) {Φ : X1 → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (x : X1) :
    kinIntPrj ℓ d Φ u x
      = ∑ k : Fin 3,
          (chiBLc ℓ d Φ k (u, x) - boxMean ℓ d u Φ * chiBLb ℓ d k (u, x)) ^ 2 := by
  have hfun : (fun y : X1 => chiB ℓ d u (y 0)
        * Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass ℓ d u)
            (dlBox ℓ d u) 0 Φ y)
      = fun y : X1 => chiB ℓ d u (y 0) * (Φ y - boxMean ℓ d u Φ) := by
    funext y
    rw [Work.UBBInputs9.B.boxQ_eq_boxMean]
  unfold kinIntPrj
  rw [hfun]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hsplit := fderiv_chiB_mul_sub hℓ hd u hΦ x k
  rw [chiBLc_apply hℓ hd u hΦ x k, chiBLb_apply hℓ hd u x k] at hsplit
  have hkey : fderiv ℝ (fun y : X1 => chiB ℓ d u (y 0) * (Φ y - boxMean ℓ d u Φ)) x
        (kcDir 1 0 k)
      = chiBLc ℓ d Φ k (u, x) - boxMean ℓ d u Φ * chiBLb ℓ d k (u, x) := by
    linarith
  rw [hkey]

/-! ## 4. The pointwise projection inequality -/

theorem proj_le_pointwise {ℓ d δ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hδ : 0 < δ)
    (hδ1 : δ < 1) {Φ : X1 → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (u : ℝ³) (x : X1) :
    (1 - δ) * kinInt ℓ d Φ u x
      - ((1 - δ) / δ) * ((boxMean ℓ d u Φ) ^ 2 * kinIntD ℓ d u x)
      ≤ kinIntPrj ℓ d Φ u x := by
  set m : ℝ := boxMean ℓ d u Φ with hm
  set a : Fin 3 → ℝ := fun k => fderiv ℝ (fun y : X1 => chiB ℓ d u (y 0)
        * (Φ y - m)) x (kcDir 1 0 k) with ha
  set b : Fin 3 → ℝ := fun k => fderiv ℝ (fun y : X1 =>
        chiB ℓ d u (y 0)) x (kcDir 1 0 k) with hb
  set c : Fin 3 → ℝ := fun k => fderiv ℝ (fun y : X1 =>
        chiB ℓ d u (y 0) * Φ y) x (kcDir 1 0 k) with hc
  have hfun : (fun y : X1 => chiB ℓ d u (y 0)
        * Work.SmallBoxTBWord.boxQ (Work.SmallBoxSliding.boxMass ℓ d u)
            (dlBox ℓ d u) 0 Φ y)
      = fun y : X1 => chiB ℓ d u (y 0) * (Φ y - m) := by
    funext y
    rw [Work.UBBInputs9.B.boxQ_eq_boxMean, ← hm]
  have hprj : kinIntPrj ℓ d Φ u x = ∑ k : Fin 3, (a k) ^ 2 := by
    unfold kinIntPrj
    rw [hfun]
  have hkin : kinInt ℓ d Φ u x = ∑ k : Fin 3, (a k + m * b k) ^ 2 := by
    unfold kinInt
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hder : c k = a k + m * b k := by
      rw [hc, ha, hb]
      exact fderiv_chiB_mul_sub hℓ hd u hΦ x k
    rw [← hder]
  have hkinD : kinIntD ℓ d u x = ∑ k : Fin 3, (b k) ^ 2 := by
    unfold kinIntD
    rfl
  rw [hprj, hkin, hkinD]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum (fun k _ => ?_)
  have h0 : 0 ≤ δ * (a k - ((1 - δ) / δ) * m * b k) ^ 2 :=
    mul_nonneg hδ.le (sq_nonneg _)
  have hid : (1 - δ) * (a k + m * b k) ^ 2 - ((1 - δ) / δ) * (m ^ 2 * (b k) ^ 2)
      = (a k) ^ 2 - δ * (a k - ((1 - δ) / δ) * m * b k) ^ 2 := by
    field_simp
    ring
  rw [hid]
  linarith

/-- Crude bound: `kinIntPrj ≤ 2 kinInt + 2M² kinIntD` whenever `|boxMean| ≤ M`. -/
theorem kinIntPrj_le_bound {ℓ d M : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {Φ : X1 → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (hM : ∀ u : ℝ³, |boxMean ℓ d u Φ| ≤ M) (u : ℝ³)
    (x : X1) :
    kinIntPrj ℓ d Φ u x ≤ 2 * kinInt ℓ d Φ u x + 2 * M ^ 2 * kinIntD ℓ d u x := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (boxMean ℓ d u Φ)) (hM u)
  have hmle : (boxMean ℓ d u Φ) ^ 2 ≤ M ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg hM0]
    exact hM u
  have h1 := kinIntPrj_eq hℓ hd u hΦ x
  have h2 := kinInt_eq hℓ hd u hΦ x
  have h3 := kinIntD_eq hℓ hd u x
  have hterm : ∀ k : Fin 3,
      (chiBLc ℓ d Φ k (u, x) - boxMean ℓ d u Φ * chiBLb ℓ d k (u, x)) ^ 2
        ≤ 2 * (chiBLc ℓ d Φ k (u, x)) ^ 2
          + 2 * (boxMean ℓ d u Φ) ^ 2 * (chiBLb ℓ d k (u, x)) ^ 2 := by
    intro k
    nlinarith [sq_nonneg (chiBLc ℓ d Φ k (u, x)
      + boxMean ℓ d u Φ * chiBLb ℓ d k (u, x))]
  rw [h1, h2, h3]
  calc ∑ k : Fin 3, (chiBLc ℓ d Φ k (u, x) - boxMean ℓ d u Φ * chiBLb ℓ d k (u, x)) ^ 2
      ≤ ∑ k : Fin 3, (2 * (chiBLc ℓ d Φ k (u, x)) ^ 2
          + 2 * (boxMean ℓ d u Φ) ^ 2 * (chiBLb ℓ d k (u, x)) ^ 2) :=
        Finset.sum_le_sum (fun k _ => hterm k)
    _ = 2 * (∑ k : Fin 3, (chiBLc ℓ d Φ k (u, x)) ^ 2)
          + 2 * (boxMean ℓ d u Φ) ^ 2 * (∑ k : Fin 3, (chiBLb ℓ d k (u, x)) ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * (∑ k : Fin 3, (chiBLc ℓ d Φ k (u, x)) ^ 2)
          + 2 * M ^ 2 * (∑ k : Fin 3, (chiBLb ℓ d k (u, x)) ^ 2) := by
        have hnn : 0 ≤ ∑ k : Fin 3, (chiBLb ℓ d k (u, x)) ^ 2 :=
          Finset.sum_nonneg (fun k _ => sq_nonneg _)
        have hstep : (boxMean ℓ d u Φ) ^ 2 * (∑ k : Fin 3, (chiBLb ℓ d k (u, x)) ^ 2)
            ≤ M ^ 2 * (∑ k : Fin 3, (chiBLb ℓ d k (u, x)) ^ 2) :=
          mul_le_mul_of_nonneg_right hmle hnn
        linarith

end Work.UBBInputs9.B.pd_aux
