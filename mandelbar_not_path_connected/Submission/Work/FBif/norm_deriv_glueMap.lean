/-
Copyright: subproject `Submission/Work/FBif/` of `mandelbar_not_path_connected`.

# `Work.FBif.norm_deriv_glueMap` — norm bounds for the Wirtinger derivatives of the glued map

`glueMap c q ε χ z = T_c z + ε · χ z · q z` (see `Submission/Work/FBif/Glue.lean`), where
`T_c` is the mandelbar, `q` an antipolynomial and `χ` a real valued cut-off.  The point of this
file is the *uniform* estimate

* `‖∂(glueMap) z‖ ≤ ε · ‖q z‖ · Kχ`,
* `2‖z‖ - ε · (‖q z‖ · Kχ + Kq) ≤ ‖∂̄(glueMap) z‖`

under the hypotheses `‖∂(χ) z‖ ≤ Kχ`, `‖∂̄q z‖ ≤ Kq`, `0 ≤ χ ≤ 1`, `ε ≥ 0`.

The proof is a direct computation with the Wirtinger calculus:

* `∂T_c = 0`, `∂̄T_c = 2 z̄` (`tantibar_wirtinger`, since `T_c` is the antipolynomial `w ↦ w² + c`);
* `∂q = 0` and `q` is C¹ (`antipoly_wirtinger`);
* scalar multiplication by a complex constant commutes with `∂`/`∂̄`
  (`dz_const_mul_of_diff`, `dzbar_const_mul_of_diff`);
* the product rule (`Work.MRMT.QC.dz_mul`, `dzbar_mul`) and the sum rule
  (`Work.MRMT.QC.dz_add_of_diff`, `dzbar_add_of_diff`) give the two derivative identities
  (`glue_wirtinger`).

The second bound needs `‖∂̄(χ) z‖ = ‖∂(χ) z‖`, which holds because `χ` is real valued
(`norm_dzbar_realCoe_eq`: `∂(χ) = conj (∂̄(χ))` by `Work.MRMT.QC.dz_conj`).
-/
import Mathlib
import Submission.Work.FBif.Glue
import Submission.Work.FBif.antipoly_wirtinger

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Complex
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

noncomputable section

namespace Work.FBif

/-! ## The Wirtinger derivatives of `T_c` -/

/-- `T_c` is the antipolynomial `w ↦ w ^ 2 + c`; in particular it is C¹, antiholomorphic
(`∂T_c = 0`) and `∂̄T_c = 2 z̄`. -/
theorem tantibar_wirtinger (c : ℂ) :
    ContDiff ℝ 1 (Tantibar c) ∧ (∀ z, Work.MRMT.dz (Tantibar c) z = 0) ∧
      (∀ z, Work.MRMT.dzbar (Tantibar c) z = 2 * star z) := by
  have hP : ∀ z : ℂ, Tantibar c z = (Polynomial.X ^ 2 + Polynomial.C c).eval (star z) := by
    intro z; simp
  obtain ⟨hc, hdz, hdzbar⟩ := antipoly_wirtinger hP
  refine ⟨hc, hdz, ?_⟩
  intro z
  rw [hdzbar z, Polynomial.derivative_add, Polynomial.derivative_X_pow, Polynomial.derivative_C]
  simp

/-! ## Scalar multiplication by a complex constant -/

/-- `∂` commutes with left multiplication by a constant. -/
theorem dz_const_mul_of_diff {F : ℂ → ℂ} {c z : ℂ} (hF : DifferentiableAt ℝ F z) :
    Work.MRMT.dz (fun w => c * F w) z = c * Work.MRMT.dz F z := by
  have hconst : DifferentiableAt ℝ (Function.const ℂ c) z := differentiableAt_const c
  have hmul := fderiv_mul hconst hF
  have hfd : fderiv ℝ (fun w => c * F w) z = c • fderiv ℝ F z := by
    have heq : (fun w : ℂ => c * F w) = (Function.const ℂ c * F) := rfl
    rw [heq, hmul]; simp
  rw [Work.MRMT.dz, Work.MRMT.dz, hfd]
  simp only [smul_apply, smul_eq_mul]
  ring

/-- `∂̄` commutes with left multiplication by a constant. -/
theorem dzbar_const_mul_of_diff {F : ℂ → ℂ} {c z : ℂ} (hF : DifferentiableAt ℝ F z) :
    Work.MRMT.dzbar (fun w => c * F w) z = c * Work.MRMT.dzbar F z := by
  have hconst : DifferentiableAt ℝ (Function.const ℂ c) z := differentiableAt_const c
  have hmul := fderiv_mul hconst hF
  have hfd : fderiv ℝ (fun w => c * F w) z = c • fderiv ℝ F z := by
    have heq : (fun w : ℂ => c * F w) = (Function.const ℂ c * F) := rfl
    rw [heq, hmul]; simp
  rw [Work.MRMT.dzbar, Work.MRMT.dzbar, hfd]
  simp only [smul_apply, smul_eq_mul]
  ring

/-! ## The Wirtinger derivatives of the glued map -/

/-- The two Wirtinger derivative identities for the glued map `T_c + ε χ q`. -/
theorem glue_wirtinger (c : ℂ) {q : ℂ → ℂ} (hq : Antipoly q) (ε : ℝ) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ 1 χ) (z : ℂ) :
    Work.MRMT.dz (glueMap c q ε χ) z = (ε : ℂ) * q z * Work.MRMT.dz (realCoe χ) z ∧
      Work.MRMT.dzbar (glueMap c q ε χ) z =
        2 * star z + (ε : ℂ) * ((χ z : ℝ) : ℂ) * Work.MRMT.dzbar q z +
          (ε : ℂ) * q z * Work.MRMT.dzbar (realCoe χ) z := by
  obtain ⟨P, hP⟩ := hq
  obtain ⟨hTc, hdzT, hdzbarT⟩ := tantibar_wirtinger c
  obtain ⟨hqc, hdzq, hdzbarq⟩ := antipoly_wirtinger hP
  have hχdiff : DifferentiableAt ℝ χ z := (hχ.differentiable (by norm_num)).differentiableAt
  have hχcdiff : DifferentiableAt ℝ (realCoe χ) z := by
    have := (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).differentiableAt (x := χ z)
    exact this.comp z hχdiff
  have hTdiff : DifferentiableAt ℝ (Tantibar c) z :=
    (hTc.differentiable (by norm_num)).differentiableAt
  have hW : DifferentiableAt ℝ (fun w : ℂ => (ε : ℂ) * (realCoe χ w)) z :=
    hχcdiff.const_mul (ε : ℂ)
  have hqdiff : DifferentiableAt ℝ q z := (hqc.differentiable (by norm_num)).differentiableAt
  have hB : DifferentiableAt ℝ (fun w : ℂ => ((ε : ℂ) * (realCoe χ w)) * q w) z :=
    hW.mul hqdiff
  have hglue : glueMap c q ε χ = fun w : ℂ => Tantibar c w + ((ε : ℂ) * (realCoe χ w)) * q w :=
    rfl
  constructor
  · rw [hglue, Work.MRMT.QC.dz_add_of_diff hTdiff hB,
      hdzT z, Work.MRMT.QC.dz_mul hW hqdiff, dz_const_mul_of_diff hχcdiff, hdzq z]
    simp only [realCoe]; ring
  · rw [hglue, Work.MRMT.QC.dzbar_add_of_diff hTdiff hB,
      hdzbarT z, Work.MRMT.QC.dzbar_mul hW hqdiff, dzbar_const_mul_of_diff hχcdiff]
    simp only [realCoe]; ring

/-- For real valued `χ`, `‖∂̄(χ) z‖ = ‖∂(χ) z‖`: indeed `∂(χ) = conj (∂̄(χ))`. -/
theorem norm_dzbar_realCoe_eq {χ : ℂ → ℝ} (hχ : ContDiff ℝ 1 χ) (z : ℂ) :
    ‖Work.MRMT.dzbar (Work.FBif.realCoe χ) z‖ = ‖Work.MRMT.dz (Work.FBif.realCoe χ) z‖ := by
  have hF : DifferentiableAt ℝ (Work.FBif.realCoe χ) z := by
    have hχdiff : DifferentiableAt ℝ χ z := (hχ.differentiable (by norm_num)).differentiableAt
    have := (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).differentiableAt (x := χ z)
    exact this.comp z hχdiff
  have hconj := Work.MRMT.QC.dz_conj hF
  have hfun : (fun w : ℂ => starRingEnd ℂ (Work.FBif.realCoe χ w)) = Work.FBif.realCoe χ := by
    funext w; simp [Work.FBif.realCoe]
  rw [hfun] at hconj
  rw [hconj, Complex.norm_conj]

/-- Elementary reverse triangle inequality in the form needed for the lower bound:
`‖a‖ - ‖b‖ - ‖d‖ ≤ ‖a + b + d‖`. -/
theorem norm_three_bound (a b d : ℂ) : ‖a‖ - ‖b‖ - ‖d‖ ≤ ‖a + b + d‖ := by
  have h1 : ‖a‖ - ‖b + d‖ ≤ ‖a - (-(b + d))‖ := by
    have h := (abs_le.mp (abs_norm_sub_norm_le a (-(b + d)))).2
    rwa [norm_neg] at h
  have h2 : ‖b + d‖ ≤ ‖b‖ + ‖d‖ := norm_add_le b d
  have h3 : a - (-(b + d)) = a + b + d := by ring
  rw [h3] at h1
  linarith

/-! ## The estimate -/

theorem norm_deriv_glueMap (c : ℂ) {q : ℂ → ℂ} (hq : Work.FBif.Antipoly q) {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ 1 χ) {ε Kχ Kq : ℝ}
    (hKχ : ∀ z : ℂ, ‖Work.MRMT.dz (Work.FBif.realCoe χ) z‖ ≤ Kχ)
    (hKq : ∀ z : ℂ, ‖Work.MRMT.dzbar q z‖ ≤ Kq)
    (hχ0 : ∀ z : ℂ, 0 ≤ χ z) (hχ1 : ∀ z : ℂ, χ z ≤ 1) (hε : 0 ≤ ε) :
    (∀ z : ℂ, ‖Work.MRMT.dz (Work.FBif.glueMap c q ε χ) z‖ ≤ ε * ‖q z‖ * Kχ) ∧
      (∀ z : ℂ, 2 * ‖z‖ - ε * (‖q z‖ * Kχ + Kq) ≤
        ‖Work.MRMT.dzbar (Work.FBif.glueMap c q ε χ) z‖) := by
  have hKχ0 : 0 ≤ Kχ := le_trans (norm_nonneg _) (hKχ 0)
  have hKq0 : 0 ≤ Kq := le_trans (norm_nonneg _) (hKq 0)
  constructor
  · intro z
    rw [(glue_wirtinger c hq ε hχ z).1, norm_mul, norm_mul]
    have heps : ‖(ε : ℂ)‖ = ε := by simp [abs_of_nonneg hε]
    rw [heps]
    exact mul_le_mul_of_nonneg_left (hKχ z) (mul_nonneg hε (norm_nonneg _))
  · intro z
    rw [(glue_wirtinger c hq ε hχ z).2]
    have hA : ‖(2 : ℂ) * star z‖ = 2 * ‖z‖ := by rw [norm_mul, norm_star]; norm_num
    have hB : ‖(ε : ℂ) * ((χ z : ℝ) : ℂ) * Work.MRMT.dzbar q z‖ ≤ ε * Kq := by
      rw [norm_mul, norm_mul]
      have heps : ‖(ε : ℂ)‖ = ε := by simp [abs_of_nonneg hε]
      have hchi : ‖((χ z : ℝ) : ℂ)‖ = χ z := by simp [abs_of_nonneg (hχ0 z)]
      rw [heps, hchi]
      calc ε * χ z * ‖Work.MRMT.dzbar q z‖ = ε * (χ z * ‖Work.MRMT.dzbar q z‖) := by ring
        _ ≤ ε * (1 * Kq) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul (hχ1 z) (hKq z) (norm_nonneg _) (by norm_num)) hε
        _ = ε * Kq := by ring
    have hC : ‖(ε : ℂ) * q z * Work.MRMT.dzbar (Work.FBif.realCoe χ) z‖ ≤ ε * ‖q z‖ * Kχ := by
      rw [norm_mul, norm_mul]
      have heps : ‖(ε : ℂ)‖ = ε := by simp [abs_of_nonneg hε]
      rw [heps, norm_dzbar_realCoe_eq hχ z]
      exact mul_le_mul_of_nonneg_left (hKχ z) (mul_nonneg hε (norm_nonneg _))
    have htri : ‖(2 : ℂ) * star z‖ - ‖(ε : ℂ) * ((χ z : ℝ) : ℂ) * Work.MRMT.dzbar q z‖ -
        ‖(ε : ℂ) * q z * Work.MRMT.dzbar (Work.FBif.realCoe χ) z‖ ≤
        ‖(2 : ℂ) * star z + (ε : ℂ) * ((χ z : ℝ) : ℂ) * Work.MRMT.dzbar q z +
          (ε : ℂ) * q z * Work.MRMT.dzbar (Work.FBif.realCoe χ) z‖ :=
      norm_three_bound _ _ _
    have hdist : ε * (‖q z‖ * Kχ + Kq) = ε * ‖q z‖ * Kχ + ε * Kq := by ring
    linarith [hA, hB, hC, htri, hdist]

end Work.FBif
