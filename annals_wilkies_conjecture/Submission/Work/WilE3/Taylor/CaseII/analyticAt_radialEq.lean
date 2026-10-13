import Mathlib

namespace Work.WilE3.Taylor.CaseII

/-! # Analyticity of the radial/orthogonality defect in Case II

This file proves that the "radial equation" defect appearing in the Taylor
expansion of Case II depends analytically on the point, provided the underlying
Pfaffian function `Φ` is analytic.

The two ingredients are:

* `analyticAt_clm_apply_const` : evaluating an analytic family of continuous
  linear maps at a *fixed* vector is analytic (used for the partial derivatives
  `x ↦ fderiv ℝ Φ x (Pi.single i 1)`);
* the closure of analyticity under finite sums, products, differences and
  powers, which handles the polynomial part and the cross terms.
-/

/-- Evaluating an analytic family of continuous linear maps at a fixed vector
is analytic. -/
theorem analyticAt_clm_apply_const {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    {f : E → (F →L[𝕜] G)} {z : E} {v : F} (hf : AnalyticAt 𝕜 f z) :
    AnalyticAt 𝕜 (fun x => f x v) z := by
  have h2 := (ContinuousLinearMap.apply 𝕜 G v).analyticAt (f z)
  convert h2.comp hf using 1
  ext x
  simp [ContinuousLinearMap.apply_apply]

theorem analyticAt_radialEq {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} {y z : Fin k → ℝ} {δ : ℝ}
    (hΦ : ∀ x, AnalyticAt ℝ Φ x) :
    AnalyticAt ℝ (fun x : Fin k → ℝ =>
      (∑ i, (x i - y i) ^ 2 - δ ^ 2) ^ 2
        + ∑ p : Fin k × Fin k, (fderiv ℝ Φ x (Pi.single p.1 1) * (x p.2 - y p.2)
            - fderiv ℝ Φ x (Pi.single p.2 1) * (x p.1 - y p.1)) ^ 2) z := by
  -- coordinate projections are analytic
  have hcoord : ∀ j : Fin k, AnalyticAt ℝ (fun x : Fin k → ℝ => x j) z :=
    fun j => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) j).analyticAt z
  -- the partial derivatives `x ↦ fderiv ℝ Φ x (Pi.single i 1)` are analytic
  have hG : ∀ i : Fin k, AnalyticAt ℝ (fun x : Fin k → ℝ => fderiv ℝ Φ x (Pi.single i 1)) z :=
    fun _i => analyticAt_clm_apply_const ((hΦ z).fderiv)
  -- the polynomial (radial) part
  have hp : AnalyticAt ℝ (fun x : Fin k → ℝ => (∑ i, (x i - y i) ^ 2 - δ ^ 2) ^ 2) z := by
    have hsum : AnalyticAt ℝ (fun x : Fin k → ℝ => ∑ i, (x i - y i) ^ 2) z := by
      have h := Finset.analyticAt_sum (𝕜 := ℝ) (Finset.univ : Finset (Fin k))
        (f := fun i (x : Fin k → ℝ) => (x i - y i) ^ 2)
        (fun i _ => ((hcoord i).sub analyticAt_const).pow 2)
      convert h using 1
      ext x
      simp [Finset.sum_apply]
    exact (hsum.sub analyticAt_const).pow 2
  -- the individual cross (orthogonality) terms
  have hcross : ∀ p : Fin k × Fin k, AnalyticAt ℝ (fun x : Fin k → ℝ =>
      (fderiv ℝ Φ x (Pi.single p.1 1) * (x p.2 - y p.2)
        - fderiv ℝ Φ x (Pi.single p.2 1) * (x p.1 - y p.1)) ^ 2) z := by
    intro p
    exact (((hG p.1).mul ((hcoord p.2).sub analyticAt_const)).sub
      ((hG p.2).mul ((hcoord p.1).sub analyticAt_const))).pow 2
  -- the finite sum of the cross terms
  have hsum2 : AnalyticAt ℝ (fun x : Fin k → ℝ => ∑ p : Fin k × Fin k,
      (fderiv ℝ Φ x (Pi.single p.1 1) * (x p.2 - y p.2)
        - fderiv ℝ Φ x (Pi.single p.2 1) * (x p.1 - y p.1)) ^ 2) z := by
    have h := Finset.analyticAt_sum (𝕜 := ℝ) (Finset.univ : Finset (Fin k × Fin k))
      (f := fun p (x : Fin k → ℝ) => (fderiv ℝ Φ x (Pi.single p.1 1) * (x p.2 - y p.2)
        - fderiv ℝ Φ x (Pi.single p.2 1) * (x p.1 - y p.1)) ^ 2)
      (fun p _ => hcross p)
    convert h using 1
    ext x
    simp [Finset.sum_apply]
  exact hp.add hsum2

end Work.WilE3.Taylor.CaseII
