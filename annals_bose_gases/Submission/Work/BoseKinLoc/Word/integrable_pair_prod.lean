import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Word.integrable_pair_prod`

Integrability, on the `n`-particle configuration space `X n = (ℝ³)ⁿ`, of the
product of the one-body window squares with a single localised pair kernel:

    `x ↦ (∏ i, θ(x i)²) · wLoc ℓ v u (x a) (x b)`.

The window product is a product of `L¹` one-body functions, hence integrable on
the finite product space (`MeasureTheory.Integrable.fintype_prod`), and by
hypothesis the localised kernel is bounded (`hbdd`); the whole integrand is
therefore dominated by `B · ∏ i, θ(x i)²` and `MeasureTheory.Integrable.mono'`
finishes.  The hypotheses on `θ` are used to build the dominating function
(smooth + compact support ⟹ `θ²` is `L¹`), while `hv` is used only to know that
`wLoc ℓ v u` is measurable.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseKinLoc.Word

/-- `χ_u` is continuous in the point variable. -/
private lemma continuous_chiU (ℓ : ℝ) (u : ℝ³) :
    Continuous (fun x : ℝ³ => Submission.BoseGases.chiU ℓ u x) := by
  unfold Submission.BoseGases.chiU
  exact Submission.BoseGases.chi_continuous.comp (by fun_prop)

/-- Measurability of `x ↦ wLoc ℓ v u (x a) (x b)` on the configuration space.
The kernel is a product of the continuous window factors with the quotient
`v/(χ⋆χ)(·/ℓ)`, whose denominator is only measurable; measurability is therefore
the natural regularity, and it is inherited from `χ` and `v`. -/
private lemma measurable_wLoc_X {n : ℕ} (ℓ : ℝ) (u : ℝ³) {v : ℝ³ → ℝ} (hv : Continuous v)
    (a b : Fin n) :
    Measurable (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.wLoc ℓ v u (x a) (x b)) := by
  have ha : Measurable (fun x : Submission.BoseGases.X n => x a) := measurable_pi_apply a
  have hb : Measurable (fun x : Submission.BoseGases.X n => x b) := measurable_pi_apply b
  have h1 : Measurable (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.chiU ℓ u (x a)) := (continuous_chiU ℓ u).measurable.comp ha
  have h2 : Measurable (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.chiU ℓ u (x b)) := (continuous_chiU ℓ u).measurable.comp hb
  have hv' : Measurable (fun x : Submission.BoseGases.X n => v (x a - x b)) :=
    hv.measurable.comp (ha.sub hb)
  have hcs : Measurable (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.convScale ℓ (x a - x b)) :=
    (Submission.BoseGases.convScale_continuous ℓ).measurable.comp (ha.sub hb)
  unfold Submission.BoseGases.wLoc Submission.BoseGases.wScaled
  exact (h1.mul (hv'.div hcs)).mul h2

/-- Measurability of the `X n`-level integrand. -/
private lemma measurable_pair_prod {n : ℕ} (ℓ : ℝ) (u : ℝ³) {v θ : ℝ³ → ℝ}
    (hv : Continuous v) (hθ : Continuous θ) (a b : Fin n) :
    Measurable (fun x : Submission.BoseGases.X n =>
      (∏ i : Fin n, (θ (x i)) ^ 2) * Submission.BoseGases.wLoc ℓ v u (x a) (x b)) := by
  have h1 : Measurable (fun x : Submission.BoseGases.X n => ∏ i : Fin n, (θ (x i)) ^ 2) :=
    (continuous_finsetProd (Finset.univ : Finset (Fin n))
      (fun i _ => (hθ.comp (continuous_apply i)).pow 2)).measurable
  exact h1.mul (measurable_wLoc_X ℓ u hv a b)

/-- The product of the squared window over the `n`-particle configuration space
is integrable: it is a product of one-coordinate `L¹` functions. -/
private lemma integrable_prod_sq {n : ℕ} {θ : ℝ³ → ℝ} (hθ : ContDiff ℝ (⊤ : ENat) θ)
    (hθcs : HasCompactSupport θ) :
    Integrable (fun x : Submission.BoseGases.X n => ∏ i : Fin n, (θ (x i)) ^ 2) := by
  have hθ2 : Integrable (fun z : ℝ³ => (θ z) ^ 2) := by
    have hcs2 : HasCompactSupport (fun z : ℝ³ => (θ z) ^ 2) :=
      hθcs.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
    exact (hθ.continuous.pow 2).integrable_of_hasCompactSupport hcs2
  exact Integrable.fintype_prod (μ := fun _ : Fin n => (volume : Measure ℝ³))
    (f := fun (_ : Fin n) (z : ℝ³) => (θ z) ^ 2) (fun _ => hθ2)

theorem integrable_pair_prod {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (u : EuclideanSpace ℝ (Fin 3))
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hv : ContDiff ℝ (⊤ : ENat) v)
    (hbdd : ∃ B : ℝ, ∀ x y : EuclideanSpace ℝ (Fin 3),
      |Submission.BoseGases.wLoc ℓ v u x y| ≤ B)
    {θ : EuclideanSpace ℝ (Fin 3) → ℝ} (hθ : ContDiff ℝ (⊤ : ENat) θ)
    (hθcs : HasCompactSupport θ) (a b : Fin n) :
    MeasureTheory.Integrable (fun x : Submission.BoseGases.X n =>
      (∏ i : Fin n, (θ (x i)) ^ 2) * Submission.BoseGases.wLoc ℓ v u (x a) (x b)) := by
  obtain ⟨B, hB⟩ := hbdd
  have hg : Integrable (fun x : Submission.BoseGases.X n => B * ∏ i : Fin n, (θ (x i)) ^ 2) :=
    (integrable_prod_sq (n := n) hθ hθcs).const_mul B
  refine Integrable.mono' hg
    (measurable_pair_prod ℓ u hv.continuous hθ.continuous a b).aestronglyMeasurable ?_
  filter_upwards with x
  have hxnn : 0 ≤ ∏ i : Fin n, (θ (x i)) ^ 2 :=
    Finset.prod_nonneg fun i _ => sq_nonneg (θ (x i))
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hxnn]
  calc (∏ i : Fin n, (θ (x i)) ^ 2) * |Submission.BoseGases.wLoc ℓ v u (x a) (x b)|
      ≤ (∏ i : Fin n, (θ (x i)) ^ 2) * B :=
        mul_le_mul_of_nonneg_left (hB (x a) (x b)) hxnn
    _ = B * ∏ i : Fin n, (θ (x i)) ^ 2 := by ring

end Work.BoseKinLoc.Word
