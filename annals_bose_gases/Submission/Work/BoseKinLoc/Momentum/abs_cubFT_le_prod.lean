import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Work.BoseKinLoc.Momentum.cubFT_fubini_complex
import Submission.Work.BoseKinLoc.Momentum.cubFT_one_dim_cos_bound
import Submission.Work.BoseKinLoc.Momentum.cubFT_one_dim_exp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The momentum-decay bound for the unit-cube symbol (FS `eq:Q1Qslide`, `lm:kinloc`)

`cubFT q = ∫_{Λ(1)} cos ⟪q,x⟫ dx` is (the real form of) the Fourier transform of the
indicator of the unit cube.  Since the cube is a product of intervals and
`e^{i⟪q,x⟫} = ∏ᵢ e^{i qᵢ xᵢ}`, the transform factorises into a product of one-dimensional
transforms, each of which is `∫_{−1/2}^{1/2} cos(qᵢ t) dt = 2 sin(qᵢ/2)/qᵢ`.  Bounding
`|sin| ≤ 1` and `|sin u| ≤ |u|` gives `|∫ cos(qᵢ t)| ≤ 2/max(1,|qᵢ|)`, whence

`|cubFT q| ≤ ∏ᵢ 2/max(1,|qᵢ|)`,

the pointwise momentum weight that turns the sliding box symbol `cubeB` into the
localisation excess of FS's `eq:Q1Qslide`.

The formalisation of the factorisation goes through the complex exponential (so that Fubini
applies to a genuine product of one-dimensional functions): `cos ⟪q,z⟫` is the real part of
`∏ᵢ e^{i qᵢ zᵢ}`, the complex Fubini lemma `cubFT_fubini_complex` factorises the integral of
the product, and each factor `∫_{−1/2}^{1/2} e^{i a t} dt` is real, equal to
`∫_{−1/2}^{1/2} cos(a t) dt` (`cubFT_one_dim_exp`), because `sin` is odd on a symmetric
interval.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real BigOperators ENNReal

namespace Work.BoseKinLoc.Momentum

open Submission.BoseGases

set_option autoImplicit false

theorem abs_cubFT_le_prod (q : EuclideanSpace ℝ (Fin 3)) :
    |cubFT q| ≤ ∏ i : Fin 3, 2 / max 1 |q i| := by
  -- **Step 1 (pointwise).** `cos ⟪q,z⟫ = Re ∏ᵢ e^{i qᵢ zᵢ}`.
  have hpt : ∀ z : EuclideanSpace ℝ (Fin 3),
      Real.cos (inner ℝ q z) = (∏ i : Fin 3, Complex.exp (↑(q i * z i) * Complex.I)).re := by
    intro z
    have hsum : ∑ i : Fin 3, (↑(q i * z i) : ℂ) * Complex.I
        = ↑(inner ℝ q z) * Complex.I := by
      rw [← Finset.sum_mul, ← Complex.ofReal_sum]
      congr 1
      rw [PiLp.inner_apply]
      simp [RCLike.inner_apply, mul_comm]
    rw [← Complex.exp_ofReal_mul_I_re (inner ℝ q z), ← hsum,
      ← Complex.exp_sum Finset.univ]
  -- **Step 2 (integrability).**  A continuous function on the compact cube is integrable.
  have hint : IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) =>
      ∏ i : Fin 3, Complex.exp (↑(q i * z i) * Complex.I)) (acube 1) volume :=
    ContinuousOn.integrableOn_compact
      (acube_compact (by norm_num : (0 : ℝ) < 1)) (by fun_prop)
  -- **Step 3 (exact factorisation of the cube transform).**
  have hmain : cubFT q = ∏ i : Fin 3,
      ∫ t in Set.Icc (-(1 : ℝ) / 2) ((1 : ℝ) / 2), Real.cos (q i * t) := by
    calc cubFT q = ∫ z in acube 1, Real.cos (inner ℝ q z) := rfl
      _ = ∫ z in acube 1,
            (∏ i : Fin 3, Complex.exp (↑(q i * z i) * Complex.I)).re := by
            exact setIntegral_congr_fun (acube_measurable 1) fun z _ => hpt z
      _ = (∫ z in acube 1, ∏ i : Fin 3, Complex.exp (↑(q i * z i) * Complex.I)).re :=
            integral_re hint
      _ = (∏ i : Fin 3,
            ∫ t in Set.Icc (-(1 : ℝ) / 2) ((1 : ℝ) / 2),
              Complex.exp (↑(q i * t) * Complex.I)).re := by
            rw [cubFT_fubini_complex 1 (fun i t => Complex.exp (↑(q i * t) * Complex.I))]
      _ = ∏ i : Fin 3,
            ∫ t in Set.Icc (-(1 : ℝ) / 2) ((1 : ℝ) / 2), Real.cos (q i * t) := by
            rw [show (∏ i : Fin 3,
                  ∫ t in Set.Icc (-(1 : ℝ) / 2) ((1 : ℝ) / 2),
                    Complex.exp (↑(q i * t) * Complex.I))
                = ∏ i : Fin 3,
                    (↑(∫ t in Set.Icc (-(1 : ℝ) / 2) ((1 : ℝ) / 2),
                        Real.cos (q i * t)) : ℂ) from
              Finset.prod_congr rfl fun i _ => cubFT_one_dim_exp (q i)]
            rw [← Complex.ofReal_prod]
            exact Complex.ofReal_re _
  -- **Step 4 (product bound).**
  rw [hmain, Finset.abs_prod]
  exact Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) fun i _ =>
    cubFT_one_dim_cos_bound (q i)

end Work.BoseKinLoc.Momentum
