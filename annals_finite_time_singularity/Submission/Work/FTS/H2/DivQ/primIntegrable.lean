import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.H2.DivQ

/-- The pointwise AM–GM split used in `primIntegrable`: for `s > 0` and any real `a`,
`2·(s^k·|a|) ≤ s^γ + s^{2k-γ}·a²`.  It is the AM–GM inequality `2uv ≤ u² + v²` applied to
`u = s^{(2k-γ)/2}·|a|`, `v = s^{γ/2}`, together with the rpow identities
`s^{(2k-γ)/2}·s^{γ/2} = s^k`, `(s^{(2k-γ)/2})² = s^{2k-γ}`, `(s^{γ/2})² = s^γ`. -/
lemma two_mul_pow_mul_abs_le_amgm (k : ℕ) (γ s a : ℝ) (hs : 0 < s) :
    2 * (s ^ k * |a|) ≤ s ^ γ + s ^ (2 * (k : ℝ) - γ) * a ^ 2 := by
  have hk2 : (2 * (k : ℝ) - γ) / 2 + γ / 2 = (k : ℝ) := by ring
  have hu : (2 * (k : ℝ) - γ) / 2 + (2 * (k : ℝ) - γ) / 2 = 2 * (k : ℝ) - γ := by ring
  have hg : γ / 2 + γ / 2 = γ := by ring
  have hL : (s ^ ((2 * (k : ℝ) - γ) / 2) * |a|) * s ^ (γ / 2) = s ^ k * |a| := by
    rw [mul_right_comm, ← Real.rpow_add hs, hk2, Real.rpow_natCast]
  have hA : (s ^ ((2 * (k : ℝ) - γ) / 2) * |a|) ^ 2 = s ^ (2 * (k : ℝ) - γ) * a ^ 2 := by
    rw [mul_pow, sq_abs, pow_two, ← Real.rpow_add hs, hu]
  have hB : (s ^ (γ / 2)) ^ 2 = s ^ γ := by
    rw [pow_two, ← Real.rpow_add hs, hg]
  have key := two_mul_le_add_sq (s ^ ((2 * (k : ℝ) - γ) / 2) * |a|) (s ^ (γ / 2))
  rw [mul_assoc, hL, hA, hB] at key
  linarith

/-- First conjunct of `Work.FTS.H2.DivQ.divSinPrimitiveIntegral`: the function
`ψ s = s^k·f^{(k+1)}(s)` is integrable on `(0,x₁]`, under `f` of class `C^∞` on `(0,x₁]`,
`γ > -1`, and the weighted square-integrability of `f^{(k+1)}`.
Route: for `s ∈ (0,x₁]`, `s^k|f^{(k+1)}(s)| = s^{γ/2}·(s^{k-γ/2}|f^{(k+1)}(s)|) ≤ s^γ + s^{2k-γ}(f^{(k+1)}(s))²`
(the AM–GM inequality `2ab ≤ a²+b²` with `a = s^{(2k-γ)/2}|f^{(k+1)}|`, `b = s^{γ/2}`; the rpow
identities are `Real.rpow_add`/`Real.rpow_natCast`).  Both summands are `IntegrableOn (Ioc 0 x₁)`:
`s ↦ s^γ` by `intervalIntegral.intervalIntegrable_rpow' hγ` plus `intervalIntegrable_iff` +
`uIoc_of_le`, and `s ↦ s^{2k-γ}(f^{(k+1)}s)²` by hypothesis.  ψ is a.e.-strongly measurable on
`Ioc 0 x₁` because `f` is smooth on the *open* set `Ioo 0 x₁ ⊇` its points (`ContDiffOn` on `Ioc`
restricts to `Ioo`, giving `ContinuousOn (iteratedDeriv (k+1) f) (Ioo 0 x₁)` via
`ContDiffOn.continuousOn_iteratedDerivWithin` + `uniqueDiffOn_Ioo` + `iteratedDerivWithin_of_isOpen`),
and `volume.restrict (Ioc 0 x₁) = volume.restrict (Ioo 0 x₁)`
(`MeasureTheory.restrict_Ioo_eq_restrict_Ioc`).  Then `Integrable.mono'`. -/
theorem primIntegrable (k : ℕ) (γ x₁ : ℝ) (hx₁ : 0 < x₁) (hγ : -1 < γ)
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioc 0 x₁))
    (hint : MeasureTheory.IntegrableOn
      (fun x : ℝ => x ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f x) ^ 2)
      (Set.Ioc 0 x₁)) :
    MeasureTheory.IntegrableOn (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s)
      (Set.Ioc 0 x₁) := by
  -- `f` is `C^∞` on the open set `Ioo 0 x₁ ⊆ Ioc 0 x₁`, so the `(k+1)`-st derivative is
  -- continuous there, hence `ψ` is a.e.-strongly measurable on `Ioc 0 x₁`.
  have hIoo : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioo 0 x₁) := hf.mono Set.Ioo_subset_Ioc_self
  have hcW : ContinuousOn (iteratedDerivWithin (k + 1) f (Set.Ioo 0 x₁)) (Set.Ioo 0 x₁) :=
    hIoo.continuousOn_iteratedDerivWithin (by simp) (uniqueDiffOn_Ioo 0 x₁)
  have hc : ContinuousOn (iteratedDeriv (k + 1) f) (Set.Ioo 0 x₁) :=
    hcW.congr (fun x hx => (iteratedDerivWithin_of_isOpen isOpen_Ioo hx).symm)
  have hcψ : ContinuousOn (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s) (Set.Ioo 0 x₁) :=
    (continuousOn_id.pow k).mul hc
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => s ^ k * iteratedDeriv (k + 1) f s) (volume.restrict (Set.Ioc 0 x₁)) := by
    have h := hcψ.aestronglyMeasurable (μ := volume) measurableSet_Ioo
    rwa [MeasureTheory.restrict_Ioo_eq_restrict_Ioc] at h
  -- The two summands of the dominating function are integrable on `(0,x₁]`.
  have h1 : MeasureTheory.Integrable (fun s : ℝ => s ^ γ) (volume.restrict (Set.Ioc 0 x₁)) := by
    have h := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := x₁) (r := γ) hγ
    rw [intervalIntegrable_iff, Set.uIoc_of_le hx₁.le] at h
    exact h
  have h2 : MeasureTheory.Integrable
      (fun s : ℝ => s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2)
      (volume.restrict (Set.Ioc 0 x₁)) := hint
  have hInt : MeasureTheory.Integrable
      (fun s : ℝ => s ^ γ + s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2)
      (volume.restrict (Set.Ioc 0 x₁)) := h1.add h2
  -- Pointwise domination on `(0,x₁]` by the AM–GM split.
  have hbound : ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 x₁)),
      ‖s ^ k * iteratedDeriv (k + 1) f s‖ ≤
        s ^ γ + s ^ (2 * (k : ℝ) - γ) * (iteratedDeriv (k + 1) f s) ^ 2 := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall (fun s hs => ?_)
    have hs0 : 0 < s := hs.1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hs0.le k)]
    have hpos : 0 ≤ s ^ k * |iteratedDeriv (k + 1) f s| :=
      mul_nonneg (pow_nonneg hs0.le k) (abs_nonneg _)
    linarith [two_mul_pow_mul_abs_le_amgm k γ s (iteratedDeriv (k + 1) f s) hs0]
  exact MeasureTheory.Integrable.mono' hInt hmeas hbound

end Work.FTS.H2.DivQ
