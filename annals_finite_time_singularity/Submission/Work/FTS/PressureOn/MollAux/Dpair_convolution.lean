/-
# `Work.FTS.PressureOn.MollAux.Dpair_convolution`

The pairing `Dpair q Φ f = ∫ ⟪Φ, f⟫ + ∫ q · div f` of the pressure reconstruction is *invariant*
under regularising the pair `(q, Φ)` by an even mollifier `ρ`, i.e.

  `Dpair q Φ (ρ ⋆ f) = Dpair (ρ ⋆ q) (ρ ⋆ Φ) f`

for `ρ` smooth, compactly supported and even, `q` and `Φ` continuous, and `f` smooth with compact
support.

## The route

Both sides are compared with the same double integral.  Writing `Dpair` out,

* `∫ x, ⟪Φ x, (ρ ⋆ f) x⟫ = ∫ x, ∫ t, ρ t * ⟪Φ x, f (x - t)⟫` (inner product out of the Bochner
  integral, using `ρ t • f (x - t)` and `⟪Φ x, r • v⟫ = r * ⟪Φ x, v⟫),
* `∫ x, q x * div (ρ ⋆ f) x = ∫ x, q x * (ρ ⋆ div f) x = ∫ x, ∫ t, q x * (ρ t * div f (x - t))`
  (the divergence commutes with the convolution, `Auxiliary.div_convolution`),

and Fubini (`MeasureTheory.integral_integral_swap`, the integrability side conditions being the
four lemmas `Auxiliary.integrable_uncurry_mul_sub`, `Auxiliary.integrable_uncurry_mul_sub_left`), the translation
invariance of Lebesgue measure (`MeasureTheory.integral_add_right_eq_self`) and its invariance
under `t ↦ -t` (`MeasureTheory.integral_neg_eq_self`) together with the evenness of `ρ` identify
the two iterated integrals.  The two identifications are exactly the lemmas
`Auxiliary.integral_inner_convolution_eq` (vector pairing) and `Auxiliary.integral_mul_convolution_eq` (scalar
pairing), applied with `b := div f`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.FTS.PressureOn.MollDefs
import Submission.Work.FTS.PressureOn.PoissonAux.Ibp
import Submission.Work.FTS.PressureOn.Auxiliary.integral_mul_div_eq_neg_inner_gradient
import Submission.Work.FTS.PressureOn.Auxiliary.div_convolution
import Submission.Work.FTS.PressureOn.Auxiliary.integral_inner_convolution_eq
import Submission.Work.FTS.PressureOn.Auxiliary.integral_mul_convolution_eq
import Submission.Work.FTS.PressureOn.Auxiliary.integrable_uncurry_mul_sub
import Submission.Work.FTS.PressureOn.Auxiliary.integrable_uncurry_mul_sub_left

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.MollAux

open MeasureTheory

/-- The divergence of a compactly supported field is compactly supported: off `tsupport f` the
field is locally zero, hence so is its derivative, hence so is the trace. -/
lemma hasCompactSupport_div (f : R3 → R3) (hfc : HasCompactSupport f) :
    HasCompactSupport (fun y => FiniteTimeSingularity.div f y) := by
  refine hfc.mono' fun y hy => ?_
  by_contra hx
  rw [Function.mem_support] at hy
  exact hy (Auxiliary.div_eq_zero_of_notMem_tsupport hx)

theorem Dpair_convolution (q : EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (ρ : EuclideanSpace ℝ (Fin 3) → ℝ) (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hρ : ∀ n : ℕ, ContDiff ℝ n ρ) (hρc : HasCompactSupport ρ) (hρeven : ∀ z, ρ (-z) = ρ z)
    (hf : ∀ n : ℕ, ContDiff ℝ n f) (hfc : HasCompactSupport f)
    (hq : Continuous q) (hΦ : Continuous Φ) :
    Work.FTS.PressureOn.Dpair q Φ
        (MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume)
      = Work.FTS.PressureOn.Dpair
          (MeasureTheory.convolution ρ q (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume)
          (MeasureTheory.convolution ρ Φ (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume) f := by
  have hρ' : Continuous ρ := (hρ 0).continuous
  have hf' : Continuous f := (hf 0).continuous
  have hdiv_cont : Continuous fun y => FiniteTimeSingularity.div f y :=
    Work.FTS.PressureOn.continuous_div_of_contDiff (hf 1)
  have hdiv_cs : HasCompactSupport fun y => FiniteTimeSingularity.div f y :=
    hasCompactSupport_div f hfc
  -- the four integrability side conditions for the Fubini steps
  have hα : MeasureTheory.Integrable (Function.uncurry fun (x t : R3) =>
      ρ t * inner ℝ (Φ x) (f (x - t))) (MeasureTheory.volume.prod MeasureTheory.volume) := by
    refine MeasureTheory.Integrable.mono'
      (Auxiliary.integrable_uncurry_mul_sub (fun x => ‖Φ x‖) (fun x => ‖f x‖) (fun t => |ρ t|)
        hΦ.norm hf'.norm hρ'.abs (hfc.comp_left (g := fun v : R3 => ‖v‖) (by simp))
        hρc.abs) ?_ ?_
    · have hcont : Continuous fun p : R3 × R3 =>
          ρ p.2 * inner ℝ (Φ p.1) (f (p.1 - p.2)) :=
        (hρ'.comp continuous_snd).mul
          ((hΦ.comp continuous_fst).inner (hf'.comp (continuous_fst.sub continuous_snd)))
      exact hcont.aestronglyMeasurable
    · filter_upwards with p
      calc ‖ρ p.2 * inner ℝ (Φ p.1) (f (p.1 - p.2))‖
          = |ρ p.2| * |inner ℝ (Φ p.1) (f (p.1 - p.2))| := by
            rw [Real.norm_eq_abs, abs_mul]
        _ ≤ |ρ p.2| * (‖Φ p.1‖ * ‖f (p.1 - p.2)‖) :=
            mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)
        _ = |ρ p.2| * ‖Φ p.1‖ * ‖f (p.1 - p.2)‖ := by ring
  have hβ : MeasureTheory.Integrable (Function.uncurry fun (x t : R3) =>
      ρ t * inner ℝ (Φ (x - t)) (f x)) (MeasureTheory.volume.prod MeasureTheory.volume) := by
    refine MeasureTheory.Integrable.mono'
      (Auxiliary.integrable_uncurry_mul_sub_left (fun x => ‖f x‖) (fun x => ‖Φ x‖) (fun t => |ρ t|)
        hf'.norm hΦ.norm hρ'.abs (hfc.comp_left (g := fun v : R3 => ‖v‖) (by simp))
        hρc.abs) ?_ ?_
    · have hcont : Continuous fun p : R3 × R3 =>
          ρ p.2 * inner ℝ (Φ (p.1 - p.2)) (f p.1) :=
        (hρ'.comp continuous_snd).mul
          ((hΦ.comp (continuous_fst.sub continuous_snd)).inner (hf'.comp continuous_fst))
      exact hcont.aestronglyMeasurable
    · filter_upwards with p
      calc ‖ρ p.2 * inner ℝ (Φ (p.1 - p.2)) (f p.1)‖
          = |ρ p.2| * |inner ℝ (Φ (p.1 - p.2)) (f p.1)| := by
            rw [Real.norm_eq_abs, abs_mul]
        _ ≤ |ρ p.2| * (‖Φ (p.1 - p.2)‖ * ‖f p.1‖) :=
            mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)
        _ = |ρ p.2| * ‖f p.1‖ * ‖Φ (p.1 - p.2)‖ := by ring
  have hγ : MeasureTheory.Integrable (Function.uncurry fun (x t : R3) =>
      q x * (ρ t * FiniteTimeSingularity.div f (x - t)))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    refine (Auxiliary.integrable_uncurry_mul_sub q (fun y => FiniteTimeSingularity.div f y) ρ
      hq hdiv_cont hρ' hdiv_cs hρc).congr ?_
    filter_upwards with p
    obtain ⟨x, t⟩ := p
    show ρ t * q x * FiniteTimeSingularity.div f (x - t)
        = q x * (ρ t * FiniteTimeSingularity.div f (x - t))
    ring
  have hδ : MeasureTheory.Integrable (Function.uncurry fun (x t : R3) =>
      (ρ t * q (x - t)) * FiniteTimeSingularity.div f x)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    refine (Auxiliary.integrable_uncurry_mul_sub_left (fun y => FiniteTimeSingularity.div f y) q ρ
      hdiv_cont hq hρ' hdiv_cs hρc).congr ?_
    filter_upwards with p
    obtain ⟨x, t⟩ := p
    show ρ t * FiniteTimeSingularity.div f x * q (x - t)
        = (ρ t * q (x - t)) * FiniteTimeSingularity.div f x
    ring
  rw [Work.FTS.PressureOn.Dpair, Work.FTS.PressureOn.Dpair]
  have h1 : ∫ x, inner ℝ (Φ x)
        (MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x)
      = ∫ x, inner ℝ
          (MeasureTheory.convolution ρ Φ (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x)
          (f x) :=
    Auxiliary.integral_inner_convolution_eq Φ f ρ hΦ hf' hfc hρ' hρc hρeven hα hβ
  have h2 : ∫ x, q x * FiniteTimeSingularity.div
        (MeasureTheory.convolution ρ f (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume) x
      = ∫ x, (MeasureTheory.convolution ρ q (ContinuousLinearMap.lsmul ℝ ℝ) MeasureTheory.volume x)
          * FiniteTimeSingularity.div f x := by
    have hdiv := Auxiliary.div_convolution ρ f ((hρ 0).continuous.locallyIntegrable) (hf 1) hfc
    simp only [hdiv]
    exact Auxiliary.integral_mul_convolution_eq q (fun y => FiniteTimeSingularity.div f y) ρ
      hq hdiv_cont hdiv_cs hρ' hρc hρeven hγ hδ
  rw [h1, h2]

end Work.FTS.PressureOn.MollAux
