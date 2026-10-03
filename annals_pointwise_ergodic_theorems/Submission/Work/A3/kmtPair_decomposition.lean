import Mathlib
import Submission.Work.A3.kmtPair_sum_right
import Submission.Work.A3.kmtPair_left_sum
import Submission.Work.Analysis.Interpolation.analyticFamily_boundary
import Submission.Work.Analysis.Interpolation.eLpNorm_eq_iSup_simpleFunc_integral
import Submission.Work.Analysis.Interpolation.riesz_thorin_linear
import Submission.Work.Analysis.Interpolation.stein_trilinear

/-!
# Level-set decomposition of the Hausdorff--Young pairing of two analytic families

The pairing `kmtPair s u v = ∫₀¹ (∑_{x ∈ s} u x · e(-xθ)) v(θ) dθ` of
`HausdorffYoungDefs`, evaluated on the two analytic families
`analyticFamily f a₀ a₁ z` and `analyticFamily g b₀ b₁ z` attached to simple functions
`f : ℤ →ₛ ℂ` and `g : ℝ →ₛ ℂ`, expands as the finite double sum over the level sets of `f`
and `g`:

`kmtPair s (f_z) (g_z) = ∑_{c ∈ f.range} ∑_{d ∈ g.range}
    (phasePow c e_z · phasePow d e'_z) · kmtPair s (1_{f ⁻¹' {c}}) (1_{g ⁻¹' {d}})`

where `e_z = expFamily a₀ a₁ z`, `e'_z = expFamily b₀ b₁ z`.

This is the "matrix coefficient" representation of the pairing: the `z`-dependence sits entirely
in the entire scalar coefficients `phasePow · (expFamily · · z)`, the pairings
`kmtPair s (1_{f ⁻¹' {c}}) (1_{g ⁻¹' {d}})` are independent of `z`.  It is the analogue, for the
(merely) bilinear form `kmtPair` — which is *not* linear in its second argument because of the
a.e.-measurability guard in its definition — of
`Work.Analysis.Interpolation.bilinear_decomposition` for an honest bilinear form.

The proof combines the level-set decomposition of a single analytic family
(`Work.Analysis.Interpolation.analyticFamily_eq_sum`) with the two linearity steps
`Work.A3.kmtPair_sum_right` (the second slot: a finite combination of measurable level-set
indicators pulls out of the pairing) and `Work.A3.kmtPair_left_sum` (the first slot).
-/

set_option autoImplicit false

namespace Work.A3

/-- Elementary rearrangement of the factors in the summand of `kmtPair_decomposition`: this is
the scalar arithmetic `δ · (γ · x) = (γ · δ) · x` responsible for the order
`phasePow c e_z * phasePow d e'_z` of the two coefficients in the decomposition. -/
private lemma kmtPair_decomposition_mul_swap (a b x : ℂ) : b * (a * x) = (a * b) * x := by
  ring

theorem kmtPair_decomposition (s : Finset ℤ) (f : MeasureTheory.SimpleFunc ℤ ℂ) (g : MeasureTheory.SimpleFunc ℝ ℂ) (a₀ a₁ b₀ b₁ : ℝ) (z : ℂ) : Work.A3.kmtPair s (Work.Analysis.Interpolation.analyticFamily (f : ℤ → ℂ) ((a₀ : ℝ) : ℂ) ((a₁ : ℝ) : ℂ) z) (Work.Analysis.Interpolation.analyticFamily (g : ℝ → ℂ) ((b₀ : ℝ) : ℂ) ((b₁ : ℝ) : ℂ) z) = ∑ c ∈ f.range, ∑ d ∈ g.range, (Work.Analysis.Interpolation.phasePow c (Work.Analysis.Interpolation.expFamily ((a₀ : ℝ) : ℂ) ((a₁ : ℝ) : ℂ) z) * Work.Analysis.Interpolation.phasePow d (Work.Analysis.Interpolation.expFamily ((b₀ : ℝ) : ℂ) ((b₁ : ℝ) : ℂ) z)) * (Work.A3.kmtPair s (Set.indicator (f ⁻¹' {c}) (fun _ => (1 : ℂ))) (Set.indicator (g ⁻¹' {d}) (fun _ => (1 : ℂ)))) := by
  -- decompose both analytic families into their level-set indicators
  rw [Work.Analysis.Interpolation.analyticFamily_eq_sum f ((a₀ : ℝ) : ℂ) ((a₁ : ℝ) : ℂ) z,
    Work.Analysis.Interpolation.analyticFamily_eq_sum g ((b₀ : ℝ) : ℂ) ((b₁ : ℝ) : ℂ) z]
  -- align the order of the two finite sums with the order in which they will be pulled out
  rw [Finset.sum_comm]
  -- pull the combination of level-set indicators of `g` out of the second slot
  rw [kmtPair_sum_right s _ g.range
    (fun d => Work.Analysis.Interpolation.phasePow d
      (Work.Analysis.Interpolation.expFamily ((b₀ : ℝ) : ℂ) ((b₁ : ℝ) : ℂ) z))
    (fun d => g ⁻¹' {d}) (fun d _ => g.measurableSet_fiber' d)]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  -- pull the combination of level-set indicators of `f` out of the first slot
  rw [kmtPair_left_sum s f.range
    (fun c => Work.Analysis.Interpolation.phasePow c
      (Work.Analysis.Interpolation.expFamily ((a₀ : ℝ) : ℂ) ((a₁ : ℝ) : ℂ) z))
    (fun c => f ⁻¹' {c}) (g ⁻¹' {d}) (g.measurableSet_fiber' d)]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun c _ => kmtPair_decomposition_mul_swap _ _ _)

end Work.A3
