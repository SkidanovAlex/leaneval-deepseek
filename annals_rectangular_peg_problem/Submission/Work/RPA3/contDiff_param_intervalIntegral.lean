import Mathlib
import Submission.Work.RPA3.Defs
import Submission.Work.RPA3.local_bound_continuous_prod

namespace Work.RPA3

universe u

open MeasureTheory
open scoped Interval

/-- Differentiation under the integral sign for a parametric *interval* integral: if
`g : X → ℝ → F` is jointly `C^1` then `x ↦ ∫ u in a..b, g x u` is differentiable at `x₀` with
derivative `∫ u in a..b, ∂₁ g (x₀,u) du`, where `∂₁ g = fderiv ℝ g ∘ inl` is the partial
derivative with respect to the parameter.

This is the inductive step of `contDiff_param_intervalIntegral`: it is
`intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le` fed with the local uniform
bound of `Work.RPA3.local_bound_continuous_prod` for the continuous derivative
`(x,u) ↦ (fderiv ℝ G (x,u)) ∘ inl`. -/
theorem hasFDerivAt_param_intervalIntegral_aux {X F : Type u} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (g : X → ℝ → F) (hg : ContDiff ℝ 1 (fun z : X × ℝ => g z.1 z.2)) (a b : ℝ) (x₀ : X) :
    HasFDerivAt (fun x : X => ∫ u in a..b, g x u)
      (∫ u in a..b,
        (fderiv ℝ (fun z : X × ℝ => g z.1 z.2) (x₀, u)).comp (ContinuousLinearMap.inl ℝ X ℝ)) x₀ := by
  let G : X × ℝ → F := fun z => g z.1 z.2
  let T : ((X × ℝ) →L[ℝ] F) →L[ℝ] (X →L[ℝ] F) :=
    ContinuousLinearMap.precomp F (ContinuousLinearMap.inl ℝ X ℝ)
  let φ : X → ℝ → (X →L[ℝ] F) := fun x u => T (fderiv ℝ G (x, u))
  have hGdiff : Differentiable ℝ G := hg.differentiable_one
  have hfdcont : Continuous (fderiv ℝ G) := hg.continuous_fderiv (by norm_num)
  have hpre : ∀ A : (X × ℝ) →L[ℝ] F, T A = A.comp (ContinuousLinearMap.inl ℝ X ℝ) :=
    fun A => ContinuousLinearMap.precomp_apply F (ContinuousLinearMap.inl ℝ X ℝ) A
  have hφcont : Continuous (fun z : X × ℝ => φ z.1 z.2) := by
    change Continuous (T ∘ fderiv ℝ G)
    exact T.continuous.comp hfdcont
  obtain ⟨δ, hδpos, C, hC⟩ := local_bound_continuous_prod hφcont x₀ a b
  have key : HasFDerivAt (fun x : X => ∫ u in a..b, g x u) (∫ u in a..b, φ x₀ u) x₀ := by
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (μ := volume) (F := fun x u => g x u) (F' := φ)
      (s := Metric.ball x₀ δ) (bound := fun _ => C)
      (Metric.ball_mem_nhds x₀ hδpos) ?_ ?_ ?_ ?_ ?_ ?_
    · refine Filter.Eventually.of_forall (fun x => ?_)
      exact ((hg.continuous.comp (continuous_const.prodMk continuous_id)) :
        Continuous (fun u : ℝ => g x u)).aestronglyMeasurable
    · exact ((hg.continuous.comp (continuous_const.prodMk continuous_id)) :
        Continuous (fun u : ℝ => g x₀ u)).intervalIntegrable a b
    · exact ((T.continuous.comp (hfdcont.comp (continuous_const.prodMk continuous_id))) :
        Continuous (fun u : ℝ => φ x₀ u)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun t ht x hx => ?_)
      exact hC x (Metric.mem_ball.mp hx) t (Set.uIoc_subset_uIcc ht)
    · exact intervalIntegrable_const
    · refine Filter.Eventually.of_forall (fun t _ht x _hx => ?_)
      show HasFDerivAt (fun x : X => g x t) (T (fderiv ℝ G (x, t))) x
      rw [hpre (fderiv ℝ G (x, t))]
      exact HasFDerivAt.comp (𝕜 := ℝ) (g := G) (f := fun e : X => (e, t)) x
        ((hGdiff (x, t)).hasFDerivAt) (hasFDerivAt_prodMk_left x t)
  have hderiv : (∫ u in a..b, φ x₀ u)
      = ∫ u in a..b,
        (fderiv ℝ (fun z : X × ℝ => g z.1 z.2) (x₀, u)).comp
          (ContinuousLinearMap.inl ℝ X ℝ) := by
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    exact hpre (fderiv ℝ G (x₀, u))
  rw [hderiv] at key
  exact key

/-- Smoothness of a parametric interval integral: if `g : X → ℝ → F` is `C^n` jointly in
`(x,u)` then `x ↦ ∫ u in a..b, g x u` is `C^n`.  (Missing from Mathlib; needed for the flux
primitive, where `h(τ,x,t) = -∫_{y=-X₀}^{x} β(τ,y,t) dy` is written as a parametric integral over a
*fixed* interval, `∫_0^1 (x+X₀) • β(τ, -X₀+s(x+X₀), t) ds`.)

Proof sketch: induction on `n` using `contDiff_succ_iff_hasFDerivAt`, or `ENat.nat_induction`; the
template is `contDiffOn_convolution_right_with_param_aux` in
`Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`.  The derivative is
`∫ u in a..b, fderiv ℝ g (x,u) du`, by
`intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`; the domination bound comes from
the tube lemma (continuity of the derivative on the compact product of a parameter neighbourhood and
the interval, in finite or infinite dimensions).  `ContDiff.fderiv` gives the `C^n`-regularity of
`(x,u) ↦ fderiv ℝ g (x,u)`, so the induction hypothesis applies to it.  The base case is
`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`.  Both spaces live in the
same universe `u` because the induction changes only the codomain, to `X →L[ℝ] F`. -/
theorem contDiff_param_intervalIntegral {X F : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (n : ENat) (g : X → ℝ → F) (hg : ContDiff ℝ n (fun z : X × ℝ => g z.1 z.2)) (a b : ℝ) :
    ContDiff ℝ n (fun x : X => ∫ u in a..b, g x u) := by
  induction n using ENat.nat_induction generalizing F g with
  | zero =>
    change ContDiff ℝ (0 : WithTop ENat) (fun z : X × ℝ => g z.1 z.2) at hg
    change ContDiff ℝ (0 : WithTop ENat) (fun x : X => ∫ u in a..b, g x u)
    rw [contDiff_zero] at hg ⊢
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hg a b
  | succ n ih =>
    push_cast at hg ⊢
    rw [contDiff_succ_iff_hasFDerivAt]
    let T : ((X × ℝ) →L[ℝ] F) →L[ℝ] (X →L[ℝ] F) :=
      ContinuousLinearMap.precomp F (ContinuousLinearMap.inl ℝ X ℝ)
    let g' : X → ℝ → (X →L[ℝ] F) := fun x u => T (fderiv ℝ (fun z : X × ℝ => g z.1 z.2) (x, u))
    refine ⟨fun x => ∫ u in a..b, g' x u, ?_, ?_⟩
    · apply ih
      have hfd : ContDiff ℝ ↑n (fderiv ℝ (fun z : X × ℝ => g z.1 z.2)) := by
        have := hg.fderiv_right (m := (↑n : ENat)) le_rfl
        simpa using this
      change ContDiff ℝ ↑n (T ∘ fderiv ℝ (fun z : X × ℝ => g z.1 z.2))
      exact T.contDiff.comp hfd
    · intro x₀
      have hg1 : ContDiff ℝ 1 (fun z : X × ℝ => g z.1 z.2) := hg.of_le (by simp)
      have hb := hasFDerivAt_param_intervalIntegral_aux (g := g) hg1 a b x₀
      have hderiv : (∫ u in a..b, g' x₀ u)
          = ∫ u in a..b,
            (fderiv ℝ (fun z : X × ℝ => g z.1 z.2) (x₀, u)).comp
              (ContinuousLinearMap.inl ℝ X ℝ) := by
        refine intervalIntegral.integral_congr (fun u _ => ?_)
        exact ContinuousLinearMap.precomp_apply F (ContinuousLinearMap.inl ℝ X ℝ)
          (fderiv ℝ (fun z : X × ℝ => g z.1 z.2) (x₀, u))
      change HasFDerivAt (fun x : X => ∫ u in a..b, g x u) (∫ u in a..b, g' x₀ u) x₀
      rw [hderiv]
      exact hb
  | top ih =>
    rw [contDiff_infty] at hg ⊢
    intro m
    exact ih m g (hg m)

end Work.RPA3
