import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.Honest.derivDeriv_divCos
import Submission.Work.FTS.EllipticEst.TanTheta.integrable_mul_of_sq_weight_of_aemeasurable
import Submission.Work.FTS.EllipticEst.AngSecond.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Honest

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-! ## Two helpers

The first is `L² · L² ⊆ L¹` for the angular weight written in the `sig`-form used by the
honest slice class; the second is the pointwise elimination of `ψ''` by the chain rule for
`u = cos θ · ψ`. -/

/-- **`L² · L² ⊆ L¹` for the angular weight `σ = sig`.**  If `f` and `g` are a.e. measurable
and `f² σ`, `g² σ` are integrable on `(0, π/2)`, then so is `f g σ`.

This is the `sig`-form of
`Work.FTS.EllipticEst.TanTheta.integrable_mul_of_sq_weight_of_aemeasurable`
(`σ θ = sin(2θ)^{-η}`). -/
private lemma integrable_mul_sig_of_sq_sig {f g : ℝ → ℝ}
    (hf : AEMeasurable f (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))))
    (hg : AEMeasurable g (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))))
    (hfsq : MeasureTheory.IntegrableOn
      (fun θ => f θ ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      (Set.Ioo 0 (Real.pi / 2)))
    (hgsq : MeasureTheory.IntegrableOn
      (fun θ => g θ ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ)
      (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.IntegrableOn
      (fun θ => f θ * g θ * Work.FTS.EllipticEst.AngSecond.sig θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  refine (Work.FTS.EllipticEst.TanTheta.integrable_mul_of_sq_weight_of_aemeasurable
    Work.Spaces.eta hf hg ?_ ?_).congr_fun ?_ measurableSet_Ioo
  · exact hfsq.congr_fun (fun θ _ => by simp [Work.FTS.EllipticEst.AngSecond.sig])
      measurableSet_Ioo
  · exact hgsq.congr_fun (fun θ _ => by simp [Work.FTS.EllipticEst.AngSecond.sig])
      measurableSet_Ioo
  · intro θ _
    simp [Work.FTS.EllipticEst.AngSecond.sig]

/-- **The pointwise elimination of `ψ''`.**  With `ψ = u / cos` and `σ = sig`, at every point
`θ` with `cos θ ≠ 0`,

  `ρ θ · ψ'(θ) · ψ''(θ) = sin θ · σ θ · ψ'(θ) · u''(θ) + cos θ · (ψ(θ) · sin θ · ψ'(θ) · σ θ)
      + 2 · (sin θ · ψ'(θ)) · (sin θ · ψ'(θ)) · σ θ`

(`ρ = wrho η`).  It is the chain-rule identity
`Work.FTS.EllipticEst.Honest.cos_mul_derivDeriv_divCos`, multiplied by `sin θ · σ θ · ψ'(θ)`. -/
private lemma wrho_mul_deriv_mul_deriv_divCos (u : ℝ → ℝ) {θ : ℝ}
    (hu : ContDiffAt ℝ 2 u θ) (hcos : Real.cos θ ≠ 0) :
    Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ * deriv (fun t => u t / Real.cos t) θ
        * deriv (deriv (fun t => u t / Real.cos t)) θ
      = (Real.sin θ * deriv (fun t => u t / Real.cos t) θ) * deriv (deriv u) θ
          * Work.FTS.EllipticEst.AngSecond.sig θ
        + Real.cos θ * ((u θ / Real.cos θ)
            * (Real.sin θ * deriv (fun t => u t / Real.cos t) θ)
            * Work.FTS.EllipticEst.AngSecond.sig θ)
        + 2 * ((Real.sin θ * deriv (fun t => u t / Real.cos t) θ)
            * (Real.sin θ * deriv (fun t => u t / Real.cos t) θ)
            * Work.FTS.EllipticEst.AngSecond.sig θ) := by
  have h := cos_mul_derivDeriv_divCos u hu hcos
  have key := congrArg (fun x => Real.sin θ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      * deriv (fun t => u t / Real.cos t) θ * x) h
  rw [mul_add, mul_add] at key
  simp only [Work.FTS.EllipticEst.TanTheta.wrho, Work.FTS.EllipticEst.AngSecond.sig]
  linear_combination key

/-- **Integrability of `ρ ψ' ψ''` on the angular slice, in the honest open-interval class.**

With `ψ = u / cos`, `σ = sin(2θ)^{-η}` (`η = Work.Spaces.eta`) and
`ρ = sin θ cos θ σ = Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta`, this says that
`∫_0^{π/2} ρ ψ' ψ''` is an honest integral, given the three integrabilities
`∫ (u'')² σ`, `∫ sin²θ (ψ')² σ`, `∫ ψ² σ` of the honest slice class.

It is the second integration-by-parts input (`hint2` of
`Work.FTS.EllipticEst.Honest.integral_Ioo_mul_deriv_eq_neg_half` with `f = ψ'`) of the proof of
`Work.FTS.EllipticEst.Honest.slice_ident_honest`, in which no integrability of `ρ ψ' ψ''` is
hypothesised and the second derivative `ψ''` must therefore be eliminated.

Hints (a full proof is expected):

* On `(0, π/2)` one has `cos θ ≠ 0`, so
  `Work.FTS.EllipticEst.Honest.cos_mul_derivDeriv_divCos` (from
  `Submission.Work.FTS.EllipticEst.Honest.derivDeriv_divCos`) turns the integrand, at every
  `θ ∈ Ioo 0 (π/2)`, into the sum of the three integrable pieces
  `sin θ · σ · ψ' · u''`, `sin θ · cos θ · σ · ψ · ψ' = (cos θ · ψ)·(sin θ · ψ')·σ` and
  `2 · sin²θ · σ · (ψ')²`.
* The first and the last follow from the `L² · L² ⊆ L¹` lemma
  `Work.FTS.EllipticEst.TanTheta.integrable_mul_of_sq_weight_of_aemeasurable`
  (`Submission/Work/FTS/EllipticEst/TanTheta/integrable_mul_of_sq_weight_of_aemeasurable.lean`,
  which also gives the `AEMeasurable` caveat) together with `hY` (for `sin²θ (ψ')² σ`) and `hX`
  (for `(u'')² σ`) -- the middle one uses `hA` (for `(cos θ · ψ)² σ`, via the bounded factor
  `cos²θ ≤ 1`) and `hY`.
* Conclude by `IntegrableOn.congr_fun` on the measurable set `Ioo 0 (π/2)` (note: no
  measurability of `ρ ψ' ψ''` itself is needed). -/
theorem integrableOn_wrho_mul_psiDeriv_mul_psiSecond (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hX : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)))
    (hY : MeasureTheory.IntegrableOn (fun θ => (Real.sin θ) ^ 2
      * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)))
    (hA : MeasureTheory.IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ
      * deriv (fun θ => u θ / Real.cos θ) θ
      * deriv (deriv (fun θ => u θ / Real.cos θ)) θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  set ψ : ℝ → ℝ := fun θ => u θ / Real.cos θ with hψ_def
  set A : ℝ → ℝ := fun θ => Real.sin θ * deriv ψ θ with hA_def
  -- `cos` does not vanish on the open interval
  have hcos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos θ ≠ 0 := by
    intro θ hθ
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2]⟩)
  -- a.e. measurability of the three factors
  have hψ_meas : AEMeasurable ψ (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    (hu.continuousOn.aemeasurable measurableSet_Ioo).div Real.measurable_cos.aemeasurable
  have hA_meas : AEMeasurable A (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    Real.measurable_sin.aemeasurable.mul (aemeasurable_deriv ψ _)
  have hu''_meas : AEMeasurable (fun θ => deriv (deriv u) θ)
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    aemeasurable_deriv (deriv u) _
  -- the three squared-weighted integrabilities, in the `sig`-form
  have hψsq : MeasureTheory.IntegrableOn (fun θ => ψ θ ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)) := hA
  have hX' : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)) := hX
  have hY' : MeasureTheory.IntegrableOn (fun θ => A θ ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)) := by
    refine hY.congr_fun (fun θ _ => ?_) measurableSet_Ioo
    show (Real.sin θ) ^ 2 * (deriv ψ θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ
      = (Real.sin θ * deriv ψ θ) ^ 2 * Work.FTS.EllipticEst.AngSecond.sig θ
    ring
  -- the three integrable pieces of the decomposition
  have hAA : MeasureTheory.IntegrableOn
      (fun θ => A θ * A θ * Work.FTS.EllipticEst.AngSecond.sig θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    integrable_mul_sig_of_sq_sig hA_meas hA_meas hY' hY'
  have hAu'' : MeasureTheory.IntegrableOn
      (fun θ => A θ * deriv (deriv u) θ * Work.FTS.EllipticEst.AngSecond.sig θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    integrable_mul_sig_of_sq_sig hA_meas hu''_meas hY' hX'
  have hψA : MeasureTheory.IntegrableOn
      (fun θ => ψ θ * A θ * Work.FTS.EllipticEst.AngSecond.sig θ)
      (Set.Ioo 0 (Real.pi / 2)) :=
    integrable_mul_sig_of_sq_sig hψ_meas hA_meas hψsq hY'
  have hP2 : MeasureTheory.IntegrableOn
      (fun θ => Real.cos θ * (ψ θ * A θ * Work.FTS.EllipticEst.AngSecond.sig θ))
      (Set.Ioo 0 (Real.pi / 2)) :=
    (show MeasureTheory.Integrable
        (fun θ => ψ θ * A θ * Work.FTS.EllipticEst.AngSecond.sig θ)
        (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) from hψA).bdd_mul
      (c := 1) Real.continuous_cos.aestronglyMeasurable (by
        filter_upwards with θ
        rw [Real.norm_eq_abs]
        exact Real.abs_cos_le_one θ)
  have h3 : MeasureTheory.IntegrableOn
      (fun θ => 2 * (A θ * A θ * Work.FTS.EllipticEst.AngSecond.sig θ))
      (Set.Ioo 0 (Real.pi / 2)) :=
    (show MeasureTheory.Integrable
        (fun θ => A θ * A θ * Work.FTS.EllipticEst.AngSecond.sig θ)
        (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) from hAA).const_mul 2
  -- assemble
  have hsum : MeasureTheory.IntegrableOn
      (fun θ => A θ * deriv (deriv u) θ * Work.FTS.EllipticEst.AngSecond.sig θ
        + Real.cos θ * (ψ θ * A θ * Work.FTS.EllipticEst.AngSecond.sig θ)
        + 2 * (A θ * A θ * Work.FTS.EllipticEst.AngSecond.sig θ))
      (Set.Ioo 0 (Real.pi / 2)) :=
    (hAu''.add hP2).add h3
  refine hsum.congr_fun (fun θ hθ => ?_) measurableSet_Ioo
  exact (wrho_mul_deriv_mul_deriv_divCos u
    (hu.contDiffAt (isOpen_Ioo.mem_nhds hθ)) (hcos θ hθ)).symm

end Work.FTS.EllipticEst.Honest
