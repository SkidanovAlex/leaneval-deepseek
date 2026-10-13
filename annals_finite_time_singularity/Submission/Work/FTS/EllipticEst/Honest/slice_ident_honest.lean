/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `I₄` slice identity in the honest (open-interval) class

`Work.FTS.EllipticEst.Honest.slice_ident_honest`: the `θ`-slice identity behind the term `I₄`
of Step 2 of Proposition `prop:H2` of T. M. Elgindi, *Finite-time singularity formation for
`C^{1,α}` solutions to the incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (3)
2021 (tex 895--915), in the *honest* class (smoothness only on the open interval `(0, π/2)`,
no neighbourhood of the closed interval, no pointwise boundedness of `ψ = u / cos θ`):
writing `ψ = u / cos θ` and `σ = sin(2θ)^{-η}`, `η = Work.Spaces.eta = 99/100`,

  `∫_θ sin θ · ψ'(θ) · u''(θ) · σ = ((1-η)/2)·∫_θ cos 2θ · ψ(θ)² · σ - ∫_θ A(θ)·ψ'(θ)²·σ`,

with `A(θ) = ((1-η)/2)·cos 2θ + 2 sin²θ = AngSecond.acoef θ`.

## Route

Both sides are rearrangements of the two integrations by parts in `θ` against the weight
`ρ θ = sin θ cos θ · σ θ = TanTheta.wrho η θ`, whose derivative is
`ρ' θ = (1-η) cos 2θ · σ θ = TanTheta.wrhoD η θ`
(`Work.FTS.EllipticEst.TanTheta.wrho_deriv`):

* `∫_θ ρ ψ ψ' = -(1/2) ∫_θ ρ' ψ²`   and   `∫_θ ρ ψ' ψ'' = -(1/2) ∫_θ ρ' (ψ')²`,

both instances of `integral_Ioo_mul_deriv_eq_neg_half` (`Honest/SliceSetup.lean`), the boundary
terms `ρ ψ² → 0`, `ρ (ψ')² → 0` at `θ = 0⁺`, `(π/2)⁻` being *hypotheses* of the lemma
(`hv1`--`hv4`) rather than consequences of pointwise boundedness of `ψ`; and the pointwise
chain rule `cos θ · ψ'' θ = u'' θ + cos θ · ψ θ + 2 sin θ · ψ' θ`
(`Honest.derivDeriv_divCos`, valid on the open interval because `cos θ > 0` there), which
rewrites the left-hand integrand as `ρ ψ' ψ'' - 2 sin²θ σ (ψ')² - ρ ψ ψ'`.

Everything is phrased with the explicit function `fun θ => u θ / Real.cos θ` (rather than a
`set` abbreviation) so that the `IntegrableOn` hypotheses of the lemma match the shapes used by
the integration-by-parts lemma up to beta-reduction.

Nothing here contains a `sorry`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Honest.SliceSetup
import Submission.Work.FTS.EllipticEst.Honest.derivDeriv_divCos
import Submission.Work.FTS.EllipticEst.Honest.integrableOn_wrho_mul_psiDeriv_mul_psiSecond
import Submission.Work.FTS.EllipticEst.TanTheta.integrable_mul_of_sq_weight_of_aemeasurable

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

/-! ## Elementary integrability helpers -/

/-- An integrable function on `(0, π/2)` times an a.e.-measurable function bounded by `c` is
integrable. -/
private theorem integrableOn_mul_of_bound {f g : ℝ → ℝ} {c : ℝ}
    (hf : MeasureTheory.IntegrableOn f (Set.Ioo 0 (Real.pi / 2)))
    (hg : MeasureTheory.AEStronglyMeasurable g
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))))
    (hb : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ‖g θ‖ ≤ c) :
    MeasureTheory.IntegrableOn (fun θ => f θ * g θ) (Set.Ioo 0 (Real.pi / 2)) :=
  hf.mul_bdd hg (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo hb)

/-- An integrable function on `(0, π/2)` times a continuous function bounded by `1` is
integrable. -/
private theorem integrableOn_mul_continuous_of_norm_le_one {f g : ℝ → ℝ}
    (hf : MeasureTheory.IntegrableOn f (Set.Ioo 0 (Real.pi / 2)))
    (hg : ContinuousOn g (Set.Ioo 0 (Real.pi / 2)))
    (hb : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ‖g θ‖ ≤ 1) :
    MeasureTheory.IntegrableOn (fun θ => f θ * g θ) (Set.Ioo 0 (Real.pi / 2)) :=
  integrableOn_mul_of_bound hf (hg.aemeasurable measurableSet_Ioo).aestronglyMeasurable hb

/-- The factor `(1 - η)·cos 2θ` of the derivative `wrhoD` of the integration weight is bounded
by `1` (here `η = 99/100`). -/
private theorem norm_one_sub_eta_mul_cos_two_le_one {θ : ℝ} :
    ‖(1 - Work.Spaces.eta) * Real.cos (2 * θ)‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_mul]
  have hη : |1 - Work.Spaces.eta| ≤ 1 := by
    have h : (1 : ℝ) - Work.Spaces.eta = 1 / 100 := by rw [Work.Spaces.eta]; norm_num
    rw [h]; norm_num
  have hc : |Real.cos (2 * θ)| ≤ 1 :=
    abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  calc |1 - Work.Spaces.eta| * |Real.cos (2 * θ)| ≤ 1 * 1 :=
        mul_le_mul hη hc (abs_nonneg _) (by norm_num)
    _ = 1 := by ring

/-- The cosine square factor `cos²θ` is bounded by `1`. -/
private theorem norm_cos_sq_le_one (θ : ℝ) : ‖(Real.cos θ) ^ 2‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact Real.cos_sq_le_one θ

/-! ## The integrability inputs of the two integrations by parts -/

/-- `∫_θ wrhoD η θ · ψ(θ)²` is honest, given `∫ ψ² σ`. -/
private theorem integrableOn_wrhoD_mul_divCos_sq (u : ℝ → ℝ)
    (hA : MeasureTheory.IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.TanTheta.wrhoD Work.Spaces.eta θ
      * (u θ / Real.cos θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) := by
  have hfac : ContinuousOn (fun θ : ℝ => (1 - Work.Spaces.eta) * Real.cos (2 * θ))
      (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
  have h := integrableOn_mul_continuous_of_norm_le_one hA hfac
    (fun θ _ => norm_one_sub_eta_mul_cos_two_le_one)
  refine h.congr_fun (fun θ _ => ?_) measurableSet_Ioo
  simp only [Work.FTS.EllipticEst.TanTheta.wrhoD, Work.FTS.EllipticEst.AngSecond.sig]
  ring

/-- `∫_θ wrhoD η θ · ψ'(θ)²` is honest, given `∫ (ψ')² σ`. -/
private theorem integrableOn_wrhoD_mul_deriv_divCos_sq (u : ℝ → ℝ)
    (hA' : MeasureTheory.IntegrableOn (fun θ =>
        (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.TanTheta.wrhoD Work.Spaces.eta θ
      * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hfac : ContinuousOn (fun θ : ℝ => (1 - Work.Spaces.eta) * Real.cos (2 * θ))
      (Set.Ioo 0 (Real.pi / 2)) := by fun_prop
  have h := integrableOn_mul_continuous_of_norm_le_one hA' hfac
    (fun θ _ => norm_one_sub_eta_mul_cos_two_le_one)
  refine h.congr_fun (fun θ _ => ?_) measurableSet_Ioo
  simp only [Work.FTS.EllipticEst.TanTheta.wrhoD, Work.FTS.EllipticEst.AngSecond.sig]
  ring

/-- `∫_θ cos 2θ · ψ'(θ)² · σ` is honest, given `∫ (ψ')² σ`. -/
private theorem integrableOn_cos_two_mul_deriv_divCos_sq (u : ℝ → ℝ)
    (hA' : MeasureTheory.IntegrableOn (fun θ =>
        (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun θ => Real.cos (2 * θ)
      * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)) := by
  have hfac : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) := by
    fun_prop
  have h := integrableOn_mul_continuous_of_norm_le_one hA' hfac (fun θ _ => by
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)
  refine h.congr_fun (fun θ _ => ?_) measurableSet_Ioo
  ring

/-- **`∫_θ ρ ψ ψ'` is honest**, where `ρ = wrho η`: `ψ ψ' σ` is in `L¹` by
Cauchy--Schwarz (`sin²θ (ψ')² σ` is hypothesised) and the factor `sin θ cos θ` is bounded. -/
private theorem integrableOn_wrho_mul_divCos_mul_deriv (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hY : MeasureTheory.IntegrableOn (fun θ => (Real.sin θ) ^ 2
      * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)))
    (hA : MeasureTheory.IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2))) :
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ
      * (u θ / Real.cos θ) * deriv (fun θ => u θ / Real.cos θ) θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
  have hcos_ne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos θ ≠ 0 := fun θ hθ =>
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)
  have hψcd : ContDiffOn ℝ 2 (fun θ : ℝ => u θ / Real.cos θ) (Set.Ioo 0 (Real.pi / 2)) :=
    hu.div (Real.contDiff_cos.contDiffOn.of_le le_top) hcos_ne
  have hψcont : ContinuousOn (fun θ : ℝ => u θ / Real.cos θ) (Set.Ioo 0 (Real.pi / 2)) :=
    hψcd.continuousOn
  have hψ'cont : ContinuousOn (deriv (fun θ : ℝ => u θ / Real.cos θ))
      (Set.Ioo 0 (Real.pi / 2)) :=
    hψcd.continuousOn_deriv_of_isOpen isOpen_Ioo (by norm_num)
  have hf_meas : AEMeasurable (fun θ : ℝ => Real.cos θ * (u θ / Real.cos θ))
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    (Real.continuous_cos.continuousOn.mul hψcont).aemeasurable measurableSet_Ioo
  have hg_meas : AEMeasurable (fun θ : ℝ => Real.sin θ
      * deriv (fun θ => u θ / Real.cos θ) θ)
      (MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))) :=
    (Real.continuous_sin.continuousOn.mul hψ'cont).aemeasurable measurableSet_Ioo
  have hf2 : MeasureTheory.IntegrableOn (fun θ => (Real.cos θ * (u θ / Real.cos θ)) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) (Set.Ioo 0 (Real.pi / 2)) := by
    have hfac : ContinuousOn (fun θ : ℝ => (Real.cos θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) := by
      fun_prop
    have h := integrableOn_mul_continuous_of_norm_le_one hA hfac
      (fun θ _ => norm_cos_sq_le_one θ)
    refine h.congr_fun (fun θ _ => ?_) measurableSet_Ioo
    simp only [Work.FTS.EllipticEst.AngSecond.sig]
    ring
  have hg2 : MeasureTheory.IntegrableOn (fun θ =>
      (Real.sin θ * deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) (Set.Ioo 0 (Real.pi / 2)) := by
    refine hY.congr_fun (fun θ _ => ?_) measurableSet_Ioo
    simp only [Work.FTS.EllipticEst.AngSecond.sig]
    ring
  have hAB := Work.FTS.EllipticEst.TanTheta.integrable_mul_of_sq_weight_of_aemeasurable
    Work.Spaces.eta hf_meas hg_meas hf2 hg2
  refine hAB.congr_fun (fun θ _ => ?_) measurableSet_Ioo
  simp only [Work.FTS.EllipticEst.TanTheta.wrho, Work.FTS.EllipticEst.AngSecond.sig]
  ring

/-! ## The slice identity -/

theorem slice_ident_honest (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    (hu0 : u 0 = 0) (hu1 : u (Real.pi / 2) = 0)
    (hB : MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)))
    (hX : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)))
    (hY : MeasureTheory.IntegrableOn (fun θ => (Real.sin θ) ^ 2
      * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)))
    (hA : MeasureTheory.IntegrableOn (fun θ => (u θ / Real.cos θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)))
    (hA' : MeasureTheory.IntegrableOn (fun θ => (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)))
    (hv1 : Filter.Tendsto (fun θ => Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ
        * (u θ / Real.cos θ) ^ 2) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hv2 : Filter.Tendsto (fun θ => Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ
        * (u θ / Real.cos θ) ^ 2) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    (hv3 : Filter.Tendsto (fun θ => Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ
        * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hv4 : Filter.Tendsto (fun θ => Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ
        * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) :
    (∫ θ in Set.Ioo 0 (Real.pi / 2), Real.sin θ * deriv (fun θ => u θ / Real.cos θ) θ
        * deriv (deriv u) θ * Work.FTS.EllipticEst.AngSecond.sig θ)
      = ((1 - Work.Spaces.eta) / 2) * (∫ θ in Set.Ioo 0 (Real.pi / 2),
            Real.cos (2 * θ) * (u θ / Real.cos θ) ^ 2
              * Work.FTS.EllipticEst.AngSecond.sig θ)
        - ∫ θ in Set.Ioo 0 (Real.pi / 2),
            Work.FTS.EllipticEst.AngSecond.acoef θ
              * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
              * Work.FTS.EllipticEst.AngSecond.sig θ := by
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by positivity
  have hcos_ne : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos θ ≠ 0 := fun θ hθ =>
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)
  -- ## `ψ = u / cos θ` is `C²` on the open interval, and the pointwise chain rule
  have hψcd : ContDiffOn ℝ 2 (fun θ : ℝ => u θ / Real.cos θ) (Set.Ioo 0 (Real.pi / 2)) :=
    hu.div (Real.contDiff_cos.contDiffOn.of_le le_top) hcos_ne
  have hψD : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (fun t : ℝ => u t / Real.cos t)
        (deriv (fun t => u t / Real.cos t) θ) θ := fun θ hθ =>
    ((hψcd.contDiffAt (isOpen_Ioo.mem_nhds hθ)).differentiableAt (by norm_num)).hasDerivAt
  have hψ'D : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt (deriv (fun t : ℝ => u t / Real.cos t))
        (deriv (deriv (fun t => u t / Real.cos t)) θ) θ := fun θ hθ =>
    (((hψcd.contDiffAt (isOpen_Ioo.mem_nhds hθ)).derivWithin (m := 1) (by norm_num)
      ).differentiableAt (by norm_num)).hasDerivAt
  have hchain : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Real.cos θ * deriv (deriv (fun t : ℝ => u t / Real.cos t)) θ
        = deriv (deriv u) θ + Real.cos θ * (u θ / Real.cos θ)
          + 2 * Real.sin θ * deriv (fun t => u t / Real.cos t) θ := fun θ hθ =>
    cos_mul_derivDeriv_divCos u (hu.contDiffAt (isOpen_Ioo.mem_nhds hθ)) (hcos_ne θ hθ)
  -- ## the integrability inputs of the two integrations by parts
  have hintA : MeasureTheory.IntegrableOn (fun θ =>
      Work.FTS.EllipticEst.TanTheta.wrhoD Work.Spaces.eta θ * (u θ / Real.cos θ) ^ 2)
      (Set.Ioo 0 (Real.pi / 2)) := integrableOn_wrhoD_mul_divCos_sq u hA
  have hintA' : MeasureTheory.IntegrableOn (fun θ =>
      Work.FTS.EllipticEst.TanTheta.wrhoD Work.Spaces.eta θ
        * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) :=
    integrableOn_wrhoD_mul_deriv_divCos_sq u hA'
  have hintJ1 : MeasureTheory.IntegrableOn (fun θ => Real.cos (2 * θ)
      * (deriv (fun θ => u θ / Real.cos θ) θ) ^ 2
      * Work.FTS.EllipticEst.AngSecond.sig θ) (Set.Ioo 0 (Real.pi / 2)) :=
    integrableOn_cos_two_mul_deriv_divCos_sq u hA'
  have hintP3 : MeasureTheory.IntegrableOn (fun θ =>
      Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ * (u θ / Real.cos θ)
        * deriv (fun θ => u θ / Real.cos θ) θ) (Set.Ioo 0 (Real.pi / 2)) :=
    integrableOn_wrho_mul_divCos_mul_deriv u hu hY hA
  have hintP2 : MeasureTheory.IntegrableOn (fun θ =>
      Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ
        * deriv (fun θ => u θ / Real.cos θ) θ
        * deriv (deriv (fun θ => u θ / Real.cos θ)) θ) (Set.Ioo 0 (Real.pi / 2)) :=
    integrableOn_wrho_mul_psiDeriv_mul_psiSecond u hu hX hY hA
  -- ## the two integrations by parts
  have hP1 := integral_Ioo_mul_deriv_eq_neg_half (a := (0 : ℝ)) (b := Real.pi / 2) hpi2
    (ρ := Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta)
    (ρ' := Work.FTS.EllipticEst.TanTheta.wrhoD Work.Spaces.eta)
    (f := fun t : ℝ => u t / Real.cos t)
    (f' := fun t : ℝ => deriv (fun s => u s / Real.cos s) t)
    (fun θ hθ => Work.FTS.EllipticEst.TanTheta.wrho_deriv Work.Spaces.eta hθ)
    hψD hintA hintP3 hv1 hv2
  have hP2 := integral_Ioo_mul_deriv_eq_neg_half (a := (0 : ℝ)) (b := Real.pi / 2) hpi2
    (ρ := Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta)
    (ρ' := Work.FTS.EllipticEst.TanTheta.wrhoD Work.Spaces.eta)
    (f := fun t : ℝ => deriv (fun s => u s / Real.cos s) t)
    (f' := fun t : ℝ => deriv (deriv (fun s => u s / Real.cos s)) t)
    (fun θ hθ => Work.FTS.EllipticEst.TanTheta.wrho_deriv Work.Spaces.eta hθ)
    hψ'D hintA' hintP2 hv3 hv4
  have hP1r : (∫ x in Set.Ioo 0 (Real.pi / 2),
        Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta x * (u x / Real.cos x)
          * deriv (fun t : ℝ => u t / Real.cos t) x)
      = -(1 / 2) * (∫ x in Set.Ioo 0 (Real.pi / 2),
          Work.FTS.EllipticEst.TanTheta.wrhoD Work.Spaces.eta x * (u x / Real.cos x) ^ 2) := by
    simpa only [] using hP1
  have hP2r : (∫ x in Set.Ioo 0 (Real.pi / 2),
        Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta x
          * deriv (fun t : ℝ => u t / Real.cos t) x
          * deriv (deriv (fun t : ℝ => u t / Real.cos t)) x)
      = -(1 / 2) * (∫ x in Set.Ioo 0 (Real.pi / 2),
          Work.FTS.EllipticEst.TanTheta.wrhoD Work.Spaces.eta x
            * (deriv (fun t : ℝ => u t / Real.cos t) x) ^ 2) := by
    simpa only [] using hP2
  -- ## the two derived integrals, in terms of `cos 2θ · ψ² · σ`
  have hP1c : (∫ x in Set.Ioo 0 (Real.pi / 2),
        Work.FTS.EllipticEst.TanTheta.wrhoD Work.Spaces.eta x * (u x / Real.cos x) ^ 2)
      = (1 - Work.Spaces.eta) * (∫ θ in Set.Ioo 0 (Real.pi / 2),
          Real.cos (2 * θ) * (u θ / Real.cos θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ) := by
    rw [show (∫ x in Set.Ioo 0 (Real.pi / 2),
          Work.FTS.EllipticEst.TanTheta.wrhoD Work.Spaces.eta x * (u x / Real.cos x) ^ 2)
        = ∫ x in Set.Ioo 0 (Real.pi / 2), (1 - Work.Spaces.eta)
            * (Real.cos (2 * x) * (u x / Real.cos x) ^ 2
              * Work.FTS.EllipticEst.AngSecond.sig x) from
      setIntegral_congr_fun measurableSet_Ioo (fun θ _ => by
        simp only [Work.FTS.EllipticEst.TanTheta.wrhoD, Work.FTS.EllipticEst.AngSecond.sig]
        ring)]
    rw [integral_const_mul]
  have hP2c : (∫ x in Set.Ioo 0 (Real.pi / 2),
        Work.FTS.EllipticEst.TanTheta.wrhoD Work.Spaces.eta x
          * (deriv (fun t : ℝ => u t / Real.cos t) x) ^ 2)
      = (1 - Work.Spaces.eta) * (∫ θ in Set.Ioo 0 (Real.pi / 2),
          Real.cos (2 * θ) * (deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ) := by
    rw [show (∫ x in Set.Ioo 0 (Real.pi / 2),
          Work.FTS.EllipticEst.TanTheta.wrhoD Work.Spaces.eta x
            * (deriv (fun t : ℝ => u t / Real.cos t) x) ^ 2)
        = ∫ x in Set.Ioo 0 (Real.pi / 2), (1 - Work.Spaces.eta)
            * (Real.cos (2 * x) * (deriv (fun t : ℝ => u t / Real.cos t) x) ^ 2
              * Work.FTS.EllipticEst.AngSecond.sig x) from
      setIntegral_congr_fun measurableSet_Ioo (fun θ _ => by
        simp only [Work.FTS.EllipticEst.TanTheta.wrhoD, Work.FTS.EllipticEst.AngSecond.sig]
        ring)]
    rw [integral_const_mul]
  -- ## the left-hand integrand, rewritten
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Real.sin θ * deriv (fun t : ℝ => u t / Real.cos t) θ * deriv (deriv u) θ
        * Work.FTS.EllipticEst.AngSecond.sig θ
      = Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ
            * deriv (fun t : ℝ => u t / Real.cos t) θ
            * deriv (deriv (fun t : ℝ => u t / Real.cos t)) θ
        - (2 * ((Real.sin θ) ^ 2 * (deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ)
          + Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ * (u θ / Real.cos θ)
            * deriv (fun t : ℝ => u t / Real.cos t) θ) := by
    intro θ hθ
    have h := hchain θ hθ
    have huu : deriv (deriv u) θ
        = Real.cos θ * deriv (deriv (fun t : ℝ => u t / Real.cos t)) θ
          - Real.cos θ * (u θ / Real.cos θ)
          - 2 * Real.sin θ * deriv (fun t : ℝ => u t / Real.cos t) θ := by linarith [h]
    rw [huu]
    simp only [Work.FTS.EllipticEst.TanTheta.wrho, Work.FTS.EllipticEst.AngSecond.sig]
    ring
  have hY2C : MeasureTheory.IntegrableOn (fun θ => 2 * ((Real.sin θ) ^ 2
        * (deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ)
      + Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ * (u θ / Real.cos θ)
        * deriv (fun t : ℝ => u t / Real.cos t) θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (hY.const_mul 2).add hintP3
  have hLHS : (∫ θ in Set.Ioo 0 (Real.pi / 2), Real.sin θ
        * deriv (fun t : ℝ => u t / Real.cos t) θ * deriv (deriv u) θ
        * Work.FTS.EllipticEst.AngSecond.sig θ)
      = (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ
            * deriv (fun t : ℝ => u t / Real.cos t) θ
            * deriv (deriv (fun t : ℝ => u t / Real.cos t)) θ)
        - (2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Real.sin θ) ^ 2
            * (deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ)
          + ∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.TanTheta.wrho Work.Spaces.eta θ
            * (u θ / Real.cos θ) * deriv (fun t : ℝ => u t / Real.cos t) θ) := by
    rw [setIntegral_congr_fun measurableSet_Ioo hpt]
    rw [integral_sub hintP2 hY2C]
    rw [integral_add (hY.const_mul 2) hintP3, integral_const_mul]
  -- ## the `acoef`-integral, split along `acoef θ = ((1-η)/2) cos 2θ + 2 sin²θ`
  have hpt2 : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.AngSecond.acoef θ
          * (deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2
          * Work.FTS.EllipticEst.AngSecond.sig θ
      = ((1 - Work.Spaces.eta) / 2) * (Real.cos (2 * θ)
            * (deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ)
        + 2 * ((Real.sin θ) ^ 2 * (deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ) := by
    intro θ _
    simp only [Work.FTS.EllipticEst.AngSecond.acoef]
    ring
  have hacoef : (∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.AngSecond.acoef θ
        * (deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2
        * Work.FTS.EllipticEst.AngSecond.sig θ)
      = ((1 - Work.Spaces.eta) / 2) * (∫ θ in Set.Ioo 0 (Real.pi / 2), Real.cos (2 * θ)
            * (deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ)
        + 2 * (∫ θ in Set.Ioo 0 (Real.pi / 2), (Real.sin θ) ^ 2
            * (deriv (fun t : ℝ => u t / Real.cos t) θ) ^ 2
            * Work.FTS.EllipticEst.AngSecond.sig θ) := by
    rw [setIntegral_congr_fun measurableSet_Ioo hpt2]
    rw [integral_add (hintJ1.const_mul ((1 - Work.Spaces.eta) / 2)) (hY.const_mul 2),
      integral_const_mul, integral_const_mul]
  -- ## assemble
  rw [hLHS, hP2r, hP2c, hP1r, hP1c, hacoef]
  ring

end Work.FTS.EllipticEst.Honest
