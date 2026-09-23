import Submission.BonnetMyers
import Submission.Commons.Analysis.Calculus.hasDerivAt_deriv_integral_of_continuousOn_Icc_prod
import Submission.Commons.Analysis.Calculus.hasDerivAt_integral_of_continuousOn_Icc_prod
import Submission.SecondVar2

/-!
# The second variation of the energy for a coordinate family by geodesics

This file contains the **classical second-variation formula of Riemannian geometry**, in one chart,
for a family whose `σ`-curves are geodesics:

`E''(0) = -2 ∫₀^L ( ⟪∇_tη,∇_tη⟫ - ⟪R(η,γ')γ',η⟫ )`,  `E(σ) = ∫₀^L ⟨∂_tψ(σ,·),∂_tψ(σ,·)⟩`,

together with the first variation `E'(0) = 2(⟪η(L),γ'(L)⟫ - ⟪η(0),γ'(0)⟫)`.

The proof is organised as follows.

* `nabS`, `dnabS`, `nabS2` are the coordinate expressions of `∇_s∂_tψ`, `∂_s(∇_s∂_tψ)` and
  `∇_s∇_s∂_tψ` for a coordinate family `ψ`, and `nabV`, `nabV2`, `jetS2`, `idxV` their point forms.
* `hasDerivAt_chartGram_fam_s` and `hasDerivAt_chartGram_fam_s2` are the two applications of the
  product rule `hasDerivAt_chartGram_curve` in the `σ`-direction, and `hasDerivAt_nabS` is the chain
  rule for the Christoffel term (`hasDerivAt_chrB_curve`); together they give
  **`hasDerivAt_deriv_chartGram_fam`**: the pointwise second `σ`-derivative of the metric integrand
  is the explicit jet expression `jetS2` (the *jet lemma*: it shows that the second derivative
  depends only on the `σ = 0` jet data `(ψ, ∂_tψ, ∂_σψ, ∂_σ²ψ, ∂_σ∂_tψ, ∂_σ²∂_tψ)`).
* `nabV2_eq_chartCurvV` identifies `∇_s∇_s∂_tψ` with the chart curvature term when the `σ`-curves are
  geodesics, and `jetS2_eq_idxV` turns the pointwise formula into the index integrand.
* The passage from the pointwise identity to the integral is the commons lemma
  `Commons.Analysis.Calculus.hasDerivAt_deriv_integral_of_continuousOn_Icc_prod`
  (and `..._integral_...` for the first variation).

**Note** that the classical formula holds for *any* family whose `σ`-curves are geodesics: the base
curve `γ = ψ(0,·)` need not be a geodesic (that hypothesis is only needed for the *vanishing* of the
first variation).  This is what makes the global (finite atlas) case accessible: the energy is
additive over a partition of `[0,L]` and the theorem applies on each chart piece separately.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory
open Submission.Geodesic
open Submission.ChartConnection
open Submission.ChartCurv
open Submission.SecondVariation
open Submission.CurvatureVec
open Submission.SecondVar2
open Submission.BonnetMyers
open Submission.Gauss

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [I.Boundaryless]

namespace Submission.SecondVarGeo

noncomputable section

variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}

/-- `∇_s h = ∂_s h + Γ(h, ∂_s ψ)`: the covariant derivative in the `s`-direction of a coordinate
field `h` along the coordinate family `ψ`, where `dh = ∂_s h` and `dv = ∂_s ψ`. -/
noncomputable def nabS (x₀ : M) (ψ h dh dv : ℝ → ℝ → E) (s t : ℝ) : E :=
  dh s t + chrB cov x₀ ((extChartAt I x₀).symm (ψ s t)) (h s t) (dv s t)

/-- **The first `s`-derivative of the chart metric integrand** of a coordinate family:
`d/dσ ⟨∂_tψ, ∂_tψ⟩ = 2 ⟨∇_s ∂_tψ, ∂_tψ⟩`. -/
theorem hasDerivAt_chartGram_fam_s (hmet : IsMetricCompatible cov) (x₀ : M)
    {ψ w v e : ℝ → ℝ → E} {s t : ℝ}
    (hψ : HasDerivAt (fun σ => ψ σ t) (v s t) s)
    (hw : HasDerivAt (fun σ => w σ t) (e s t) s)
    (htgt : ψ s t ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ σ in 𝓝 s, ψ σ t ∈ (extChartAt I x₀).target) :
    HasDerivAt (fun σ => chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ σ t)) (w σ t) (w σ t))
      (2 * chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ s t))
        (nabS (cov := cov) x₀ ψ w e v s t) (w s t)) s := by
  have h := hasDerivAt_chartGram_curve (cov := cov) (hmet := hmet) (x₀ := x₀)
    (u := fun σ => ψ σ t) (v := v s t) (t := s) hψ htgt hstay
    (h₁ := fun σ => w σ t) (h₂ := fun σ => w σ t) (h₁' := e s t) (h₂' := e s t) hw hw
  have hval : chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ s t))
        (e s t + christoffelEval cov x₀ ((extChartAt I x₀).symm (ψ s t)) (w s t)
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (ψ s t)) (v s t))) (w s t)
      + chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ s t)) (w s t)
        (e s t + christoffelEval cov x₀ ((extChartAt I x₀).symm (ψ s t)) (w s t)
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (ψ s t)) (v s t)))
      = 2 * chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ s t))
        (nabS (cov := cov) x₀ ψ w e v s t) (w s t) := by
    rw [show christoffelEval cov x₀ ((extChartAt I x₀).symm (ψ s t)) (w s t)
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (ψ s t)) (v s t))
        = chrB cov x₀ ((extChartAt I x₀).symm (ψ s t)) (w s t) (v s t) from rfl]
    simp only [nabS]
    rw [chartGram_comm (I := I) x₀ ((extChartAt I x₀).symm (ψ s t))
      (w s t) (e s t + chrB cov x₀ ((extChartAt I x₀).symm (ψ s t)) (w s t) (v s t))]
    ring
  exact h.congr_deriv hval

/-- **The `s`-derivative of `⟨W, ∂_tψ⟩`** for a coordinate field `W` along the family. -/
theorem hasDerivAt_chartGram_fam_s2 (hmet : IsMetricCompatible cov) (x₀ : M)
    {ψ w v W dW e : ℝ → ℝ → E} {s t : ℝ}
    (hψ : HasDerivAt (fun σ => ψ σ t) (v s t) s)
    (hW : HasDerivAt (fun σ => W σ t) (dW s t) s)
    (hw : HasDerivAt (fun σ => w σ t) (e s t) s)
    (htgt : ψ s t ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ σ in 𝓝 s, ψ σ t ∈ (extChartAt I x₀).target) :
    HasDerivAt (fun σ => chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ σ t)) (W σ t) (w σ t))
      (chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ s t))
          (nabS (cov := cov) x₀ ψ W dW v s t) (w s t)
        + chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ s t)) (W s t)
          (nabS (cov := cov) x₀ ψ w e v s t)) s := by
  have h := hasDerivAt_chartGram_curve (cov := cov) (hmet := hmet) (x₀ := x₀)
    (u := fun σ => ψ σ t) (v := v s t) (t := s) hψ htgt hstay
    (h₁ := fun σ => W σ t) (h₂ := fun σ => w σ t) (h₁' := dW s t) (h₂' := e s t) hW hw
  exact h.congr_deriv (by
    simp only [nabS]
    rw [show christoffelEval cov x₀ ((extChartAt I x₀).symm (ψ s t)) (W s t)
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (ψ s t)) (v s t))
        = chrB cov x₀ ((extChartAt I x₀).symm (ψ s t)) (W s t) (v s t) from rfl,
      show christoffelEval cov x₀ ((extChartAt I x₀).symm (ψ s t)) (w s t)
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (ψ s t)) (v s t))
        = chrB cov x₀ ((extChartAt I x₀).symm (ψ s t)) (w s t) (v s t) from rfl])

/-- **The chain rule for the Christoffel term in `∇_s`**: the `s`-derivative of
`σ ↦ ∂_s h(σ,t) + Γ(ψ(σ,t); h(σ,t), ∂_sψ(σ,t))`. -/
theorem hasDerivAt_nabS [ContMDiffCovariantDerivative cov ∞] (x₀ : M)
    {ψ w v a e ea : ℝ → ℝ → E} {s t : ℝ}
    (hψ : HasDerivAt (fun σ => ψ σ t) (v s t) s)
    (hv : HasDerivAt (fun σ => v σ t) (a s t) s)
    (hw : HasDerivAt (fun σ => w σ t) (e s t) s)
    (he : HasDerivAt (fun σ => e σ t) (ea s t) s)
    (htgt : ψ s t ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ σ in 𝓝 s, ψ σ t ∈ (extChartAt I x₀).target) :
    HasDerivAt (fun σ => nabS (cov := cov) x₀ ψ w e v σ t)
      (ea s t + dB cov x₀ ((extChartAt I x₀).symm (ψ s t)) (v s t) (w s t) (v s t)
        + chrB cov x₀ ((extChartAt I x₀).symm (ψ s t)) (e s t) (v s t)
        + chrB cov x₀ ((extChartAt I x₀).symm (ψ s t)) (w s t) (a s t)) s := by
  have h := hasDerivAt_chrB_curve (cov := cov) (x₀ := x₀) (u := fun σ => ψ σ t) (a := fun σ => w σ t)
    (b := fun σ => v σ t) (v := v s t) (a' := e s t) (b' := a s t) (t := s) hψ hw hv htgt hstay
  have h2 := he.add h
  have hfun : (fun σ => nabS (cov := cov) x₀ ψ w e v σ t)
      = ((fun σ => e σ t) + fun σ => chrB cov x₀ ((extChartAt I x₀).symm (ψ σ t))
          (w σ t) (v σ t)) := by
    funext σ
    rfl
  rw [hfun]
  exact h2.congr_deriv (by abel)

/-- The `s`-derivative of `∇_s ∂_tψ` as a coordinate expression. -/
noncomputable def dnabS (x₀ : M) (ψ w v a e ea : ℝ → ℝ → E) (s t : ℝ) : E :=
  ea s t + dB cov x₀ ((extChartAt I x₀).symm (ψ s t)) (v s t) (w s t) (v s t)
    + chrB cov x₀ ((extChartAt I x₀).symm (ψ s t)) (e s t) (v s t)
    + chrB cov x₀ ((extChartAt I x₀).symm (ψ s t)) (w s t) (a s t)

/-- `∇_s∇_s ∂_tψ` as a coordinate expression. -/
noncomputable def nabS2 (x₀ : M) (ψ w v a e ea : ℝ → ℝ → E) (s t : ℝ) : E :=
  dnabS (cov := cov) x₀ ψ w v a e ea s t
    + chrB cov x₀ ((extChartAt I x₀).symm (ψ s t)) (nabS (cov := cov) x₀ ψ w e v s t) (v s t)

/-- The value form of `∇_s ∂_tψ` at a point. -/
noncomputable def nabV (x₀ : M) (p w v e : E) : E :=
  e + chrB cov x₀ ((extChartAt I x₀).symm p) w v

/-- The value form of `∇_s∇_s ∂_tψ` at a point. -/
noncomputable def nabV2 (x₀ : M) (p w v a e ea : E) : E :=
  ea + dB cov x₀ ((extChartAt I x₀).symm p) v w v
    + chrB cov x₀ ((extChartAt I x₀).symm p) e v
    + chrB cov x₀ ((extChartAt I x₀).symm p) w a
    + chrB cov x₀ ((extChartAt I x₀).symm p) (nabV (cov := cov) x₀ p w v e) v

/-- **The pointwise second `s`-derivative of the chart metric integrand**, as a function of the
`s = 0` jet data: `p = ψ(0,t)`, `w = ∂_tψ`, `v = ∂_sψ`, `a = ∂_s²ψ`, `e = ∂_s∂_tψ` and
`ea = ∂_s²∂_tψ`.  This is the quantity that the second-variation formula integrates. -/
noncomputable def jetS2 (x₀ : M) (p w v a e ea : E) : ℝ :=
  2 * (chartGram (I := I) x₀ ((extChartAt I x₀).symm p) (nabV2 (cov := cov) x₀ p w v a e ea) w
      + chartGram (I := I) x₀ ((extChartAt I x₀).symm p) (nabV (cov := cov) x₀ p w v e)
          (nabV (cov := cov) x₀ p w v e))

/-- **The second `s`-derivative of the chart metric integrand** of a coordinate family, in terms of
the jet data at the base point. -/
theorem hasDerivAt_deriv_chartGram_fam [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (x₀ : M)
    {ψ w v a e ea : ℝ → ℝ → E} {s t : ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hψ : ∀ σ ∈ Ioo (s - δ) (s + δ), HasDerivAt (fun σ' => ψ σ' t) (v σ t) σ)
    (hv : ∀ σ ∈ Ioo (s - δ) (s + δ), HasDerivAt (fun σ' => v σ' t) (a σ t) σ)
    (hw : ∀ σ ∈ Ioo (s - δ) (s + δ), HasDerivAt (fun σ' => w σ' t) (e σ t) σ)
    (he : ∀ σ ∈ Ioo (s - δ) (s + δ), HasDerivAt (fun σ' => e σ' t) (ea σ t) σ)
    (htgt : ∀ σ ∈ Ioo (s - δ) (s + δ), ψ σ t ∈ (extChartAt I x₀).target) :
    HasDerivAt (deriv (fun σ => chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ σ t))
        (w σ t) (w σ t)))
      (jetS2 (cov := cov) x₀ (ψ s t) (w s t) (v s t) (a s t) (e s t) (ea s t)) s := by
  have hs : s ∈ Ioo (s - δ) (s + δ) := ⟨by linarith, by linarith⟩
  have hstay : ∀ σ ∈ Ioo (s - δ) (s + δ), ∀ᶠ σ' in 𝓝 σ, ψ σ' t ∈ (extChartAt I x₀).target :=
    fun σ hσ => (hψ σ hσ).continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_target x₀).mem_nhds (htgt σ hσ))
  have h1 : ∀ σ ∈ Ioo (s - δ) (s + δ), HasDerivAt (fun σ' => chartGram (I := I) x₀
      ((extChartAt I x₀).symm (ψ σ' t)) (w σ' t) (w σ' t))
      (2 * chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ σ t))
        (nabS (cov := cov) x₀ ψ w e v σ t) (w σ t)) σ := fun σ hσ =>
    hasDerivAt_chartGram_fam_s (cov := cov) hmet x₀ (hψ σ hσ) (hw σ hσ) (htgt σ hσ) (hstay σ hσ)
  have hev : deriv (fun σ => chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ σ t))
        (w σ t) (w σ t))
      =ᶠ[𝓝 s] (fun σ => 2 * chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ σ t))
        (nabS (cov := cov) x₀ ψ w e v σ t) (w σ t)) :=
    Filter.eventuallyEq_of_mem (Ioo_mem_nhds (by linarith : s - δ < s) (by linarith : s < s + δ))
      (fun σ hσ => (h1 σ hσ).deriv)
  have hW : HasDerivAt (fun σ => nabS (cov := cov) x₀ ψ w e v σ t)
      (dnabS (cov := cov) x₀ ψ w v a e ea s t) s :=
    hasDerivAt_nabS (cov := cov) (x₀ := x₀) (hψ s hs) (hv s hs) (hw s hs) (he s hs)
      (htgt s hs) (hstay s hs)
  have h2a := hasDerivAt_chartGram_fam_s2 (cov := cov) hmet x₀
    (ψ := ψ) (w := w) (v := v) (W := fun σ _ => nabS (cov := cov) x₀ ψ w e v σ t)
    (dW := fun σ _ => dnabS (cov := cov) x₀ ψ w v a e ea σ t) (e := e) (s := s) (t := t)
    (hψ s hs) hW (hw s hs) (htgt s hs) (hstay s hs)
  have h2a' : HasDerivAt (fun σ => chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ σ t))
      (nabS (cov := cov) x₀ ψ w e v σ t) (w σ t))
      (chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ s t))
          (nabS2 (cov := cov) x₀ ψ w v a e ea s t) (w s t)
        + chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ s t))
          (nabS (cov := cov) x₀ ψ w e v s t) (nabS (cov := cov) x₀ ψ w e v s t)) s :=
    h2a.congr_deriv (by simp only [nabS2, nabS, dnabS])
  have h2 := h2a'.const_mul 2
  refine (h2.congr_of_eventuallyEq hev).congr_deriv ?_
  simp only [jetS2, nabV2, nabV, nabS2, nabS, dnabS]

/-- The chart curvature expression appearing as `∇_s∇_s ∂_tψ` on a variation by `s`-geodesics. -/
noncomputable def chartCurvV (x₀ : M) (p v w : E) : E :=
  dB cov x₀ ((extChartAt I x₀).symm p) v v w
    - dB cov x₀ ((extChartAt I x₀).symm p) w v v
    + chrB cov x₀ ((extChartAt I x₀).symm p) (chrB cov x₀ ((extChartAt I x₀).symm p) v w) v
    - chrB cov x₀ ((extChartAt I x₀).symm p) (chrB cov x₀ ((extChartAt I x₀).symm p) v v) w

/-- **`∇_s∇_s∂_tψ` on a variation by `s`-geodesics is the curvature term**: under the two relations
`∂_s²ψ = -Γ(∂_sψ,∂_sψ)` (the `s`-curves are geodesics) and its `t`-derivative
`∂_s²∂_tψ = -∂_tΓ(∂_sψ,∂_sψ)`, the second `s`-covariant derivative of the velocity equals the chart
curvature expression `R(∂_sψ, ∂_tψ)∂_sψ`. -/
theorem nabV2_eq_chartCurvV [ContMDiffCovariantDerivative cov ∞] (htor : cov.torsion = 0)
    (x₀ : M) {p w v a e ea : E} (hsrc : (extChartAt I x₀).symm p ∈ (chartAt H x₀).source)
    (hgeo : a = -chrB cov x₀ ((extChartAt I x₀).symm p) v v)
    (hgeo' : ea = -(dB cov x₀ ((extChartAt I x₀).symm p) w v v
      + chrB cov x₀ ((extChartAt I x₀).symm p) e v
      + chrB cov x₀ ((extChartAt I x₀).symm p) v e)) :
    nabV2 (cov := cov) x₀ p w v a e ea = chartCurvV (cov := cov) x₀ p v w := by
  have hcn : chrB cov x₀ ((extChartAt I x₀).symm p) w
      (-chrB cov x₀ ((extChartAt I x₀).symm p) v v)
      = -chrB cov x₀ ((extChartAt I x₀).symm p) w
          (chrB cov x₀ ((extChartAt I x₀).symm p) v v) := by
    rw [← neg_one_smul ℝ (chrB cov x₀ ((extChartAt I x₀).symm p) v v), chrB_smul_snd,
      neg_one_smul]
  simp only [nabV2, nabV, chartCurvV, hgeo, hgeo']
  rw [hcn, neg_add, neg_add,
    chrB_add_fst (cov := cov) x₀ ((extChartAt I x₀).symm p) e
      (chrB cov x₀ ((extChartAt I x₀).symm p) w v) v hsrc,
    chrB_comm (cov := cov) htor hsrc v e, dB_comm_snd (cov := cov) htor hsrc v w v,
    chrB_comm (cov := cov) htor hsrc w v,
    chrB_comm (cov := cov) htor hsrc w (chrB cov x₀ ((extChartAt I x₀).symm p) v v)]
  abel

/-- The value form of the index integrand `⟨∇_tV,∇_tV⟩ - ⟨R(V,γ')γ',V⟩` at a point. -/
noncomputable def idxV (x₀ : M) (p w v z : E) : ℝ :=
  inner ℝ (frameVector (I := I) x₀ ((extChartAt I x₀).symm p) v)
      (curvVec cov ((extChartAt I x₀).symm p)
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm p) v)
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm p) w)
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm p) w))
    - chartGram (I := I) x₀ ((extChartAt I x₀).symm p) z z

/-- **The pointwise second `s`-derivative of the chart metric integrand is (minus) the index
integrand**, for a variation whose `s`-curves are geodesics: this is the classical second-variation
formula `E''(0) = 2∫(‖∇_tV‖² - ⟨R(V,γ')γ',V⟩)` at the level of integrands. -/
theorem jetS2_eq_idxV [ContMDiffCovariantDerivative cov ∞] (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) (x₀ : M) {p w v a e ea : E}
    (hsrc : (extChartAt I x₀).symm p ∈ (chartAt H x₀).source)
    (hgeo : a = -chrB cov x₀ ((extChartAt I x₀).symm p) v v)
    (hgeo' : ea = -(dB cov x₀ ((extChartAt I x₀).symm p) w v v
      + chrB cov x₀ ((extChartAt I x₀).symm p) e v
      + chrB cov x₀ ((extChartAt I x₀).symm p) v e)) :
    jetS2 (cov := cov) x₀ p w v a e ea
      = -2 * idxV (cov := cov) x₀ p w v (nabV (cov := cov) x₀ p w v e) := by
  have hχ : nabV2 (cov := cov) x₀ p w v a e ea = chartCurvV (cov := cov) x₀ p v w :=
    nabV2_eq_chartCurvV (cov := cov) htor x₀ hsrc hgeo hgeo'
  have hcv : curvVec cov ((extChartAt I x₀).symm p)
      (frameVector (I := I) x₀ ((extChartAt I x₀).symm p) v)
      (frameVector (I := I) x₀ ((extChartAt I x₀).symm p) w)
      (frameVector (I := I) x₀ ((extChartAt I x₀).symm p) v)
      = frameVector (I := I) x₀ ((extChartAt I x₀).symm p)
          (chartCurvV (cov := cov) x₀ p v w) :=
    curvVec_eq_chart (cov := cov) htor x₀ ((extChartAt I x₀).symm p) v w v hsrc
  have hsk : chartGram (I := I) x₀ ((extChartAt I x₀).symm p)
        (chartCurvV (cov := cov) x₀ p v w) w
      = - inner ℝ (frameVector (I := I) x₀ ((extChartAt I x₀).symm p) v)
          (curvVec cov ((extChartAt I x₀).symm p)
            (frameVector (I := I) x₀ ((extChartAt I x₀).symm p) v)
            (frameVector (I := I) x₀ ((extChartAt I x₀).symm p) w)
            (frameVector (I := I) x₀ ((extChartAt I x₀).symm p) w)) := by
    rw [chartGram_apply, ← hcv,
      inner_curvVec_skew (cov := cov) ‹ContMDiffCovariantDerivative cov ∞› hmet
        ((extChartAt I x₀).symm p)
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm p) v)
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm p) w)
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm p) v)
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm p) w)]
  simp only [jetS2, idxV, nabV, hχ, hsk]
  ring

/-- **The second variation of the energy, in one chart.**  For a coordinate family `ψ` whose
`s`-curves are geodesics (`hgeo` is the chart geodesic equation and `hgeo'` its `t`-derivative), the
energy `E(σ) = ∫₀^L ⟨∂_tψ(σ,·),∂_tψ(σ,·)⟩` of the family satisfies the classical second-variation
formula

`E''(0) = -2 ∫₀^L ( ⟪∇_tη,∇_tη⟫ - ⟪R(η,γ')γ',η⟫ ) = -2 ∫₀^L indexIntegrand`,

where `η = ∂_σψ(0,·)` is the variation field and `γ' = ∂_tψ(0,·)`. -/
theorem energy_second_deriv_chart [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (x₀ : M)
    {ψ w v a e ea : ℝ → ℝ → E} {L : ℝ} (hL : 0 < L) {δ : ℝ} (hδ : 0 < δ)
    (hψt : ∀ σ ∈ Ioo (-δ) δ, ∀ t ∈ Icc 0 L, HasDerivAt (fun t' => ψ σ t') (w σ t) t)
    (hψs : ∀ σ ∈ Ioo (-δ) δ, ∀ t ∈ Icc 0 L, HasDerivAt (fun σ' => ψ σ' t) (v σ t) σ)
    (hvs : ∀ σ ∈ Ioo (-δ) δ, ∀ t ∈ Icc 0 L, HasDerivAt (fun σ' => v σ' t) (a σ t) σ)
    (hws : ∀ σ ∈ Ioo (-δ) δ, ∀ t ∈ Icc 0 L, HasDerivAt (fun σ' => w σ' t) (e σ t) σ)
    (hes : ∀ σ ∈ Ioo (-δ) δ, ∀ t ∈ Icc 0 L, HasDerivAt (fun σ' => e σ' t) (ea σ t) σ)
    (htgt : ∀ σ ∈ Icc (-δ) δ, ∀ t ∈ Icc 0 L, ψ σ t ∈ (extChartAt I x₀).target)
    (hgeo : ∀ t ∈ Icc 0 L,
      a 0 t = -chrB cov x₀ ((extChartAt I x₀).symm (ψ 0 t)) (v 0 t) (v 0 t))
    (hgeo' : ∀ t ∈ Icc 0 L, ea 0 t
      = -(dB cov x₀ ((extChartAt I x₀).symm (ψ 0 t)) (w 0 t) (v 0 t) (v 0 t)
        + chrB cov x₀ ((extChartAt I x₀).symm (ψ 0 t)) (e 0 t) (v 0 t)
        + chrB cov x₀ ((extChartAt I x₀).symm (ψ 0 t)) (v 0 t) (e 0 t)))
    (hg : ContinuousOn (fun p : ℝ × ℝ =>
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ p.1 p.2)) (w p.1 p.2) (w p.1 p.2))
      (Icc (-δ) δ ×ˢ Icc 0 L))
    (hg' : ContinuousOn (fun p : ℝ × ℝ =>
      2 * chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ p.1 p.2))
        (nabS (cov := cov) x₀ ψ w e v p.1 p.2) (w p.1 p.2)) (Icc (-δ) δ ×ˢ Icc 0 L))
    (hg'' : ContinuousOn (fun p : ℝ × ℝ =>
      jetS2 (cov := cov) x₀ (ψ p.1 p.2) (w p.1 p.2) (v p.1 p.2) (a p.1 p.2) (e p.1 p.2)
        (ea p.1 p.2)) (Icc (-δ) δ ×ˢ Icc 0 L)) :
    HasDerivAt (deriv (fun σ : ℝ => ∫ t in (0 : ℝ)..L,
        chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ σ t)) (w σ t) (w σ t)))
      (-2 * ∫ t in (0 : ℝ)..L, indexIntegrand cov x₀ (fun t => ψ 0 t) (fun t => v 0 t)
        (fun t => w 0 t) (fun t => e 0 t) t) 0 := by
  have hmem0 : (0 : ℝ) ∈ Icc (-δ) δ := ⟨by linarith, hδ.le⟩
  have hmem0' : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have hderiv : ∀ σ ∈ Ioo (-δ) δ, ∀ t ∈ Icc 0 L,
      HasDerivAt (fun σ' => chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ σ' t))
          (w σ' t) (w σ' t))
        (2 * chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ σ t))
          (nabS (cov := cov) x₀ ψ w e v σ t) (w σ t)) σ := by
    intro σ hσ t ht
    have hstay : ∀ᶠ σ' in 𝓝 σ, ψ σ' t ∈ (extChartAt I x₀).target :=
      (hψs σ hσ t ht).continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_target x₀).mem_nhds (htgt σ ⟨hσ.1.le, hσ.2.le⟩ t ht))
    exact hasDerivAt_chartGram_fam_s (cov := cov) hmet x₀ (hψs σ hσ t ht) (hws σ hσ t ht)
      (htgt σ ⟨hσ.1.le, hσ.2.le⟩ t ht) hstay
  have hderiv' : ∀ σ ∈ Ioo (-δ) δ, ∀ t ∈ Icc 0 L,
      HasDerivAt (fun σ' => 2 * chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ σ' t))
          (nabS (cov := cov) x₀ ψ w e v σ' t) (w σ' t))
        (jetS2 (cov := cov) x₀ (ψ σ t) (w σ t) (v σ t) (a σ t) (e σ t) (ea σ t)) σ := by
    intro σ hσ t ht
    have hδ' : 0 < min (σ + δ) (δ - σ) / 2 := by
      have h1 : 0 < σ + δ := by linarith [hσ.1]
      have h2 : 0 < δ - σ := by linarith [hσ.2]
      positivity
    have hsub : Ioo (σ - min (σ + δ) (δ - σ) / 2) (σ + min (σ + δ) (δ - σ) / 2)
        ⊆ Ioo (-δ) δ := by
      intro σ' hσ'
      constructor
      · linarith [hσ'.1, min_le_left (σ + δ) (δ - σ)]
      · linarith [hσ'.2, min_le_right (σ + δ) (δ - σ)]
    have hfine := hasDerivAt_deriv_chartGram_fam (cov := cov) hmet x₀ (s := σ) (t := t) hδ'
      (fun σ' hσ' => hψs σ' (hsub hσ') t ht) (fun σ' hσ' => hvs σ' (hsub hσ') t ht)
      (fun σ' hσ' => hws σ' (hsub hσ') t ht) (fun σ' hσ' => hes σ' (hsub hσ') t ht)
      (fun σ' hσ' => htgt σ' ⟨(hsub hσ').1.le, (hsub hσ').2.le⟩ t ht)
    refine hfine.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds (by linarith : σ - min (σ + δ) (δ - σ) / 2 < σ)
      (by linarith : σ < σ + min (σ + δ) (δ - σ) / 2)] with σ' hσ'
    exact ((hderiv σ' (hsub hσ') t ht).deriv).symm
  have han := Commons.Analysis.Calculus.hasDerivAt_deriv_integral_of_continuousOn_Icc_prod
    (g := fun σ t => chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ σ t)) (w σ t) (w σ t))
    (g' := fun σ t => 2 * chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ σ t))
      (nabS (cov := cov) x₀ ψ w e v σ t) (w σ t))
    (g'' := fun σ t => jetS2 (cov := cov) x₀ (ψ σ t) (w σ t) (v σ t) (a σ t) (e σ t)
      (ea σ t))
    hL.le hδ hg hg' hg'' hderiv hderiv'
  have hpoint : ∀ t ∈ Icc 0 L,
      jetS2 (cov := cov) x₀ (ψ 0 t) (w 0 t) (v 0 t) (a 0 t) (e 0 t) (ea 0 t)
        = -2 * indexIntegrand cov x₀ (fun t => ψ 0 t) (fun t => v 0 t) (fun t => w 0 t)
            (fun t => e 0 t) t := by
    intro t ht
    have hsrc : (extChartAt I x₀).symm (ψ 0 t) ∈ (chartAt H x₀).source :=
      mem_source_chartCurve (I := I) (htgt 0 hmem0 t ht)
    rw [jetS2_eq_idxV (cov := cov) hmet htor x₀ hsrc (hgeo t ht) (hgeo' t ht)]
    congr 1
    simp only [idxV, indexIntegrand, Rt, Gt, DtQ, covDsP, fam, famP, nabV, zero_smul, add_zero]
  have hint : (∫ t in (0 : ℝ)..L,
        jetS2 (cov := cov) x₀ (ψ 0 t) (w 0 t) (v 0 t) (a 0 t) (e 0 t) (ea 0 t))
      = -2 * ∫ t in (0 : ℝ)..L, indexIntegrand cov x₀ (fun t => ψ 0 t) (fun t => v 0 t)
          (fun t => w 0 t) (fun t => e 0 t) t := by
    rw [intervalIntegral.integral_congr (fun t ht => hpoint t (by rwa [uIcc_of_le hL.le] at ht)),
      intervalIntegral.integral_const_mul]
  exact han.congr_deriv hint

/-- **The first variation of the energy, in one chart.**  For a coordinate family along a chart
geodesic `t ↦ ψ(0,t)` with velocity `w(0,·)` and acceleration `w'`, the energy
`E(σ) = ∫₀^L ⟨∂_tψ(σ,·),∂_tψ(σ,·)⟩` has first derivative

`E'(0) = 2 ( ⟪η(L),γ'(L)⟫ - ⟪η(0),γ'(0)⟫ )`,

where `η = ∂_σψ(0,·)` — the classical first-variation formula, in the case where the base curve is a
geodesic (so that the interior term `∫⟪η,∇_tγ'⟫` vanishes). -/
theorem energy_first_deriv_chart [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (x₀ : M)
    {ψ w v a e : ℝ → ℝ → E} {w' : ℝ → E} {L : ℝ} (hL : 0 < L) {δ : ℝ} (hδ : 0 < δ)
    (hψt : ∀ σ ∈ Ioo (-δ) δ, ∀ t ∈ Icc 0 L, HasDerivAt (fun t' => ψ σ t') (w σ t) t)
    (hψs : ∀ σ ∈ Ioo (-δ) δ, ∀ t ∈ Icc 0 L, HasDerivAt (fun σ' => ψ σ' t) (v σ t) σ)
    (hvs : ∀ σ ∈ Ioo (-δ) δ, ∀ t ∈ Icc 0 L, HasDerivAt (fun σ' => v σ' t) (a σ t) σ)
    (hws : ∀ σ ∈ Ioo (-δ) δ, ∀ t ∈ Icc 0 L, HasDerivAt (fun σ' => w σ' t) (e σ t) σ)
    (hvt : ∀ t ∈ Icc 0 L, HasDerivAt (fun t' => v 0 t') (e 0 t) t)
    (hwt : ∀ t ∈ Icc 0 L, HasDerivAt (fun t' => w 0 t') (w' t) t)
    (hgeoB : ∀ t ∈ Icc 0 L,
      w' t + chrB cov x₀ ((extChartAt I x₀).symm (ψ 0 t)) (w 0 t) (w 0 t) = 0)
    (htgt : ∀ σ ∈ Icc (-δ) δ, ∀ t ∈ Icc 0 L, ψ σ t ∈ (extChartAt I x₀).target)
    (hg : ContinuousOn (fun p : ℝ × ℝ =>
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ p.1 p.2)) (w p.1 p.2) (w p.1 p.2))
      (Icc (-δ) δ ×ˢ Icc 0 L))
    (hg' : ContinuousOn (fun p : ℝ × ℝ =>
      2 * chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ p.1 p.2))
        (nabS (cov := cov) x₀ ψ w e v p.1 p.2) (w p.1 p.2)) (Icc (-δ) δ ×ˢ Icc 0 L)) :
    HasDerivAt (fun σ : ℝ => ∫ t in (0 : ℝ)..L,
        chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ σ t)) (w σ t) (w σ t))
      (2 * (chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ 0 L)) (v 0 L) (w 0 L)
        - chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ 0 0)) (v 0 0) (w 0 0))) 0 := by
  have hmem0 : (0 : ℝ) ∈ Icc (-δ) δ := ⟨by linarith, hδ.le⟩
  have hmem0' : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have hsrc0 : (extChartAt I x₀).symm (ψ 0 0) ∈ (chartAt H x₀).source :=
    mem_source_chartCurve (I := I) (htgt 0 hmem0 0 ⟨le_refl 0, hL.le⟩)
  have hstay : ∀ σ ∈ Ioo (-δ) δ, ∀ t ∈ Icc 0 L, ∀ᶠ σ' in 𝓝 σ,
      ψ σ' t ∈ (extChartAt I x₀).target := fun σ hσ t ht =>
    (hψs σ hσ t ht).continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_target x₀).mem_nhds (htgt σ ⟨hσ.1.le, hσ.2.le⟩ t ht))
  have hderiv : ∀ σ ∈ Ioo (-δ) δ, ∀ t ∈ Icc 0 L,
      HasDerivAt (fun σ' => chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ σ' t))
          (w σ' t) (w σ' t))
        (2 * chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ σ t))
          (nabS (cov := cov) x₀ ψ w e v σ t) (w σ t)) σ := fun σ hσ t ht =>
    hasDerivAt_chartGram_fam_s (cov := cov) hmet x₀ (hψs σ hσ t ht) (hws σ hσ t ht)
      (htgt σ ⟨hσ.1.le, hσ.2.le⟩ t ht) (hstay σ hσ t ht)
  have han := Commons.Analysis.Calculus.hasDerivAt_integral_of_continuousOn_Icc_prod
    (g := fun σ t => chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ σ t)) (w σ t) (w σ t))
    (g' := fun σ t => 2 * chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ σ t))
      (nabS (cov := cov) x₀ ψ w e v σ t) (w σ t))
    hL.le hδ hg hg' hderiv
  have hstayt : ∀ t ∈ Icc 0 L, ∀ᶠ t' in 𝓝 t, ψ 0 t' ∈ (extChartAt I x₀).target := fun t ht =>
    (hψt 0 hmem0' t ht).continuousAt.preimage_mem_nhds
      ((isOpen_extChartAt_target x₀).mem_nhds (htgt 0 hmem0 t ht))
  have hF : ∀ t ∈ Icc 0 L, HasDerivAt (fun t' => chartGram (I := I) x₀
      ((extChartAt I x₀).symm (ψ 0 t')) (v 0 t') (w 0 t'))
      (chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ 0 t))
        (nabS (cov := cov) x₀ ψ w e v 0 t) (w 0 t)) t := by
    intro t ht
    have h := hasDerivAt_chartGram_curve (cov := cov) (hmet := hmet) (x₀ := x₀)
      (u := fun t' => ψ 0 t') (v := w 0 t) (t := t) (hψt 0 hmem0' t ht)
      (htgt 0 hmem0 t ht) (hstayt t ht)
      (h₁ := fun t' => v 0 t') (h₂ := fun t' => w 0 t') (h₁' := e 0 t) (h₂' := w' t)
      (hvt t ht) (hwt t ht)
    refine h.congr_deriv ?_
    have hsrc : (extChartAt I x₀).symm (ψ 0 t) ∈ (chartAt H x₀).source :=
      mem_source_chartCurve (I := I) (htgt 0 hmem0 t ht)
    simp only [nabS]
    rw [show christoffelEval cov x₀ ((extChartAt I x₀).symm (ψ 0 t)) (v 0 t)
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (ψ 0 t)) (w 0 t))
        = chrB cov x₀ ((extChartAt I x₀).symm (ψ 0 t)) (v 0 t) (w 0 t) from rfl,
      show christoffelEval cov x₀ ((extChartAt I x₀).symm (ψ 0 t)) (w 0 t)
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (ψ 0 t)) (w 0 t))
        = chrB cov x₀ ((extChartAt I x₀).symm (ψ 0 t)) (w 0 t) (w 0 t) from rfl,
      hgeoB t ht, chartGram_zero_snd, add_zero]
    rw [chrB_comm (cov := cov) htor hsrc (v 0 t) (w 0 t)]
  have hint : (∫ t in (0 : ℝ)..L, 2 * chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ 0 t))
        (nabS (cov := cov) x₀ ψ w e v 0 t) (w 0 t))
      = 2 * (chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ 0 L)) (v 0 L) (w 0 L)
        - chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ 0 0)) (v 0 0) (w 0 0)) := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hF t (by rwa [uIcc_of_le hL.le] at ht)) ?_]
    have hcont : ContinuousOn (fun t : ℝ => ((0 : ℝ), t)) (Icc 0 L) :=
      ((continuous_const : Continuous fun _ : ℝ => (0 : ℝ)).prodMk continuous_id).continuousOn
    have hslice : ContinuousOn (fun t : ℝ => 2 * chartGram (I := I) x₀
        ((extChartAt I x₀).symm (ψ 0 t)) (nabS (cov := cov) x₀ ψ w e v 0 t) (w 0 t))
        (Icc 0 L) :=
      ContinuousOn.comp'
        (g := fun p : ℝ × ℝ => 2 * chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ p.1 p.2))
          (nabS (cov := cov) x₀ ψ w e v p.1 p.2) (w p.1 p.2))
        (f := fun t : ℝ => ((0 : ℝ), t)) hg' hcont
        (fun t ht => ⟨⟨by linarith [hδ], by linarith [hδ]⟩, ht⟩)
    refine ((hslice.const_mul (1 / 2)).congr (fun t ht => ?_)).intervalIntegrable_of_Icc hL.le
    ring
  rw [hint] at han
  exact han

/-- **The first variation vanishes for a variation with fixed endpoints along a geodesic**: the
classical statement `E'(0) = 0`, i.e. geodesics are critical points of the energy. -/
theorem energy_first_deriv_chart_eq_zero [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (x₀ : M)
    {ψ w v a e : ℝ → ℝ → E} {w' : ℝ → E} {L : ℝ} (hL : 0 < L) {δ : ℝ} (hδ : 0 < δ)
    (hψt : ∀ σ ∈ Ioo (-δ) δ, ∀ t ∈ Icc 0 L, HasDerivAt (fun t' => ψ σ t') (w σ t) t)
    (hψs : ∀ σ ∈ Ioo (-δ) δ, ∀ t ∈ Icc 0 L, HasDerivAt (fun σ' => ψ σ' t) (v σ t) σ)
    (hvs : ∀ σ ∈ Ioo (-δ) δ, ∀ t ∈ Icc 0 L, HasDerivAt (fun σ' => v σ' t) (a σ t) σ)
    (hws : ∀ σ ∈ Ioo (-δ) δ, ∀ t ∈ Icc 0 L, HasDerivAt (fun σ' => w σ' t) (e σ t) σ)
    (hvt : ∀ t ∈ Icc 0 L, HasDerivAt (fun t' => v 0 t') (e 0 t) t)
    (hwt : ∀ t ∈ Icc 0 L, HasDerivAt (fun t' => w 0 t') (w' t) t)
    (hgeoB : ∀ t ∈ Icc 0 L,
      w' t + chrB cov x₀ ((extChartAt I x₀).symm (ψ 0 t)) (w 0 t) (w 0 t) = 0)
    (htgt : ∀ σ ∈ Icc (-δ) δ, ∀ t ∈ Icc 0 L, ψ σ t ∈ (extChartAt I x₀).target)
    (hv0 : v 0 0 = 0) (hvL : v 0 L = 0)
    (hg : ContinuousOn (fun p : ℝ × ℝ =>
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ p.1 p.2)) (w p.1 p.2) (w p.1 p.2))
      (Icc (-δ) δ ×ˢ Icc 0 L))
    (hg' : ContinuousOn (fun p : ℝ × ℝ =>
      2 * chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ p.1 p.2))
        (nabS (cov := cov) x₀ ψ w e v p.1 p.2) (w p.1 p.2)) (Icc (-δ) δ ×ˢ Icc 0 L)) :
    HasDerivAt (fun σ : ℝ => ∫ t in (0 : ℝ)..L,
        chartGram (I := I) x₀ ((extChartAt I x₀).symm (ψ σ t)) (w σ t) (w σ t)) 0 0 := by
  have h := energy_first_deriv_chart (cov := cov) hmet htor x₀ hL hδ hψt hψs hvs hws hvt hwt
    hgeoB htgt hg hg'
  rw [hvL, hv0, chartGram_zero_fst, chartGram_zero_fst, sub_zero, mul_zero] at h
  exact h

end

end Submission.SecondVarGeo

