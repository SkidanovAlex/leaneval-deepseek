import Submission.ChartConnection
import Submission.Commons.Analysis.Calculus.eqOn_of_hasDerivAt_eq_zero_Icc
import Submission.Commons.Analysis.Calculus.hasDerivAt_deriv_fst_of_contDiffAt
import Submission.Commons.Analysis.ODE.exists_uniform_secondOrderODE_solution_in_open
import Submission.Commons.Analysis.ODE.contDiffAt_solutionMap_of_eventually
import Submission.Commons.Geometry.Manifold.Tangent.hasMFDerivAt_extChartAt_symm_comp

/-!
# The geodesic flow in a chart, and Gauss's lemma

This module completes the local Riemannian geometry chapter started in `Submission/Geodesic.lean`.
Starting from the chart connection and the product rule of `Submission/ChartConnection.lean`, it
builds the *geodesic flow* and proves **Gauss's lemma**.

## Main results

* `exists_geodesicFlow_local`: a uniform solution family `sol : E → ℝ → E × E` of the chart geodesic
  equation on `Ioo (-2) 2` for all initial velocities in a ball, with
  * the initial conditions `sol ϑ 0 = ((extChartAt I x₀) x₀, ϑ)`,
  * the chart geodesic equation `sol ϑ ' = ((sol ϑ).2, chartGeodesicVectorField cov x₀ (sol ϑ))`,
  * the confinement of the positions in the chart target,
  * **joint smoothness** `ContDiffAt ℝ ∞ (fun p : E × ℝ => sol p.1 p.2) (ϑ, s)` (from the commons
    ODE lemma `contDiffAt_solutionMap_of_eventually`),
  * the identification `expMap cov x₀ (c • ϑ) = (extChartAt I x₀).symm ((sol ϑ c).1)` for `|c| ≤ 1`.
* `exists_geodesicVariation`: the two-parameter family `Φ (s, t) = sol (v + t • w) s` of geodesics
  with initial velocities along the line through `v` in direction `w`, again with joint smoothness
  in `(s, t)` near `(s₀, 0)` and the ODE in `s`.
* `chart_gauss`: **Gauss's lemma in chart coordinates**.  For such a family,
  `⟪∂_s Φ, ∂_t Φ⟫ (s, 0) = s ⟪v, w⟫`.  The proof uses
  (i) the product rule for the chart metric along curves (`hasDerivAt_chartGram_curve`),
  (ii) metric compatibility to show that the speed of the geodesics is constant in `s`
      (`hEd`, `hEconst`, `hasDerivAt_affine_chartGram_self`),
  (iii) torsion-freeness (`christoffelEval_comm`) to identify the two mixed second derivatives,
      using Clairaut's theorem
      (`Commons.Analysis.Calculus.hasDerivAt_deriv_fst_of_contDiffAt`), and
  (iv) the constancy lemma `Commons.Analysis.Calculus.eqOn_of_hasDerivAt_eq_zero_Icc` to integrate
      the identity in `s`.
* `gauss_lemma`: **Gauss's lemma** for the exponential map: for `‖v‖` small, `0 < s < 1` and any
  `w`,
  `⟪(d exp_{x₀})_{s v} v, (d exp_{x₀})_{s v} (s w)⟫ = s ⟪v, w⟫`,
  where the scalar product on the right is the Riemannian metric at `x₀` evaluated on the
  coordinate vectors `v`, `w` (written `chartGram x₀ x₀ v w`: by `frameVector_self` the frame
  vectors at the base point are the coordinate vectors themselves).

## Notes

The statement of `gauss_lemma` uses the chart metric `chartGram x₀ x₀ v w` rather than
`inner ℝ v w` for the scalar product at the base point: in this development the inner product on
the tangent space `TangentSpace I x₀` is provided by the `RiemannianBundle` instance (and type
synonymy with `E` makes direct use of `inner ℝ` on `E` unreliable), so the metric is always written
through `chartGram`.

## Next steps

* normal coordinates: `expMap` is injective on a ball and the metric in those coordinates satisfies
  `chartGram x₀ (expMap v) ... `-relations coming from Gauss's lemma;
* the Riemannian distance (length of curves), the first and second variation of energy, Jacobi
  fields, and the comparison theorems (Rauch, Toponogov);
* Klingenberg's injectivity radius estimate and Berger's lemma, leading to the topological sphere
  theorem.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Geodesic
open Submission.Variation
open Submission.ChartConnection

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [I.Boundaryless]

namespace Submission.Gauss

noncomputable section

/-- **The local geodesic flow in a chart.**  There is a radius `ρ > 0` and a family
`sol : E → ℝ → E × E` of solutions of the chart geodesic equation on `Ioo (-2) 2`, for every
initial velocity `ϑ` with `‖ϑ‖ ≤ ρ`, with initial position `(extChartAt I x₀) x₀` and initial
velocity `ϑ`; the family is jointly smooth in `(ϑ, s)`, its positions stay in the chart target, and
its positions are the exponential map. -/
theorem exists_geodesicFlow_local
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞] (x₀ : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ sol : E → ℝ → E × E,
      (∀ ϑ : E, ‖ϑ‖ ≤ ρ → sol ϑ 0 = ((extChartAt I x₀) x₀, ϑ)) ∧
      (∀ ϑ : E, ‖ϑ‖ ≤ ρ → ∀ s ∈ Ioo (-2 : ℝ) 2,
          HasDerivAt (sol ϑ) ((sol ϑ s).2, chartGeodesicVectorField cov x₀ (sol ϑ s)) s) ∧
      (∀ ϑ : E, ‖ϑ‖ ≤ ρ → ∀ s ∈ Ioo (-2 : ℝ) 2,
          (sol ϑ s).1 ∈ (extChartAt I x₀).target) ∧
      (∀ ϑ : E, ‖ϑ‖ < ρ → ∀ s ∈ Ioo (-2 : ℝ) 2,
          ContDiffAt ℝ ∞ (fun p : E × ℝ => sol p.1 p.2) (ϑ, s)) ∧
      (∀ ϑ : E, ‖ϑ‖ ≤ ρ → ∀ c : ℝ, |c| ≤ 1 →
          expMap cov x₀ (c • ϑ) = (extChartAt I x₀).symm ((sol ϑ c).1)) := by
  classical
  obtain ⟨U, G, hUopen, hz0U, hUsub, hGU, hGsm, hG0⟩ :=
    exists_contMDiff_spray_extension (cov := cov) x₀
  have hGdiff : ContDiff ℝ ∞ G := contMDiff_iff_contDiff.mp hGsm
  obtain ⟨ρ, hρ, hunif⟩ :=
    Commons.Analysis.ODE.exists_uniform_secondOrderODE_solution_in_open (G := G)
      (U := U) (p₀ := (extChartAt I x₀) x₀) hUopen hz0U
      (fun z hz => (hGsm.contMDiffAt.contDiffAt).of_le (by norm_num)) hG0
  let sol : E → ℝ → E × E := fun w =>
    if h : ∃ α : ℝ → E × E, α 0 = ((extChartAt I x₀) x₀, w) ∧
        (∀ t ∈ Ioo (-2) 2, α t ∈ U) ∧
        (∀ t ∈ Ioo (-2) 2, HasDerivAt α ((α t).2, G (α t)) t)
      then Classical.choose h else fun _ => ((extChartAt I x₀) x₀, w)
  have hex : ∀ w : E, ‖w‖ ≤ ρ → ∃ α : ℝ → E × E,
      α 0 = ((extChartAt I x₀) x₀, w) ∧ (∀ t ∈ Ioo (-2) 2, α t ∈ U) ∧
      (∀ t ∈ Ioo (-2) 2, HasDerivAt α ((α t).2, G (α t)) t) := by
    intro w hw
    obtain ⟨u, v, hu0, hv0, hmem, hdu, hdv⟩ := hunif w hw
    refine ⟨fun t => (u t, v t), ?_, ?_, ?_⟩
    · simp [hu0, hv0]
    · exact fun t ht => by simpa using hmem t ht
    · intro t ht
      exact HasDerivAt.prodMk (hdu t ht) (hdv t ht)
  have hsolf : ∀ w : E, ‖w‖ ≤ ρ → ∀ t ∈ Ioo (-2 : ℝ) 2,
      HasDerivAt (sol w) ((sol w t).2, G (sol w t)) t := by
    intro w hw t ht
    dsimp only [sol]
    rw [dif_pos (hex w hw)]
    exact (Classical.choose_spec (hex w hw)).2.2 t ht
  have hmemf : ∀ w : E, ‖w‖ ≤ ρ → ∀ t ∈ Ioo (-2 : ℝ) 2, sol w t ∈ U := by
    intro w hw t ht
    dsimp only [sol]
    rw [dif_pos (hex w hw)]
    exact (Classical.choose_spec (hex w hw)).2.1 t ht
  have h0f : ∀ w : E, ‖w‖ ≤ ρ → sol w 0 = ((extChartAt I x₀) x₀, w) := by
    intro w hw
    dsimp only [sol]
    rw [dif_pos (hex w hw)]
    exact (Classical.choose_spec (hex w hw)).1
  have huniqf : ∀ w : E, ‖w‖ ≤ ρ → ∀ y : ℝ → E × E,
      (∀ t ∈ Ioo (-2 : ℝ) 2, HasDerivAt y ((y t).2, G (y t)) t) →
      y 0 = ((extChartAt I x₀) x₀, w) → ∀ t ∈ Ioo (-2 : ℝ) 2, y t = sol w t := by
    intro w hw y hy hy0 t ht
    refine prod_eqOn (a := -2) (b := 2) hGdiff (by norm_num) (by norm_num) ?_ ?_ ?_ t ht
    · exact fun s hs => hy s hs
    · exact fun s hs => hsolf w hw s hs
    · rw [hy0, h0f w hw]
  refine ⟨ρ, hρ, sol, h0f, ?_, ?_, ?_, ?_⟩
  · -- the chart geodesic equation
    intro w hw s hs
    have hd := hsolf w hw s hs
    rw [hGU (sol w s) (hmemf w hw s hs)] at hd
    exact hd
  · -- positions stay in the chart target
    intro w hw s hs
    exact (hUsub (hmemf w hw s hs)).1
  · -- joint smoothness
    intro w₀ hw₀ s₀ hs₀
    have hρ' : ∀ᶠ w in 𝓝 w₀, ‖w‖ ≤ ρ := by
      filter_upwards [Metric.ball_mem_nhds w₀ (by linarith : (0:ℝ) < ρ - ‖w₀‖)] with w hw
      rw [Metric.mem_ball, dist_eq_norm] at hw
      have h1 : ‖w‖ = ‖(w - w₀) + w₀‖ := by rw [sub_add_cancel]
      rw [h1]
      linarith [norm_add_le (w - w₀) w₀]
    have h0e : ∀ᶠ w in 𝓝 w₀, sol w 0 = ((extChartAt I x₀) x₀, w) := by
      filter_upwards [hρ'] with w hw
      exact h0f w hw
    have hsole : ∀ᶠ w in 𝓝 w₀, ∀ t ∈ Ioo (-2 : ℝ) 2,
        HasDerivAt (sol w) ((sol w t).2, G (sol w t)) t := by
      filter_upwards [hρ'] with w hw
      exact fun t ht => hsolf w hw t ht
    have huni : ∀ᶠ w in 𝓝 w₀, ∀ y : ℝ → E × E,
        (∀ t ∈ Ioo (-2 : ℝ) 2, HasDerivAt y ((y t).2, G (y t)) t) →
        y 0 = ((extChartAt I x₀) x₀, w) → ∀ t ∈ Ioo (-2 : ℝ) 2, y t = sol w t := by
      filter_upwards [hρ'] with w hw
      exact fun y hy hy0 t ht => huniqf w hw y hy hy0 t ht
    exact Commons.Analysis.ODE.contDiffAt_solutionMap_of_eventually
      (X := E) (E := E × E) (a := -2) (b := 2)
      (f := fun (_ : ℝ) (z : E × E) => (z.2, G z))
      (by have := hGdiff; fun_prop) (by norm_num) (by norm_num)
      (c := fun w : E => ((extChartAt I x₀) x₀, w)) (by fun_prop)
      (x₀ := w₀) (u := sol) h0e hsole huni hs₀
  · -- identification with the exponential map
    intro w hw c hc
    have hH : HasChartGeodesic cov x₀ w (fun t => (sol w t).1) (fun t => (sol w t).2) := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · show (sol w 0).1 = (extChartAt I x₀) x₀
        rw [h0f w hw]
      · show (sol w 0).2
            = (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x₀ w
        rw [h0f w hw, continuousLinearMapAt_trivializationAt_self]
        rfl
      · intro t ht
        exact (hUsub (hmemf w hw t ht)).1
      · intro t ht
        exact (hsolf w hw t ht).fst
      · intro t ht
        have hd := hsolf w hw t ht
        rw [hGU (sol w t) (hmemf w hw t ht)] at hd
        exact hd.snd
    exact expMap_smul (I := I) (x := x₀) (v := w) hc hH

/-! ## The two-parameter family of geodesics with velocities `v + t w` -/

/-- Joint smoothness of the components of a smooth map into a product. -/
lemma contDiffAt_fst_comp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : ℝ × ℝ → E × E} {p : ℝ × ℝ}
    (h : ContDiffAt ℝ ∞ Φ p) :
    ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => (Φ q).1) p :=
  contDiffAt_fst.comp p h

/-- Joint smoothness of the components of a smooth map into a product. -/
lemma contDiffAt_snd_comp {Φ : ℝ × ℝ → E × E} {p : ℝ × ℝ}
    (h : ContDiffAt ℝ ∞ Φ p) :
    ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => (Φ q).2) p :=
  contDiffAt_snd.comp p h

/-- A smooth two-variable function is differentiable along any horizontal line, and its derivative
is the `deriv` of the restricted function. -/
lemma hasDerivAt_line {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} {s : ℝ}
    (h : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => f p) (s, 0)) :
    HasDerivAt (fun t => f (s, t)) (deriv (fun t => f (s, t)) 0) 0 := by
  have hline : ContDiffAt ℝ ∞ (fun t : ℝ => (s, t)) 0 :=
    contDiffAt_const.prodMk contDiffAt_id
  have hcomp : ContDiffAt ℝ ∞ ((fun p : ℝ × ℝ => f p) ∘ fun t : ℝ => (s, t)) 0 :=
    h.comp 0 hline
  have hd : DifferentiableAt ℝ (fun t => f (s, t)) 0 := hcomp.differentiableAt (by norm_num)
  exact hd.hasDerivAt

/-- **The two-parameter family of geodesics with initial velocity `v + t • w`.** -/
theorem exists_geodesicVariation
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞] (x₀ : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ v : E, ‖v‖ < ρ → ∀ w : E,
      ∃ (δ : ℝ) (Φ : ℝ × ℝ → E × E), 0 < δ ∧
        (∀ t ∈ Ioo (-δ) δ, (Φ (0, t)).1 = (extChartAt I x₀) x₀) ∧
        (∀ t ∈ Ioo (-δ) δ, (Φ (0, t)).2 = v + t • w) ∧
        (∀ t ∈ Ioo (-δ) δ, ∀ s ∈ Ioo (-2 : ℝ) 2,
            HasDerivAt (fun s' : ℝ => Φ (s', t))
              ((Φ (s, t)).2, chartGeodesicVectorField cov x₀ (Φ (s, t))) s) ∧
        (∀ t ∈ Ioo (-δ) δ, ∀ s ∈ Ioo (-2 : ℝ) 2,
            (Φ (s, t)).1 ∈ (extChartAt I x₀).target) ∧
        (∀ s ∈ Ioo (-2 : ℝ) 2, ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => Φ p) (s, 0)) ∧
        (∀ s : ℝ, |s| ≤ 1 → ∀ t ∈ Ioo (-δ) δ,
            expMap cov x₀ (s • (v + t • w)) = (extChartAt I x₀).symm ((Φ (s, t)).1)) := by
  classical
  obtain ⟨ρ, hρ, sol, h0, hode, htgt, hsm, hexp⟩ := exists_geodesicFlow_local (cov := cov) x₀
  refine ⟨ρ, hρ, fun v hv w => ?_⟩
  -- a neighbourhood of `0` where `‖v + t • w‖ < ρ`
  have hcont : Continuous fun t : ℝ => ‖v + t • w‖ :=
    continuous_norm.comp (continuous_const.add (continuous_id.smul continuous_const))
  have h0lt : (0 : ℝ) ∈ {t : ℝ | ‖v + t • w‖ < ρ} := by
    simp only [Set.mem_ofPred_eq, zero_smul, add_zero]
    exact hv
  have hnb : {t : ℝ | ‖v + t • w‖ < ρ} ∈ 𝓝 0 :=
    IsOpen.mem_nhds (isOpen_lt hcont continuous_const) h0lt
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hnb
  have hδmem : ∀ t ∈ Ioo (-δ) δ, ‖v + t • w‖ < ρ := by
    intro t ht
    refine hδsub ?_
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine ⟨δ, fun p => sol (v + p.2 • w) p.1, hδ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact (Prod.ext_iff.mp (h0 (v + t • w) (le_of_lt (hδmem t ht)))).1
  · intro t ht
    exact (Prod.ext_iff.mp (h0 (v + t • w) (le_of_lt (hδmem t ht)))).2
  · intro t ht s hs
    exact hode (v + t • w) (le_of_lt (hδmem t ht)) s hs
  · intro t ht s hs
    exact htgt (v + t • w) (le_of_lt (hδmem t ht)) s hs
  · intro s₀ hs₀
    have h1 : ContDiffAt ℝ ∞ (fun p : E × ℝ => sol p.1 p.2) (v + 0 • w, s₀) :=
      hsm (v + 0 • w) (by simpa using hv) s₀ hs₀
    have h1' : ContDiffAt ℝ ∞ (fun p : E × ℝ => sol p.1 p.2)
        ((fun p : ℝ × ℝ => (v + p.2 • w, p.1)) (s₀, 0)) := by
      simpa using h1
    have h2 : ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => (v + p.2 • w, p.1)) (s₀, 0) :=
      (contDiffAt_const.add (contDiffAt_snd.smul contDiffAt_const)).prodMk contDiffAt_fst
    have h3 : ContDiffAt ℝ ∞ ((fun p : E × ℝ => sol p.1 p.2) ∘ fun p : ℝ × ℝ => (v + p.2 • w, p.1)) (s₀, 0) :=
      h1'.comp (s₀, 0) h2
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards with p
    rfl
  · intro s hs t ht
    exact hexp (v + t • w) (le_of_lt (hδmem t ht)) s hs

/-! ## Small auxiliary lemmas -/

/-- The frame vector at its own base point is the coordinate vector itself. -/
lemma frameVector_self (x₀ : M) (a : E) : frameVector (I := I) x₀ x₀ a = a := by
  have hb : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet :=
    mem_chart_source H x₀
  have h1 := Trivialization.symmL_continuousLinearMapAt (R := ℝ)
    (e := trivializationAt E (TangentSpace I) x₀) hb a
  rw [continuousLinearMapAt_trivializationAt_self] at h1
  show (Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) x₀) a = a
  exact h1

/-- The frame vector of the zero coordinate vector vanishes. -/
@[simp]
lemma frameVector_zero (x₀ p : M) : frameVector (I := I) x₀ p (0 : E) = 0 :=
  map_zero _

/-- The chart metric vanishes if one of the coordinate vectors vanishes. -/
@[simp]
lemma chartGram_zero_snd (x₀ p : M) (a : E) :
    chartGram (I := I) x₀ p a 0 = 0 := by
  rw [chartGram_apply, frameVector_zero, inner_zero_right]

/-- The chart metric vanishes if one of the coordinate vectors vanishes. -/
@[simp]
lemma chartGram_zero_fst (x₀ p : M) (b : E) :
    chartGram (I := I) x₀ p 0 b = 0 := by
  rw [chartGram_apply, frameVector_zero, inner_zero_left]

/-- The first component of a `HasDerivAt` of a pair-valued function. -/
lemma hasDerivAt_fst {Φ : ℝ → E × E} {a b : E} {t : ℝ}
    (h : HasDerivAt Φ (a, b) t) : HasDerivAt (fun s => (Φ s).1) a t := by
  have h' := HasFDerivAt.comp_hasDerivAt t
    (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.fst ℝ E E)) h
  exact h'.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq (by funext s; rfl))

/-- The second component of a `HasDerivAt` of a pair-valued function. -/
lemma hasDerivAt_snd {Φ : ℝ → E × E} {a b : E} {t : ℝ}
    (h : HasDerivAt Φ (a, b) t) : HasDerivAt (fun s => (Φ s).2) b t := by
  have h' := HasFDerivAt.comp_hasDerivAt t
    (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.snd ℝ E E)) h
  exact h'.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq (by funext s; rfl))

/-- The derivative of the chart metric at `x₀` along the line `t ↦ v + t • w`:
`d/dt ⟪v + t w, v + t w⟫ = 2 ⟪v, w⟫`. -/
lemma hasDerivAt_affine_chartGram_self (x₀ : M) (v w : E) :
    HasDerivAt (fun t : ℝ => chartGram (I := I) x₀ x₀ (v + t • w) (v + t • w))
      (2 * chartGram (I := I) x₀ x₀ v w) 0 := by
  have hlin : HasDerivAt (fun t : ℝ =>
      frameVector (I := I) x₀ x₀ v + t • frameVector (I := I) x₀ x₀ w)
      (frameVector (I := I) x₀ x₀ w) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (frameVector (I := I) x₀ x₀ w) |>.const_add
      (frameVector (I := I) x₀ x₀ v)
  have h := HasDerivAt.inner ℝ hlin hlin
  have heq : (fun t : ℝ => Inner.inner ℝ
        (frameVector (I := I) x₀ x₀ v + t • frameVector (I := I) x₀ x₀ w)
        (frameVector (I := I) x₀ x₀ v + t • frameVector (I := I) x₀ x₀ w))
      = (fun t : ℝ => chartGram (I := I) x₀ x₀ (v + t • w) (v + t • w)) := by
    funext t
    rw [chartGram_apply, frameVector_add, frameVector_smul]
  rw [show (frameVector (I := I) x₀ x₀ v + (0:ℝ) • frameVector (I := I) x₀ x₀ w)
      = frameVector (I := I) x₀ x₀ v from by simp] at h
  have h1 : HasDerivAt (fun t : ℝ => chartGram (I := I) x₀ x₀ (v + t • w) (v + t • w))
      (Inner.inner ℝ (frameVector (I := I) x₀ x₀ v) (frameVector (I := I) x₀ x₀ w)
        + Inner.inner ℝ (frameVector (I := I) x₀ x₀ w) (frameVector (I := I) x₀ x₀ v)) 0 :=
    h.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq heq.symm)
  have hval : Inner.inner ℝ (frameVector (I := I) x₀ x₀ v) (frameVector (I := I) x₀ x₀ w)
        + Inner.inner ℝ (frameVector (I := I) x₀ x₀ w) (frameVector (I := I) x₀ x₀ v)
      = 2 * chartGram (I := I) x₀ x₀ v w := by
    rw [chartGram_apply, real_inner_comm]
    ring
  rwa [hval] at h1

/-! ## Gauss's lemma in a chart -/

/-- **Gauss's lemma, chart form.**  Let `Φ` be the family of geodesics with initial velocity
`v + t w` (position and velocity coordinates) satisfying the chart geodesic equation in the first
variable, with `Φ (0, t)` the point `(extChartAt I x₀) x₀`.  Then the derivative in the `s`
direction of the scalar product of the velocity with the variation field is `⟪v, w⟫`, so that

`⟪∂_s Φ, ∂_t Φ⟫ (s, 0) = s ⟪v, w⟫`.

This is Gauss's lemma in chart coordinates; the ingredients are metric compatibility
(`hasDerivAt_chartGram_curve`) and torsion-freeness (`christoffelEval_comm`), together with
Clairaut's theorem for the mixed partial derivatives. -/
theorem chart_gauss
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (x₀ : M)
    {v w : E} {δ : ℝ} {Φ : ℝ × ℝ → E × E} (hδ : 0 < δ)
    (hinit1 : ∀ t ∈ Ioo (-δ) δ, (Φ (0, t)).1 = (extChartAt I x₀) x₀)
    (hinit2 : ∀ t ∈ Ioo (-δ) δ, (Φ (0, t)).2 = v + t • w)
    (hODE : ∀ t ∈ Ioo (-δ) δ, ∀ s' ∈ Ioo (-2 : ℝ) 2,
        HasDerivAt (fun r : ℝ => Φ (r, t))
          ((Φ (s', t)).2, chartGeodesicVectorField cov x₀ (Φ (s', t))) s')
    (htgt : ∀ t ∈ Ioo (-δ) δ, ∀ s' ∈ Ioo (-2 : ℝ) 2,
        (Φ (s', t)).1 ∈ (extChartAt I x₀).target)
    (hC : ∀ s' ∈ Ioo (-2 : ℝ) 2, ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => Φ p) (s', 0))
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    chartGram (I := I) x₀ ((extChartAt I x₀).symm ((Φ (s, 0)).1)) ((Φ (s, 0)).2)
        (deriv (fun t : ℝ => (Φ (s, t)).1) 0)
      = s * chartGram (I := I) x₀ x₀ v w := by
  classical
  have hδ0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have hsIoo : s ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  -- points of the family are in the chart
  have hsrc : ∀ t ∈ Ioo (-δ) δ, ∀ s' ∈ Ioo (-2 : ℝ) 2,
      (extChartAt I x₀).symm ((Φ (s', t)).1) ∈ (chartAt H x₀).source :=
    fun t ht s' hs' => mem_source_chartCurve (I := I) (x₀ := x₀)
      (u := fun r : ℝ => (Φ (r, t)).1) (htgt t ht s' hs')
  -- the characteristic ODE, componentwise
  have hPs : ∀ t ∈ Ioo (-δ) δ, ∀ s' ∈ Ioo (-2 : ℝ) 2,
      HasDerivAt (fun r : ℝ => (Φ (r, t)).1) ((Φ (s', t)).2) s' :=
    fun t ht s' hs' => hasDerivAt_fst (hODE t ht s' hs')
  have hVs : ∀ t ∈ Ioo (-δ) δ, ∀ s' ∈ Ioo (-2 : ℝ) 2,
      HasDerivAt (fun r : ℝ => (Φ (r, t)).2)
        (- christoffelEval cov x₀ ((extChartAt I x₀).symm ((Φ (s', t)).1)) ((Φ (s', t)).2)
            (frameVector (I := I) x₀ ((extChartAt I x₀).symm ((Φ (s', t)).1))
              ((Φ (s', t)).2))) s' := by
    intro t ht s' hs'
    have h := hasDerivAt_snd (hODE t ht s' hs')
    simpa only [chartGeodesicVectorField] using h
  -- derivatives of the components along the horizontal line `t ↦ (s', t)`
  have hPL : ∀ s' ∈ Ioo (-2 : ℝ) 2, HasDerivAt (fun t : ℝ => (Φ (s', t)).1)
      (deriv (fun t : ℝ => (Φ (s', t)).1) 0) 0 :=
    fun s' hs' => hasDerivAt_line ((hC s' hs').fst)
  have hVL : ∀ s' ∈ Ioo (-2 : ℝ) 2, HasDerivAt (fun t : ℝ => (Φ (s', t)).2)
      (deriv (fun t : ℝ => (Φ (s', t)).2) 0) 0 :=
    fun s' hs' => hasDerivAt_line ((hC s' hs').snd)
  -- Clairaut: the `s`-derivative of `∂_t Φ₁` is `∂_t Φ₂`
  have hCl : ∀ s' ∈ Ioo (-2 : ℝ) 2,
      HasDerivAt (fun r : ℝ => deriv (fun t : ℝ => (Φ (r, t)).1) 0)
        (deriv (fun t : ℝ => (Φ (s', t)).2) 0) s' := by
    intro s' hs'
    have h1 := Commons.Analysis.Calculus.hasDerivAt_deriv_fst_of_contDiffAt
      (f := fun r t => (Φ (r, t)).1) (a := s') (b := 0)
      (((hC s' hs').fst).of_le (WithTop.coe_le_coe.mpr le_top))
    have heq : (fun t : ℝ => deriv (fun r : ℝ => (Φ (r, t)).1) s') =ᶠ[𝓝 0]
        (fun t : ℝ => (Φ (s', t)).2) := by
      filter_upwards [Ioo_mem_nhds (by linarith : -δ < 0) hδ] with t ht
      exact (hPs t ht s' hs').deriv
    rwa [heq.deriv_eq] at h1
  -- ## Step A: the speed of the geodesics is constant in `s`
  have hEd : ∀ t ∈ Ioo (-δ) δ, ∀ s' ∈ Ioo (-2 : ℝ) 2,
      HasDerivAt (fun r : ℝ => chartGram (I := I) x₀ ((extChartAt I x₀).symm ((Φ (r, t)).1))
        ((Φ (r, t)).2) ((Φ (r, t)).2)) 0 s' := by
    intro t ht s' hs'
    have hstay : ∀ᶠ r in 𝓝 s', (Φ (r, t)).1 ∈ (extChartAt I x₀).target := by
      filter_upwards [Ioo_mem_nhds hs'.1 hs'.2] with r hr
      exact htgt t ht r hr
    have h := hasDerivAt_chartGram_curve (cov := cov) hmet x₀
      (u := fun r : ℝ => (Φ (r, t)).1) (v := (Φ (s', t)).2)
      (hPs t ht s' hs') (htgt t ht s' hs') hstay (hVs t ht s' hs') (hVs t ht s' hs')
    convert h using 1
    simp
  -- ## Step B: constancy in `s` on `[0,1]`
  have hEconst : ∀ t ∈ Ioo (-δ) δ, ∀ s' ∈ Icc (0 : ℝ) 1,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm ((Φ (s', t)).1)) ((Φ (s', t)).2)
        ((Φ (s', t)).2)
      = chartGram (I := I) x₀ ((extChartAt I x₀).symm ((Φ (0, t)).1)) ((Φ (0, t)).2)
        ((Φ (0, t)).2) := by
    intro t ht s' hs'
    exact Commons.Analysis.Calculus.eqOn_of_hasDerivAt_eq_zero_Icc (a := 0) (b := 1)
      zero_le_one (fun r hr => hEd t ht r ⟨by linarith [hr.1], by linarith [hr.2]⟩) s' hs'
  -- value at `s = 0`
  have hE0 : ∀ t ∈ Ioo (-δ) δ,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm ((Φ (0, t)).1)) ((Φ (0, t)).2)
        ((Φ (0, t)).2)
      = chartGram (I := I) x₀ x₀ (v + t • w) (v + t • w) := by
    intro t ht
    rw [hinit1 t ht, hinit2 t ht]
    rw [show (extChartAt I x₀).symm ((extChartAt I x₀) x₀) = x₀ from
      (extChartAt I x₀).left_inv (mem_extChartAt_source x₀)]
  -- ## Step E: the derivative of the speed in `t`
  have hg : (fun t : ℝ => chartGram (I := I) x₀ ((extChartAt I x₀).symm ((Φ (s, t)).1))
        ((Φ (s, t)).2) ((Φ (s, t)).2))
      =ᶠ[𝓝 0] (fun t : ℝ => chartGram (I := I) x₀ x₀ (v + t • w) (v + t • w)) := by
    filter_upwards [Ioo_mem_nhds (by linarith : -δ < 0) hδ] with t ht
    rw [hEconst t ht s ⟨le_of_lt hs.1, le_of_lt hs.2⟩, hE0 t ht]
  have hgderiv : deriv (fun t : ℝ => chartGram (I := I) x₀ ((extChartAt I x₀).symm ((Φ (s, t)).1))
      ((Φ (s, t)).2) ((Φ (s, t)).2)) 0 = 2 * chartGram (I := I) x₀ x₀ v w := by
    rw [hg.deriv_eq, (hasDerivAt_affine_chartGram_self (I := I) x₀ v w).deriv]
  -- ## Step D: the derivative of the speed in `t` from the product rule
  have hD : HasDerivAt (fun t : ℝ => chartGram (I := I) x₀ ((extChartAt I x₀).symm ((Φ (s, t)).1))
        ((Φ (s, t)).2) ((Φ (s, t)).2))
      (chartGram (I := I) x₀ ((extChartAt I x₀).symm ((Φ (s, 0)).1))
          (deriv (fun t : ℝ => (Φ (s, t)).2) 0
            + christoffelEval cov x₀ ((extChartAt I x₀).symm ((Φ (s, 0)).1)) ((Φ (s, 0)).2)
                (frameVector (I := I) x₀ ((extChartAt I x₀).symm ((Φ (s, 0)).1))
                  (deriv (fun t : ℝ => (Φ (s, t)).1) 0))) ((Φ (s, 0)).2)
        + chartGram (I := I) x₀ ((extChartAt I x₀).symm ((Φ (s, 0)).1)) ((Φ (s, 0)).2)
          (deriv (fun t : ℝ => (Φ (s, t)).2) 0
            + christoffelEval cov x₀ ((extChartAt I x₀).symm ((Φ (s, 0)).1)) ((Φ (s, 0)).2)
                (frameVector (I := I) x₀ ((extChartAt I x₀).symm ((Φ (s, 0)).1))
                  (deriv (fun t : ℝ => (Φ (s, t)).1) 0)))) 0 := by
    have hstay : ∀ᶠ r in 𝓝 0, (Φ (s, r)).1 ∈ (extChartAt I x₀).target := by
      filter_upwards [Ioo_mem_nhds (by linarith : -δ < 0) hδ] with r hr
      exact htgt r hr s hsIoo
    exact hasDerivAt_chartGram_curve (cov := cov) hmet x₀
      (u := fun r : ℝ => (Φ (s, r)).1) (v := deriv (fun r : ℝ => (Φ (s, r)).1) 0)
      (hPL s hsIoo) (htgt 0 hδ0 s hsIoo) hstay (hVL s hsIoo) (hVL s hsIoo)
  -- ## (★) the key identity
  have hstar : chartGram (I := I) x₀ ((extChartAt I x₀).symm ((Φ (s, 0)).1)) ((Φ (s, 0)).2)
      (deriv (fun t : ℝ => (Φ (s, t)).2) 0
        + christoffelEval cov x₀ ((extChartAt I x₀).symm ((Φ (s, 0)).1)) ((Φ (s, 0)).2)
            (frameVector (I := I) x₀ ((extChartAt I x₀).symm ((Φ (s, 0)).1))
              (deriv (fun t : ℝ => (Φ (s, t)).1) 0)))
      = chartGram (I := I) x₀ x₀ v w := by
    have h2 : 2 * chartGram (I := I) x₀ ((extChartAt I x₀).symm ((Φ (s, 0)).1)) ((Φ (s, 0)).2)
        (deriv (fun t : ℝ => (Φ (s, t)).2) 0
          + christoffelEval cov x₀ ((extChartAt I x₀).symm ((Φ (s, 0)).1)) ((Φ (s, 0)).2)
              (frameVector (I := I) x₀ ((extChartAt I x₀).symm ((Φ (s, 0)).1))
                (deriv (fun t : ℝ => (Φ (s, t)).1) 0)))
        = 2 * chartGram (I := I) x₀ x₀ v w := by
      rw [← hgderiv, hD.deriv]
      rw [chartGram_comm (I := I) x₀ ((extChartAt I x₀).symm ((Φ (s, 0)).1))
        (deriv (fun t : ℝ => (Φ (s, t)).2) 0
          + christoffelEval cov x₀ ((extChartAt I x₀).symm ((Φ (s, 0)).1)) ((Φ (s, 0)).2)
              (frameVector (I := I) x₀ ((extChartAt I x₀).symm ((Φ (s, 0)).1))
                (deriv (fun t : ℝ => (Φ (s, t)).1) 0))) ((Φ (s, 0)).2)]
      ring
    exact mul_left_cancel₀ two_ne_zero h2
  -- ## Step H: the derivative in `s` of `⟪∂_s Φ, ∂_t Φ⟫`
  have hH : HasDerivAt (fun r : ℝ => chartGram (I := I) x₀ ((extChartAt I x₀).symm ((Φ (r, 0)).1))
        ((Φ (r, 0)).2) (deriv (fun t : ℝ => (Φ (r, t)).1) 0))
      (chartGram (I := I) x₀ x₀ v w) s := by
    have hstay : ∀ᶠ r in 𝓝 s, (Φ (r, 0)).1 ∈ (extChartAt I x₀).target := by
      filter_upwards [Ioo_mem_nhds hsIoo.1 hsIoo.2] with r hr
      exact htgt 0 hδ0 r hr
    have h := hasDerivAt_chartGram_curve (cov := cov) hmet x₀
      (u := fun r : ℝ => (Φ (r, 0)).1) (v := (Φ (s, 0)).2)
      (hPs 0 hδ0 s hsIoo) (htgt 0 hδ0 s hsIoo) hstay
      (hVs 0 hδ0 s hsIoo) (hCl s hsIoo)
    have hzero : - christoffelEval cov x₀ ((extChartAt I x₀).symm ((Φ (s, 0)).1)) ((Φ (s, 0)).2)
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm ((Φ (s, 0)).1)) ((Φ (s, 0)).2))
        + christoffelEval cov x₀ ((extChartAt I x₀).symm ((Φ (s, 0)).1)) ((Φ (s, 0)).2)
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm ((Φ (s, 0)).1)) ((Φ (s, 0)).2)) = 0 :=
      neg_add_cancel _
    rw [hzero, chartGram_zero_fst, zero_add] at h
    have hcomm := christoffelEval_comm (I := I) htor x₀ ((extChartAt I x₀).symm ((Φ (s, 0)).1))
      (hsrc 0 hδ0 s hsIoo) ((Φ (s, 0)).2) (deriv (fun t : ℝ => (Φ (s, t)).1) 0)
    rw [← hcomm] at h
    rwa [hstar] at h
  -- ## Step G: integrate from `0` to `s`
  have h0deriv : deriv (fun t : ℝ => (Φ (0, t)).1) 0 = 0 := by
    have he : (fun t : ℝ => (Φ (0, t)).1) =ᶠ[𝓝 0]
        (fun _ : ℝ => (extChartAt I x₀) x₀) := by
      filter_upwards [Ioo_mem_nhds (by linarith : -δ < 0) hδ] with t ht
      exact hinit1 t ht
    rw [he.deriv_eq, deriv_const]
  have hfder : ∀ r ∈ Icc (0 : ℝ) s,
      HasDerivAt (fun r' : ℝ => chartGram (I := I) x₀ ((extChartAt I x₀).symm ((Φ (r', 0)).1))
          ((Φ (r', 0)).2) (deriv (fun t : ℝ => (Φ (r', t)).1) 0)
          - r' * chartGram (I := I) x₀ x₀ v w) 0 r := by
    intro r hr
    have hr2 : r ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [hr.1], by linarith [hr.2, hs.2]⟩
    have hstay : ∀ᶠ r' in 𝓝 r, (Φ (r', 0)).1 ∈ (extChartAt I x₀).target := by
      filter_upwards [Ioo_mem_nhds hr2.1 hr2.2] with r' hr'
      exact htgt 0 hδ0 r' hr'
    have h := hasDerivAt_chartGram_curve (cov := cov) hmet x₀
      (u := fun r' : ℝ => (Φ (r', 0)).1) (v := (Φ (r, 0)).2)
      (hPs 0 hδ0 r hr2) (htgt 0 hδ0 r hr2) hstay
      (hVs 0 hδ0 r hr2) (hCl r hr2)
    have hzero : - christoffelEval cov x₀ ((extChartAt I x₀).symm ((Φ (r, 0)).1)) ((Φ (r, 0)).2)
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm ((Φ (r, 0)).1)) ((Φ (r, 0)).2))
        + christoffelEval cov x₀ ((extChartAt I x₀).symm ((Φ (r, 0)).1)) ((Φ (r, 0)).2)
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm ((Φ (r, 0)).1)) ((Φ (r, 0)).2)) = 0 :=
      neg_add_cancel _
    rw [hzero, chartGram_zero_fst, zero_add] at h
    have hcomm := christoffelEval_comm (I := I) htor x₀ ((extChartAt I x₀).symm ((Φ (r, 0)).1))
      (hsrc 0 hδ0 r hr2) ((Φ (r, 0)).2) (deriv (fun t : ℝ => (Φ (r, t)).1) 0)
    rw [← hcomm] at h
    have hstar' : chartGram (I := I) x₀ ((extChartAt I x₀).symm ((Φ (r, 0)).1)) ((Φ (r, 0)).2)
        (deriv (fun t : ℝ => (Φ (r, t)).2) 0
          + christoffelEval cov x₀ ((extChartAt I x₀).symm ((Φ (r, 0)).1)) ((Φ (r, 0)).2)
              (frameVector (I := I) x₀ ((extChartAt I x₀).symm ((Φ (r, 0)).1))
                (deriv (fun t : ℝ => (Φ (r, t)).1) 0)))
        = chartGram (I := I) x₀ x₀ v w := by
      -- the same argument as for `hstar`
      have hM : (fun t : ℝ => chartGram (I := I) x₀ ((extChartAt I x₀).symm ((Φ (r, t)).1))
          ((Φ (r, t)).2) ((Φ (r, t)).2))
          =ᶠ[𝓝 0] (fun t : ℝ => chartGram (I := I) x₀ x₀ (v + t • w) (v + t • w)) := by
        filter_upwards [Ioo_mem_nhds (by linarith : -δ < 0) hδ] with t ht
        rw [hEconst t ht r ⟨by linarith [hr.1], by linarith [hr.2, hs.2]⟩, hE0 t ht]
      have hMd : deriv (fun t : ℝ => chartGram (I := I) x₀ ((extChartAt I x₀).symm ((Φ (r, t)).1))
          ((Φ (r, t)).2) ((Φ (r, t)).2)) 0 = 2 * chartGram (I := I) x₀ x₀ v w := by
        rw [hM.deriv_eq, (hasDerivAt_affine_chartGram_self (I := I) x₀ v w).deriv]
      have hDm : HasDerivAt (fun t : ℝ => chartGram (I := I) x₀ ((extChartAt I x₀).symm ((Φ (r, t)).1))
            ((Φ (r, t)).2) ((Φ (r, t)).2))
          (chartGram (I := I) x₀ ((extChartAt I x₀).symm ((Φ (r, 0)).1))
              (deriv (fun t : ℝ => (Φ (r, t)).2) 0
                + christoffelEval cov x₀ ((extChartAt I x₀).symm ((Φ (r, 0)).1)) ((Φ (r, 0)).2)
                    (frameVector (I := I) x₀ ((extChartAt I x₀).symm ((Φ (r, 0)).1))
                      (deriv (fun t : ℝ => (Φ (r, t)).1) 0))) ((Φ (r, 0)).2)
            + chartGram (I := I) x₀ ((extChartAt I x₀).symm ((Φ (r, 0)).1)) ((Φ (r, 0)).2)
              (deriv (fun t : ℝ => (Φ (r, t)).2) 0
                + christoffelEval cov x₀ ((extChartAt I x₀).symm ((Φ (r, 0)).1)) ((Φ (r, 0)).2)
                    (frameVector (I := I) x₀ ((extChartAt I x₀).symm ((Φ (r, 0)).1))
                      (deriv (fun t : ℝ => (Φ (r, t)).1) 0)))) 0 := by
        have hstay2 : ∀ᶠ t in 𝓝 0, (Φ (r, t)).1 ∈ (extChartAt I x₀).target := by
          filter_upwards [Ioo_mem_nhds (by linarith : -δ < 0) hδ] with t ht
          exact htgt t ht r hr2
        exact hasDerivAt_chartGram_curve (cov := cov) hmet x₀
          (u := fun t : ℝ => (Φ (r, t)).1) (v := deriv (fun t : ℝ => (Φ (r, t)).1) 0)
          (hPL r hr2) (htgt 0 hδ0 r hr2) hstay2 (hVL r hr2) (hVL r hr2)
      have h2 : 2 * chartGram (I := I) x₀ ((extChartAt I x₀).symm ((Φ (r, 0)).1)) ((Φ (r, 0)).2)
          (deriv (fun t : ℝ => (Φ (r, t)).2) 0
            + christoffelEval cov x₀ ((extChartAt I x₀).symm ((Φ (r, 0)).1)) ((Φ (r, 0)).2)
                (frameVector (I := I) x₀ ((extChartAt I x₀).symm ((Φ (r, 0)).1))
                  (deriv (fun t : ℝ => (Φ (r, t)).1) 0)))
          = 2 * chartGram (I := I) x₀ x₀ v w := by
        rw [← hMd, hDm.deriv]
        rw [chartGram_comm (I := I) x₀ ((extChartAt I x₀).symm ((Φ (r, 0)).1))
          (deriv (fun t : ℝ => (Φ (r, t)).2) 0
            + christoffelEval cov x₀ ((extChartAt I x₀).symm ((Φ (r, 0)).1)) ((Φ (r, 0)).2)
                (frameVector (I := I) x₀ ((extChartAt I x₀).symm ((Φ (r, 0)).1))
                  (deriv (fun t : ℝ => (Φ (r, t)).1) 0))) ((Φ (r, 0)).2)]
        ring
      exact mul_left_cancel₀ two_ne_zero h2
    rw [hstar'] at h
    have hlin : HasDerivAt (fun r' : ℝ => r' * chartGram (I := I) x₀ x₀ v w)
        (chartGram (I := I) x₀ x₀ v w) r := by
      simpa using (hasDerivAt_id r).mul_const (chartGram (I := I) x₀ x₀ v w)
    have hsub := h.sub hlin
    have hev : (fun r' : ℝ => chartGram (I := I) x₀ ((extChartAt I x₀).symm ((Φ (r', 0)).1))
          ((Φ (r', 0)).2) (deriv (fun t : ℝ => (Φ (r', t)).1) 0) - r' * chartGram (I := I) x₀ x₀ v w)
        =ᶠ[𝓝 r] ((fun s : ℝ => chartGram (I := I) x₀ ((extChartAt I x₀).symm ((Φ (s, 0)).1))
          ((Φ (s, 0)).2) (deriv (fun t : ℝ => (Φ (s, t)).1) 0))
            - fun r' : ℝ => r' * chartGram (I := I) x₀ x₀ v w) :=
      Filter.EventuallyEq.of_eq (by funext r'; simp)
    have hsub' := hsub.congr_of_eventuallyEq hev
    rwa [sub_self] at hsub'
  have hfinal := Commons.Analysis.Calculus.eqOn_of_hasDerivAt_eq_zero_Icc
    (a := 0) (b := s) (le_of_lt hs.1) hfder s ⟨le_of_lt hs.1, le_refl s⟩
  have hf0 : chartGram (I := I) x₀ ((extChartAt I x₀).symm ((Φ (0, 0)).1)) ((Φ (0, 0)).2)
        (deriv (fun t : ℝ => (Φ (0, t)).1) 0) - 0 * chartGram (I := I) x₀ x₀ v w = 0 := by
    rw [h0deriv, zero_mul, sub_zero, chartGram_zero_snd]
  rw [hf0] at hfinal
  linarith [hfinal]

/-! ## Gauss's lemma for the exponential map -/

/-- **Gauss's lemma.**  For a torsion-free connection compatible with the Riemannian metric, the
differential of the exponential map at `s • v` (with `0 < s < 1` and `‖v‖` small) preserves the
scalar product of `v` with any vector, up to the factor `s`:

`⟪(d exp_{x₀})_{s v} v, (d exp_{x₀})_{s v} (s w)⟫ = s ⟪v, w⟫`. -/
theorem gauss_lemma
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (x₀ : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ v : E, ‖v‖ < ρ → ∀ w : E, ∀ s : ℝ, 0 < s → s < 1 →
      inner ℝ (mfderiv 𝓘(ℝ, E) I (fun u : E => expMap cov x₀ u) (s • v) v)
        (mfderiv 𝓘(ℝ, E) I (fun u : E => expMap cov x₀ u) (s • v) (s • w))
      = s * chartGram (I := I) x₀ x₀ v w := by
  classical
  obtain ⟨ρ₁, hρ₁, hvar⟩ := exists_geodesicVariation (cov := cov) x₀
  obtain ⟨ρ₂, hρ₂, hsm⟩ := exists_radius_contMDiffAt_expMap (cov := cov) x₀
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun v hv w s hs0 hs1 => ?_⟩
  have hv₁ : ‖v‖ < ρ₁ := lt_of_lt_of_le hv (min_le_left _ _)
  have hv₂ : ‖v‖ < ρ₂ := lt_of_lt_of_le hv (min_le_right _ _)
  obtain ⟨δ, Φ, hδ, hinit1, hinit2, hODE, htgt, hC, hexp⟩ := hvar v hv₁ w
  have hcg := chart_gauss (cov := cov) hmet htor x₀ hδ hinit1 hinit2 hODE htgt hC ⟨hs0, hs1⟩
  have hδ0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  have hsIoo : s ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith, by linarith⟩
  have hsabs : |s| ≤ 1 := abs_le.mpr ⟨by linarith, le_of_lt hs1⟩
  have hsv_lt : ‖s • v‖ < ρ₂ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg v) hsabs) hv₂
  -- the point of the family at `t = 0` is the exponential of `s • v`
  have hP : (extChartAt I x₀).symm ((Φ (s, 0)).1) = expMap cov x₀ (s • v) := by
    have h := hexp s hsabs 0 hδ0
    rw [show v + (0 : ℝ) • w = v from by simp] at h
    exact h.symm
  -- the `t`-derivative of the position along the `s`-line
  have hline : (fun a : ℝ => (Φ (s, a)).1) =ᶠ[𝓝 0]
      (fun a : ℝ => (Φ (s, a)).1) := Filter.EventuallyEq.rfl
  -- ## the differential in the radial direction
  have hd1 : mfderiv 𝓘(ℝ, E) I (fun u : E => expMap cov x₀ u) (s • v) v
      = frameVector (I := I) x₀ ((extChartAt I x₀).symm ((Φ (s, 0)).1)) ((Φ (s, 0)).2) := by
    have hdiff : MDifferentiableAt 𝓘(ℝ, E) I (fun u : E => expMap cov x₀ u) (s • v) :=
      (hsm (s • v) hsv_lt).mdifferentiableAt (by norm_num)
    have hγ : HasDerivAt (fun c : ℝ => c • v) v s := by
      simpa using (hasDerivAt_id s).smul_const v
    have hchain := mfderiv_expMap_comp (cov := cov) x₀ (γ := fun c : ℝ => c • v)
      (t := s) (c' := v) hdiff hγ
    have hev : (fun c : ℝ => expMap cov x₀ (c • v)) =ᶠ[𝓝 s]
        (fun c : ℝ => (extChartAt I x₀).symm ((Φ (c, 0)).1)) := by
      filter_upwards [Metric.ball_mem_nhds s
        (by have h : |s| < 1 := abs_lt.mpr ⟨by linarith, hs1⟩; linarith : (0 : ℝ) < 1 - |s|)]
        with c hc
      rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] at hc
      have h2 : |c| ≤ 1 := by
        have h3 : ‖(c - s) + s‖ ≤ ‖c - s‖ + ‖s‖ := norm_add_le _ _
        rw [sub_add_cancel] at h3
        have h4 : |c| ≤ |c - s| + |s| := by simpa [Real.norm_eq_abs] using h3
        linarith
      have h5 := hexp c h2 0 hδ0
      rw [show v + (0 : ℝ) • w = v from by simp] at h5
      exact h5
    have hcv : curveVelocity (I := I) (fun c : ℝ => expMap cov x₀ (c • v)) s
        = curveVelocity (I := I) (fun c : ℝ => (extChartAt I x₀).symm ((Φ (c, 0)).1)) s := by
      have h := hev.mfderiv_eq (I := 𝓘(ℝ)) (I' := I)
      rw [curveVelocity_apply, curveVelocity_apply, h]
      rfl
    have hu : HasDerivAt (fun c : ℝ => (Φ (c, 0)).1) ((Φ (s, 0)).2) s :=
      hasDerivAt_fst (hODE 0 hδ0 s hsIoo)
    have hstay : ∀ᶠ c in 𝓝 s, (Φ (c, 0)).1 ∈ (extChartAt I x₀).target := by
      filter_upwards [Ioo_mem_nhds hsIoo.1 hsIoo.2] with c hc
      exact htgt 0 hδ0 c hc
    have hcv2 := curveVelocity_extChartAt_symm (I := I) (x₀ := x₀)
      (u := fun c : ℝ => (Φ (c, 0)).1) (t := s) (v := (Φ (s, 0)).2) hu
      (htgt 0 hδ0 s hsIoo) hstay
    rw [hchain, hcv, hcv2]
    rfl
  -- ## the differential along the variation
  have hd2 : mfderiv 𝓘(ℝ, E) I (fun u : E => expMap cov x₀ u) (s • v) (s • w)
      = frameVector (I := I) x₀ ((extChartAt I x₀).symm ((Φ (s, 0)).1))
          (deriv (fun t : ℝ => (Φ (s, t)).1) 0) := by
    have hsv0_lt : ‖s • (v + (0:ℝ) • w)‖ < ρ₂ := by
      rw [show v + (0:ℝ) • w = v from by simp]
      exact hsv_lt
    have hdiff : MDifferentiableAt 𝓘(ℝ, E) I (fun u : E => expMap cov x₀ u) (s • (v + (0:ℝ) • w)) :=
      (hsm _ hsv0_lt).mdifferentiableAt (by norm_num)
    have hγ : HasDerivAt (fun a : ℝ => s • (v + a • w)) (s • w) 0 := by
      have h1 : HasDerivAt (fun a : ℝ => v + a • w) w 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).smul_const w |>.const_add v
      refine (h1.const_smul s).congr_of_eventuallyEq ?_
      exact Filter.EventuallyEq.of_eq (by funext a; rfl)
    have hchain := mfderiv_expMap_comp (cov := cov) x₀ (γ := fun a : ℝ => s • (v + a • w))
      (t := 0) (c' := s • w) hdiff hγ
    rw [show v + (0:ℝ) • w = v from by simp] at hchain
    have hev : (fun a : ℝ => expMap cov x₀ (s • (v + a • w))) =ᶠ[𝓝 0]
        (fun a : ℝ => (extChartAt I x₀).symm ((Φ (s, a)).1)) := by
      filter_upwards [Ioo_mem_nhds (by linarith : -δ < 0) hδ] with a ha
      exact hexp s hsabs a ha
    have hcv : curveVelocity (I := I) (fun a : ℝ => expMap cov x₀ (s • (v + a • w))) 0
        = curveVelocity (I := I) (fun a : ℝ => (extChartAt I x₀).symm ((Φ (s, a)).1)) 0 := by
      have h := hev.mfderiv_eq (I := 𝓘(ℝ)) (I' := I)
      rw [curveVelocity_apply, curveVelocity_apply, h]
      rfl
    have hu : HasDerivAt (fun a : ℝ => (Φ (s, a)).1)
        (deriv (fun a : ℝ => (Φ (s, a)).1) 0) 0 :=
      hasDerivAt_line ((hC s hsIoo).fst)
    have hstay : ∀ᶠ a in 𝓝 0, (Φ (s, a)).1 ∈ (extChartAt I x₀).target := by
      filter_upwards [Ioo_mem_nhds (by linarith : -δ < 0) hδ] with a ha
      exact htgt a ha s hsIoo
    have hcv2 := curveVelocity_extChartAt_symm (I := I) (x₀ := x₀)
      (u := fun a : ℝ => (Φ (s, a)).1) (t := 0)
      (v := deriv (fun a : ℝ => (Φ (s, a)).1) 0) hu (htgt 0 hδ0 s hsIoo) hstay
    rw [hchain, hcv, hcv2]
    rfl
  rw [hd1, hd2, chartGram_apply, ← hP]
  exact hcg

/-! ## Corollaries of Gauss's lemma -/

/-- **Gauss's lemma: `expMap` preserves the radial metric.**  The squared speed of the radial
geodesic `s ↦ expMap x₀ (s • v)` at `s` is the metric norm of `v` at the base point. -/
theorem gauss_lemma_radial_metric
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (x₀ : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ v : E, ‖v‖ < ρ → ∀ s : ℝ, 0 < s → s < 1 →
      inner ℝ (mfderiv 𝓘(ℝ, E) I (fun u : E => expMap cov x₀ u) (s • v) v)
        (mfderiv 𝓘(ℝ, E) I (fun u : E => expMap cov x₀ u) (s • v) v)
      = chartGram (I := I) x₀ x₀ v v := by
  obtain ⟨ρ, hρ, h⟩ := gauss_lemma (cov := cov) hmet htor x₀
  refine ⟨ρ, hρ, fun v hv s hs0 hs1 => ?_⟩
  have h1 := h v hv v s hs0 hs1
  have hA : mfderiv 𝓘(ℝ, E) I (fun u : E => expMap cov x₀ u) (s • v) (s • v)
      = s • mfderiv 𝓘(ℝ, E) I (fun u : E => expMap cov x₀ u) (s • v) v :=
    map_smul _ s v
  rw [hA, inner_smul_right] at h1
  exact mul_left_cancel₀ (ne_of_gt hs0) h1

/-- **Gauss's lemma, differential form.**  There is `ρ > 0` such that for every `u` with `‖u‖ < ρ`
and every `X`,
`⟪(d exp_{x₀})_u u, (d exp_{x₀})_u X⟫ = ⟪u, X⟫_{x₀}`,
where the scalar product on the right is the Riemannian metric at `x₀` (written through the chart
metric `chartGram`).  This is the form in which Gauss's lemma is used to prove the local
minimising property of geodesics. -/
theorem gauss_lemma_fderiv
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (x₀ : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ u : E, ‖u‖ < ρ → ∀ X : E,
      inner ℝ (mfderiv 𝓘(ℝ, E) I (fun w : E => expMap cov x₀ w) u u)
        (mfderiv 𝓘(ℝ, E) I (fun w : E => expMap cov x₀ w) u X)
      = chartGram (I := I) x₀ x₀ u X := by
  obtain ⟨ρ, hρ, h⟩ := gauss_lemma (cov := cov) hmet htor x₀
  refine ⟨ρ, hρ, fun u hu X => ?_⟩
  have huρ : ‖u‖ / ρ < 1 := (div_lt_one hρ).mpr hu
  set s : ℝ := (‖u‖ / ρ + 1) / 2 with hsdef
  have hsu : ‖u‖ / ρ < s := by rw [hsdef]; linarith
  have hs1 : s < 1 := by rw [hsdef]; linarith
  have hs0 : 0 < s := lt_of_le_of_lt (by positivity) hsu
  have hsne : s ≠ 0 := ne_of_gt hs0
  have hsv : ‖s⁻¹ • u‖ < ρ := by
    have h1 : ‖u‖ < s * ρ := (div_lt_iff₀ hρ).mp hsu
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs0), inv_mul_eq_div,
      div_lt_iff₀ hs0]
    linarith
  have hsvu : s • (s⁻¹ • u) = u := by rw [smul_smul, mul_inv_cancel₀ hsne, one_smul]
  have hsvX : s • (s⁻¹ • X) = X := by rw [smul_smul, mul_inv_cancel₀ hsne, one_smul]
  have hg := h (s⁻¹ • u) hsv (s⁻¹ • X) s hs0 hs1
  rw [hsvX] at hg
  generalize hD0 :
    (mfderiv 𝓘(ℝ, E) I (fun w : E => expMap cov x₀ w) (s • (s⁻¹ • u))) = D0 at hg
  have hstep : inner ℝ (D0 (s⁻¹ • u)) (D0 X) = s⁻¹ * inner ℝ (D0 u) (D0 X) := by
    have h1 : D0 (s⁻¹ • u) = s⁻¹ • D0 u := map_smul D0 s⁻¹ u
    calc inner ℝ (D0 (s⁻¹ • u)) (D0 X)
        = inner ℝ (s⁻¹ • D0 u) (D0 X) := by rw [h1]
      _ = s⁻¹ * inner ℝ (D0 u) (D0 X) := by
            rw [inner_smul_left, starRingEnd_apply, star_trivial]
  rw [hstep] at hg
  rw [chartGram_smul_fst, chartGram_smul_snd] at hg
  have h2 : s * (s⁻¹ * (s⁻¹ * chartGram (I := I) x₀ x₀ u X))
      = s⁻¹ * chartGram (I := I) x₀ x₀ u X := by
    rw [← mul_assoc, mul_inv_cancel₀ hsne, one_mul]
  rw [h2] at hg
  have hres : inner ℝ (D0 u) (D0 X) = chartGram (I := I) x₀ x₀ u X :=
    mul_left_cancel₀ (inv_ne_zero hsne) hg
  have hsvuT : (s • (s⁻¹ • u) : TangentSpace I x₀) = u := by
    rw [smul_smul, mul_inv_cancel₀ hsne, one_smul]
  rw [hsvuT] at hres
  have hb : mfderiv 𝓘(ℝ, E) I (fun w : E => expMap cov x₀ w) (s • (s⁻¹ • u))
      = mfderiv 𝓘(ℝ, E) I (fun w : E => expMap cov x₀ w) u :=
    mfderiv_congr_point (I := 𝓘(ℝ, E)) (I' := I) hsvu
  rw [← hb, hD0]
  exact hres

/-- **Gauss's lemma, orthogonality form.**  The differential of `expMap` along the variation is
orthogonal to the radial direction whenever the corresponding coordinate vectors are orthogonal at
the base point. -/
theorem gauss_lemma_orthogonal
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (x₀ : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ v w : E, ‖v‖ < ρ → chartGram (I := I) x₀ x₀ v w = 0 →
      ∀ s : ℝ, 0 < s → s < 1 →
      inner ℝ (mfderiv 𝓘(ℝ, E) I (fun u : E => expMap cov x₀ u) (s • v) v)
        (mfderiv 𝓘(ℝ, E) I (fun u : E => expMap cov x₀ u) (s • v) (s • w)) = 0 := by
  obtain ⟨ρ, hρ, h⟩ := gauss_lemma (cov := cov) hmet htor x₀
  exact ⟨ρ, hρ, fun v w hv hvw s hs0 hs1 => by rw [h v hv w s hs0 hs1, hvw, mul_zero]⟩

end

end Submission.Gauss
