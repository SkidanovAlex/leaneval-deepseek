import Mathlib
import Submission.Work.OddBound.LiftKit
import Submission.Work.OddBound.polygon.riemannianDist_eq_toReal
import Submission.Work.OddBound.polygonValue.Basic
import Submission.Work.OddBound.pvCrux.InterpAux
import Submission.Work.OddBound.pvCrux.edist_GExp_ray_sub
import Submission.Work.OddBound.pvCrux.gExp_joint_tendsto
import Submission.Work.OddBound.pvCrux.joint_inverse_continuity

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.OddBound.pvCrux

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]

/-- **The unique minimising tangent vector.**  For a point `τ` of `[0,1]`, the point `y τ` is inside
the injectivity ball of `x τ` (`hclose`), so there is a *unique* tangent vector `v` at `x τ` with
`GExp (x τ) v = y τ` and `d (x τ) (y τ) = ‖v‖`
(`Submission.InjRadius.exists_unique_GExp_of_injAtLeast`).  Outside `[0,1]` the value is set to `0`
(it is never used there: the injectivity radius gives no information without `hclose`). -/
noncomputable def minimisingVec (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    (htor : cov.torsion = 0) {ρ : ℝ}
    (hinj : ∀ q : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet q ρ)
    (x y : ℝ → M)
    (hclose : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      Manifold.riemannianEDist I (x τ) (y τ) < ENNReal.ofReal ρ)
    (τ : ℝ) : TangentSpace I (x τ) :=
  if hτ : τ ∈ Set.Icc (0 : ℝ) 1 then
    (Submission.InjRadius.exists_unique_GExp_of_injAtLeast (cov := cov) hmet htor
      (hinj (x τ)) (hclose τ hτ)).exists.choose
  else 0

/-- The defining properties of `minimisingVec` on `[0,1]`. -/
theorem minimisingVec_spec (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    (htor : cov.torsion = 0) {ρ : ℝ}
    (hinj : ∀ q : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet q ρ)
    (x y : ℝ → M)
    (hclose : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      Manifold.riemannianEDist I (x τ) (y τ) < ENNReal.ofReal ρ)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    Submission.GlobalExp.GExp (cov := cov) hmet (x τ) (minimisingVec hmet htor hinj x y hclose τ)
        = y τ ∧
      Manifold.riemannianEDist I (x τ) (y τ)
        = ENNReal.ofReal ‖minimisingVec hmet htor hinj x y hclose τ‖ := by
  have hspec := (Submission.InjRadius.exists_unique_GExp_of_injAtLeast (cov := cov) hmet htor
    (hinj (x τ)) (hclose τ hτ)).exists.choose_spec
  have hval : minimisingVec hmet htor hinj x y hclose τ
      = (Submission.InjRadius.exists_unique_GExp_of_injAtLeast (cov := cov) hmet htor
          (hinj (x τ)) (hclose τ hτ)).exists.choose := by
    change (dite (τ ∈ Set.Icc (0 : ℝ) 1)
      (fun hτ => (Submission.InjRadius.exists_unique_GExp_of_injAtLeast (cov := cov) hmet htor
        (hinj (x τ)) (hclose τ hτ)).exists.choose) (fun _ => 0)) = _
    rw [dif_pos hτ]
  rw [hval]
  exact hspec

/-- The norm of `minimisingVec` is the Riemannian distance of the two points. -/
theorem norm_minimisingVec (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    (htor : cov.torsion = 0) {ρ : ℝ}
    (hinj : ∀ q : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet q ρ)
    (x y : ℝ → M)
    (hclose : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      Manifold.riemannianEDist I (x τ) (y τ) < ENNReal.ofReal ρ)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    ‖minimisingVec hmet htor hinj x y hclose τ‖
      = Submission.Distance.riemannianDist (I := I) (x τ) (y τ) := by
  have hspec := (minimisingVec_spec (I := I) (cov := cov) hmet htor hinj x y hclose hτ).2
  rw [Work.OddBound.polygon.riemannianDist_eq_toReal (I := I) (x τ) (y τ), hspec,
    ENNReal.toReal_ofReal (norm_nonneg _)]

/-- Uniqueness: any vector with the two defining properties of the minimising vector agrees with
`minimisingVec`. -/
theorem eq_minimisingVec (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov)
    (htor : cov.torsion = 0) {ρ : ℝ}
    (hinj : ∀ q : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet q ρ)
    (x y : ℝ → M)
    (hclose : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      Manifold.riemannianEDist I (x τ) (y τ) < ENNReal.ofReal ρ)
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1) {v : TangentSpace I (x τ)}
    (hv : Submission.GlobalExp.GExp (cov := cov) hmet (x τ) v = y τ)
    (hvn : Manifold.riemannianEDist I (x τ) (y τ) = ENNReal.ofReal ‖v‖) :
    v = minimisingVec hmet htor hinj x y hclose τ := by
  have huniq := Submission.InjRadius.exists_unique_GExp_of_injAtLeast (cov := cov) hmet htor
    (hinj (x τ)) (hclose τ hτ)
  have hval : minimisingVec hmet htor hinj x y hclose τ = huniq.exists.choose := by
    change (dite (τ ∈ Set.Icc (0 : ℝ) 1)
      (fun hτ => (Submission.InjRadius.exists_unique_GExp_of_injAtLeast (cov := cov) hmet htor
        (hinj (x τ)) (hclose τ hτ)).exists.choose) (fun _ => 0)) = _
    rw [dif_pos hτ]
  rw [hval]
  exact huniq.unique ⟨hv, hvn⟩ huniq.exists.choose_spec

/-- **The Riemannian distance is continuous**, in the form of an arbitrary filter. -/
theorem tendsto_riemannianDist_of_tendsto' {α : Type*} {l : Filter α} {q r : α → M} {p r₀ : M}
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hq : Filter.Tendsto q l (𝓝 p)) (hr : Filter.Tendsto r l (𝓝 r₀)) :
    Filter.Tendsto (fun t => Submission.Distance.riemannianDist (I := I) (q t) (r t)) l
      (𝓝 (Submission.Distance.riemannianDist (I := I) p r₀)) := by
  classical
  haveI hcb : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  obtain ⟨v₀, -, hv₀⟩ :=
    Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (cov := cov) hmet htor p r₀
  have hBne : Manifold.riemannianEDist I p r₀ ≠ ⊤ := by
    rw [hv₀]; exact ENNReal.ofReal_ne_top
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε4 : (0 : ℝ) < ε / 4 := by positivity
  have hc4 : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 4) := ENNReal.ofReal_pos.mpr hε4
  have hevq : ∀ᶠ t in l, Manifold.riemannianEDist I p (q t) < ENNReal.ofReal (ε / 4) :=
    hq (Submission.EDist.eventually_riemannianEDist_lt (I := I) p hc4)
  have hevr : ∀ᶠ t in l, Manifold.riemannianEDist I r₀ (r t) < ENNReal.ofReal (ε / 4) :=
    hr (Submission.EDist.eventually_riemannianEDist_lt (I := I) r₀ hc4)
  filter_upwards [hevq, hevr] with t htq htr
  have hPne : Manifold.riemannianEDist I p (q t) ≠ ⊤ := ne_top_of_lt htq
  have hQne : Manifold.riemannianEDist I r₀ (r t) ≠ ⊤ := ne_top_of_lt htr
  have hPt : (Manifold.riemannianEDist I p (q t)).toReal ≤ ε / 4 := by
    have h1 := ENNReal.toReal_mono (ENNReal.ofReal_ne_top (r := ε / 4)) htq.le
    rwa [ENNReal.toReal_ofReal hε4.le] at h1
  have hQt : (Manifold.riemannianEDist I r₀ (r t)).toReal ≤ ε / 4 := by
    have h1 := ENNReal.toReal_mono (ENNReal.ofReal_ne_top (r := ε / 4)) htr.le
    rwa [ENNReal.toReal_ofReal hε4.le] at h1
  have t1 : Manifold.riemannianEDist I (q t) (r t)
      ≤ Manifold.riemannianEDist I p (q t) + Manifold.riemannianEDist I p (r t) := by
    have h := Manifold.riemannianEDist_triangle (I := I) (x := q t) (y := p) (z := r t)
    rwa [Manifold.riemannianEDist_comm (I := I) (x := q t) (y := p)] at h
  have t2 : Manifold.riemannianEDist I p (r t)
      ≤ Manifold.riemannianEDist I p r₀ + Manifold.riemannianEDist I r₀ (r t) :=
    Manifold.riemannianEDist_triangle (I := I) (x := p) (y := r₀) (z := r t)
  have t3 : Manifold.riemannianEDist I p (r t)
      ≤ Manifold.riemannianEDist I p (q t) + Manifold.riemannianEDist I (q t) (r t) :=
    Manifold.riemannianEDist_triangle (I := I) (x := p) (y := q t) (z := r t)
  have t4 : Manifold.riemannianEDist I p r₀
      ≤ Manifold.riemannianEDist I r₀ (r t) + Manifold.riemannianEDist I p (r t) := by
    have h := Manifold.riemannianEDist_triangle (I := I) (x := r₀) (y := r t) (z := p)
    rw [Manifold.riemannianEDist_comm (I := I) (x := r₀) (y := p),
      Manifold.riemannianEDist_comm (I := I) (x := r t) (y := p)] at h
    exact h
  have hle1 : Manifold.riemannianEDist I (q t) (r t)
      ≤ Manifold.riemannianEDist I p (q t) + Manifold.riemannianEDist I p r₀
        + Manifold.riemannianEDist I r₀ (r t) := by
    calc Manifold.riemannianEDist I (q t) (r t)
        ≤ Manifold.riemannianEDist I p (q t) + Manifold.riemannianEDist I p (r t) := t1
      _ ≤ Manifold.riemannianEDist I p (q t)
            + (Manifold.riemannianEDist I p r₀ + Manifold.riemannianEDist I r₀ (r t)) :=
          add_le_add le_rfl t2
      _ = Manifold.riemannianEDist I p (q t) + Manifold.riemannianEDist I p r₀
            + Manifold.riemannianEDist I r₀ (r t) := by rw [add_assoc]
  have hsum1 : Manifold.riemannianEDist I p (q t) + Manifold.riemannianEDist I p r₀
      + Manifold.riemannianEDist I r₀ (r t) ≠ ⊤ := by
    rw [ENNReal.add_ne_top, ENNReal.add_ne_top]
    exact ⟨⟨hPne, hBne⟩, hQne⟩
  have hAne : Manifold.riemannianEDist I (q t) (r t) ≠ ⊤ := ne_top_of_le_ne_top hsum1 hle1
  have hA1 : (Manifold.riemannianEDist I (q t) (r t)).toReal
      ≤ (Manifold.riemannianEDist I p r₀).toReal + ε / 2 := by
    have h1 : (Manifold.riemannianEDist I (q t) (r t)).toReal
        ≤ (Manifold.riemannianEDist I p (q t) + Manifold.riemannianEDist I p r₀
            + Manifold.riemannianEDist I r₀ (r t)).toReal := ENNReal.toReal_mono hsum1 hle1
    have h2 : (Manifold.riemannianEDist I p (q t) + Manifold.riemannianEDist I p r₀
        + Manifold.riemannianEDist I r₀ (r t)).toReal
        ≤ (Manifold.riemannianEDist I p (q t)).toReal
          + (Manifold.riemannianEDist I p r₀).toReal
          + (Manifold.riemannianEDist I r₀ (r t)).toReal := by
      refine le_trans ENNReal.toReal_add_le ?_
      exact add_le_add ENNReal.toReal_add_le le_rfl
    linarith
  have hle2 : Manifold.riemannianEDist I p r₀
      ≤ Manifold.riemannianEDist I p (q t) + Manifold.riemannianEDist I (q t) (r t)
        + Manifold.riemannianEDist I r₀ (r t) := by
    calc Manifold.riemannianEDist I p r₀
        ≤ Manifold.riemannianEDist I r₀ (r t) + Manifold.riemannianEDist I p (r t) := t4
      _ ≤ Manifold.riemannianEDist I r₀ (r t)
            + (Manifold.riemannianEDist I p (q t) + Manifold.riemannianEDist I (q t) (r t)) :=
          add_le_add le_rfl t3
      _ = Manifold.riemannianEDist I p (q t) + Manifold.riemannianEDist I (q t) (r t)
            + Manifold.riemannianEDist I r₀ (r t) := by
          rw [add_comm (Manifold.riemannianEDist I r₀ (r t))]
  have hsum2 : Manifold.riemannianEDist I p (q t) + Manifold.riemannianEDist I (q t) (r t)
      + Manifold.riemannianEDist I r₀ (r t) ≠ ⊤ := by
    rw [ENNReal.add_ne_top, ENNReal.add_ne_top]
    exact ⟨⟨hPne, hAne⟩, hQne⟩
  have hB2 : (Manifold.riemannianEDist I p r₀).toReal
      ≤ (Manifold.riemannianEDist I (q t) (r t)).toReal + ε / 2 := by
    have h1 : (Manifold.riemannianEDist I p r₀).toReal
        ≤ (Manifold.riemannianEDist I p (q t) + Manifold.riemannianEDist I (q t) (r t)
            + Manifold.riemannianEDist I r₀ (r t)).toReal := ENNReal.toReal_mono hsum2 hle2
    have h2 : (Manifold.riemannianEDist I p (q t) + Manifold.riemannianEDist I (q t) (r t)
        + Manifold.riemannianEDist I r₀ (r t)).toReal
        ≤ (Manifold.riemannianEDist I p (q t)).toReal
          + (Manifold.riemannianEDist I (q t) (r t)).toReal
          + (Manifold.riemannianEDist I r₀ (r t)).toReal := by
      refine le_trans ENNReal.toReal_add_le ?_
      exact add_le_add ENNReal.toReal_add_le le_rfl
    linarith
  rw [Work.OddBound.polygon.riemannianDist_eq_toReal (I := I) (q t) (r t),
    Work.OddBound.polygon.riemannianDist_eq_toReal (I := I) p r₀, Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- **The chart coordinates of the minimising vectors are continuous in the parameter.**

If `V τ` is the minimising vector from `x τ` to `y τ` (below the injectivity radius `ρ`) and `x, y`
are continuous, then in the chart at `x τ₀` the coordinate vectors of `V` tend to the coordinate
vector of `V τ₀` as `τ → τ₀` along `[0,1]`.

This is where the *uniform* injectivity radius is used: `Work.OddBound.polygonValue.
joint_inverse_continuity` says that close base points with close images have close coordinates, and
the norm bound `‖V τ‖ ≤ ρ' < ρ` used there holds near `τ₀` because `‖V τ‖ = d (x τ) (y τ)` is
continuous in `τ` (`tendsto_riemannianDist_of_tendsto'`). -/
theorem tendsto_coords_of_minimising
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {x y : ℝ → M} (hxc : Continuous x) (hyc : Continuous y)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hinj : ∀ q : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet q ρ)
    (hclose : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      Manifold.riemannianEDist I (x τ) (y τ) < ENNReal.ofReal ρ)
    (V : (τ : ℝ) → TangentSpace I (x τ))
    (hV : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      Submission.GlobalExp.GExp (cov := cov) hmet (x τ) (V τ) = y τ ∧
        Manifold.riemannianEDist I (x τ) (y τ) = ENNReal.ofReal ‖V τ‖)
    {τ₀ : ℝ} (hτ₀ : τ₀ ∈ Set.Icc (0 : ℝ) 1) :
    Filter.Tendsto
      (fun τ : ℝ =>
        (trivializationAt E (TangentSpace I) (x τ₀)).continuousLinearMapAt ℝ (x τ) (V τ))
      (𝓝[Set.Icc (0 : ℝ) 1] τ₀)
      (𝓝 ((trivializationAt E (TangentSpace I) (x τ₀)).continuousLinearMapAt ℝ (x τ₀) (V τ₀))) := by
  classical
  haveI hcb : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  -- a compact chart piece around `x τ₀`
  obtain ⟨Z, hZc, hx₀Z, hZsrc, e, hepos, -, hZeq⟩ :=
    Submission.GSField.exists_isCompact_subset_chart_source (I := I) (M := M) (x τ₀)
  have hZnhds : Z ∈ 𝓝 (x τ₀) := by
    rw [hZeq]
    exact (Submission.EDist.eventually_riemannianEDist_lt (I := I) (x τ₀) hepos).mono
      (fun y hy => hy.le)
  -- the injectivity radius bounds `‖V τ₀‖`
  have hLρ : ‖V τ₀‖ < ρ := by
    have h3 := hclose τ₀ hτ₀
    rw [(hV τ₀ hτ₀).2] at h3
    exact (ENNReal.ofReal_lt_ofReal_iff hρ).mp h3
  set ρ' : ℝ := (‖V τ₀‖ + ρ) / 2 with hρ'def
  have hρ'pos : 0 < ρ' := by rw [hρ'def]; linarith [norm_nonneg (V τ₀), hρ]
  have hρ'ρ : ρ' < ρ := by rw [hρ'def]; linarith
  have hLρ' : ‖V τ₀‖ < ρ' := by rw [hρ'def]; linarith
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδpos, hδspec⟩ := joint_inverse_continuity (I := I) (cov := cov) hmet htor hZsrc hZc
    hρ'pos hρ'ρ (fun q _ => hinj q) hε
  -- eventual properties
  have h1 : ∀ᶠ τ in 𝓝[Set.Icc (0 : ℝ) 1] τ₀, x τ ∈ Z :=
    (hxc.continuousAt.continuousWithinAt).eventually hZnhds
  have h2 : ∀ᶠ τ in 𝓝[Set.Icc (0 : ℝ) 1] τ₀, ‖V τ‖ ≤ ρ' := by
    have hdist : Filter.Tendsto (fun τ => Submission.Distance.riemannianDist (I := I) (x τ) (y τ))
        (𝓝[Set.Icc (0 : ℝ) 1] τ₀)
        (𝓝 (Submission.Distance.riemannianDist (I := I) (x τ₀) (y τ₀))) :=
      tendsto_riemannianDist_of_tendsto' (I := I) (cov := cov) hmet htor
        hxc.continuousAt.continuousWithinAt hyc.continuousAt.continuousWithinAt
    have hlim : Submission.Distance.riemannianDist (I := I) (x τ₀) (y τ₀) = ‖V τ₀‖ := by
      rw [Work.OddBound.polygon.riemannianDist_eq_toReal (I := I) (x τ₀) (y τ₀), (hV τ₀ hτ₀).2,
        ENNReal.toReal_ofReal (norm_nonneg _)]
    rw [hlim] at hdist
    filter_upwards [hdist.eventually (eventually_lt_nhds hLρ'), self_mem_nhdsWithin] with τ hlt hτmem
    have hv : ‖V τ‖ = Submission.Distance.riemannianDist (I := I) (x τ) (y τ) := by
      rw [Work.OddBound.polygon.riemannianDist_eq_toReal (I := I) (x τ) (y τ), (hV τ hτmem).2,
        ENNReal.toReal_ofReal (norm_nonneg _)]
    rw [hv]
    exact hlt.le
  have h3 : ∀ᶠ τ in 𝓝[Set.Icc (0 : ℝ) 1] τ₀,
      ‖(extChartAt I (x τ₀)) (x τ) - (extChartAt I (x τ₀)) (x τ₀)‖ < δ := by
    have hcz : ContinuousAt (extChartAt I (x τ₀)) (x τ₀) :=
      continuousAt_extChartAt' (I := I) (x := x τ₀) (mem_extChartAt_source (I := I) (x τ₀))
    have hcomp : ContinuousAt ((extChartAt I (x τ₀)) ∘ x) τ₀ :=
      hcz.comp hxc.continuousAt
    have hball := (hcomp.continuousWithinAt (s := Set.Icc (0 : ℝ) 1)).eventually
      (Metric.ball_mem_nhds ((extChartAt I (x τ₀)) (x τ₀)) hδpos)
    simpa [Metric.mem_ball, dist_eq_norm, Function.comp_apply] using hball
  have h4 : ∀ᶠ τ in 𝓝[Set.Icc (0 : ℝ) 1] τ₀,
      Manifold.riemannianEDist I
        (Submission.GlobalExp.GExp (cov := cov) hmet (x τ)
          (Submission.Geodesic.frameVector (I := I) (x τ₀) (x τ)
            ((trivializationAt E (TangentSpace I) (x τ₀)).continuousLinearMapAt ℝ (x τ) (V τ))))
        (Submission.GlobalExp.GExp (cov := cov) hmet (x τ₀)
          (Submission.Geodesic.frameVector (I := I) (x τ₀) (x τ₀)
            ((trivializationAt E (TangentSpace I) (x τ₀)).continuousLinearMapAt ℝ (x τ₀)
              (V τ₀))))
        < ENNReal.ofReal δ := by
    have hev := (hyc.continuousAt.continuousWithinAt (s := Set.Icc (0 : ℝ) 1)).eventually
      (Submission.EDist.eventually_riemannianEDist_lt (I := I) (y τ₀)
        (ENNReal.ofReal_pos.mpr hδpos))
    filter_upwards [hev, h1, self_mem_nhdsWithin] with τ himg hτZ hτmem
    have hsrcτ : x τ ∈ (extChartAt I (x τ₀)).source := by simpa using hZsrc hτZ
    have hsrc₀ : x τ₀ ∈ (extChartAt I (x τ₀)).source := mem_extChartAt_source (I := I) (x τ₀)
    rw [Submission.GExpFlow.frameVector_clm (I := I) hsrcτ (V τ),
      Submission.GExpFlow.frameVector_clm (I := I) hsrc₀ (V τ₀),
      (hV τ hτmem).1, (hV τ₀ hτ₀).1, Manifold.riemannianEDist_comm (I := I) (x := y τ) (y := y τ₀)]
    exact himg
  filter_upwards [h1, h2, h3, h4] with τ hτZ hτle hτchart hτimg
  have hsrcτ : x τ ∈ (extChartAt I (x τ₀)).source := by simpa using hZsrc hτZ
  have hsrc₀ : x τ₀ ∈ (extChartAt I (x τ₀)).source := mem_extChartAt_source (I := I) (x τ₀)
  have hn1 : ‖Submission.Geodesic.frameVector (I := I) (x τ₀) (x τ)
      ((trivializationAt E (TangentSpace I) (x τ₀)).continuousLinearMapAt ℝ (x τ) (V τ))‖ ≤ ρ' := by
    rw [Submission.GExpFlow.frameVector_clm (I := I) hsrcτ (V τ)]
    exact hτle
  have hn2 : ‖Submission.Geodesic.frameVector (I := I) (x τ₀) (x τ₀)
      ((trivializationAt E (TangentSpace I) (x τ₀)).continuousLinearMapAt ℝ (x τ₀) (V τ₀))‖ ≤ ρ' := by
    rw [Submission.GExpFlow.frameVector_clm (I := I) hsrc₀ (V τ₀)]
    exact hLρ'.le
  rw [dist_eq_norm]
  exact hδspec (x τ) hτZ (x τ₀) hx₀Z _ _ hn1 hn2 hτchart hτimg

/-- **Joint continuity of the minimising interpolation** (assembly): once the chart coordinates of
the minimising vectors are continuous in the parameter (`tendsto_coords_of_minimising`), the joint
continuity of `(q, a) ↦ GExp q (frameVector z₀ q a)`
(`Work.OddBound.polygonValue.gExp_joint_tendsto`, which is
`Submission.GExpJointPt.tendsto_GExp_frameVector` for an arbitrary countably generated filter)
transfers it to `S r τ = GExp (x τ) (r • V τ)`. -/
theorem continuousOn_interp_of_minimising
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {x y : ℝ → M} (hxc : Continuous x) (hyc : Continuous y)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hinj : ∀ q : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet q ρ)
    (hclose : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      Manifold.riemannianEDist I (x τ) (y τ) < ENNReal.ofReal ρ)
    (V : (τ : ℝ) → TangentSpace I (x τ))
    (hV : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      Submission.GlobalExp.GExp (cov := cov) hmet (x τ) (V τ) = y τ ∧
        Manifold.riemannianEDist I (x τ) (y τ) = ENNReal.ofReal ‖V τ‖) :
    ContinuousOn
      (fun u : ℝ × ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (x u.2) (u.1 • V u.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
  rintro ⟨r₀, τ₀⟩ ⟨hr₀, hτ₀⟩
  -- the chart at `x τ₀` and the coordinate family
  have hu : Filter.Tendsto
      (fun τ : ℝ =>
        (trivializationAt E (TangentSpace I) (x τ₀)).continuousLinearMapAt ℝ (x τ) (V τ))
      (𝓝[Set.Icc (0 : ℝ) 1] τ₀)
      (𝓝 ((trivializationAt E (TangentSpace I) (x τ₀)).continuousLinearMapAt ℝ (x τ₀) (V τ₀))) :=
    tendsto_coords_of_minimising (I := I) (cov := cov) hmet htor hxc hyc hρ hinj hclose V hV hτ₀
  have hsrc₀ : x τ₀ ∈ (chartAt H (x τ₀)).source := mem_chart_source H (x τ₀)
  -- the projections and the product map
  have hproj : Filter.Tendsto (fun u : ℝ × ℝ => u.2)
      (𝓝[Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1] (r₀, τ₀)) (𝓝[Set.Icc (0 : ℝ) 1] τ₀) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨(continuous_snd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds),
      mem_of_superset self_mem_nhdsWithin (fun u hu => hu.2)⟩
  have hfirst : Filter.Tendsto (fun u : ℝ × ℝ => u.1)
      (𝓝[Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1] (r₀, τ₀)) (𝓝 r₀) :=
    continuous_fst.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hu' : Filter.Tendsto
      (fun u : ℝ × ℝ => (trivializationAt E (TangentSpace I) (x τ₀)).continuousLinearMapAt ℝ (x u.2) (V u.2))
      (𝓝[Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1] (r₀, τ₀))
      (𝓝 ((trivializationAt E (TangentSpace I) (x τ₀)).continuousLinearMapAt ℝ (x τ₀) (V τ₀))) :=
    hu.comp hproj
  have hxu : Filter.Tendsto x (𝓝[Set.Icc (0 : ℝ) 1] τ₀) (𝓝 (x τ₀)) :=
    (show Filter.Tendsto x (𝓝 τ₀) (𝓝 (x τ₀)) from hxc.continuousAt).mono_left nhdsWithin_le_nhds
  have hq : Filter.Tendsto (fun u : ℝ × ℝ => x u.2)
      (𝓝[Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1] (r₀, τ₀)) (𝓝 (x τ₀)) := hxu.comp hproj
  have ha : Filter.Tendsto
      (fun u : ℝ × ℝ =>
        u.1 • (trivializationAt E (TangentSpace I) (x τ₀)).continuousLinearMapAt ℝ (x u.2) (V u.2))
      (𝓝[Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1] (r₀, τ₀))
      (𝓝 (r₀ • (trivializationAt E (TangentSpace I) (x τ₀)).continuousLinearMapAt ℝ (x τ₀)
        (V τ₀))) := hfirst.smul hu'
  have hmain := gExp_joint_tendsto (I := I) (cov := cov) hmet htor hsrc₀ hq ha
  -- the chart identification
  have hchartsrc : ∀ᶠ u in 𝓝[Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1] (r₀, τ₀),
      x u.2 ∈ (chartAt H (x τ₀)).source :=
    hq.eventually ((chartAt H (x τ₀)).open_source.mem_nhds (mem_chart_source H (x τ₀)))
  have hev : (fun u : ℝ × ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (x u.2)
        (Submission.Geodesic.frameVector (I := I) (x τ₀) (x u.2)
          (u.1 • (trivializationAt E (TangentSpace I) (x τ₀)).continuousLinearMapAt ℝ (x u.2)
            (V u.2))))
      =ᶠ[𝓝[Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1] (r₀, τ₀)]
      (fun u : ℝ × ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (x u.2) (u.1 • V u.2)) := by
    filter_upwards [hchartsrc] with u hu_src
    have hsrc : x u.2 ∈ (extChartAt I (x τ₀)).source := by
      rw [extChartAt_source]; exact hu_src
    rw [Submission.Geodesic.frameVector_smul,
      Submission.GExpFlow.frameVector_clm (I := I) hsrc (V u.2)]
  have hlim : Submission.GlobalExp.GExp (cov := cov) hmet (x τ₀)
      (Submission.Geodesic.frameVector (I := I) (x τ₀) (x τ₀)
        (r₀ • (trivializationAt E (TangentSpace I) (x τ₀)).continuousLinearMapAt ℝ (x τ₀)
          (V τ₀)))
      = Submission.GlobalExp.GExp (cov := cov) hmet (x τ₀) (r₀ • V τ₀) := by
    have hsrc : x τ₀ ∈ (extChartAt I (x τ₀)).source := mem_extChartAt_source (I := I) (x τ₀)
    rw [Submission.Geodesic.frameVector_smul,
      Submission.GExpFlow.frameVector_clm (I := I) hsrc (V τ₀)]
  rw [hlim] at hmain
  exact hmain.congr' hev

/-- **Continuity of the minimising interpolation between moving nearby points.**

For continuous families `x, y : ℝ → M` with `d (x τ) (y τ) < ρ` on `[0,1]`, where `ρ` is a uniform
lower bound for the injectivity radius, there is a *jointly continuous* family
`S : ℝ → ℝ → M` whose `τ`-slice `r ↦ S r τ` is the minimising geodesic from `x τ` to `y τ`
parametrised proportionally to arclength (so constant speed `d (x τ) (y τ)`), with the arclength
identifications at `r = 0`, `r = 1` and the distance formulas.  The family is *the* natural one,
`S r τ = GExp (x τ) (r • W τ)` for the unique minimising vector `W τ`, hence is canonical.

Proof route: fix `τ₀` and a chart `z₀` at `x τ₀` with a compact piece `Z` containing `x τ₀` in its
interior; write `W τ = frameVector z₀ (x τ) (u τ)`.  The coordinate vectors `u τ` are bounded
(by `‖W τ‖ / √λ`, `λ` the Gram lower bound on `Z`), so a sequentially compact argument on a
convergent subsequence `u_{n_k} → u∞` gives, using the *joint* continuity of
`(q,u) ↦ GExp (cov := cov) hmet q (frameVector z₀ q u)` on `Z × E` (for a pointwise version see
`Submission.GSField`) and continuity of the chart Gram in the base point, that
`GExp (x τ₀) (frameVector z₀ (x τ₀) u∞) = y τ₀` and `‖frameVector z₀ (x τ₀) u∞‖ = d (x τ₀) (y τ₀)`,
so that vector is minimising from `x τ₀` to `y τ₀`, hence (uniqueness below the injectivity radius,
`Submission.SegmentDomain.injOn_GExp_segmentDomain` /
`Submission.SegmentDomain.exists_unique_segmentDomain_vec`) equals `W τ₀`.  Hence `u τ → u τ₀` along
every sequence, which is the required continuity (the fibre-norm version is
`Submission.InjRadius`/`Submission.SegmentDomain` bookkeeping; the `riemannianEDist`-to-`riemannianDist`
bridge is `Work.OddBound.polygon.riemannianDist_eq_toReal`). -/
theorem continuousMinimisingInterp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {x y : ℝ → M} (hxc : Continuous x) (hyc : Continuous y)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hinj : ∀ q : M, Submission.InjRadius.InjAtLeast (I := I) (cov := cov) hmet q ρ)
    (hclose : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      Submission.Distance.riemannianDist (I := I) (x τ) (y τ) < ρ) :
    ∃ S : ℝ → ℝ → M,
      ContinuousOn (fun u : ℝ × ℝ => S u.1 u.2)
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, S 0 τ = x τ) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, S 1 τ = y τ) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1,
        ContMDiffOn 𝓘(ℝ) I 1 (fun r : ℝ => S r τ) (Set.Icc (0 : ℝ) 1)) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
        Submission.Length.curveLength (I := I) (fun r : ℝ => S r τ) a b
          = (b - a) * Submission.Distance.riemannianDist (I := I) (x τ) (y τ)) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ r ∈ Set.Icc (0 : ℝ) 1,
        Manifold.riemannianEDist I (x τ) (S r τ) = ENNReal.ofReal
          (r * Submission.Distance.riemannianDist (I := I) (x τ) (y τ))) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ r ∈ Set.Icc (0 : ℝ) 1,
        Manifold.riemannianEDist I (S r τ) (y τ) = ENNReal.ofReal
          ((1 - r) * Submission.Distance.riemannianDist (I := I) (x τ) (y τ))) := by
  classical
  -- the extended-distance form of the hypothesis (Hopf--Rinow makes it equivalent below `ρ`)
  have hclose' : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      Manifold.riemannianEDist I (x τ) (y τ) < ENNReal.ofReal ρ :=
    fun τ hτ => edist_lt_of_riemannianDist_lt (I := I) (cov := cov) hmet htor hρ (hclose τ hτ)
  -- the family of minimising vectors
  let W : (τ : ℝ) → TangentSpace I (x τ) := fun τ =>
    minimisingVec (I := I) (cov := cov) hmet htor hinj x y hclose' τ
  have hWspec : ∀ τ (hτ : τ ∈ Set.Icc (0 : ℝ) 1),
      Submission.GlobalExp.GExp (cov := cov) hmet (x τ) (W τ) = y τ ∧
        Manifold.riemannianEDist I (x τ) (y τ) = ENNReal.ofReal ‖W τ‖ := by
    intro τ hτ
    dsimp only [W]
    exact minimisingVec_spec (I := I) (cov := cov) hmet htor hinj x y hclose' hτ
  have hWn : ∀ τ (hτ : τ ∈ Set.Icc (0 : ℝ) 1),
      ‖W τ‖ = Submission.Distance.riemannianDist (I := I) (x τ) (y τ) := by
    intro τ hτ
    dsimp only [W]
    exact norm_minimisingVec (I := I) (cov := cov) hmet htor hinj x y hclose' hτ
  have hWle : ∀ τ (hτ : τ ∈ Set.Icc (0 : ℝ) 1), ‖W τ‖ ≤ ρ := by
    intro τ hτ
    rw [hWn τ hτ]
    exact (hclose τ hτ).le
  refine ⟨fun r τ => Submission.GlobalExp.GExp (cov := cov) hmet (x τ) (r • W τ),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show ContinuousOn
      (fun u : ℝ × ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (x u.2) (u.1 • W u.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)
    exact continuousOn_interp_of_minimising (I := I) (cov := cov) hmet htor hxc hyc hρ
      hinj hclose' W hWspec
  · intro τ hτ
    show Submission.GlobalExp.GExp (cov := cov) hmet (x τ) (0 • W τ) = x τ
    rw [zero_smul, Submission.GlobalExp.GExp_zero]
  · intro τ hτ
    show Submission.GlobalExp.GExp (cov := cov) hmet (x τ) (1 • W τ) = y τ
    rw [one_smul]
    exact (hWspec τ hτ).1
  · intro τ hτ
    show ContMDiffOn 𝓘(ℝ) I 1
      (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (x τ) (r • W τ))
      (Set.Icc (0 : ℝ) 1)
    exact contMDiffOn_GExp_ray (I := I) (cov := cov) hmet (x τ) (W τ)
  · intro τ hτ a b ha hab hb
    show Submission.Length.curveLength (I := I)
      (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet (x τ) (r • W τ)) a b
      = (b - a) * Submission.Distance.riemannianDist (I := I) (x τ) (y τ)
    rw [curveLength_GExp_ray (I := I) (cov := cov) hmet (x τ) (W τ) hab, hWn τ hτ]
  · intro τ hτ r hr
    show Manifold.riemannianEDist I (x τ)
      (Submission.GlobalExp.GExp (cov := cov) hmet (x τ) (r • W τ))
      = ENNReal.ofReal (r * Submission.Distance.riemannianDist (I := I) (x τ) (y τ))
    have h := edist_GExp_ray_sub (I := I) (cov := cov) hmet htor (hinj (x τ)) (v := W τ)
      (hWle τ hτ) (a := 0) (b := r) (le_refl 0) hr.1 hr.2
    rwa [zero_smul, Submission.GlobalExp.GExp_zero, sub_zero, hWn τ hτ] at h
  · intro τ hτ r hr
    show Manifold.riemannianEDist I
      (Submission.GlobalExp.GExp (cov := cov) hmet (x τ) (r • W τ)) (y τ)
      = ENNReal.ofReal ((1 - r) * Submission.Distance.riemannianDist (I := I) (x τ) (y τ))
    have h := edist_GExp_ray_sub (I := I) (cov := cov) hmet htor (hinj (x τ)) (v := W τ)
      (hWle τ hτ) (a := r) (b := 1) hr.1 hr.2 le_rfl
    rwa [one_smul, (hWspec τ hτ).1, hWn τ hτ] at h

end Work.OddBound.pvCrux
