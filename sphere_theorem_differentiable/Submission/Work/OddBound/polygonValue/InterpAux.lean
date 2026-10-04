import Mathlib
import Submission.Work.OddBound.LiftKit
import Submission.Work.OddBound.polygon.riemannianDist_eq_toReal

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Auxiliary lemmas for the continuity of the minimising interpolation

Small, independent facts used by `Work.OddBound.polygonValue.continuousMinimisingInterp`:

* `curveLength_GExp_ray` — the ray `r ↦ GExp p (r • v)` has length `(b - a) * ‖v‖` over `[a,b]`
  (constant speed `‖v‖`, also for `v = 0`);
* `contMDiffOn_GExp_ray` — the same ray is `C¹` on `[0,1]`;
* `edist_lt_of_riemannianDist_lt` — the bridge from `Submission.Distance.riemannianDist` to
  Mathlib's `riemannianEDist` *below* a radius, via Hopf–Rinow (which bounds the extended distance);
* `tendsto_riemannianDist_of_tendsto_of_metricCompatible` — **the Riemannian distance is continuous**: if `q n → p` and
  `r n → r₀` then `d (q n) (r n) → d p r₀`.  This is the ingredient that lets the norm
  `‖W τ‖ = d (x τ) (y τ)` of the minimising vector be passed to the limit.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval

namespace Work.OddBound.polygonValue

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]

noncomputable section

/-- The Riemannian length of the ray `r ↦ GExp p (r • v)` over `[a,b]` is `(b - a) * ‖v‖`. -/
theorem curveLength_GExp_ray (hmet : IsMetricCompatible cov) (p : M) (v : TangentSpace I p)
    {a b : ℝ} (hab : a ≤ b) :
    Submission.Length.curveLength (I := I)
      (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (r • v)) a b
      = (b - a) * ‖v‖ := by
  rcases eq_or_ne v 0 with hv | hv
  · subst hv
    have hconst : (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (r • (0 : TangentSpace I p)))
        = fun _ : ℝ => p := by
      funext r
      rw [smul_zero, Submission.GlobalExp.GExp_zero]
    rw [hconst, Submission.Length.curveLength_const, norm_zero, mul_zero]
  · rw [Submission.BrokenLength.curveLength_GExp_ray (cov := cov) hmet p hv hab, mul_comm]

/-- The ray `r ↦ GExp p (r • v)` is `C¹` on `[0,1]`. -/
theorem contMDiffOn_GExp_ray (hmet : IsMetricCompatible cov) (p : M) (v : TangentSpace I p) :
    ContMDiffOn 𝓘(ℝ) I 1 (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (r • v))
      (Set.Icc (0 : ℝ) 1) := by
  rcases eq_or_ne v 0 with hv | hv
  · subst hv
    have hconst : (fun r : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet p (r • (0 : TangentSpace I p)))
        = fun _ : ℝ => p := by
      funext r
      rw [smul_zero, Submission.GlobalExp.GExp_zero]
    rw [hconst]
    exact contMDiffOn_const
  · exact (Submission.ConjEnergy.contMDiff_GExp_smul (cov := cov) hmet p hv).contMDiffOn.of_le
      (by norm_num)

/-- **Below a radius, the piecewise-path distance and the extended distance agree in the strong
form** `edist < ofReal ρ` from `riemannianDist < ρ`.  The extended distance is finite by
Hopf–Rinow, so `riemannianDist = (riemannianEDist).toReal` can be inverted. -/
theorem edist_lt_of_riemannianDist_lt (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p q : M} {ρ : ℝ} (hρ : 0 < ρ)
    (h : Submission.Distance.riemannianDist (I := I) p q < ρ) :
    Manifold.riemannianEDist I p q < ENNReal.ofReal ρ := by
  obtain ⟨v, -, hv⟩ :=
    Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (cov := cov) hmet htor p q
  rw [Work.OddBound.polygon.riemannianDist_eq_toReal (I := I) p q, hv,
    ENNReal.toReal_ofReal (norm_nonneg v)] at h
  rw [hv, ENNReal.ofReal_lt_ofReal_iff hρ]
  exact h

/-- **The Riemannian distance is continuous.**  If `q n → p` and `r n → r₀`, then
`d (q n) (r n) → d p r₀`.

Proof: the extended distances tend to zero along a convergent sequence near a point
(`Submission.EDist.eventually_riemannianEDist_lt`), and the triangle inequality for
`Manifold.riemannianEDist` turns the two limits into the two-sided bound
`|d (q n) (r n) - d p r₀| ≤ d (q n) p + d r₀ (r n)`. -/
theorem tendsto_riemannianDist_of_tendsto_of_metricCompatible (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {q r : ℕ → M} {p r₀ : M} (hq : Filter.Tendsto q atTop (𝓝 p))
    (hr : Filter.Tendsto r atTop (𝓝 r₀)) :
    Filter.Tendsto (fun n => Submission.Distance.riemannianDist (I := I) (q n) (r n)) atTop
      (𝓝 (Submission.Distance.riemannianDist (I := I) p r₀)) := by
  classical
  haveI hcb : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  obtain ⟨v₀, -, hv₀⟩ :=
    Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (cov := cov) hmet htor p r₀
  have hBne : Manifold.riemannianEDist I p r₀ ≠ ⊤ := by
    rw [hv₀]; exact ENNReal.ofReal_ne_top
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε4 : (0 : ℝ) < ε / 4 := by positivity
  have hc4 : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / 4) := ENNReal.ofReal_pos.mpr hε4
  have hevq : ∀ᶠ n in atTop, Manifold.riemannianEDist I p (q n) < ENNReal.ofReal (ε / 4) :=
    hq (Submission.EDist.eventually_riemannianEDist_lt (I := I) p hc4)
  have hevr : ∀ᶠ n in atTop, Manifold.riemannianEDist I r₀ (r n) < ENNReal.ofReal (ε / 4) :=
    hr (Submission.EDist.eventually_riemannianEDist_lt (I := I) r₀ hc4)
  have hgoal : ∀ᶠ n in atTop, |Submission.Distance.riemannianDist (I := I) (q n) (r n)
      - Submission.Distance.riemannianDist (I := I) p r₀| < ε := by
    filter_upwards [hevq, hevr] with n hnq hnr
    have hPne : Manifold.riemannianEDist I p (q n) ≠ ⊤ := ne_top_of_lt hnq
    have hQne : Manifold.riemannianEDist I r₀ (r n) ≠ ⊤ := ne_top_of_lt hnr
    have hPt : (Manifold.riemannianEDist I p (q n)).toReal ≤ ε / 4 := by
      have h1 := ENNReal.toReal_mono (ENNReal.ofReal_ne_top (r := ε / 4)) hnq.le
      rwa [ENNReal.toReal_ofReal hε4.le] at h1
    have hQt : (Manifold.riemannianEDist I r₀ (r n)).toReal ≤ ε / 4 := by
      have h1 := ENNReal.toReal_mono (ENNReal.ofReal_ne_top (r := ε / 4)) hnr.le
      rwa [ENNReal.toReal_ofReal hε4.le] at h1
    -- the two triangle inequalities
    have t1 : Manifold.riemannianEDist I (q n) (r n)
        ≤ Manifold.riemannianEDist I p (q n) + Manifold.riemannianEDist I p (r n) := by
      have h := Manifold.riemannianEDist_triangle (I := I) (x := q n) (y := p) (z := r n)
      rwa [Manifold.riemannianEDist_comm (I := I) (x := q n) (y := p)] at h
    have t2 : Manifold.riemannianEDist I p (r n)
        ≤ Manifold.riemannianEDist I p r₀ + Manifold.riemannianEDist I r₀ (r n) :=
      Manifold.riemannianEDist_triangle (I := I) (x := p) (y := r₀) (z := r n)
    have t3 : Manifold.riemannianEDist I p (r n)
        ≤ Manifold.riemannianEDist I p (q n) + Manifold.riemannianEDist I (q n) (r n) :=
      Manifold.riemannianEDist_triangle (I := I) (x := p) (y := q n) (z := r n)
    have t4 : Manifold.riemannianEDist I p r₀
        ≤ Manifold.riemannianEDist I r₀ (r n) + Manifold.riemannianEDist I p (r n) := by
      have h := Manifold.riemannianEDist_triangle (I := I) (x := r₀) (y := r n) (z := p)
      rw [Manifold.riemannianEDist_comm (I := I) (x := r₀) (y := p),
        Manifold.riemannianEDist_comm (I := I) (x := r n) (y := p)] at h
      exact h
    -- `A ≤ P + B + Q`
    have hle1 : Manifold.riemannianEDist I (q n) (r n)
        ≤ Manifold.riemannianEDist I p (q n) + Manifold.riemannianEDist I p r₀
          + Manifold.riemannianEDist I r₀ (r n) := by
      calc Manifold.riemannianEDist I (q n) (r n)
          ≤ Manifold.riemannianEDist I p (q n) + Manifold.riemannianEDist I p (r n) := t1
        _ ≤ Manifold.riemannianEDist I p (q n)
              + (Manifold.riemannianEDist I p r₀ + Manifold.riemannianEDist I r₀ (r n)) :=
            add_le_add le_rfl t2
        _ = Manifold.riemannianEDist I p (q n) + Manifold.riemannianEDist I p r₀
              + Manifold.riemannianEDist I r₀ (r n) := by rw [add_assoc]
    have hsum1 : Manifold.riemannianEDist I p (q n) + Manifold.riemannianEDist I p r₀
        + Manifold.riemannianEDist I r₀ (r n) ≠ ⊤ := by
      rw [ENNReal.add_ne_top, ENNReal.add_ne_top]
      exact ⟨⟨hPne, hBne⟩, hQne⟩
    have hAne : Manifold.riemannianEDist I (q n) (r n) ≠ ⊤ := ne_top_of_le_ne_top hsum1 hle1
    have hA1 : (Manifold.riemannianEDist I (q n) (r n)).toReal
        ≤ (Manifold.riemannianEDist I p r₀).toReal + ε / 2 := by
      have h1 : (Manifold.riemannianEDist I (q n) (r n)).toReal
          ≤ (Manifold.riemannianEDist I p (q n) + Manifold.riemannianEDist I p r₀
              + Manifold.riemannianEDist I r₀ (r n)).toReal := ENNReal.toReal_mono hsum1 hle1
      have h2 : (Manifold.riemannianEDist I p (q n) + Manifold.riemannianEDist I p r₀
          + Manifold.riemannianEDist I r₀ (r n)).toReal
          ≤ (Manifold.riemannianEDist I p (q n)).toReal
            + (Manifold.riemannianEDist I p r₀).toReal
            + (Manifold.riemannianEDist I r₀ (r n)).toReal := by
        refine le_trans ENNReal.toReal_add_le ?_
        exact add_le_add ENNReal.toReal_add_le le_rfl
      linarith
    -- `B ≤ P + A + Q`
    have hle2 : Manifold.riemannianEDist I p r₀
        ≤ Manifold.riemannianEDist I p (q n) + Manifold.riemannianEDist I (q n) (r n)
          + Manifold.riemannianEDist I r₀ (r n) := by
      calc Manifold.riemannianEDist I p r₀
          ≤ Manifold.riemannianEDist I r₀ (r n) + Manifold.riemannianEDist I p (r n) := t4
        _ ≤ Manifold.riemannianEDist I r₀ (r n)
              + (Manifold.riemannianEDist I p (q n) + Manifold.riemannianEDist I (q n) (r n)) :=
            add_le_add le_rfl t3
        _ = Manifold.riemannianEDist I p (q n) + Manifold.riemannianEDist I (q n) (r n)
              + Manifold.riemannianEDist I r₀ (r n) := by
            rw [add_comm (Manifold.riemannianEDist I r₀ (r n))]
    have hsum2 : Manifold.riemannianEDist I p (q n) + Manifold.riemannianEDist I (q n) (r n)
        + Manifold.riemannianEDist I r₀ (r n) ≠ ⊤ := by
      rw [ENNReal.add_ne_top, ENNReal.add_ne_top]
      exact ⟨⟨hPne, hAne⟩, hQne⟩
    have hB2 : (Manifold.riemannianEDist I p r₀).toReal
        ≤ (Manifold.riemannianEDist I (q n) (r n)).toReal + ε / 2 := by
      have h1 : (Manifold.riemannianEDist I p r₀).toReal
          ≤ (Manifold.riemannianEDist I p (q n) + Manifold.riemannianEDist I (q n) (r n)
              + Manifold.riemannianEDist I r₀ (r n)).toReal := ENNReal.toReal_mono hsum2 hle2
      have h2 : (Manifold.riemannianEDist I p (q n) + Manifold.riemannianEDist I (q n) (r n)
          + Manifold.riemannianEDist I r₀ (r n)).toReal
          ≤ (Manifold.riemannianEDist I p (q n)).toReal
            + (Manifold.riemannianEDist I (q n) (r n)).toReal
            + (Manifold.riemannianEDist I r₀ (r n)).toReal := by
        refine le_trans ENNReal.toReal_add_le ?_
        exact add_le_add ENNReal.toReal_add_le le_rfl
      linarith
    rw [Work.OddBound.polygon.riemannianDist_eq_toReal (I := I) (q n) (r n),
      Work.OddBound.polygon.riemannianDist_eq_toReal (I := I) p r₀]
    rw [abs_lt]
    constructor <;> linarith
  exact Filter.eventually_atTop.mp hgoal

end

end Work.OddBound.polygonValue
