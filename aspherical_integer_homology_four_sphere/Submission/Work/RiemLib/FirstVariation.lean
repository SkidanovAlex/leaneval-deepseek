import Submission.Work.RiemLib.ExpBound2
import Submission.Work.RiemLib.GeoBack
import Submission.Work.RiemLib.Minimising
import Submission.Work.RiemLib.Commons.Analysis.Calculus.eventually_sqrt_le_sqrt_add_mul_add

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The first variation formula of the distance function (upper bound)

Let `γ` be a unit-speed *minimising* geodesic on `[0,L]`, `q = γ 0`, `p = γ L`.  The classical first
variation formula computes the one-sided derivative of `ρ t = d(q, σ t)` for a curve `σ` through `p`
with velocity `V`:

  `ρ'(0+) = ⟨V, γ'(L)⟩`  (up to the cut locus; in general `≤`).

Toponogov's hinge comparison only needs the *upper* bound `ρ'(0+) ≤ ⟨V, γ'(L)⟩`, and that is what is
proved here, in the clean form

  `ρ t ≤ L + t * (⟨V, γ'(L)⟩ + ε)`  for all small `t > 0` and every `ε > 0`.

The proof is elementary:  put `δ = √t`.  The backward point `γ (L - δ)` is the exponential image of
`-δ • γ'(L)` (`Submission/GeoBack.lean`), the sub-arc `[0, L-δ]` is minimising, and the chordal bound
of `Submission/ExpBound2.lean` bounds the distance between `γ (L-δ)` and `exp_p (t • V)`.  The
triangle inequality and the numerical lemma
`Commons.Analysis.Calculus.eventually_sqrt_le_sqrt_add_mul_add` then give the result.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.ChartBounds
open Submission.GeodesicSpeed
open Submission.Length
open Submission.Minimal
open Submission.ExpBound2
open Submission.Minimising
open Submission.Distance
open Submission.GlobalExp
open Submission.GeoBack

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.FirstVariation

noncomputable section

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- Bilinearity of the chart metric in the two slots (both scalars). -/
lemma chartGram_smul_smul' (x₀ p : M) (a b : ℝ) (u v : E) :
    chartGram (I := I) x₀ p (a • u) (b • v)
      = a * b * chartGram (I := I) x₀ p u v := by
  rw [chartGram_smul_fst, chartGram_smul_snd]
  ring

/-- The chart metric of a unit tangent vector is `1`. -/
lemma chartGram_self_eq_one_of_norm_eq_one {p : M} {w : TangentSpace I p} (hw : ‖w‖ = 1) :
    chartGram (I := I) p p (show E from w) (show E from w) = 1 := by
  rw [chartGram_self_apply, real_inner_self_eq_norm_sq, hw]
  norm_num

/-- **The first variation formula, upper bound.**  Let `γ` be a unit-speed minimising geodesic on
`[0,L]` (`L > 0`), `q = γ 0`, `p = γ L`, and suppose the backward point of `γ` is the exponential
image of `-s • γ'(L)` (`hback`, provided by `Submission/GeoBack.lean`).  Then for every `ε > 0` and
all `t > 0` close to `0`,

  `d(q, exp_p (t • V)) ≤ L + t * (⟨V, γ'(L)⟩ + ε)`. -/
theorem firstVariation_upper [Nontrivial E] [CompactSpace M]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    {γ : ℝ → M} {L : ℝ} (hL : 0 < L)
    (hγ : CMDiff[Icc (0:ℝ) L] 1 γ)
    (hsp : ∀ t ∈ Icc (0:ℝ) L, ‖curveVelocity (I := I) γ t‖ = 1)
    (hmin : Manifold.riemannianEDist I (γ 0) (γ L) = ENNReal.ofReal L)
    (hback : ∃ ρb : ℝ, 0 < ρb ∧ ∀ s : ℝ, 0 ≤ s → s < ρb → s ≤ L →
      γ (L - s) = expMap cov (γ L) ((-s) • curveVelocity (I := I) γ L))
    (V : E) :
    ∀ ε > 0, ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
      (Manifold.riemannianEDist I (γ 0) (expMap cov (γ L) (t • V))).toReal
        ≤ L + t * (chartGram (I := I) (γ L) (γ L) V (curveVelocity (I := I) γ L) + ε) := by
  intro ε hε
  obtain ⟨ρc, hρc, hchord⟩ := edist_expMap_le_chordal (cov := cov) hmet htor hpinch (γ L)
  obtain ⟨ρb, hρb, hback'⟩ := hback
  set A : ℝ := chartGram (I := I) (γ L) (γ L) V V with hAdef
  set B : ℝ := chartGram (I := I) (γ L) (γ L) V (curveVelocity (I := I) γ L) with hBdef
  set wL : E := curveVelocity (I := I) γ L with hwLdef
  have hAnn : 0 ≤ A := by
    rw [hAdef]; exact chartGram_self_nonneg (I := I) (γ L) (γ L) V
  have hwLunit : chartGram (I := I) (γ L) (γ L) wL wL = 1 := by
    rw [hwLdef]
    exact chartGram_self_eq_one_of_norm_eq_one (I := I) (hsp L ⟨hL.le, le_refl L⟩)
  have hnum := Commons.Analysis.Calculus.eventually_sqrt_le_sqrt_add_mul_add
    (A := A) (B := B) (ε := ε) hAnn hε
  have hsqrt_tendsto : Tendsto (fun t : ℝ => Real.sqrt t)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (𝓝 0) :=
    (by
      have h := (Real.continuous_sqrt.continuousAt (x := (0:ℝ))).tendsto
      have h2 := h.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
      rwa [Real.sqrt_zero] at h2)
  have hid : Tendsto (fun t : ℝ => t) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have htA : Tendsto (fun t : ℝ => t * Real.sqrt A)
      (nhdsWithin (0:ℝ) (Set.Ioi 0)) (𝓝 0) := by
    have h := hid.mul tendsto_const_nhds (b := Real.sqrt A)
    simpa using h
  have h1 : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), Real.sqrt t < ρb :=
    hsqrt_tendsto.eventually_lt_const hρb
  have h2 : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), Real.sqrt t < L :=
    hsqrt_tendsto.eventually_lt_const hL
  have h3 : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), Real.sqrt t < ρc :=
    hsqrt_tendsto.eventually_lt_const hρc
  have h4 : ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0), t * Real.sqrt A < ρc :=
    htA.eventually_lt_const hρc
  filter_upwards [hnum, h1, h2, h3, h4, self_mem_nhdsWithin] with t hnumt h1t h2t h3t h4t htpos
  rw [Set.mem_Ioi] at htpos
  -- the backward point
  have hbp : γ (L - Real.sqrt t) = expMap cov (γ L) ((-(Real.sqrt t)) • wL) :=
    hback' (Real.sqrt t) (Real.sqrt_nonneg t) h1t (le_of_lt h2t)
  have hLsqrt : 0 ≤ L - Real.sqrt t := by linarith
  have hsub_min : Manifold.riemannianEDist I (γ 0) (γ (L - Real.sqrt t))
      = ENNReal.ofReal (L - Real.sqrt t) := by
    have h := Minimising.riemannianEDist_eq_ofReal_of_unit_speed_of_minimising
      (γ := γ) (L := L) hL.le hγ hsp hmin 0 ⟨le_refl 0, hL.le⟩ (L - Real.sqrt t)
      ⟨hLsqrt, sub_le_self L (Real.sqrt_nonneg t)⟩ hLsqrt
    simpa using h
  -- the metric bounds for the chordal bound
  have hsmL : Real.sqrt (chartGram (I := I) (γ L) (γ L) ((-(Real.sqrt t)) • wL)
      ((-(Real.sqrt t)) • wL)) < ρc := by
    have hsq : chartGram (I := I) (γ L) (γ L) ((-(Real.sqrt t)) • wL) ((-(Real.sqrt t)) • wL)
        = (Real.sqrt t) ^ 2 := by
      rw [chartGram_smul_smul', hwLunit]
      ring
    rw [hsq, Real.sqrt_sq_eq_abs, abs_of_nonneg (Real.sqrt_nonneg t)]
    exact h3t
  have hsmV : Real.sqrt (chartGram (I := I) (γ L) (γ L) (t • V) (t • V)) < ρc := by
    have hsq : chartGram (I := I) (γ L) (γ L) (t • V) (t • V) = t ^ 2 * A := by
      rw [chartGram_smul_smul', hAdef]
      ring
    rw [hsq, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs, abs_of_nonneg htpos.le]
    exact h4t
  have hch := hchord ((-(Real.sqrt t)) • wL) (t • V) hsmL hsmV
  have hch2 : Manifold.riemannianEDist I (γ (L - Real.sqrt t)) (expMap cov (γ L) (t • V))
      ≤ ENNReal.ofReal (Real.sqrt t + t * (B + ε)) := by
    rw [hbp]
    refine le_trans hch (ENNReal.ofReal_le_ofReal ?_)
    have hsub : t • V - (-(Real.sqrt t)) • wL = t • V + Real.sqrt t • wL := by
      rw [neg_smul, sub_neg_eq_add]
    have hrad : chartGram (I := I) (γ L) (γ L) (t • V + Real.sqrt t • wL)
        (t • V + Real.sqrt t • wL) = t ^ 2 * A + 2 * (t * Real.sqrt t) * B + t := by
      rw [ChartConnection.chartGram_add_fst, ChartConnection.chartGram_add_snd,
        ChartConnection.chartGram_add_snd, chartGram_smul_smul',
        chartGram_smul_smul', chartGram_smul_smul', chartGram_smul_smul', hwLunit, hAdef, hBdef,
        ChartConnection.chartGram_comm (I := I) (γ L) (γ L) wL V]
      rw [Real.mul_self_sqrt htpos.le]
      ring
    rw [hsub, hrad]
    exact hnumt
  -- triangle inequality
  have htri : Manifold.riemannianEDist I (γ 0) (expMap cov (γ L) (t • V))
      ≤ Manifold.riemannianEDist I (γ 0) (γ (L - Real.sqrt t))
        + Manifold.riemannianEDist I (γ (L - Real.sqrt t)) (expMap cov (γ L) (t • V)) :=
    Manifold.riemannianEDist_triangle
  have hBnn : 0 ≤ Real.sqrt t + t * (B + ε) :=
    le_trans (Real.sqrt_nonneg (t ^ 2 * A + 2 * (t * Real.sqrt t) * B + t)) hnumt
  calc (Manifold.riemannianEDist I (γ 0) (expMap cov (γ L) (t • V))).toReal
      ≤ (ENNReal.ofReal (L - Real.sqrt t)
          + ENNReal.ofReal (Real.sqrt t + t * (B + ε))).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
            ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)
          (le_trans htri (add_le_add hsub_min.le hch2))
    _ = L + t * (B + ε) := by
        rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
          ENNReal.toReal_ofReal hLsqrt, ENNReal.toReal_ofReal hBnn]
        ring


/-- **The first variation formula along the chosen minimising geodesic.**  Specialisation of
`firstVariation_upper` to the project's global geodesic segments: the backward-point identity is
supplied by `Submission/GeoBack.lean` and the smoothness/unit speed by `geodCurve_spec`. -/
theorem firstVariation_upper_geodCurve [Nontrivial E] [CompactSpace M]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    {q : M} {ξ : TangentSpace I q} (hξ : ‖ξ‖ = 1) {T L : ℝ} (hT : 0 ≤ T) (hL : 0 < L)
    (hLT : L ≤ T)
    (hmin : Manifold.riemannianEDist I q
      ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) L) = ENNReal.ofReal L)
    (V : E) :
    ∀ ε > 0, ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
      (Manifold.riemannianEDist I q
        (expMap cov ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) L) (t • V))).toReal
        ≤ L + t * (chartGram (I := I)
            ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) L)
            ((geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) L) V
            (curveVelocity (I := I) (geodCurve (cov := cov) hmet T hT q ξ hξ : ℝ → M) L) + ε) := by
  set G : ℝ → M := geodCurve (cov := cov) hmet T hT q ξ hξ with hGdef
  obtain ⟨hG0, -, hGsm, -, hGsp⟩ := geodCurve_spec (cov := cov) hmet T hT q ξ hξ
  have hδ : 0 < geodDelta (cov := cov) hmet := geodDelta_pos (cov := cov) hmet
  have hsub : Icc (0:ℝ) L ⊆
      Ioo (-(geodDelta (cov := cov) hmet)) (T + geodDelta (cov := cov) hmet) :=
    fun t ht => ⟨by linarith [hδ, ht.1], by linarith [hδ, ht.2, hLT]⟩
  have hγ : CMDiff[Icc (0:ℝ) L] 1 G := (hGsm.mono hsub).of_le (WithTop.coe_le_coe.mpr le_top)
  have hsp : ∀ t ∈ Icc (0:ℝ) L, ‖curveVelocity (I := I) G t‖ = 1 := fun t ht => hGsp t (hsub ht)
  have hmin' : Manifold.riemannianEDist I (G 0) (G L) = ENNReal.ofReal L := by
    rw [hGdef, hG0]; exact hmin
  have hback : ∃ ρb : ℝ, 0 < ρb ∧ ∀ s : ℝ, 0 ≤ s → s < ρb → s ≤ L →
      G (L - s) = expMap cov (G L) ((-s) • curveVelocity (I := I) G L) :=
    GeoBack.geodCurve_sub_eq_expMap (cov := cov) hmet (q := q) (ξ := ξ) hξ (T := T) hT
      (t := L) hL.le hLT
  have hG0' : G 0 = q := by rw [hGdef]; exact hG0
  intro ε hε
  have h := firstVariation_upper (cov := cov) hmet htor hpinch hL hγ hsp hmin' hback V ε hε
  rw [hG0'] at h
  simpa only [hGdef] using h

end

end Submission.FirstVariation
