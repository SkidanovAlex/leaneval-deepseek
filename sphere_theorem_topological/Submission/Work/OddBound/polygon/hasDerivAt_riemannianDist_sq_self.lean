import Mathlib
import Submission.Work.OddBound.LiftKit
import Submission.Work.OddBound.polygon.polygon_energy_aux
import Submission.Work.OddBound.polygon.riemannianDist_eq_toReal

/-!
# The derivative of the squared distance at the base point

For a globally smooth curve `v` on a Riemannian manifold with `v 0 = x₀`, the function
`t ↦ d(v t, x₀)²` has derivative `0` at `t = 0`.

This is the degenerate case `y₀ = x₀` of the first variation formula for the squared distance
(`Work.OddBound.polygon.hasDerivAt_riemannianDist_sq_along`): the distance function is *not*
smooth at the point itself, but its square is differentiable with vanishing derivative there,
because the curve leaves `x₀` at finite speed:

* `curveSpeed v` is continuous (`continuous_curveSpeed`), so it is bounded by a constant `C` on a
  neighbourhood `(-δ, δ)` of `0`;
* `riemannianDist_le_curveLength_Icc` bounds the distance between two points of the curve by the
  length of the curve segment joining them, and the length of such a segment contained in
  `(-δ, δ)` is at most `C` times its duration;
* hence `d(v t, x₀) ≤ C * |t|` for `|t| < δ`, so `d(v t, x₀)² = O(t²) = o(t)` and the derivative
  at `0` vanishes.

The distance is used in the reversed order `d(v t, x₀)`; the symmetry of the distance
(`riemannianEDist_comm`, via `riemannianDist_eq_toReal`) supplies the two orders.
-/

namespace Work.OddBound.polygon

open scoped ContDiff Manifold
open scoped Interval
open scoped Topology
open Bundle

theorem hasDerivAt_riemannianDist_sq_self
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {x₀ : M} {v : ℝ → M} (hv : ContMDiff 𝓘(ℝ) I ∞ v) (hv0 : v 0 = x₀) :
    HasDerivAt (fun t : ℝ => (Submission.Distance.riemannianDist (I := I) (v t) x₀) ^ 2) 0 0 := by
  classical
  -- The curve is in particular `C¹`.
  have hv1 : ContMDiff 𝓘(ℝ) I 1 v := hv.of_le (WithTop.coe_le_coe.mpr le_top)
  -- The Riemannian distance is symmetric (both orders are needed below).
  have hsymm : ∀ t : ℝ, Submission.Distance.riemannianDist (I := I) (v t) x₀
      = Submission.Distance.riemannianDist (I := I) x₀ (v t) := by
    intro t
    rw [riemannianDist_eq_toReal (I := I) (v t) x₀,
      riemannianDist_eq_toReal (I := I) x₀ (v t), Manifold.riemannianEDist_comm]
  -- The speed of the curve is continuous, hence bounded near `0`.
  have hcont : Continuous (fun s : ℝ => Submission.Length.curveSpeed (I := I) v s) :=
    continuous_curveSpeed (I := I) hv1
  have hcont0 : ContinuousAt (fun s : ℝ => Submission.Length.curveSpeed (I := I) v s) 0 :=
    hcont.continuousAt
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, dist y 0 < δ →
      dist (Submission.Length.curveSpeed (I := I) v y)
        (Submission.Length.curveSpeed (I := I) v 0) < 1 :=
    Metric.eventually_nhds_iff_ball.mp ((Metric.continuousAt_iff'.mp hcont0) 1 zero_lt_one)
  obtain ⟨C, hCpos, hCb⟩ : ∃ C : ℝ, 0 < C ∧ ∀ s : ℝ, |s| < δ →
      Submission.Length.curveSpeed (I := I) v s ≤ C := by
    refine ⟨Submission.Length.curveSpeed (I := I) v 0 + 1, by
      linarith [Submission.Length.curveSpeed_nonneg (I := I) v 0], ?_⟩
    intro s hs
    have h1 : dist (Submission.Length.curveSpeed (I := I) v s)
        (Submission.Length.curveSpeed (I := I) v 0) < 1 :=
      hδ s (Metric.mem_ball.mpr (by simpa [Real.dist_eq] using hs))
    rw [Real.dist_eq] at h1
    linarith [(abs_lt.mp h1).2]
  -- The integral of the speed over a segment on which it is bounded by `C`.
  have hInt : ∀ a b : ℝ, a ≤ b → (∀ s ∈ Set.Icc a b,
      Submission.Length.curveSpeed (I := I) v s ≤ C) →
      ∫ s in a..b, Submission.Length.curveSpeed (I := I) v s ≤ C * (b - a) := by
    intro a b hab hb
    have h1 : ‖∫ s in a..b, Submission.Length.curveSpeed (I := I) v s‖ ≤ C * |b - a| :=
      intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun s : ℝ => Submission.Length.curveSpeed (I := I) v s)
        (C := C) (a := a) (b := b) (fun x hx => by
          rw [Real.norm_of_nonneg (Submission.Length.curveSpeed_nonneg (I := I) v x)]
          refine hb x ?_
          rw [← Set.uIcc_of_le hab]
          exact Set.uIoc_subset_uIcc hx)
    have h2 : 0 ≤ ∫ s in a..b, Submission.Length.curveSpeed (I := I) v s :=
      intervalIntegral.integral_nonneg_of_forall hab
        (fun s => Submission.Length.curveSpeed_nonneg (I := I) v s)
    rw [Real.norm_of_nonneg h2, abs_of_nonneg (sub_nonneg.mpr hab)] at h1
    exact h1
  -- The key estimate: `d(v t, x₀) ≤ C * |t|` for `|t| < δ`.
  have hbound : ∀ t : ℝ, |t| < δ →
      Submission.Distance.riemannianDist (I := I) (v t) x₀ ≤ C * |t| := by
    intro t ht
    rcases le_total 0 t with ht0 | ht0
    · -- `t ≥ 0`: the segment of the curve from `0` to `t` joins `x₀` to `v t`.
      have ht' : t < δ := by rwa [abs_of_nonneg ht0] at ht
      have hd := riemannianDist_le_curveLength_Icc (I := I) hv1 ht0
      rw [hv0, Submission.Length.curveLength_def] at hd
      have hsp : ∀ s ∈ Set.Icc (0 : ℝ) t,
          Submission.Length.curveSpeed (I := I) v s ≤ C := by
        intro s hs
        refine hCb s ?_
        rw [abs_of_nonneg hs.1]
        linarith [hs.2]
      have hi := hInt 0 t ht0 hsp
      rw [hsymm t, abs_of_nonneg ht0]
      linarith
    · -- `t ≤ 0`: the segment from `t` to `0` joins `v t` to `x₀` in the stated order.
      have ht' : -t < δ := by rwa [abs_of_nonpos ht0] at ht
      have hd := riemannianDist_le_curveLength_Icc (I := I) hv1 ht0
      rw [hv0, Submission.Length.curveLength_def] at hd
      have hsp : ∀ s ∈ Set.Icc t 0,
          Submission.Length.curveSpeed (I := I) v s ≤ C := by
        intro s hs
        refine hCb s ?_
        rw [abs_of_nonpos hs.2]
        linarith [hs.1]
      have hi := hInt t 0 ht0 hsp
      rw [abs_of_nonpos ht0]
      linarith
  -- Hence `d(v t, x₀)² = O(t²)` near `0`.
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ),
      Submission.Distance.riemannianDist (I := I) (v t) x₀ ≤ C * |t| := by
    refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : ℝ) hδpos) ?_
    intro t ht
    exact hbound t (by simpa [Real.dist_eq] using ht)
  have hO : (fun t : ℝ => (Submission.Distance.riemannianDist (I := I) (v t) x₀) ^ 2)
      =O[𝓝 (0 : ℝ)] (fun t : ℝ => t ^ 2) := by
    refine Asymptotics.IsBigO.of_bound (C ^ 2) ?_
    filter_upwards [hev] with t ht
    rw [Real.norm_of_nonneg (sq_nonneg (Submission.Distance.riemannianDist (I := I) (v t) x₀)),
      Real.norm_of_nonneg (sq_nonneg t)]
    calc (Submission.Distance.riemannianDist (I := I) (v t) x₀) ^ 2
        ≤ (C * |t|) ^ 2 :=
          pow_le_pow_left₀ (Submission.Distance.riemannianDist_nonneg _ _) ht 2
      _ = C ^ 2 * t ^ 2 := by rw [mul_pow, sq_abs]
  -- And `t² = o(t)` at `0`, so `d(v t, x₀)² = o(t)`, which is the derivative statement.
  have hlittle : (fun t : ℝ => (Submission.Distance.riemannianDist (I := I) (v t) x₀) ^ 2)
      =o[𝓝 (0 : ℝ)] (fun t : ℝ => t) :=
    hO.trans_isLittleO (Asymptotics.isLittleO_pow_id (n := 2) (by norm_num))
  refine HasDerivAt.of_isLittleO ?_
  have hfun : (fun t : ℝ => (fun s : ℝ => (Submission.Distance.riemannianDist (I := I) (v s) x₀) ^ 2) t
      - (fun s : ℝ => (Submission.Distance.riemannianDist (I := I) (v s) x₀) ^ 2) 0
      - (t - 0) • (0 : ℝ))
      = fun t : ℝ => (Submission.Distance.riemannianDist (I := I) (v t) x₀) ^ 2 := by
    funext t
    simp [hv0, Submission.Distance.riemannianDist_self]
  rw [hfun]
  have hfun2 : (fun t : ℝ => t - 0) = fun t : ℝ => t := by funext t; simp
  rw [hfun2]
  exact hlittle

end Work.OddBound.polygon
