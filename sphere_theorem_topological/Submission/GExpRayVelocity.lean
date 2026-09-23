import Submission.GExpRayIdent
import Submission.GExpVelocity

/-!
# The velocity of a `GExp`-ray is the velocity of *the* geodesic with the same initial data

`Submission.GExpRayIdent.eqOn_Icc_GExp_of_isGeodesicAt` identifies the `GExp`-ray of a vector `V`
with any geodesic `γ` through `p` having the same initial data, on an interval `[0,T]`.  This file
transfers the *velocities* as well:

* `curveVelocity_GExp_eq_of_isGeodesicAt`: on `[0,T]` the velocity `s ↦ d/ds GExp p (s • V)` agrees
  with `s ↦ γ̇(s)`.

The transfer is immediate from the pointwise agreement (the germ of a curve determines its velocity,
`GeodesicExtend.curveVelocity_congr_of_eventuallyEq`), except at `t = 0` where the agreement is
one-sided; there the two velocities are both equal to `V`
(`GExpVelocity.curveVelocity_GExp_smul_zero` and the hypothesis `hvel`).

This is the "one-step velocity lemma" of `Submission/Roadmap.lean` §73.9/§74.6 item 3: together with
`GExpFlow.GExp_eq_chartFlow` (which exhibits the chart-flow lines as exactly such geodesics) it
identifies the *state* `(position, velocity)` of a `GExp`-ray at the end of a chart-flow box with
the chart-flow state — the input of every continuation argument along a ray.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.HopfRinow
open Submission.ChartBounds
open Submission.GeodesicExtend
open Submission.GExpTwoSided
open Submission.GExpRayIdent
open Submission.GExpVelocity

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.GExpRayVelocity

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **The velocity of the `GExp`-ray agrees with that of any geodesic with the same initial
data.** -/
theorem curveVelocity_GExp_eq_of_isGeodesicAt (hmet : IsMetricCompatible cov)
    {p : M} {V : TangentSpace I p} (hV : V ≠ 0)
    {a b T : ℝ} (ha : a < 0) (hTnn : 0 ≤ T) (hTb : T < b) {γ : ℝ → M}
    (hsm : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo a b))
    (hgeo : ∀ t ∈ Ioo a b, IsGeodesicAt cov γ t)
    (hne : ∀ t ∈ Ioo a b, curveVelocity (I := I) γ t ≠ 0)
    (h0 : γ 0 = p) (hvel : curveVelocity (I := I) γ 0 = V) :
    ∀ t ∈ Icc (0 : ℝ) T,
      curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet p (s • V)) t
        = curveVelocity (I := I) γ t := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h0t | hpos
  · subst h0t
    rw [curveVelocity_GExp_smul_zero (cov := cov) hmet p hV, hvel]
  · -- the agreement on `[0, T']` with `T' > T` gives a two-sided neighbourhood of `t`
    set T' : ℝ := (T + b) / 2 with hT'def
    have hT'T : T < T' := by rw [hT'def]; linarith
    have hT'b : T' < b := by rw [hT'def]; linarith
    have hT'nn : 0 ≤ T' := by rw [hT'def]; linarith
    have hEqOn : ∀ s ∈ Icc (0 : ℝ) T', γ s = GExp (cov := cov) hmet p (s • V) :=
      eqOn_Icc_GExp_of_isGeodesicAt (cov := cov) hmet hV ha hT'nn hT'b hsm hgeo hne h0 hvel
    have hnb : Icc (0 : ℝ) T' ∈ 𝓝 t := by
      set δ : ℝ := min ((T' - T) / 2) (t / 2) with hδdef
      have hδpos : 0 < δ := by
        rw [hδdef]; exact lt_min (by linarith) (by linarith)
      have hδ1 : δ ≤ t / 2 := by rw [hδdef]; exact min_le_right _ _
      have hδ2 : δ ≤ (T' - T) / 2 := by rw [hδdef]; exact min_le_left _ _
      refine Filter.mem_of_superset
        (isOpen_Ioo.mem_nhds (show t ∈ Ioo (t - δ) (t + δ) from
          ⟨sub_lt_self t hδpos, lt_add_of_pos_right t hδpos⟩)) ?_
      intro s hs
      exact ⟨by linarith [hs.1, ht.1, hδ1], by linarith [hs.2, ht.2, hδ2]⟩
    have hev : (fun s : ℝ => GExp (cov := cov) hmet p (s • V)) =ᶠ[𝓝 t] γ := by
      filter_upwards [hnb] with s hs
      exact (hEqOn s hs).symm
    exact curveVelocity_congr_of_eventuallyEq (I := I) hev

end

end Submission.GExpRayVelocity
