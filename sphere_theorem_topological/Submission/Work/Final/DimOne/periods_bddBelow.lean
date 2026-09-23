import Mathlib
import Submission.Work.Final.DimOne.Defs

namespace Work.Final.DimOne

open scoped Manifold ContDiff Bundle Topology ENNReal
open LeanEval.Geometry.SphereTheorem
open CovariantDerivative
open Submission.GlobalExp

/-- **The positive periods of the ray `s ↦ GExp p (s • u)` are bounded below by a positive
constant.**

If `Q > 0` is a period of the unit-speed ray starting at `p` in the direction `u`,
`GExp p ((s + Q) • u) = GExp p (s • u)` for all `s`, then the ray returns to its starting point
after time `Q`: `GExp p (Q • u) = GExp p 0 = p`.  But for small positive times the Riemannian
distance from `p` to `GExp p (t • u)` is *exactly* the length `t` of the geodesic segment
(`exists_pos_riemannianEDist_GExp_smul`, local minimality of the exponential map), so a period
`0 < Q < ρ` would give `0 = riemannianEDist p p = ofReal Q > 0`, a contradiction. -/
theorem periods_bddBelow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (p : M) (u : TangentSpace I p) (hu : ‖u‖ = 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ Q : ℝ, 0 < Q →
      (∀ s : ℝ, GExp (cov := cov) hmet p ((s + Q) • u) = GExp (cov := cov) hmet p (s • u)) →
      ρ ≤ Q := by
  -- the local minimality radius of the exponential map at `p`
  obtain ⟨ρ, hρ, hdist⟩ := exists_pos_riemannianEDist_GExp_smul (cov := cov) hmet htor p
  refine ⟨ρ, hρ, fun Q hQ hper => ?_⟩
  by_contra hcon
  have hQρ : Q < ρ := not_le.mp hcon
  have hu_ne : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu
    exact one_ne_zero hu.symm
  -- a period makes the ray return to `p`
  have hself : GExp (cov := cov) hmet p (Q • u) = p := by
    have h0 := hper 0
    simpa using h0
  have hnorm : ‖Q • u‖ = Q := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hQ, hu, mul_one]
  -- the distance from `p` to the point at time `Q` on the ray is exactly `Q`
  have hd := hdist u hu_ne Q hQ.le (by simpa [hu] using hQρ)
  rw [hself, Manifold.riemannianEDist_self, hnorm] at hd
  exact (ENNReal.ofReal_ne_zero_iff.mpr hQ) hd.symm

end Work.Final.DimOne
