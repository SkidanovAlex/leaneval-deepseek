import Mathlib
import Submission.Work.Final.DimOne.Defs

namespace Work.Final.DimOne

open scoped Manifold ContDiff Bundle Topology ENNReal
open LeanEval.Geometry.SphereTheorem
open CovariantDerivative
open Submission.GlobalExp

set_option maxHeartbeats 800000

/-- **One-dimensional linear algebra.**  In a one-dimensional real vector space every vector is a
real multiple of any given nonzero vector. -/
lemma exists_smul_eq_of_finrank_eq_one {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (hdim : Module.finrank ℝ V = 1) {u v : V} (hu : u ≠ 0) :
    ∃ s : ℝ, v = s • u := by
  classical
  have b : Module.Basis (Fin 1) ℝ V := Module.finBasisOfFinrankEq ℝ V hdim
  have hu' : u = (b.repr u) 0 • b 0 := by simpa using (b.sum_repr u).symm
  have hv' : v = (b.repr v) 0 • b 0 := by simpa using (b.sum_repr v).symm
  have hc : (b.repr u) 0 ≠ 0 := by
    intro h0
    exact hu (by rw [hu', h0, zero_smul])
  refine ⟨(b.repr v) 0 / (b.repr u) 0, ?_⟩
  calc v = (b.repr v) 0 • b 0 := hv'
    _ = (((b.repr v) 0 / (b.repr u) 0) * (b.repr u) 0) • b 0 := by rw [div_mul_cancel₀ _ hc]
    _ = ((b.repr v) 0 / (b.repr u) 0) • ((b.repr u) 0 • b 0) := (smul_smul _ _ _).symm
    _ = ((b.repr v) 0 / (b.repr u) 0) • u := by rw [← hu']

/-- **The unit-speed geodesic ray of a compact one-dimensional manifold is not injective.**

Write `γ s = GExp p (s • u)` for the unit-speed ray of a unit tangent vector `u` at `p`.  There are
two cases.

* If the ray ceases to be minimising at some time `s > 0`, i.e. `d(p, γ s) < s`, then Hopf–Rinow
  produces a minimising geodesic from `p` to `γ s`, i.e. a vector `v` with `GExp p v = γ s` and
  `‖v‖ = d(p, γ s) < s`.  In dimension one `v = c • u` for some `c ≠ s`, so `γ c = γ s`: the ray
  self-intersects.
* If the ray is minimising at all times, `d(p, γ s) = s` for every `s > 0`, pick `s` beyond the
  diameter of `M` (finite, `M` being compact): `d(p, γ s) = s > diam M ≥ d(p, γ s)`, a
  contradiction. -/
theorem exists_ne_of_GExp_ray
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hdim : Module.finrank ℝ E = 1) (p : M) (u : TangentSpace I p) (hu : ‖u‖ = 1) :
    ∃ a b : ℝ, a ≠ b ∧
      GExp (cov := cov) hmet p (a • u) = GExp (cov := cov) hmet p (b • u) := by
  classical
  haveI : RegularSpace M := by
    have : SigmaCompactSpace M := inferInstance
    have : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
    exact inferInstance
  haveI : Nonempty M := ⟨p⟩
  have hu0 : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hu
    norm_num at hu
  by_cases hA : ∃ s : ℝ, 0 < s ∧
      Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (s • u)) < ENNReal.ofReal s
  · -- the ray stops being minimising: Hopf–Rinow gives a second vector with the same image
    obtain ⟨s, hs, hlt⟩ := hA
    obtain ⟨v, hvG, hvd⟩ := Submission.HopfRinow.exists_geodesic_riemannianEDist_eq
      (I := I) (cov := cov) hmet htor p (GExp (cov := cov) hmet p (s • u))
    have hvlt : ‖v‖ < s := by
      have h : ENNReal.ofReal ‖v‖ < ENNReal.ofReal s := by rw [← hvd]; exact hlt
      exact (ENNReal.ofReal_lt_ofReal_iff hs).mp h
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hdim hu0 (v := v)
    have hcne : c ≠ s := by
      intro hcs
      have hcv : ‖c • u‖ = |c| := by rw [norm_smul, hu, mul_one, Real.norm_eq_abs]
      have hnorm : ‖v‖ = |c| :=
        (congrArg (fun w : TangentSpace I p => ‖w‖) hc).trans hcv
      rw [hcs, abs_of_nonneg hs.le] at hnorm
      linarith
    exact ⟨c, s, hcne,
      (congrArg (fun w : TangentSpace I p => GExp (cov := cov) hmet p w) hc).symm.trans hvG⟩
  · -- the ray is minimising at all times: it is longer than the diameter of `M`
    have hbound : ∀ s : ℝ, 0 < s →
        Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (s • u)) = ENNReal.ofReal s := by
      intro s hs
      refine le_antisymm ?_ (not_lt.mp fun h => hA ⟨s, hs, h⟩)
      have h := Submission.CutWitness.edist_GExp_le_norm (cov := cov) hmet (s • u)
      rw [norm_smul, hu, mul_one, Real.norm_of_nonneg hs.le] at h
      exact h
    obtain ⟨p₀, q₀, hdiam⟩ := Submission.Klingenberg.exists_diam_pair (I := I) (M := M)
    have hfin : Manifold.riemannianEDist I p₀ q₀ < ⊤ :=
      Submission.HopfRinow.riemannianEDist_lt_top (I := I) (cov := cov) hmet htor p₀ q₀
    set D : ℝ := (Manifold.riemannianEDist I p₀ q₀).toReal with hDdef
    have hD : Manifold.riemannianEDist I p₀ q₀ = ENNReal.ofReal D :=
      (ENNReal.ofReal_toReal hfin.ne).symm
    have hDnn : 0 ≤ D := ENNReal.toReal_nonneg
    obtain ⟨s, hsgt⟩ := exists_gt D
    have hspos : 0 < s := by linarith
    have h1 : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (s • u))
        = ENNReal.ofReal s := hbound s hspos
    have h2 : Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (s • u))
        ≤ ENNReal.ofReal D := by
      rw [← hD]
      exact hdiam p _
    have h3 : ENNReal.ofReal D < ENNReal.ofReal s :=
      (ENNReal.ofReal_lt_ofReal_iff hspos).mpr hsgt
    have h4 : ENNReal.ofReal s ≤ ENNReal.ofReal D := by rw [← h1]; exact h2
    exact absurd (lt_of_lt_of_le h3 h4) (lt_irrefl (ENNReal.ofReal D))

end Work.Final.DimOne
