import Mathlib
import Submission.EDist
import Submission.Work.OddBound.polygonValue.balancing.Instances
import Submission.Work.OddBound.polygon.riemannianDist_eq_toReal

/-!
# Continuity of the Riemannian distance

`Submission.Distance.riemannianDist I x y` is the infimum of the lengths of piecewise smooth paths
from `x` to `y`.  On a path-connected, compact Riemannian manifold it is continuous as a function
of the pair `(x, y)`.

The proof goes through Mathlib's extended Riemannian distance `Manifold.riemannianEDist I`:

* `Manifold.riemannianEDist I` is continuous on `M × M`.  Mathlib's
  `PseudoEMetricSpace.ofRiemannianMetric I M` is a pseudo extended metric structure on `M` whose
  topology is *definitionally* the manifold topology and whose `edist` is `riemannianEDist I`; hence
  `continuous_edist` (continuity of `edist` in a pseudo emetric space) applies directly.
* `riemannianEDist I x y ≠ ⊤` for all `x y`: the set of `y` at finite extended distance from `x` is
  clopen (open by continuity, closed by the triangle inequality and the fact that points close in the
  topology are close for `riemannianEDist`), so it is everything, by connectedness of `M`.
* Finally `riemannianDist` is the real part of `riemannianEDist`
  (`Work.OddBound.polygon.riemannianDist_eq_toReal`), and `ENNReal.toReal` is continuous at every
  point of `ℝ≥0∞` different from `⊤`.
-/
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle

namespace Work.OddBound.polygonValue.balancing

theorem continuousRiemannianDist
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I (WithTop.some (⊤ : ENat)) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I (WithTop.some (⊤ : ENat)) E
      (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M] :
    Continuous (fun q : M × M => Submission.Distance.riemannianDist (I := I) q.1 q.2) := by
  -- Mathlib's smooth Riemannian bundle is a continuous Riemannian bundle
  haveI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  -- ### Step 1: `riemannianEDist I` is continuous on `M × M`
  have hcont : Continuous (fun q : M × M => Manifold.riemannianEDist I q.1 q.2) := by
    -- the pseudo emetric space structure of Mathlib has `edist = riemannianEDist I` and induces
    -- the manifold topology (definitionally), so `edist` is continuous for it
    letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
    exact continuous_edist
  -- ### Step 2: the extended Riemannian distance is finite
  have hfin : ∀ x y : M, Manifold.riemannianEDist I x y ≠ ⊤ := by
    intro x y
    -- the set of points at finite distance from `x` is closed ...
    have hclosed : IsClosed {z : M | Manifold.riemannianEDist I x z = ⊤} :=
      isClosed_singleton.preimage (hcont.comp (continuous_const.prodMk continuous_id))
    -- ... and open: points at distance `⊤` from `x` stay so on a small ball around them
    have hopen : IsOpen {z : M | Manifold.riemannianEDist I x z = ⊤} := by
      rw [isOpen_iff_mem_nhds]
      intro z hz
      filter_upwards [Submission.EDist.eventually_riemannianEDist_lt (I := I) z
        (show (0 : ℝ≥0∞) < 1 by norm_num)] with w hw
      by_contra hne
      have h1 : Manifold.riemannianEDist I w z < 1 := by
        rw [Manifold.riemannianEDist_comm]
        exact hw
      have htri := Manifold.riemannianEDist_triangle (I := I) (x := x) (y := w) (z := z)
      rw [hz] at htri
      exact absurd htri (not_le.mpr (ENNReal.add_lt_top.mpr
        ⟨lt_top_iff_ne_top.mpr hne, h1.trans ENNReal.one_lt_top⟩))
    have hcomp : {z : M | Manifold.riemannianEDist I x z ≠ ⊤}
        = {z : M | Manifold.riemannianEDist I x z = ⊤}ᶜ := by
      ext z; simp
    -- hence it is clopen, and it contains `x`, so it is everything (by connectedness)
    have hS : {z : M | Manifold.riemannianEDist I x z ≠ ⊤} = Set.univ := by
      refine IsClopen.eq_univ ?_ ⟨x, ?_⟩
      · rw [hcomp]; exact ⟨hopen.isClosed_compl, hclosed.isOpen_compl⟩
      · rw [hcomp]; simp [Manifold.riemannianEDist_self]
    have hy : y ∈ {z : M | Manifold.riemannianEDist I x z ≠ ⊤} := by rw [hS]; trivial
    exact hy
  -- ### Step 3: `riemannianDist` is the real part of the (finite) extended distance
  have heq : (fun q : M × M => Submission.Distance.riemannianDist (I := I) q.1 q.2)
      = fun q : M × M => (Manifold.riemannianEDist I q.1 q.2).toReal := by
    funext q
    exact Work.OddBound.polygon.riemannianDist_eq_toReal (I := I) q.1 q.2
  rw [heq, continuous_iff_continuousAt]
  intro q
  have hca : ContinuousAt (fun q : M × M => Manifold.riemannianEDist I q.1 q.2) q :=
    hcont.continuousAt
  exact ContinuousAt.comp (g := ENNReal.toReal)
    (f := fun q : M × M => Manifold.riemannianEDist I q.1 q.2) (x := q)
    (ENNReal.continuousAt_toReal (hfin q.1 q.2)) hca

end Work.OddBound.polygonValue.balancing
