import Submission.Work.RiemLib.MetricScale
import Submission.Work.RiemLib.GSRestricted
import Submission.Work.RiemLib.GlobalBM
import Submission.Work.RiemLib.PinchUniform
import Submission.Work.RiemLib.Commons.Geometry.Manifold.Riemannian.exists_scaleMetric
import Submission.Work.RiemLib.Commons.Geometry.Manifold.Riemannian.isContMDiffRiemannianBundle_scaleMetric

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Klingenberg's estimate: the remaining input, and the resulting assembly

**`KlingenbergBound cov`** below is the *only* classical input still missing from
`Submission.sphere_theorem`: Klingenberg's diameter estimate.  In the normalisation of the project
(sectional curvature `≤ K`) it says that a compact, simply connected manifold has a **diameter
pair** `(p,q)` with `d(p,q) ≥ π/√K`.  Its proof requires (a) the conjugate-radius half
`conj ≥ π/√K` (Rauch; **already in the library**, `Submission.ConjRadius`) and (b) Klingenberg's
estimate `ℓ ≥ 2π/√K` for closed geodesics/geodesic loops (Klingenberg 1959/1961; the deep part).

**`sphere_theorem_of_klingenberg`** shows that this is *all* that is missing: from the target's
hypotheses plus `KlingenbergBound cov` we deduce `M ≃ₜ S^{n+1}`.  The proof is

1. uniform strict pinching `c < sec` (`Submission.PinchUniform`);
2. rescale the metric by `c`: the new metric `g' = c · g` has `sec ∈ (1, 4/c]` — so `sec ≤ 4/c`
   with **`4/c < 4` strictly**, which is what makes Klingenberg's estimate strict;
3. Klingenberg with `K = 4/c` gives a diameter pair with `d' ≥ π/√(4/c) > π/2`;
4. strict Bonnet–Myers (`Submission.GlobalBM`) gives `diam' < π`;
5. Grove–Shiohama (`Submission.GSRestricted`) applied to `g'` finishes.

Because two `RiemannianBundle` instances on `TangentSpace I` cannot be compared by the elaborator,
the step "apply the arguments to the rescaled metric" is done through the auxiliary theorem
`sphere_theorem_of_metric`, whose *metric* is an explicit parameter and all of whose hypotheses are
written in the instance-free forms (`…For g`, or through `g.inner`), so that it can be applied with
the scaled metric `g'` from a context carrying the ambient instance.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.Curvature
open Submission.CurvatureVec
open Submission.EDist

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]

namespace Submission.Klingenberg

noncomputable section

/-- **Klingenberg's diameter estimate** (the remaining classical input of the sphere theorem).

For every Riemannian metric `g` on `M` (given by its family of fibre inner products), with `M`
compact and simply connected, if the sectional curvature satisfies `1 ≤ sec < 4` at every
orthonormal pair, then there is a **diameter pair** `(p,q)` with `d(p,q) > π/2`.

**The two curvature hypotheses are both essential.**  This is the `K = 4` case of Klingenberg's
estimate in the normalisation `sec ≥ 1`: the classical statement (Klingenberg 1959/1961; see the
discussion of Berger's spheres) is that in that normalisation the *injectivity radius* is `> π/2`
in every dimension, and the diameter bound follows because the diameter dominates the injectivity
radius at a diameter point (`ofReal_le_edist_of_injOn_of_forall_le` below).

* The *lower* bound `1 ≤ sec` cannot be dropped: the Berger spheres
  `(S³, σ₁² + σ₂² + τ²σ₃²)` have `sec ∈ [τ², 4 - 3τ²]`, and scaling by `4 - 3τ²` puts them in the
  normalisation `sec ∈ [1/4, 1]`; there the injectivity radius is only `π/2·(something < 2)` and,
  as the classical literature notes, Klingenberg's estimate fails.  Equivalently: the estimate is
  *not* scale invariant, it holds in the normalisation `sec ≥ 1`.
* The *upper* bound `sec < 4` is what produces the **strict** inequality `d > π/2`: the closed
  case `sec ∈ [1,4]` is attained by the complex projective spaces (`sec ∈ [1,4]`, `inj = π/2`).

Both hypotheses are satisfied by the metric `g' = c · g` of `sphere_theorem_of_metric`, whose
curvature lies in `(1, 4/c]` with `c > 1` (whence `π/√(4/c) > π/2`).

**Note (torsion).**  The hypothesis `cov.torsion = 0` is part of the statement: the classical estimate
is about the *Levi-Civita* connection, and the project hypothesizes the connection abstractly, so
torsion-freeness is assumed rather than derived. -/
def KlingenbergBound [I.Boundaryless] [CompactSpace M] [SimplyConnectedSpace M]
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) : Prop :=
  ∀ (g : RiemannianMetric (fun x : M ↦ TangentSpace I x)),
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g⟩
    IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) →
    MetricScale.IsMetricCompatibleFor g cov →
    cov.torsion = 0 →
    (∀ (p : M) (u v : TangentSpace I p), g.inner p u u = 1 → g.inner p v v = 1 →
      g.inner p u v = 0 → (1 : ℝ) ≤ g.inner p (curvVec cov p u v v) u) →
    (∀ (p : M) (u v : TangentSpace I p), g.inner p u u = 1 → g.inner p v v = 1 →
      g.inner p u v = 0 → g.inner p (curvVec cov p u v v) u < (4 : ℝ)) →
    ∃ p q : M, ENNReal.ofReal (Real.pi / 2) < Manifold.riemannianEDist I p q

/-! ## The farthest point lies beyond the injectivity radius

This is the first step of Klingenberg's estimate: `diam ≥ inj`.  We phrase "the exponential map is
injective on the ball of radius `r`" directly in terms of `GExp`, which is enough for the argument
(and avoids defining the injectivity radius as a supremum). -/

/-- **A geodesic ray is minimising up to the injectivity radius.**  If `GExp p` is injective on the
ball of radius `r` and `0 < ‖u‖ < r`, then `d(p, GExp p u) = ‖u‖`. -/
theorem edist_GExp_eq_norm_of_injOn
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {p : M} {r : ℝ}
    (hinj : ∀ u v : TangentSpace I p, ‖u‖ < r → ‖v‖ < r →
      GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v → u = v)
    {u : TangentSpace I p} (hu : ‖u‖ < r) (hune : u ≠ 0) :
    Manifold.riemannianEDist I p (GExp (cov := cov) hmet p u) = ENNReal.ofReal ‖u‖ := by
  refine le_antisymm ?_ ?_
  · -- the ray bound
    set η : TangentSpace I p := unitOf u hune with hηdef
    have hη : ‖η‖ = 1 := unitOf_norm u hune
    have hscale : ‖u‖ • η = u := by
      rw [hηdef]
      show ‖u‖ • unitOf u hune = u
      rw [unitOf, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hune), one_smul]
    have h := Submission.GExpRay.edist_GExp_smul_le (cov := cov) hmet p hη
      (a := 0) (b := ‖u‖) le_rfl (norm_nonneg u) (norm_nonneg u)
    rwa [zero_smul, GExp_zero, sub_zero, hscale] at h
  · -- if `u` were not minimising, there would be a second vector in the ball
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨w, hwG, hwd⟩ :=
      Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (cov := cov) hmet htor p
        (GExp (cov := cov) hmet p u)
    rw [hwd] at hcon
    have hwlt : ‖w‖ < ‖u‖ := by
      have h := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top).mpr hcon
      simpa [ENNReal.toReal_ofReal (norm_nonneg w), ENNReal.toReal_ofReal (norm_nonneg u)] using h
    have hwu : w = u := hinj w u (lt_trans hwlt hu) hu (by rw [hwG])
    rw [hwu] at hwlt
    exact lt_irrefl _ hwlt

/-- **The farthest point lies beyond the injectivity radius.**  If `GExp p` is injective on the ball
of radius `r` and `q` is a point of `M` at maximal distance from `p`, then `d(p,q) ≥ r`. -/
theorem ofReal_le_edist_of_injOn_of_forall_le
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) {p q : M} {r : ℝ} (hr : 0 < r)
    (hinj : ∀ u v : TangentSpace I p, ‖u‖ < r → ‖v‖ < r →
      GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v → u = v)
    (hmax : ∀ y : M, Manifold.riemannianEDist I p y ≤ Manifold.riemannianEDist I p q) :
    ENNReal.ofReal r ≤ Manifold.riemannianEDist I p q := by
  by_contra hcon
  rw [not_le] at hcon
  have hqr : Manifold.riemannianEDist I p q < ENNReal.ofReal r := hcon
  have hfin : Manifold.riemannianEDist I p q ≠ ⊤ :=
    (lt_of_lt_of_le hqr ENNReal.ofReal_lt_top.le).ne
  have hqr' : (Manifold.riemannianEDist I p q).toReal < r := by
    rw [← ENNReal.ofReal_toReal hfin] at hqr
    exact (ENNReal.ofReal_lt_ofReal_iff hr).mp hqr
  set s : ℝ := ((Manifold.riemannianEDist I p q).toReal + r) / 2 with hsdef
  have hsto : (Manifold.riemannianEDist I p q).toReal < s := by rw [hsdef]; linarith
  have hslt : s < r := by rw [hsdef]; linarith
  have hspos : 0 < s := lt_of_le_of_lt ENNReal.toReal_nonneg hsto
  obtain ⟨η, hη⟩ : ∃ η : TangentSpace I p, ‖η‖ = 1 := by
    obtain ⟨e, he⟩ : ∃ e : E, e ≠ 0 := exists_ne 0
    have hfv : frameVector (I := I) p p e ≠ 0 := fun h =>
      he ((Submission.ChartBounds.frameVector_eq_zero_iff (I := I) (mem_chart_source H p) e).mp h)
    exact ⟨unitOf (frameVector (I := I) p p e) hfv, unitOf_norm _ hfv⟩
  have hsn : ‖s • η‖ = s := by
    rw [norm_smul, hη, mul_one, Real.norm_of_nonneg (le_of_lt hspos)]
  have hsne : s • η ≠ 0 :=
    smul_ne_zero (ne_of_gt hspos) (by rw [← norm_pos_iff, hη]; norm_num)
  have hmain := edist_GExp_eq_norm_of_injOn (cov := cov) hmet htor hinj (u := s • η)
    (by rw [hsn]; exact hslt) hsne
  have hgt : Manifold.riemannianEDist I p q <
      Manifold.riemannianEDist I p (GExp (cov := cov) hmet p (s • η)) := by
    rw [hmain, hsn, ← ENNReal.ofReal_toReal hfin]
    exact (ENNReal.ofReal_lt_ofReal_iff hspos).mpr hsto
  exact absurd (hmax _) (not_le.mpr hgt)

/-- **The diameter is attained** on a compact Riemannian manifold (with the manifold topology being
the metric topology): there is a pair of points at maximal distance. -/
theorem exists_diam_pair [I.Boundaryless] [RegularSpace M] [CompactSpace M] [Nonempty M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)] :
    ∃ p q : M, ∀ r s : M, Manifold.riemannianEDist I r s ≤ Manifold.riemannianEDist I p q := by
  haveI : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  letI : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  have hcont : Continuous (fun z : M × M => Manifold.riemannianEDist I z.1 z.2) :=
    continuous_edist.congr (fun z => Submission.EDist.edist_eq_riemannianEDist (I := I) z.1 z.2)
  obtain ⟨z₀, -, hmax⟩ :=
    isCompact_univ.exists_isMaxOn Set.univ_nonempty hcont.continuousOn
  exact ⟨z₀.1, z₀.2, fun r s => hmax (Set.mem_univ (r, s))⟩

/-- **The sphere theorem for a single metric whose curvature is `≤ K` with `K < 4`.**

The metric is an explicit parameter (so that this can be applied to a rescaled metric), and all
hypotheses are stated in the instance-free forms. -/
theorem sphere_theorem_of_metric
    [I.Boundaryless] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
    (hdim : 2 ≤ Module.finrank ℝ E)
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    (htor : cov.torsion = 0)
    (g : RiemannianMetric (fun x : M ↦ TangentSpace I x))
    (hsmooth : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g⟩
      IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x))
    (hmet : MetricScale.IsMetricCompatibleFor g cov)
    (hpinch : MetricScale.QuarterPinchedFor g cov)
    (hK : KlingenbergBound (I := I) (M := M) cov)
    {K : ℝ} (hKpos : 0 < K) (hKlt : K < 4)
    (hsec : ∀ (p : M) (u v : TangentSpace I p), g.inner p u u = 1 → g.inner p v v = 1 →
      g.inner p u v = 0 → g.inner p (curvVec cov p u v v) u ≤ K) :
    Nonempty
      (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) 1) := by
  classical
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g⟩
  letI : IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) := hsmooth
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by linarith)
  haveI : PathConnectedSpace M := inferInstance
  haveI : RegularSpace M := inferInstance
  haveI : Nonempty M := PathConnectedSpace.nonempty
  have hmetI : IsMetricCompatible cov :=
    (Submission.MetricScale.isMetricCompatibleFor_iff (I := I) (cov := cov)).mpr hmet
  have hpinchI : QuarterPinched cov :=
    (Submission.MetricScale.quarterPinchedFor_iff (I := I) (cov := cov)).mpr hpinch
  -- the two curvature bounds in the normalisation `1 ≤ sec < 4` required by Klingenberg's estimate
  have hge : ∀ (p : M) (u v : TangentSpace I p), g.inner p u u = 1 → g.inner p v v = 1 →
      g.inner p u v = 0 → (1 : ℝ) ≤ g.inner p (curvVec cov p u v v) u :=
    fun p u v hu hv huv =>
      (Submission.MetricScale.quarterPinchedFor_pointwise (I := I) (cov := cov)
        hpinch p u v hu hv huv).1.le
  have hlt4 : ∀ (p : M) (u v : TangentSpace I p), g.inner p u u = 1 → g.inner p v v = 1 →
      g.inner p u v = 0 → g.inner p (curvVec cov p u v v) u < (4 : ℝ) :=
    fun p u v hu hv huv => lt_of_le_of_lt (hsec p u v hu hv huv) hKlt
  obtain ⟨p₀, q₀, hlower⟩ := hK g hsmooth hmet htor hge hlt4
  -- the diameter is attained, so `p₀ q₀` can be replaced by a diameter pair
  obtain ⟨p, q, hdiam⟩ := exists_diam_pair (I := I) (M := M)
  have hpq₀ : Manifold.riemannianEDist I p₀ q₀ ≤ Manifold.riemannianEDist I p q := hdiam p₀ q₀
  have hltπ : Manifold.riemannianEDist I p q < ENNReal.ofReal Real.pi :=
    Submission.GlobalBM.riemannianEDist_lt_pi (I := I) (cov := cov) hmetI htor hpinchI hdim p q
  have hfin : Manifold.riemannianEDist I p q ≠ ⊤ :=
    (lt_of_lt_of_le hltπ ENNReal.ofReal_lt_top.le).ne
  set D : ℝ := (Manifold.riemannianEDist I p q).toReal with hDdef
  have hpq : Manifold.riemannianEDist I p q = ENNReal.ofReal D :=
    (ENNReal.ofReal_toReal hfin).symm
  have hDnn : 0 ≤ D := by rw [hDdef]; exact ENNReal.toReal_nonneg
  have hDgt : Real.pi / 2 < D := by
    have h3 : ENNReal.ofReal (Real.pi / 2) < ENNReal.ofReal D := by
      calc ENNReal.ofReal (Real.pi / 2) < Manifold.riemannianEDist I p₀ q₀ := hlower
        _ ≤ Manifold.riemannianEDist I p q := hpq₀
        _ = ENNReal.ofReal D := hpq
    exact (ENNReal.ofReal_lt_ofReal_iff'.mp h3).1
  have hDlt : D < Real.pi := by
    have h3 : ENNReal.ofReal D < ENNReal.ofReal Real.pi := by
      calc ENNReal.ofReal D = Manifold.riemannianEDist I p q := hpq.symm
        _ < ENNReal.ofReal Real.pi := hltπ
    exact (ENNReal.ofReal_lt_ofReal_iff Real.pi_pos).mp h3
  exact Submission.GSRestricted.restricted_sphere_theorem (I := I) (cov := cov) hmetI htor hpinchI
    (fun r s => by rw [← hpq]; exact hdiam r s) hDgt hDlt ⟨p, q, hpq⟩

/-- **The sphere theorem from Klingenberg's estimate.**  This is the target statement of the
project with the single extra hypothesis `KlingenbergBound cov`. -/
theorem sphere_theorem_of_klingenberg
    [I.Boundaryless] [T2Space M] [CompactSpace M] [SimplyConnectedSpace M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
    (hdim : 2 ≤ Module.finrank ℝ E)
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    (htor : cov.torsion = 0) (hmet : IsMetricCompatible cov) (hpinch : QuarterPinched cov)
    (hK : KlingenbergBound (I := I) (M := M) cov) :
    Nonempty
      (M ≃ₜ sphere (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) 1) := by
  classical
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℝ) (by linarith)
  haveI : PathConnectedSpace M := inferInstance
  haveI : RegularSpace M := inferInstance
  haveI : Nonempty M := PathConnectedSpace.nonempty
  -- the ambient fibre metric, as a plain `RiemannianMetric`
  set g₀ : RiemannianMetric (fun x : M ↦ TangentSpace I x) :=
    (inferInstance : RiemannianBundle (fun x : M ↦ TangentSpace I x)).g with hg₀def
  -- step 1: uniform strict pinching
  obtain ⟨c, hc1, hlt⟩ :=
    Submission.PinchUniform.exists_uniform_lt_curvVec (I := I) (cov := cov) hmet hpinch htor
  have hcpos : 0 < c := lt_trans zero_lt_one hc1
  have hlt' : ∀ (p : M) (u v : TangentSpace I p), g₀.inner p u u = 1 → g₀.inner p v v = 1 →
      g₀.inner p u v = 0 → c < g₀.inner p (curvVec cov p u v v) u := hlt
  have hup4 : ∀ (p : M) (u v : TangentSpace I p), g₀.inner p u u = 1 → g₀.inner p v v = 1 →
      g₀.inner p u v = 0 → g₀.inner p (curvVec cov p u v v) u ≤ 4 :=
    fun p u v hu hv huv =>
      Submission.MetricScale.quarterPinched_pointwise_le (I := I) (cov := cov) hpinch p u v hu hv huv
  -- step 2: the scaled metric
  obtain ⟨g', hinner⟩ :=
    Commons.Geometry.Manifold.Riemannian.exists_scaleMetric
      (E := fun x : M ↦ TangentSpace I x) g₀ hcpos
  -- step 3: the transfers
  have hsmooth₀ : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀⟩
      IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    (inferInstance : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g₀⟩
      IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x))
  have hsmooth' : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g'⟩
      IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x) :=
    Commons.Geometry.Manifold.Riemannian.isContMDiffRiemannianBundle_scaleMetric
      (IB := I) (B := M) (F := E) (E := fun x : M ↦ TangentSpace I x) g₀ g' hcpos hinner hsmooth₀
  have hmetFor' : Submission.MetricScale.IsMetricCompatibleFor g' cov :=
    Submission.MetricScale.isMetricCompatibleFor_scale (I := I) (cov := cov)
      ((Submission.MetricScale.isMetricCompatibleFor_iff (I := I) (cov := cov)).mp hmet) hcpos g' hinner
  have hpinchFor' : Submission.MetricScale.QuarterPinchedFor g' cov :=
    Submission.MetricScale.quarterPinchedFor_scale (I := I) (cov := cov) hc1 g' hinner hpinch hlt'
  have hsec' : ∀ (p : M) (u v : TangentSpace I p), g'.inner p u u = 1 → g'.inner p v v = 1 →
      g'.inner p u v = 0 → g'.inner p (curvVec cov p u v v) u ≤ 4 / c :=
    Submission.MetricScale.scaled_sec_le (I := I) (cov := cov) hc1 g' hinner hup4
  -- step 4: apply the sphere theorem to the rescaled metric, with `K = 4 / c < 4`
  exact sphere_theorem_of_metric (I := I) (cov := cov) hdim htor g' hsmooth' hmetFor' hpinchFor' hK
    (by positivity) (by rw [div_lt_iff₀ hcpos]; linarith [hc1]) hsec'

end

end Submission.Klingenberg
