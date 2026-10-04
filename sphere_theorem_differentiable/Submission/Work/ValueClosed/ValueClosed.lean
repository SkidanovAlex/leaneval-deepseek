import Submission.Work.ValueClosed.Defs
import Submission.Work.ValueClosed.Periodic
import Submission.Work.ValueClosed.Minimiser

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Submission.XuReduction.PinchedLoopLengthLowerBound`: the value-closed Klingenberg length bound,
from the closed-geodesic bound

## What this subproject delivers

The sibling subprojects `Submission/Work/EvenBound` and `Submission/Work/OddBound` prove, by parity of
the dimension, Klingenberg's length bound for **closed** geodesics (velocity matched at the base
point):

  `hclosed : ∀ p T γ, IsClosedGeodesicLoopAt hmet p T γ → 2π/√K ≤ T`,    (K)

while the reduction of the sphere theorem consumes the same bound for **value-closed** geodesic loops
(Xu's notion, `Submission.GeodesicLoop.IsGeodesicLoopAt`: a unit-speed global geodesic with
`γ 0 = γ T = p` and *no* velocity matching at the base point), i.e. the `Prop`

  `Submission.XuReduction.PinchedLoopLengthLowerBound (I := I) (cov := cov) hmet K`.

This file closes the gap.  **Main results:**

* `Work.ValueClosed.pinchedLoopLengthLowerBound` — (K) implies
  `PinchedLoopLengthLowerBound (I := I) (cov := cov) hmet K`, i.e. the packaged `Prop` consumed by
  `Submission.XuReduction.diameter_gt_half_pi_of_pinchedLoopLengthLowerBound`;
* `Work.ValueClosed.pinched_loop_length_lower_bound` — the same, with the explicit signature
  requested by the reduction (`hpinch`, `hK4` and `[SimplyConnectedSpace M]` are *present but unused*:
  the glue needs only `sec ≤ K`, `hclosed` and the loop).

**Import** `Submission.Work.ValueClosed.ValueClosed`.  The supporting API is in
`Submission.Work.ValueClosed.Defs` (`loopLengthSet`, `loopLengthInf`, and the structural lemmas
`loopLengthInf_le_of_isGeodesicLoopAt`, `two_mul_injSup_le_of_mem_loopLengthSet`, `loopLengthInf_pos`,
`injAllAtLeast_loopLengthInf_div_two`), `...Periodic` (`isClosedGeodesicLoopAt_of_ray_periodic`,
`GExp_return_of_raySeq_tendsto`) and `...Minimiser` (`loopLengthInf_attained`).

## The argument

Let `ℓ = loopLengthInf hmet` be the infimum of the lengths of value-closed geodesic loops.

* **The structural half** (`injAllAtLeast_loopLengthInf_div_two`): `InjAllAtLeast hmet (ℓ/2)`.  If
  some point `z` had maximal injectivity radius `m < ℓ/2`, then `m < π/√K`, the cut-point step
  (`Submission.RayConj.exists_two_minimising_of_injAtLeast_of_lt_pi_div_sqrt`) would produce two
  distinct minimising vectors of norm `m` with the same image, and the *proved* Klingenberg–Xu step
  (`Submission.XuReduction.klingenbergLoopStep`) a value-closed geodesic loop at `z` of length
  `≤ 2m < ℓ` — contradicting the definition of `ℓ`.
* **The compactness half** (`loopLengthInf_attained`): `ℓ` is attained, by a loop `γ*` at `p*`.  A
  minimising sequence of loops is turned into a sequence of unit initial velocities, a subsequence of
  which converges in a compact chart piece (`exists_chart_convergent_subseq`), and
  `Submission.GExpJointPt.tendsto_GExp_ray_length` identifies the limiting ray, which returns to its
  base point at time `ℓ` (this is where the positivity of `ℓ` is used).
* **The conclusion.**  With `m := ℓ/2` we have `ℓ = 2m`, the loop `γ*` has length `2m`, so `m` is the
  *maximal* injectivity radius at `p*` (every value-closed loop at `p*` has length `≥ 2m`).  Since
  `m < π/√K` (otherwise `ℓ ≥ 2π/√K` already), the cut-point step at `(p*, m)` gives two distinct
  minimising rays meeting at `q*` with opposite velocities, and — because `m` is a *uniform*
  injectivity radius — Xu's Theorem B applied at `p*` **and at `q*`** shows that the two directions
  are antipodal.  `Submission.KlingenbergEven.ray_periodic_of_two_minimising` then makes the ray of
  `p*` periodic of period `2m`: the shortest value-closed loop is a **closed** geodesic of length
  `ℓ`, to which (K) applies.  Hence `2π/√K ≤ ℓ ≤ T` for every value-closed loop.

The last step is the point of the interplay with the siblings: (K) alone does not bound a loop with a
corner at its base point, and it is the minimality of `ℓ` that makes the corner disappear (that is
also why simple connectivity is required for the unpinched statement: the flat Klein bottle has a
flush (value-closed) loop of length `2 inj(p)` which is *not* closed, so the pointwise statement is
false without the minimality/compactness argument used here).

## Honest status

The statement is proved **given** (K), exactly as requested; the closed-geodesic bound (K) itself
(equivalently Klingenberg 1961) is *not* proved here — that is the EvenBound/OddBound work.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.InjRadius

namespace Work.ValueClosed

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **The glue, given the minimiser.**  Assuming that the infimum `ℓ` of the lengths of value-closed
geodesic loops is attained (`hmin`), the closed-geodesic bound `hclosed` implies the value-closed
bound.  The final theorem `pinched_loop_length_lower_bound` supplies `hmin` from
`Work.ValueClosed.exists_isGeodesicLoopAt_loopLengthInf`. -/
theorem pinched_loop_length_lower_bound_of_minimiser
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {K : ℝ} (hK : 0 < K)
    (hcurv : Submission.RauchK.CurvLe cov K)
    (hclosed : ∀ (p : M) (T : ℝ) (γ : ℝ → M),
      Submission.KlingenbergLemma.IsClosedGeodesicLoopAt hmet p T γ →
      2 * Real.pi / Real.sqrt K ≤ T)
    (hmin : ∃ (p : M) (γ : ℝ → M),
      Submission.GeodesicLoop.IsGeodesicLoopAt (I := I) (cov := cov) hmet p
        (loopLengthInf (I := I) (cov := cov) hmet) γ)
    {p : M} {T : ℝ} {γ : ℝ → M}
    (hloop : Submission.GeodesicLoop.IsGeodesicLoopAt (I := I) (cov := cov) hmet p T γ) :
    2 * Real.pi / Real.sqrt K ≤ T := by
  set B : ℝ := Real.pi / Real.sqrt K with hB
  have hB2 : 2 * B = 2 * Real.pi / Real.sqrt K := by
    rw [hB]
    exact (mul_div_assoc 2 Real.pi (Real.sqrt K)).symm
  rw [← hB2]
  have hclosedB : ∀ (p' : M) (T' : ℝ) (γ' : ℝ → M),
      Submission.KlingenbergLemma.IsClosedGeodesicLoopAt hmet p' T' γ' → 2 * B ≤ T' :=
    fun p' T' γ' h => by
      have h' := hclosed p' T' γ' h
      rw [← hB2] at h'
      exact h'
  by_contra hcon
  have hTlt : T < 2 * B := not_le.mp hcon
  have hTmem : T ∈ loopLengthSet (I := I) (cov := cov) hmet := ⟨p, γ, hloop⟩
  have hne : (loopLengthSet (I := I) (cov := cov) hmet).Nonempty := ⟨T, hTmem⟩
  have hℓpos : 0 < loopLengthInf (I := I) (cov := cov) hmet :=
    loopLengthInf_pos (I := I) (cov := cov) hmet htor hne
  have hℓT : loopLengthInf (I := I) (cov := cov) hmet ≤ T :=
    loopLengthInf_le_of_mem hTmem
  obtain ⟨pstar, γstar, hloopstar⟩ := hmin
  set m : ℝ := loopLengthInf (I := I) (cov := cov) hmet / 2 with hm
  have hℓeq : loopLengthInf (I := I) (cov := cov) hmet = 2 * m := by rw [hm]; ring
  have hmpos : 0 < m := by linarith
  have hmπ : m < Real.pi / Real.sqrt K := by rw [← hB]; linarith
  -- the uniform injectivity radius at `m = ℓ/2`
  have hinjall : InjAllAtLeast hmet m :=
    injAllAtLeast_loopLengthInf_div_two (I := I) (cov := cov) hmet htor hcurv hK
      (by rw [hℓeq]; linarith)
  have hinjp : InjAtLeast hmet pstar m :=
    Submission.InjRadius.injAtLeast_of_injAllAtLeast (I := I) hmet hinjall pstar
  -- `m` is the maximal injectivity radius at `pstar`
  have hmaxp : ∀ r : ℝ, m < r → ¬ InjAtLeast hmet pstar r := by
    intro r hr hcon'
    have h2 := Submission.GeodesicLoop.IsGeodesicLoopAt.two_mul_le_injAtLeast (I := I)
      (cov := cov) hmet htor hloopstar hcon'
    rw [hℓeq] at h2
    linarith
  -- the flush (Klingenberg) configuration at `(pstar, m)`
  obtain ⟨ξ, η, hξ, hη, hξη, hmeet, -, -, -, -, -, hminξ, hminη⟩ :=
    Submission.RayConj.exists_broken_minimising_loop_of_injAtLeast_of_lt_pi_div_sqrt (cov := cov)
      hmet htor hcurv hK hmpos hmπ hinjp hmaxp
  have hminξm : Manifold.riemannianEDist I pstar (GExp (cov := cov) hmet pstar (m • ξ))
      = ENNReal.ofReal m := hminξ m ⟨hmpos.le, le_rfl⟩
  have hminηm : Manifold.riemannianEDist I pstar (GExp (cov := cov) hmet pstar (m • η))
      = ENNReal.ofReal m := by
    have h0 := hminη 0 ⟨le_rfl, hmpos.le⟩
    rw [sub_zero] at h0
    exact h0
  -- the ray of `ξ` is periodic of period `2m`
  have hper := Submission.KlingenbergEven.ray_periodic_of_two_minimising (cov := cov)
    hmet htor hcurv hK hmpos hmπ hinjp hmaxp hinjall hξ hη hξη hmeet hminξm hminηm
  -- hence a *closed* geodesic loop of length `2m = ℓ`
  have hclosedloop : Submission.KlingenbergLemma.IsClosedGeodesicLoopAt hmet pstar (2 * m)
      (fun s : ℝ => GExp (cov := cov) hmet pstar (s • ξ)) :=
    isClosedGeodesicLoopAt_of_ray_periodic (I := I) (cov := cov) hmet hξ hmpos hper
  have h1 := hclosedB pstar (2 * m) _ hclosedloop
  linarith

/-- **The packaged form consumed by the reduction.**  With the minimiser supplied, `hclosed` gives the
whole `Prop` `Submission.XuReduction.PinchedLoopLengthLowerBound`, i.e. the statement the project's
reduction to `(K2)` consumes: *for every metric with `sec ∈ [K/4, K]`, every value-closed geodesic
loop has length `≥ 2π/√K`* (the pinching hypothesis is simply discarded, as the bound is proved from
`hclosed` alone together with `sec ≤ K`). -/
theorem pinchedLoopLengthLowerBound_of_closedGeodesicBound
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {K : ℝ} (hK : 0 < K) (hcurv : Submission.RauchK.CurvLe cov K)
    (hclosed : ∀ (p : M) (T : ℝ) (γ : ℝ → M),
      Submission.KlingenbergLemma.IsClosedGeodesicLoopAt hmet p T γ →
      2 * Real.pi / Real.sqrt K ≤ T)
    (hmin : ∃ (p : M) (γ : ℝ → M),
      Submission.GeodesicLoop.IsGeodesicLoopAt (I := I) (cov := cov) hmet p
        (loopLengthInf (I := I) (cov := cov) hmet) γ) :
    Submission.XuReduction.PinchedLoopLengthLowerBound (I := I) (cov := cov) hmet K :=
  fun _hpinch _p _T _γ hloop =>
    pinched_loop_length_lower_bound_of_minimiser (I := I) (cov := cov) hmet htor hK hcurv
      hclosed hmin hloop

/-- **The content of the glue, without the hypotheses that the glue does not use.**  Here the
assumptions are exactly `0 < K`, `sec ≤ K` and the closed-geodesic bound (K); neither the pinching
hypothesis, nor `K < 4`, nor simple connectivity is needed. -/
theorem pinched_loop_length_lower_bound_core
    [PathConnectedSpace M] [RegularSpace M]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {K : ℝ} (hK : 0 < K)
    (hcurv : Submission.RauchK.CurvLe cov K)
    (hclosed : ∀ (p : M) (T : ℝ) (γ : ℝ → M),
      Submission.KlingenbergLemma.IsClosedGeodesicLoopAt hmet p T γ →
      2 * Real.pi / Real.sqrt K ≤ T)
    {p : M} {T : ℝ} {γ : ℝ → M}
    (hloop : Submission.GeodesicLoop.IsGeodesicLoopAt (I := I) (cov := cov) hmet p T γ) :
    2 * Real.pi / Real.sqrt K ≤ T := by
  have hne : (loopLengthSet (I := I) (cov := cov) hmet).Nonempty := ⟨T, ⟨p, γ, hloop⟩⟩
  have hpos : 0 < loopLengthInf (I := I) (cov := cov) hmet :=
    loopLengthInf_pos (I := I) (cov := cov) hmet htor hne
  exact pinched_loop_length_lower_bound_of_minimiser (I := I) (cov := cov) hmet htor hK hcurv
    hclosed (loopLengthInf_attained (I := I) (cov := cov) hmet htor hpos) hloop

/-- **THE DELIVERABLE.**  The value-closed Klingenberg length bound, from the closed-geodesic bound
of the sibling subprojects: for a compact, connected Riemannian manifold with `sec ≤ K` (`0 < K`),
if every **closed** geodesic loop has length `≥ 2π/√K`, then every **value-closed** geodesic loop
(`Submission.GeodesicLoop.IsGeodesicLoopAt`, no velocity matching at the base point) has length
`≥ 2π/√K`.

This is the statement requested by the reduction of the sphere theorem, with the signature it asked
for: the extra hypotheses `hpinch` (quarter-pinching) and `hK4` (`K < 4`) are *not used* — the bound
is forced by `hclosed` and `sec ≤ K` through Klingenberg's structure theorem — and
`[SimplyConnectedSpace M]` is likewise not needed by this glue. -/
theorem pinched_loop_length_lower_bound
    [PathConnectedSpace M] [RegularSpace M] [SimplyConnectedSpace M]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {K : ℝ} (hK : 0 < K) (hK4 : K < 4)
    (hcurv : Submission.RauchK.CurvLe cov K)
    (hpinch : ∀ (p : M) (u v : TangentSpace I p), ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
      K / 4 ≤ inner ℝ (Submission.CurvatureVec.curvVec cov p u v v) u)
    (hclosed : ∀ (p : M) (T : ℝ) (γ : ℝ → M),
      Submission.KlingenbergLemma.IsClosedGeodesicLoopAt hmet p T γ →
      2 * Real.pi / Real.sqrt K ≤ T)
    {p : M} {T : ℝ} {γ : ℝ → M}
    (hloop : Submission.GeodesicLoop.IsGeodesicLoopAt (I := I) (cov := cov) hmet p T γ) :
    2 * Real.pi / Real.sqrt K ≤ T := by
  have hne : (loopLengthSet (I := I) (cov := cov) hmet).Nonempty := ⟨T, ⟨p, γ, hloop⟩⟩
  have hpos : 0 < loopLengthInf (I := I) (cov := cov) hmet :=
    loopLengthInf_pos (I := I) (cov := cov) hmet htor hne
  exact pinched_loop_length_lower_bound_of_minimiser (I := I) (cov := cov) hmet htor hK hcurv
    hclosed (loopLengthInf_attained (I := I) (cov := cov) hmet htor hpos) hloop

/-- **The packaged `Prop`.**  Same statement as `pinched_loop_length_lower_bound`, in the form in
which the reduction consumes it: `Submission.XuReduction.PinchedLoopLengthLowerBound (I := I)
(cov := cov) hmet K`. -/
theorem pinchedLoopLengthLowerBound
    [PathConnectedSpace M] [RegularSpace M]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {K : ℝ} (hK : 0 < K)
    (hcurv : Submission.RauchK.CurvLe cov K)
    (hclosed : ∀ (p : M) (T : ℝ) (γ : ℝ → M),
      Submission.KlingenbergLemma.IsClosedGeodesicLoopAt hmet p T γ →
      2 * Real.pi / Real.sqrt K ≤ T) :
    Submission.XuReduction.PinchedLoopLengthLowerBound (I := I) (cov := cov) hmet K :=
  fun _hpinch p T γ hloop =>
    pinched_loop_length_lower_bound_core hmet htor hK hcurv hclosed hloop

end

end Work.ValueClosed
