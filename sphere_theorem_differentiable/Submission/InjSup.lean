import Submission.InjRadiusCut
import Submission.CutWitness
import Submission.CutPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The global injectivity radius

`Submission/InjRadius.lean` works with the *pointwise* predicate `InjAtLeast hmet x r` ("`GExp x`
is injective on the ball of radius `r` in `T_xM`") and with the *uniform* predicate
`InjAllAtLeast hmet r` ("`InjAtLeast x r` for every `x`").  The classical Klingenberg estimate
(Petersen 6.5.1, Cheeger–Ebin 5.6) is stated in terms of the **injectivity radius of the manifold**
`inj(M) = inf_x inj(x)`, and its proof needs that number as an actual object with two properties:

* `InjAllAtLeast hmet injM` (the infimum is a lower bound for every point), and
* `¬ InjAllAtLeast hmet r` for every `r > injM` (maximality).

This file provides both, taking `injM` to be `sSup {r | InjAllAtLeast hmet r}`:

* `injSup hmet`: the global injectivity radius as a supremum;
* **`injAllAtLeast_injSup`**: `InjAllAtLeast hmet (injSup hmet)` — proved *without compactness*;
  the point is that the set `{r | InjAtLeast x r}` is downward closed and closed from below
  (if `InjAtLeast x r'` holds for all `r' < r`, then it holds at `r`, because a pair of witnesses
  at radius `r` already has a *finite* maximal norm);
* `injAtLeast_of_lt_injSup`, `injAllAtLeast_of_lt_injSup`: the downward-closed form;
* `not_injAllAtLeast_of_injSup_lt`: maximality, given that the set is bounded above;
* `exists_not_injAtLeast_of_diam_lt`: on a manifold where distances are attained and bounded by `D`,
  injectivity **fails** at every radius `> D`: a vector of norm `> D` whose image is closer than its
  norm is not a minimising ray, and a non-minimising ray already produces two distinct vectors of
  the same image below its norm (`CutWitness.exists_lt_of_not_minimising_ray` +
  `HopfRinow.exists_geodesic_riemannianEDist_eq`).  Together with
  `Klingenberg.exists_diam_pair` this yields the boundedness needed for the maximality statement.
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
open Submission.CutWitness
open Submission.GExpRay

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.InjSup

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **The injectivity radius of the manifold**, as the supremum of the radii at which the
exponential map is injective at every point. -/
noncomputable def injSup (hmet : IsMetricCompatible cov) : ℝ :=
  sSup {r : ℝ | InjAllAtLeast hmet r}

/-- `InjAtLeast x 0` holds trivially (the ball is empty). -/
theorem injAtLeast_zero (hmet : IsMetricCompatible cov) (x : M) : InjAtLeast hmet x 0 :=
  fun u v hu _ _ => absurd hu (not_lt_of_ge (norm_nonneg u))

/-- The set of radii of uniform injectivity is nonempty. -/
theorem injAllAtLeast_zero (hmet : IsMetricCompatible cov) : InjAllAtLeast hmet 0 :=
  fun x => injAtLeast_zero hmet x

/-- **Below the global injectivity radius, injectivity holds at every point.** -/
theorem injAllAtLeast_of_lt_injSup (hmet : IsMetricCompatible cov) {r : ℝ}
    (hr : r < injSup hmet) : InjAllAtLeast hmet r := by
  have hAne : ({r : ℝ | InjAllAtLeast hmet r}).Nonempty :=
    ⟨0, injAllAtLeast_zero hmet⟩
  obtain ⟨r', hr'A, hrr'⟩ := exists_lt_of_lt_csSup hAne hr
  exact fun p => injAtLeast_mono hmet (hr'A p) hrr'.le

/-- **The global injectivity radius is itself a radius of uniform injectivity.**
No compactness is needed: the set `{r | InjAtLeast x r}` is downward closed *and* closed from below,
because two witnesses at radius `r` already have a finite maximal norm. -/
theorem injAllAtLeast_injSup (hmet : IsMetricCompatible cov) : InjAllAtLeast hmet (injSup hmet) := by
  have hAne : ({r : ℝ | InjAllAtLeast hmet r}).Nonempty :=
    ⟨0, injAllAtLeast_zero hmet⟩
  intro p u v hu hv huv
  have hmax : max ‖u‖ ‖v‖ < injSup hmet := max_lt hu hv
  obtain ⟨r, hrA, hrlt⟩ := exists_lt_of_lt_csSup hAne hmax
  exact hrA p u v (lt_of_le_of_lt (le_max_left _ _) hrlt)
    (lt_of_le_of_lt (le_max_right _ _) hrlt) huv

/-- The pointwise downward-closed form. -/
theorem injAtLeast_of_lt_injSup (hmet : IsMetricCompatible cov) {p : M} {r : ℝ}
    (hr : r < injSup hmet) : InjAtLeast hmet p r :=
  injAtLeast_of_injAllAtLeast hmet (injAllAtLeast_of_lt_injSup hmet hr) p

/-- **Maximality of the global injectivity radius**: no larger radius is a radius of uniform
injectivity, provided the set of such radii is bounded above. -/
theorem not_injAllAtLeast_of_injSup_lt (hmet : IsMetricCompatible cov)
    (hbdd : BddAbove {r : ℝ | InjAllAtLeast hmet r}) {r : ℝ} (hr : injSup hmet < r) :
    ¬ InjAllAtLeast hmet r :=
  fun h => absurd (le_csSup hbdd h) (not_le.mpr hr)

/-- **A ray that is not minimising produces two distinct vectors with the same image.**  If
`d(x, GExp x (s • ξ)) < s` for a unit vector `ξ`, then there is a vector `w` with
`GExp x w = GExp x (s • ξ)` and `‖w‖ < s`, whence `(w, s • ξ)` is a witness pair and injectivity
fails at every radius above `s`. -/
theorem not_injAtLeast_of_edist_lt_norm (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {x : M} {ξ : TangentSpace I x} (hξ : ‖ξ‖ = 1) {s : ℝ} (hs : 0 < s)
    (hlt : Manifold.riemannianEDist I x (GExp (cov := cov) hmet x (s • ξ)) < ENNReal.ofReal s) :
    ∃ w : TangentSpace I x, ‖w‖ < s ∧
      GExp (cov := cov) hmet x w = GExp (cov := cov) hmet x (s • ξ) ∧ w ≠ s • ξ := by
  obtain ⟨w, hwG, hwd⟩ :=
    Submission.HopfRinow.exists_geodesic_riemannianEDist_eq (cov := cov) hmet htor x
      (GExp (cov := cov) hmet x (s • ξ))
  have hwlt : ‖w‖ < s := by
    have h := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top).mpr
      (by rw [hwd] at hlt; exact hlt)
    simpa [ENNReal.toReal_ofReal (norm_nonneg w), ENNReal.toReal_ofReal hs.le] using h
  have hsne : s • ξ ≠ w := by
    intro hcon
    have : ‖s • ξ‖ = ‖w‖ := by rw [hcon]
    rw [norm_smul, hξ, mul_one, Real.norm_of_nonneg hs.le] at this
    linarith
  exact ⟨w, hwlt, hwG, hsne.symm⟩

/-- **Injectivity fails above the diameter.**  If `GExp x (s • ξ)` is at distance `< s` from `x`
(for a unit `ξ`), then `InjAtLeast x r` fails for every `r > s`. -/
theorem not_injAtLeast_of_lt_diam (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {x : M} {D s : ℝ} (hs : 0 < s) (hDs : D < s)
    (hdiam : ∀ y : M, Manifold.riemannianEDist I x y ≤ ENNReal.ofReal D)
    {r : ℝ} (hr : s < r) : ¬ InjAtLeast hmet x r := by
  obtain ⟨e, he⟩ : ∃ e : E, e ≠ 0 := exists_ne 0
  have hfv : frameVector (I := I) x x e ≠ 0 := fun h =>
    he ((Submission.ChartBounds.frameVector_eq_zero_iff (I := I) (mem_chart_source H x) e).mp h)
  set ξ : TangentSpace I x := unitOf (frameVector (I := I) x x e) hfv with hξdef
  have hξ : ‖ξ‖ = 1 := unitOf_norm _ hfv
  have hlt : Manifold.riemannianEDist I x (GExp (cov := cov) hmet x (s • ξ)) < ENNReal.ofReal s := by
    have h1 : Manifold.riemannianEDist I x (GExp (cov := cov) hmet x (s • ξ)) ≤ ENNReal.ofReal D :=
      hdiam _
    have h2 : ENNReal.ofReal D < ENNReal.ofReal s := ENNReal.ofReal_lt_ofReal_iff hs |>.mpr hDs
    exact lt_of_le_of_lt h1 h2
  obtain ⟨w, hwlt, hwG, hwne⟩ := not_injAtLeast_of_edist_lt_norm (cov := cov) hmet htor hξ hs hlt
  intro hinj
  refine hwne ?_
  refine hinj w (s • ξ) (lt_trans hwlt hr) ?_ hwG
  rw [norm_smul, hξ, mul_one, Real.norm_of_nonneg hs.le]
  exact hr


/-- **Injectivity fails at a radius above a diameter bound.**  If every point is within distance `D`
of `x`, then `InjAtLeast x r` fails for every `r` above `max D 1`; hence `InjAllAtLeast` fails there
and the set of radii of uniform injectivity is bounded. -/
theorem not_injAllAtLeast_of_diam_le (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {x : M} {D : ℝ} (hdiam : ∀ y : M, Manifold.riemannianEDist I x y ≤ ENNReal.ofReal D) :
    ∃ r : ℝ, ¬ InjAllAtLeast hmet r := by
  set s : ℝ := max D 0 + 1 with hsdef
  have hspos : 0 < s := by rw [hsdef]; linarith [le_max_right D (0:ℝ)]
  have hDs : D < s := by
    have h1 : D ≤ max D 0 := le_max_left _ _
    rw [hsdef]; linarith
  refine ⟨s + 1, fun hcon => ?_⟩
  exact (not_injAtLeast_of_lt_diam (cov := cov) hmet htor hspos hDs hdiam
    (by linarith : s < s + 1)) (hcon x)

/-- **The set of radii of uniform injectivity is bounded above**, given a point with a finite
diameter bound. -/
theorem bddAbove_injAllAtLeast_of_diam_le (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {x : M} {D : ℝ} (hdiam : ∀ y : M, Manifold.riemannianEDist I x y ≤ ENNReal.ofReal D) :
    BddAbove {r : ℝ | InjAllAtLeast hmet r} := by
  obtain ⟨r₀, hr₀⟩ := not_injAllAtLeast_of_diam_le (cov := cov) hmet htor hdiam
  refine ⟨r₀, fun r hr => ?_⟩
  by_contra hcon
  rw [not_le] at hcon
  exact hr₀ (fun p => injAtLeast_mono hmet (show InjAtLeast hmet p r from hr p) hcon.le)

/-- **The global injectivity radius, packaged**: it is a radius of uniform injectivity, and no
larger radius is. -/
theorem injSup_spec (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {x : M} {D : ℝ} (hdiam : ∀ y : M, Manifold.riemannianEDist I x y ≤ ENNReal.ofReal D) :
    InjAllAtLeast hmet (injSup hmet) ∧
      ∀ r : ℝ, injSup hmet < r → ¬ InjAllAtLeast hmet r :=
  ⟨injAllAtLeast_injSup hmet,
    fun _ hr => not_injAllAtLeast_of_injSup_lt hmet
      (bddAbove_injAllAtLeast_of_diam_le (cov := cov) hmet htor hdiam) hr⟩

end

end Submission.InjSup
