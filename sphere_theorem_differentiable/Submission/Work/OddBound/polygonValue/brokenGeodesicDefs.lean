import Mathlib
import Submission.SegmentDomain
import Submission.Work.OddBound.PolygonModel
import Submission.Work.OddBound.polygonValue.Basic
import Submission.Work.OddBound.polygon.riemannianDist_eq_toReal

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The balanced broken-geodesic family: definitions

This module sets up the vocabulary of `Work.OddBound.polygonValue.brokenGeodesicFamily`.

Given a based closed `N`-gon `w` (its interior vertices), the *side* `i : Fin N` joins
`gonVert p w i` to `gonVert p w (i+1)`.  When the side is shorter than the injectivity radius, it
carries a unique *segment-domain* vector `sideVec`, and `sideCurve i r` is the point at parameter `r`
of the minimising geodesic of that side.

`sideLen`, `cumLen`, `totLen` are the side lengths, their partial sums and their total.  The closed
loop of the slice `t` is then parametrised *proportionally to arclength*: `glue t u` is the point of
the broken geodesic at arclength `totLen t * u`; the index of the side containing that arclength is
`slot`, and `balancedLoop s t = glue t (fract s)` is the 1-periodic-in-`s` family of loops.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open Submission.Geodesic Submission.GlobalExp Submission.Length Submission.InjRadius
open Submission.SegmentDomain Submission.Distance

namespace Work.OddBound.polygonValue

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
variable [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-! ## 1. Clamping -/

/-- Clamp a real number to the interval `[0,1]`. -/
def clamp01 (x : ℝ) : ℝ := max 0 (min x 1)

theorem clamp01_continuous : Continuous clamp01 := by
  show Continuous fun x : ℝ => max 0 (min x 1)
  fun_prop

theorem clamp01_nonneg (x : ℝ) : 0 ≤ clamp01 x := le_max_left _ _

theorem clamp01_le_one (x : ℝ) : clamp01 x ≤ 1 :=
  max_le (by norm_num) (min_le_right _ _)

theorem clamp01_mem (x : ℝ) : clamp01 x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨clamp01_nonneg x, clamp01_le_one x⟩

theorem clamp01_eq_self {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : clamp01 x = x := by
  show max 0 (min x 1) = x
  rw [min_eq_left h1, max_eq_right h0]

theorem clamp01_eq_zero_of_nonpos {x : ℝ} (h : x ≤ 0) : clamp01 x = 0 := by
  show max 0 (min x 1) = 0
  rw [min_eq_left (le_trans h zero_le_one), max_eq_left h]

theorem clamp01_eq_one_of_one_le {x : ℝ} (h : 1 ≤ x) : clamp01 x = 1 := by
  show max 0 (min x 1) = 1
  rw [min_eq_right h, max_eq_right zero_le_one]

theorem clamp01_idem (x : ℝ) : clamp01 (clamp01 x) = clamp01 x :=
  clamp01_eq_self (clamp01_nonneg x) (clamp01_le_one x)

/-! ## 2. The sides of a slice -/

/-- The `i`-th side length of the slice at `t`. -/
noncomputable def sideLen (p : M) {N : ℕ} (w : ℝ → Fin (N - 1) → M) (t : ℝ) (i : ℕ) : ℝ :=
  gonSideLen (I := I) p (w t) i

/-- The partial sums of the side lengths of the slice at `t`. -/
noncomputable def cumLen (p : M) {N : ℕ} (w : ℝ → Fin (N - 1) → M) (t : ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range i, sideLen (I := I) p w t j

/-- The total length of the slice at `t`. -/
noncomputable def totLen (p : M) {N : ℕ} (w : ℝ → Fin (N - 1) → M) (t : ℝ) : ℝ :=
  gonLength (I := I) p (w t)

theorem sideLen_nonneg (p : M) {N : ℕ} (w : ℝ → Fin (N - 1) → M) (t : ℝ) (i : ℕ) :
    0 ≤ sideLen (I := I) p w t i :=
  gonSideLen_nonneg (I := I) p (w t) i

theorem cumLen_zero (p : M) {N : ℕ} (w : ℝ → Fin (N - 1) → M) (t : ℝ) :
    cumLen (I := I) p w t 0 = 0 := by
  simp [cumLen]

theorem cumLen_succ (p : M) {N : ℕ} (w : ℝ → Fin (N - 1) → M) (t : ℝ) (i : ℕ) :
    cumLen (I := I) p w t (i + 1) = cumLen (I := I) p w t i + sideLen (I := I) p w t i := by
  simp [cumLen, Finset.sum_range_succ]

theorem cumLen_nonneg (p : M) {N : ℕ} (w : ℝ → Fin (N - 1) → M) (t : ℝ) (i : ℕ) :
    0 ≤ cumLen (I := I) p w t i :=
  Finset.sum_nonneg fun j _ => sideLen_nonneg (I := I) p w t j

theorem cumLen_mono (p : M) {N : ℕ} (w : ℝ → Fin (N - 1) → M) (t : ℝ) {i j : ℕ} (h : i ≤ j) :
    cumLen (I := I) p w t i ≤ cumLen (I := I) p w t j := by
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h) ?_
  intro k _ _; exact sideLen_nonneg (I := I) p w t k

theorem totLen_eq_cumLen (p : M) {N : ℕ} (w : ℝ → Fin (N - 1) → M) (t : ℝ) :
    totLen (I := I) p w t = cumLen (I := I) p w t N := by
  simp only [totLen, gonLength, cumLen, sideLen]
  rw [Finset.sum_fin_eq_sum_range]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < N := Finset.mem_range.mp hi
  simp [hi']

theorem totLen_nonneg (p : M) {N : ℕ} (w : ℝ → Fin (N - 1) → M) (t : ℝ) :
    0 ≤ totLen (I := I) p w t :=
  gonLength_nonneg (I := I) p (w t)

/-! ## 3. The segment-domain vector of a side and the side curve -/

/-- The segment-domain vector of the side `i` of the polygon `w`: the unique
`v ∈ segmentDomain hmet (gonVert p w i)` with `GExp (gonVert p w i) v = gonVert p w (i+1)`
(a junk value if there is none). -/
noncomputable def sideVec (hmet : IsMetricCompatible cov) (p : M) {N : ℕ}
    (w : Fin (N - 1) → M) (i : Fin N) : TangentSpace I (gonVert p w (i : ℕ)) := by
  classical
  exact if h : ∃ v : TangentSpace I (gonVert p w (i : ℕ)),
      v ∈ segmentDomain hmet (gonVert p w (i : ℕ)) ∧
        GExp (cov := cov) hmet (gonVert p w (i : ℕ)) v = gonVert p w ((i : ℕ) + 1)
    then Classical.choose h else 0

/-- The point at parameter `r` of the minimising geodesic of the side `i`. -/
noncomputable def sideCurve (hmet : IsMetricCompatible cov) (p : M) {N : ℕ}
    (w : Fin (N - 1) → M) (i : Fin N) (r : ℝ) : M :=
  GExp (cov := cov) hmet (gonVert p w (i : ℕ)) (r • sideVec hmet p w i)

/-! ## 4. The side containing a given arclength, and the balanced curve -/

/-- The number of sides entirely before the arclength `a` of the slice at `t`. -/
noncomputable def slotIdx (p : M) {N : ℕ} (w : ℝ → Fin (N - 1) → M) (t a : ℝ) : ℕ := by
  classical
  exact ((Finset.range N).filter (fun i => cumLen (I := I) p w t (i + 1) < a)).card

theorem slotIdx_le (p : M) {N : ℕ} (w : ℝ → Fin (N - 1) → M) (t a : ℝ) :
    slotIdx (I := I) p w t a ≤ N := by
  classical
  have h := Finset.card_le_card (Finset.filter_subset
    (fun i => cumLen (I := I) p w t (i + 1) < a) (Finset.range N))
  simpa [slotIdx] using h

/-- The index of the side containing the arclength `a` of the slice at `t` (clamped to `Fin N`). -/
noncomputable def slot (p : M) {N : ℕ} (hN : 0 < N) (w : ℝ → Fin (N - 1) → M)
    (t a : ℝ) : Fin N :=
  ⟨min (slotIdx (I := I) p w t a) (N - 1), by
    have h := slotIdx_le (I := I) p w t a
    have h2 : N - 1 < N := Nat.sub_lt hN (by norm_num)
    omega⟩

/-- The point of the broken geodesic of the slice `t` at arclength `a`. -/
noncomputable def sideOfPoint (hmet : IsMetricCompatible cov) (p : M) {N : ℕ} (hN : 0 < N)
    (w : ℝ → Fin (N - 1) → M) (t a : ℝ) : M :=
  sideCurve hmet p (w t) (slot (I := I) p hN w t a)
    (clamp01 ((a - cumLen (I := I) p w t (slot (I := I) p hN w t a)) /
      sideLen (I := I) p w t (slot (I := I) p hN w t a)))

/-- The arclength-proportional parametrisation of the slice at `t`: `glue t u` is the point of the
broken geodesic at arclength `totLen t * u`. -/
noncomputable def glue (hmet : IsMetricCompatible cov) (p : M) {N : ℕ} (hN : 0 < N)
    (w : ℝ → Fin (N - 1) → M) (t u : ℝ) : M :=
  if totLen (I := I) p w (clamp01 t) = 0 then p
  else sideOfPoint hmet p hN w (clamp01 t) (totLen (I := I) p w (clamp01 t) * u)

/-- **The balanced broken-geodesic family**: the 1-periodic-in-`s` family of loops whose slice at
`t` traverses the broken geodesic of the polygon `w t` proportionally to arclength. -/
noncomputable def balancedLoop (hmet : IsMetricCompatible cov) (p : M) {N : ℕ} (hN : 0 < N)
    (w : ℝ → Fin (N - 1) → M) (s t : ℝ) : M :=
  glue hmet p hN w t (Int.fract s)

end

end Work.OddBound.polygonValue
