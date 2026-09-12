import Mathlib
import Submission.PolyaShell
import Submission.DirSet
import Submission.DirCycle

/-!
# The telescoping fold: summing the annular-sector cell identities

Every verified cell of the E2b deformation gives the vanishing of the
rectangle-boundary integral of the pulled-back 1-form
`F(w) := h (exp w) · exp w` over its w-rectangle `[[a,b]] ×ℂ [[c,d]]`
(`Submission.PolyaShell.sector_cell_boundary_integral_eq_zero`), i.e.

    cellExpr F a b c d = 0

where `cellExpr` is the four-side boundary expression: two radial side
integrals (at the angles `c`, `d`, from `Re = a` to `Re = b`) and two arc
integrals (at radii `e^a`, `e^b`, over the angles `c..d`), the latter with
the `I`-factors coming from the change of variables `X = exp w`.

This module proves the *summation bookkeeping* that turns the local cell
identities into the global identity:

  `cellExpr_add_adjacent`: two cells in the same angular gap sharing the
  radial boundary at angle `m` glue together -- their shared radial side
  appears with opposite signs and cancels, so the sum of the two cell
  identities is the identity for the combined angular range (this is the
  heart of the fold; it is a pure interval-integral identity, no analysis);

  `cellExpr_sum_range`: over a sequence `t₀ < t₁ < … < tₙ` of angles, the
  sum of the cell identities over the consecutive pairs is the identity for
  `[t₀, tₙ]` -- the radial sides telescope and the arcs add by
  `intervalIntegral.sum_integral_adjacent_intervals`;

  `gap_cell_zero`: the bridge instantiating the per-cell Cauchy identity
  (from the `hno`-type gap hypothesis and the direction-set facts) in
  `cellExpr` form.

MAIN DEFORMATION THEOREM (stated; proved in later sessions): take
`t_j := (dirList S)`-entries bounding the angular gaps of the hedgehog;
choose, inside each gap, a cell angle-range (and, around each direction, the
wedge/cap cells at distance `ε`, and the wrap cell after the last direction
via `exp`-periodicity); the summed identities give

    ∮_{|X|=ρ} h dX  =  ∮_Γ h dX

for a contour `Γ ⊆ FatStar S ε` surrounding `star S` (with `Γ` at positive
distance from `star S`), which is the analytic input of the Pólya/Hankel
estimate (E2c).  All the analytic content is in the cell identity; this
module supplies the fold.
-/

noncomputable section

open scoped Complex Real Interval
open Complex

namespace Submission.Fold

open Submission.PolyaShell

/-- Radial-side integral: along the ray at angle `c`, from `Re = a` to
`Re = b` in the `w = x + c·I` parametrization. -/
def radInt (F : ℂ → ℂ) (a b c : ℝ) : ℂ :=
  (∫ x : ℝ in a..b, F (x + c * Complex.I))

/-- Arc integral: at `Re = u` (radius `e^u`), over the angular range
`[c,d]` in the `w = u + y·I` parametrization. -/
def arcInt (F : ℂ → ℂ) (u c d : ℝ) : ℂ :=
  (∫ y : ℝ in c..d, F (u + y * Complex.I))

/-- The four-side boundary integral of the pulled-back 1-form `F` over the
w-rectangle `[[a,b]] ×ℂ [[c,d]]` (the rectangle-boundary expression of the
Cauchy theorem): two radial-side integrals at angles `c`, `d` and two arc
integrals at `Re = b`, `Re = a` over the angles `c..d`. -/
def cellExpr (F : ℂ → ℂ) (a b c d : ℝ) : ℂ :=
  radInt F a b c - radInt F a b d + Complex.I • arcInt F b c d
    - Complex.I • arcInt F a c d

/-- Radial-side integrals telescope over the angle: the `m`-terms cancel. -/
lemma radial_telescope_two (F : ℂ → ℂ) (a b c m d : ℝ) :
    (radInt F a b c - radInt F a b m) +
    (radInt F a b m - radInt F a b d) =
    radInt F a b c - radInt F a b d := by
  abel

/-- Arc integrals glue over adjacent intervals (bottom arc at `Re = b`). -/
lemma arc_add_adjacent_b (F : ℂ → ℂ) (b c m d : ℝ)
    (hbmc : IntervalIntegrable (fun y : ℝ => F (b + y * Complex.I))
      MeasureTheory.volume c m)
    (hbmd : IntervalIntegrable (fun y : ℝ => F (b + y * Complex.I))
      MeasureTheory.volume m d) :
    arcInt F b c m + arcInt F b m d = arcInt F b c d := by
  unfold arcInt
  exact intervalIntegral.integral_add_adjacent_intervals hbmc hbmd

/-- Arc integrals glue over adjacent intervals (top arc at `Re = a`). -/
lemma arc_add_adjacent_a (F : ℂ → ℂ) (a c m d : ℝ)
    (hamc : IntervalIntegrable (fun y : ℝ => F (a + y * Complex.I))
      MeasureTheory.volume c m)
    (hamd : IntervalIntegrable (fun y : ℝ => F (a + y * Complex.I))
      MeasureTheory.volume m d) :
    arcInt F a c m + arcInt F a m d = arcInt F a c d := by
  unfold arcInt
  exact intervalIntegral.integral_add_adjacent_intervals hamc hamd

/-- **Two adjacent cells glue.**  Two annular-sector cells over the same
radial range `[a,b]` and adjacent angular ranges `[c,m]`, `[m,d]` share the
radial boundary at angle `m`, which appears with opposite signs and cancels:
the sum of the two cell expressions is the cell expression over `[c,d]`.
(Pure interval-integral identity.) -/
lemma cellExpr_add_adjacent (F : ℂ → ℂ) (a b c m d : ℝ)
    (hbmc : IntervalIntegrable (fun y : ℝ => F (b + y * Complex.I))
      MeasureTheory.volume c m)
    (hbmd : IntervalIntegrable (fun y : ℝ => F (b + y * Complex.I))
      MeasureTheory.volume m d)
    (hamc : IntervalIntegrable (fun y : ℝ => F (a + y * Complex.I))
      MeasureTheory.volume c m)
    (hamd : IntervalIntegrable (fun y : ℝ => F (a + y * Complex.I))
      MeasureTheory.volume m d) :
    cellExpr F a b c m + cellExpr F a b m d = cellExpr F a b c d := by
  classical
  have harcb : arcInt F b c m + arcInt F b m d = arcInt F b c d :=
    arc_add_adjacent_b F b c m d hbmc hbmd
  have harCa : arcInt F a c m + arcInt F a m d = arcInt F a c d :=
    arc_add_adjacent_a F a c m d hamc hamd
  have hIb : Complex.I • arcInt F b c m + Complex.I • arcInt F b m d =
      Complex.I • arcInt F b c d := by
    rw [← smul_add]
    exact congrArg (fun t : ℂ => Complex.I • t) harcb
  have hIa : Complex.I • arcInt F a c m + Complex.I • arcInt F a m d =
      Complex.I • arcInt F a c d := by
    rw [← smul_add]
    exact congrArg (fun t : ℂ => Complex.I • t) harCa
  calc
    cellExpr F a b c m + cellExpr F a b m d
        = radInt F a b c - radInt F a b d
            + (Complex.I • arcInt F b c m + Complex.I • arcInt F b m d)
            - (Complex.I • arcInt F a c m + Complex.I • arcInt F a m d) := by
          unfold cellExpr
          abel
    _ = radInt F a b c - radInt F a b d
            + Complex.I • arcInt F b c d - Complex.I • arcInt F a c d := by
          rw [hIb, hIa]
    _ = cellExpr F a b c d := by
          unfold cellExpr
          abel

/-- A degenerate cell (empty angular range) vanishes. -/
lemma cellExpr_self (F : ℂ → ℂ) (a b c : ℝ) : cellExpr F a b c c = 0 := by
  unfold cellExpr radInt arcInt
  rw [intervalIntegral.integral_same, intervalIntegral.integral_same]
  abel

/-- Radial-side integrals telescope over a whole range. -/
lemma radInt_sum_range (F : ℂ → ℂ) (a b : ℝ) (t : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, radInt F a b (t j)) -
      (∑ j ∈ Finset.range n, radInt F a b (t (j + 1))) =
    radInt F a b (t 0) - radInt F a b (t n) := by
  have h := Finset.sum_range_sub' (fun j : ℕ => radInt F a b (t j)) n
  simpa [Finset.sum_sub_distrib] using h

/-- The `I`-scaled bottom arcs telescope over adjacent intervals. -/
lemma smul_arc_sum_range_b (F : ℂ → ℂ) (b : ℝ) (t : ℕ → ℝ) (n : ℕ)
    (hb : ∀ j : ℕ, j < n → IntervalIntegrable
      (fun y : ℝ => F (b + y * Complex.I)) MeasureTheory.volume (t j) (t (j + 1))) :
    (∑ j ∈ Finset.range n, Complex.I • arcInt F b (t j) (t (j + 1))) =
      Complex.I • arcInt F b (t 0) (t n) := by
  rw [← Finset.smul_sum]
  congr 1
  simpa [arcInt] using (intervalIntegral.sum_integral_adjacent_intervals
    (f := fun y : ℝ => F (b + y * Complex.I)) (a := t) (n := n) hb)

/-- The `I`-scaled top arcs telescope over adjacent intervals. -/
lemma smul_arc_sum_range_a (F : ℂ → ℂ) (a : ℝ) (t : ℕ → ℝ) (n : ℕ)
    (ha : ∀ j : ℕ, j < n → IntervalIntegrable
      (fun y : ℝ => F (a + y * Complex.I)) MeasureTheory.volume (t j) (t (j + 1))) :
    (∑ j ∈ Finset.range n, Complex.I • arcInt F a (t j) (t (j + 1))) =
      Complex.I • arcInt F a (t 0) (t n) := by
  rw [← Finset.smul_sum]
  congr 1
  simpa [arcInt] using (intervalIntegral.sum_integral_adjacent_intervals
    (f := fun y : ℝ => F (a + y * Complex.I)) (a := t) (n := n) ha)

/-- **The telescoping fold.**  Over a sequence `t : ℕ → ℝ` of angles, the
sum of the cell expressions over the consecutive pairs `(t j, t (j+1))`,
`j < n`, is the cell expression over `[t 0, t n]`: radial sides telescope,
arcs add over adjacent intervals. -/
lemma cellExpr_sum_range (F : ℂ → ℂ) (a b : ℝ) (t : ℕ → ℝ) (n : ℕ)
    (hb : ∀ j : ℕ, j < n → IntervalIntegrable
      (fun y : ℝ => F (b + y * Complex.I)) MeasureTheory.volume (t j) (t (j + 1)))
    (ha : ∀ j : ℕ, j < n → IntervalIntegrable
      (fun y : ℝ => F (a + y * Complex.I)) MeasureTheory.volume (t j) (t (j + 1))) :
    (∑ j ∈ Finset.range n, cellExpr F a b (t j) (t (j + 1))) =
      cellExpr F a b (t 0) (t n) := by
  classical
  calc
    (∑ j ∈ Finset.range n, cellExpr F a b (t j) (t (j + 1)))
        = (∑ j ∈ Finset.range n,
            (radInt F a b (t j) - radInt F a b (t (j + 1))
              + Complex.I • arcInt F b (t j) (t (j + 1))
              - Complex.I • arcInt F a (t j) (t (j + 1)))) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          rfl
    _ = (∑ j ∈ Finset.range n, radInt F a b (t j))
          - (∑ j ∈ Finset.range n, radInt F a b (t (j + 1)))
          + (∑ j ∈ Finset.range n, Complex.I • arcInt F b (t j) (t (j + 1)))
          - (∑ j ∈ Finset.range n, Complex.I • arcInt F a (t j) (t (j + 1))) := by
          simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
            sub_eq_add_neg, Finset.sum_neg_distrib]
    _ = radInt F a b (t 0) - radInt F a b (t n)
          + Complex.I • arcInt F b (t 0) (t n)
          - Complex.I • arcInt F a (t 0) (t n) := by
          rw [radInt_sum_range F a b t n,
            smul_arc_sum_range_b F b t n hb, smul_arc_sum_range_a F a t n ha]
    _ = cellExpr F a b (t 0) (t n) := by
          unfold cellExpr
          abel

/-- **Vanishing of the folded identity from vanishing cells.**  If every
cell over consecutive pairs `(t j, t (j+1))` satisfies the Cauchy identity
(`cellExpr … = 0`), then the cell over the whole range `[t 0, t n]` also
vanishes (with the same integrability hypotheses as the fold). -/
lemma cellExpr_sum_zero (F : ℂ → ℂ) (a b : ℝ) (t : ℕ → ℝ) (n : ℕ)
    (hz : ∀ j : ℕ, j < n → cellExpr F a b (t j) (t (j + 1)) = 0)
    (hb : ∀ j : ℕ, j < n → IntervalIntegrable
      (fun y : ℝ => F (b + y * Complex.I)) MeasureTheory.volume (t j) (t (j + 1)))
    (ha : ∀ j : ℕ, j < n → IntervalIntegrable
      (fun y : ℝ => F (a + y * Complex.I)) MeasureTheory.volume (t j) (t (j + 1))) :
    cellExpr F a b (t 0) (t n) = 0 := by
  classical
  rw [← cellExpr_sum_range F a b t n hb ha]
  exact Finset.sum_eq_zero (fun j hj => hz j (by simpa using hj))

/-- The per-cell Cauchy identity (in `cellExpr` form) for the pulled-back
integrand `w ↦ h (exp w) * exp w`, when the stated rectangle boundary
identity holds. -/
lemma pullback_cell_zero (h : ℂ → ℂ) (a b c d : ℝ)
    (hs : (∫ x : ℝ in a..b,
          h (Complex.exp (x + c * Complex.I)) * Complex.exp (x + c * Complex.I)) -
        (∫ x : ℝ in a..b,
          h (Complex.exp (x + d * Complex.I)) * Complex.exp (x + d * Complex.I)) +
        Complex.I • (∫ y : ℝ in c..d,
          h (Complex.exp (b + y * Complex.I)) * Complex.exp (b + y * Complex.I)) -
        Complex.I • (∫ y : ℝ in c..d,
          h (Complex.exp (a + y * Complex.I)) * Complex.exp (a + y * Complex.I)) = 0) :
    cellExpr (fun w : ℂ => h (Complex.exp w) * Complex.exp w) a b c d = 0 := by
  simpa [cellExpr, radInt, arcInt] using hs

/-- **Gap-cell Cauchy identity in `cellExpr` form.**  Under the gap
hypothesis (no spike-endpoint argument in `[c,d] ⊆ (-π,π]`), the pulled-back
cell over `[[a,b]] ×ℂ [[c,d]]` has zero boundary integral. -/
lemma gap_cell_zero {S : Finset ℂ} (hS0 : ∀ z ∈ S, z ≠ 0)
    {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Submission.XTransfer.star S)ᶜ)
    (a b : ℝ) {c d : ℝ} (hc : c < d) (hcl : -π < c) (hdu : d ≤ π)
    (hno : ∀ z ∈ S,
      Complex.arg (z ^ 2) ∉ Set.Icc c d ∧ Complex.arg (z ^ 4) ∉ Set.Icc c d) :
    cellExpr (fun w : ℂ => h (Complex.exp w) * Complex.exp w) a b c d = 0 := by
  exact pullback_cell_zero h a b c d
    (sector_cell_boundary_integral_eq_zero (S := S) hS0 hh a b hc hcl hdu hno)

end Submission.Fold

end
