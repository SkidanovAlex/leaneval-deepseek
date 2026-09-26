import Submission.Work.Smooth.JordanSeparation.NoSeparation
import Submission.Work.Smooth.JordanSeparation.SimpleCurves
import Submission.Work.Smooth.JordanSeparation.Corollaries

/-!
# The Jordan separation theorem for a `C¹` simple closed plane curve

This file records the **unconditional** form of the chapter's main theorem, obtained by
discharging the hypothesis `NoSeparationOfSubcontinuum` of `MainGeneral.lean` with
`Work.Smooth.JordanSeparation.noSeparationOfSubcontinuum` (byte-level proof in `NoSeparation.lean`).

## The class of curves

Everything is stated for a `C¹` (`ContDiff ℝ 1`) `2π`-periodic plane curve that is injective on one
period (`PlaneCurve.IsSimple`).  **No immersion hypothesis is used**: cusped curves such as
`t ↦ (t², t³)` are covered.  The `C¹` hypothesis is used only through the index theory of
`Submission/Work/Smooth/Jordan`.

## Main results

* `jordanSeparation_of_isSimple` — `Nonempty (PlaneSeparation c.toPlaneCurve)`: the complement of
  the trace of a `C¹` simple closed plane curve is the disjoint union of two non-empty preconnected
  open sets `U` (unbounded) and `V` (bounded);
* `planeSeparation_of_contDiff` — the same without the `SmoothPlaneCurve` wrapper, in the exact
  shape demanded by a `JordanInput`-style consumer;
* `nonempty_planeJordanSeparation_of_isSimple` — the separation together with the values of the
  index: `ind c x = 0` on `U`, `|ind c x| = 1` on `V`;
* `ind_eq_zero_of_mem_U_of_isSimple`, `ind_abs_eq_one_of_mem_V_of_isSimple` (in `SimpleCurves.lean`)
  — the same two index clauses for *any* `PlaneSeparation` of `c`;
* `SmoothSimpleInput` / `smoothSimpleInput`, `ContDiffSimpleInput` / `contDiffSimpleInput` — the
  hypotheses in packaged `Prop` form.

The Schoenflies half (a spanning embedded disc, `Work.Smooth.Jordan.PlaneSchoenflies`) is **not**
proved here; see the README for the exact reduction and what remains.
-/

open Set
open Work.Smooth.Jordan

namespace Work.Smooth.JordanSeparation

noncomputable section

/-! ## The two halves of the separation theorem -/

/-- **At most two components.**  Of any three points off the trace of a `C¹` simple closed plane
curve, two lie in the same component of the complement.  (The other half, *at least two
components*, is `exists_two_components_of_isSimple`.) -/
theorem atMostTwo_connectedComponentIn_of_isSimple (c : SmoothPlaneCurve)
    (hs : c.toPlaneCurve.IsSimple) :
    ∀ x y z : ℂ, x ∉ c.trace → y ∉ c.trace → z ∉ c.trace →
      connectedComponentIn c.traceᶜ x = connectedComponentIn c.traceᶜ y ∨
      connectedComponentIn c.traceᶜ x = connectedComponentIn c.traceᶜ z ∨
      connectedComponentIn c.traceᶜ y = connectedComponentIn c.traceᶜ z :=
  atMostTwo_of_noSeparation c hs (noSeparationOfSubcontinuum c hs)

/-- **Jordan separation for a `C¹` simple closed plane curve.**  The complement of the trace of a
`ContDiff ℝ 1`, `2π`-periodic curve injective on one period is the disjoint union of two non-empty
preconnected open sets `U` (unbounded) and `V` (bounded). -/
theorem jordanSeparation_of_isSimple (c : SmoothPlaneCurve) (hs : c.toPlaneCurve.IsSimple) :
    Nonempty (PlaneSeparation c.toPlaneCurve) :=
  jordanSeparation_of_noSeparation c hs (noSeparationOfSubcontinuum c hs)

/-- **Jordan separation with the index values, for a `C¹` simple closed plane curve.**  In
addition to the two sides, `ind c x = 0` for `x` on the unbounded side `U` and `|ind c x| = 1` for
`x` on the bounded side `V`.  This is `Work.Smooth.Jordan.PlaneJordanSchoenflies` without the
spanning disc. -/
theorem nonempty_planeJordanSeparation_of_isSimple (c : SmoothPlaneCurve)
    (hs : c.toPlaneCurve.IsSimple) : Nonempty (PlaneJordanSeparation c) := by
  obtain ⟨S⟩ := jordanSeparation_of_isSimple c hs
  exact ⟨{ sep := S
           ind_eq_zero_U := fun x hx => ind_eq_zero_of_mem_U_of_isSimple c hs hx
           ind_abs_eq_one_V := fun x hx => ind_abs_eq_one_of_mem_V_of_isSimple c hs hx }⟩

/-- **Jordan separation in the exact shape of `Work.Smooth.Jordan.JordanInput`.**  For a `C¹`
`2π`-periodic plane curve `c : ℝ → ℂ` which is injective on one period, the complement of its trace
is the disjoint union of two non-empty preconnected open sets, the unbounded side `U` and the
bounded side `V`.  This is `Nonempty (PlaneSeparation c)` itself, without going through the
`SmoothPlaneCurve` wrapper, and without any immersion hypothesis. -/
theorem planeSeparation_of_contDiff_of_isSimple (c : PlaneCurve) (hdiff : ContDiff ℝ 1 c.γ)
    (hs : c.IsSimple) : Nonempty (PlaneSeparation c) :=
  jordanSeparation_of_isSimple { c with contDiff := hdiff } hs

/-- **The class of curves covered by this chapter**: `C¹` `2π`-periodic curves injective on one
period (no immersion hypothesis). -/
def SmoothSimpleInput : Prop :=
  ∀ c : SmoothPlaneCurve, c.toPlaneCurve.IsSimple → Nonempty (PlaneSeparation c.toPlaneCurve)

/-- **`SmoothSimpleInput` holds.**  This is the Jordan curve theorem for `C¹` simple closed plane
curves. -/
theorem smoothSimpleInput : SmoothSimpleInput :=
  fun c hs => jordanSeparation_of_isSimple c hs

/-- **The class of curves covered by this chapter**, in the `PlaneCurve` form: `C¹` `2π`-periodic
curves injective on one period.  (For arbitrary *continuous* simple closed curves the theorem is
also true but is not reached by the index-theoretic route used here.) -/
def ContDiffSimpleInput : Prop :=
  ∀ c : PlaneCurve, ContDiff ℝ 1 c.γ → c.IsSimple → Nonempty (PlaneSeparation c)

/-- **`ContDiffSimpleInput` holds.** -/
theorem contDiffSimpleInput : ContDiffSimpleInput :=
  fun c hdiff hs => planeSeparation_of_contDiff_of_isSimple c hdiff hs

/-- **Jordan separation in the `JordanInput` shape, at a `C¹` curve.**  The sibling chapter's
`Work.Smooth.Jordan.JordanInput c` demands `PlaneCurve.IsSimple c → Nonempty (PlaneSeparation c)`;
the present chapter supplies it for `c` of class `C¹`. -/
theorem jordanInput_of_contDiff (c : PlaneCurve) (hdiff : ContDiff ℝ 1 c.γ) :
    JordanInput c :=
  fun hs => planeSeparation_of_contDiff_of_isSimple c hdiff hs

/-! ## The values of the index on the sides, unconditionally -/

/-- **A point off the trace lies on the unbounded side iff the index vanishes there.** -/
theorem mem_U_iff_ind_eq_zero_of_isSimple (c : SmoothPlaneCurve) (hs : c.toPlaneCurve.IsSimple)
    {S : PlaneSeparation c.toPlaneCurve} {x : ℂ} (hx : x ∉ c.trace) :
    x ∈ S.U ↔ ind c x = 0 := by
  constructor
  · intro h; exact ind_eq_zero_of_mem_U_of_isSimple c hs h
  · intro h
    by_contra hU
    have hV : x ∈ S.V := (S.union_eq ▸ hx : x ∈ S.U ∪ S.V).elim (fun h' => absurd h' hU) id
    have := ind_abs_eq_one_of_mem_V_of_isSimple c hs hV
    rw [h] at this; norm_num at this

/-- **A point off the trace lies on the bounded side iff the index does not vanish there.** -/
theorem mem_V_iff_ind_ne_zero_of_isSimple (c : SmoothPlaneCurve) (hs : c.toPlaneCurve.IsSimple)
    {S : PlaneSeparation c.toPlaneCurve} {x : ℂ} (hx : x ∉ c.trace) :
    x ∈ S.V ↔ ind c x ≠ 0 := by
  constructor
  · intro h h0
    have := ind_abs_eq_one_of_mem_V_of_isSimple c hs h
    rw [h0] at this; norm_num at this
  · intro h
    by_contra hV
    have hU : x ∈ S.U := (S.union_eq ▸ hx : x ∈ S.U ∪ S.V).elim id (fun h' => absurd h' hV)
    exact h (ind_eq_zero_of_mem_U_of_isSimple c hs hU)

/-- **`|ind| ≤ 1` off the trace**, for a `C¹` simple closed plane curve (no immersion
hypothesis). -/
theorem ind_abs_le_one_of_isSimple (c : SmoothPlaneCurve) (hs : c.toPlaneCurve.IsSimple)
    {S : PlaneSeparation c.toPlaneCurve} {x : ℂ} (hx : x ∉ c.trace) : |ind c x| ≤ 1 := by
  rcases (S.union_eq ▸ hx : x ∈ S.U ∪ S.V) with h | h
  · rw [ind_eq_zero_of_mem_U_of_isSimple c hs h]; norm_num
  · rw [ind_abs_eq_one_of_mem_V_of_isSimple c hs h]

/-- **The index takes only the values `0`, `1`, `-1` off the trace**, for a `C¹` simple closed
plane curve. -/
theorem ind_eq_zero_or_abs_eq_one_of_isSimple (c : SmoothPlaneCurve) (hs : c.toPlaneCurve.IsSimple)
    {S : PlaneSeparation c.toPlaneCurve} {x : ℂ} (hx : x ∉ c.trace) :
    ind c x = 0 ∨ ind c x = 1 ∨ ind c x = -1 := by
  rcases (S.union_eq ▸ hx : x ∈ S.U ∪ S.V) with h | h
  · exact Or.inl (ind_eq_zero_of_mem_U_of_isSimple c hs h)
  · have := ind_abs_eq_one_of_mem_V_of_isSimple c hs h
    rcases abs_cases (ind c x) with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Or.inr (Or.inl (by rw [h1] at this; exact this))
    · exact Or.inr (Or.inr (by rw [h1] at this; linarith))

/-! ## The two sides are the components of the complement, and the curve is their common frontier -/

/-- **The unbounded side is a component of the complement.** -/
theorem connectedComponentIn_eq_U_of_isSimple (c : SmoothPlaneCurve) (hs : c.toPlaneCurve.IsSimple)
    {S : PlaneSeparation c.toPlaneCurve} {u : ℂ} (hu : u ∈ S.U) :
    connectedComponentIn c.traceᶜ u = S.U := by
  have huc : u ∈ c.traceᶜ := by rw [← S.union_eq]; exact Or.inl hu
  refine Set.Subset.antisymm ?_ (S.preconn_U.subset_connectedComponentIn hu
    (fun w hw => by rw [← S.union_eq]; exact Or.inl hw))
  intro z hz
  have hzsub : z ∈ c.traceᶜ := connectedComponentIn_subset _ _ hz
  rcases (S.union_eq ▸ hzsub : z ∈ S.U ∪ S.V) with h | h
  · exact h
  · exfalso
    have hcov : connectedComponentIn c.traceᶜ u ⊆ S.U ∪ S.V := fun w hw => by
      rw [S.union_eq]; exact connectedComponentIn_subset _ _ hw
    rcases (isPreconnected_connectedComponentIn (F := c.traceᶜ) (x := u)).subset_or_subset
        S.isOpen_U S.isOpen_V S.disjoint_UV hcov with h' | h'
    · exact Set.disjoint_left.mp S.disjoint_UV (h' hz) h
    · exact Set.disjoint_left.mp S.disjoint_UV hu (h' (mem_connectedComponentIn huc))

/-- **The bounded side is a component of the complement.** -/
theorem connectedComponentIn_eq_V_of_isSimple (c : SmoothPlaneCurve) (hs : c.toPlaneCurve.IsSimple)
    {S : PlaneSeparation c.toPlaneCurve} {v : ℂ} (hv : v ∈ S.V) :
    connectedComponentIn c.traceᶜ v = S.V := by
  have hvc : v ∈ c.traceᶜ := by rw [← S.union_eq]; exact Or.inr hv
  refine Set.Subset.antisymm ?_ (S.preconn_V.subset_connectedComponentIn hv
    (fun w hw => by rw [← S.union_eq]; exact Or.inr hw))
  intro z hz
  have hzsub : z ∈ c.traceᶜ := connectedComponentIn_subset _ _ hz
  rcases (S.union_eq ▸ hzsub : z ∈ S.U ∪ S.V) with h | h
  · exfalso
    have hcov : connectedComponentIn c.traceᶜ v ⊆ S.U ∪ S.V := fun w hw => by
      rw [S.union_eq]; exact connectedComponentIn_subset _ _ hw
    rcases (isPreconnected_connectedComponentIn (F := c.traceᶜ) (x := v)).subset_or_subset
        S.isOpen_U S.isOpen_V S.disjoint_UV hcov with h' | h'
    · exact Set.disjoint_left.mp S.disjoint_UV (h' (mem_connectedComponentIn hvc)) hv
    · exact Set.disjoint_left.mp S.disjoint_UV h (h' hz)
  · exact h

/-- **The frontier of the unbounded side is the curve**, for a `C¹` simple closed plane curve. -/
theorem frontier_eq_trace_of_isSimple (c : SmoothPlaneCurve) (hs : c.toPlaneCurve.IsSimple)
    {S : PlaneSeparation c.toPlaneCurve} : frontier S.U = c.trace := by
  obtain ⟨u, hu⟩ := S.nonempty_U
  have huc : u ∈ c.traceᶜ := by rw [← S.union_eq]; exact Or.inl hu
  rw [← connectedComponentIn_eq_U_of_isSimple c hs hu]
  exact frontier_eq_trace_of_component c hs (noSeparationOfSubcontinuum c hs) huc

/-- **The frontier of the bounded side is the curve**, for a `C¹` simple closed plane curve. -/
theorem frontier_V_eq_trace_of_isSimple (c : SmoothPlaneCurve) (hs : c.toPlaneCurve.IsSimple)
    {S : PlaneSeparation c.toPlaneCurve} : frontier S.V = c.trace := by
  obtain ⟨v, hv⟩ := S.nonempty_V
  have hvc : v ∈ c.traceᶜ := by rw [← S.union_eq]; exact Or.inr hv
  rw [← connectedComponentIn_eq_V_of_isSimple c hs hv]
  exact frontier_eq_trace_of_component c hs (noSeparationOfSubcontinuum c hs) hvc

/-- **The closure of the unbounded side is the side together with the curve.** -/
theorem closure_U_eq_of_isSimple (c : SmoothPlaneCurve) (hs : c.toPlaneCurve.IsSimple)
    {S : PlaneSeparation c.toPlaneCurve} : closure S.U = S.U ∪ c.trace := by
  rw [closure_eq_self_union_frontier, frontier_eq_trace_of_isSimple c hs]

/-- **The closure of the bounded side is the side together with the curve.** -/
theorem closure_V_eq_of_isSimple (c : SmoothPlaneCurve) (hs : c.toPlaneCurve.IsSimple)
    {S : PlaneSeparation c.toPlaneCurve} : closure S.V = S.V ∪ c.trace := by
  rw [closure_eq_self_union_frontier, frontier_V_eq_trace_of_isSimple c hs]

/-! ## What the Schoenflies half would give -/

/-- **The full classical input of the sibling chapter, from separation plus a spanning disc.**
This is `Work.Smooth.Jordan.PlaneJordanSchoenflies c` for a `C¹` simple closed (not necessarily
immersed) curve, obtained from this chapter's separation together with the *only* remaining
classical input, a spanning disc `PlaneSchoenflies c.toPlaneCurve`.  It is recorded with an
explicit `PlaneSchoenflies` hypothesis: the Schoenflies theorem is not proved in this chapter. -/
def planeJordanSchoenflies_of_planeSchoenflies (c : SmoothPlaneCurve)
    (hs : c.toPlaneCurve.IsSimple) (hS : PlaneSchoenflies c.toPlaneCurve) :
    PlaneJordanSchoenflies c :=
  { sep := hS.toPlaneSeparation
    ind_eq_zero_U := fun _ hx => ind_eq_zero_of_mem_U_of_isSimple c hs hx
    ind_abs_eq_one_V := fun _ hx => ind_abs_eq_one_of_mem_V_of_isSimple c hs hx
    e := hS.e
    inj := hS.inj
    boundary := hS.boundary
    range_e := hS.range_e }

end

end Work.Smooth.JordanSeparation
