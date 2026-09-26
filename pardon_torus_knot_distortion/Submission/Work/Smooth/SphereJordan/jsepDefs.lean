import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.planeIndexGeom

/-!
# An unconditional Jordan separation datum for a simple closed plane curve

The workspace's `Work.Smooth.Jordan.PlaneSeparation` (Jordan separation: the complement of a simple
closed plane curve is the disjoint union of two non-empty preconnected open sets, the bounded side
`V` and the unbounded side `U`) is what the whole `Work.Smooth.SphereJordan` chapter consumes.

Here we isolate the *canonical* datum which the two unconditional tools available in this workspace
(`Work.Topology.PlaneCurve.compl_jordan_atMostTwo`, the "at most two components" half, and
`Work.Smooth.SphereJordan.exists_windNumber_ne_zero`, the "at least two components" half via the
winding number) produce:

* `U` is the connected component of a point far outside the trace (the **unbounded side**): the
  winding number vanishes identically on it;
* `V` is the component of a point of non-zero winding number (the **bounded side**): the winding
  number is the constant non-zero value there.

The extra fields beyond `Work.Smooth.Jordan.PlaneSeparation` record exactly the facts the
"removal of a disc glued to a side" argument (the `bumpSideV` / `bumpSideU` step, i.e. the
replacement of a boundary arc of the curve by the complementary arc of the disc) needs: the
frontier of each side is the whole trace, and the vanishing of the winding number characterises the
unbounded side.
-/

open Set

namespace Work.Smooth.SphereJordan

noncomputable section

/-- **An unconditional Jordan separation datum** for a simple closed plane curve `γ`: the
complement of the trace is the disjoint union of two non-empty open preconnected sets `U` (the
unbounded side, on which the winding number vanishes identically) and `V` (the bounded side, on
which the winding number is a non-zero constant). -/
structure JSep (γ : Work.Smooth.Jordan.PlaneCurve) where
  /-- the unbounded side -/
  U : Set ℂ
  /-- the bounded side -/
  V : Set ℂ
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  preconn_U : IsPreconnected U
  preconn_V : IsPreconnected V
  nonempty_U : U.Nonempty
  nonempty_V : V.Nonempty
  disjoint_UV : Disjoint U V
  union_eq : U ∪ V = γ.traceᶜ
  /-- the bounded side is bounded -/
  bounded_V : Bornology.IsBounded V
  /-- the frontier of the unbounded side is the trace -/
  frontier_U : frontier U = γ.trace
  /-- the frontier of the bounded side is the trace -/
  frontier_V : frontier V = γ.trace
  /-- the winding number vanishes exactly on the unbounded side -/
  wind_zero_iff_U : ∀ x : ℂ, x ∉ γ.trace → (windNumber γ.γ γ.cont x = 0 ↔ x ∈ U)

namespace JSep

variable {γ : Work.Smooth.Jordan.PlaneCurve}

theorem wind_ne_zero_of_mem_V (S : JSep γ) {x : ℂ} (hx : x ∈ S.V) :
    windNumber γ.γ γ.cont x ≠ 0 := by
  intro h0
  have hxt : x ∉ γ.trace := by
    intro hcon
    have hmem : x ∈ S.U ∪ S.V := Or.inr hx
    rw [S.union_eq] at hmem
    exact hmem hcon
  have hxU : x ∈ S.U := (S.wind_zero_iff_U x hxt).mp h0
  exact Set.disjoint_left.mp S.disjoint_UV hxU hx

/-- The datum packaged as a `Work.Smooth.Jordan.PlaneSeparation`. -/
def toPlaneSeparation (S : JSep γ) (h : γ.IsSimple) : Work.Smooth.Jordan.PlaneSeparation γ where
  simple := h
  U := S.U
  V := S.V
  isOpen_U := S.isOpen_U
  isOpen_V := S.isOpen_V
  preconn_U := S.preconn_U
  preconn_V := S.preconn_V
  nonempty_U := S.nonempty_U
  nonempty_V := S.nonempty_V
  disjoint_UV := S.disjoint_UV
  union_eq := S.union_eq
  bounded_V := S.bounded_V

/-- The trace of the curve is contained in the complements of both sides. -/
theorem trace_subset_compl (S : JSep γ) : γ.trace ⊆ S.Uᶜ ∩ S.Vᶜ := by
  intro x hx
  constructor
  · intro hcon
    have : x ∈ S.U ∪ S.V := Or.inl hcon
    rw [S.union_eq] at this
    exact this hx
  · intro hcon
    have : x ∈ S.U ∪ S.V := Or.inr hcon
    rw [S.union_eq] at this
    exact this hx

end JSep

end

end Work.Smooth.SphereJordan
