/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cocompactness transfers to the lifted graph

The lifting construction of `Submission.Work.ORBassSerre.Action.Lift.Basic` trades a `G`-graph
`V` for the `LGroup G V`-graph `VLx G V`, both living in the common universe `max u v w`.  Here
we show that this trade preserves *cocompactness*: finitely many orbits of vertices and of edges
on `V` give finitely many orbits of vertices and of edges on `VLx G V`.

The mechanism is the pair of equivariant bijections `VLx.equiv : VLx G V ≃ V` and
`totalEquiv : Quiver.Total (VLx G V) ≃ Quiver.Total V` supplied by `Basic`.  For every
`g : LGroup G V` and `a : VLx G V` one has `(g • a).down = g.down • a.down` (definitionally,
cf. `smul_VLx`), and likewise on arrows (`totalEquiv_smul_VLx` below).  Hence the orbit relations
correspond exactly, so `Quotient.congr` transports the orbit sets, and `Equiv.finite_iff`
transports finiteness.
-/
import Mathlib
import Submission.Work.ORBassSerre.Action.Lift.Basic

namespace Work.ORBassSerre.Action.Lift

/-- The bijection `totalEquiv` between the arrows of the lifted graph and the arrows of `V` is
equivariant: the lifted action of `LGroup G V` corresponds to the action of `G` along it. -/
theorem totalEquiv_smul_VLx {G : Type*} {V : Type*} [Quiver V] [Group G]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V]
    (g : LGroup G V) (e : Quiver.Total (VLx G V)) :
    totalEquiv G V (g • e) = g.down • totalEquiv G V e := by
  rw [smulTotal_VLx_apply]
  exact (totalEquiv G V).apply_symm_apply _

theorem isCocompact_VLx {G : Type*} {V : Type*} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
    [MulAction G V] [Work.ORBassSerre.GraphAction G V]
    (hcc : Work.ORBassSerre.IsCocompact G V) :
    Work.ORBassSerre.IsCocompact (Work.ORBassSerre.Action.Lift.LGroup G V)
      (Work.ORBassSerre.Action.Lift.VLx G V) := by
  -- The lifted `LGroup G V`-orbit relation on vertices is the orbit relation of `G` on `V`,
  -- read along `VLx.equiv`.
  have hV : ∀ a b : VLx G V,
      MulAction.orbitRel (LGroup G V) (VLx G V) a b ↔
        MulAction.orbitRel G V a.down b.down := by
    intro a b
    constructor
    · intro h
      obtain ⟨g, hg⟩ := h
      exact ⟨g.down, by simpa using congrArg (fun x : VLx G V => x.down) hg⟩
    · intro h
      obtain ⟨g, hg⟩ := h
      refine ⟨(ULift.up g : LGroup G V), ?_⟩
      apply VLx.ext
      simp only [smul_VLx, VLx.down_up, hg]
  -- The same, for arrows, read along `totalEquiv`.
  have hE : ∀ e f : Quiver.Total (VLx G V),
      MulAction.orbitRel (LGroup G V) (Quiver.Total (VLx G V)) e f ↔
        MulAction.orbitRel G (Quiver.Total V) (totalEquiv G V e) (totalEquiv G V f) := by
    intro e f
    constructor
    · intro h
      obtain ⟨g, hg⟩ := h
      refine ⟨g.down, ?_⟩
      have h1 := congrArg (totalEquiv G V) hg
      rwa [totalEquiv_smul_VLx] at h1
    · intro h
      obtain ⟨g, hg⟩ := h
      refine ⟨(ULift.up g : LGroup G V), ?_⟩
      apply (totalEquiv G V).injective
      rw [totalEquiv_smul_VLx]
      simp only [hg]
  constructor
  · exact (Quotient.congr (VLx.equiv G V) hV).finite_iff.mpr hcc.1
  · exact (Quotient.congr (totalEquiv G V) hE).finite_iff.mpr hcc.2

end Work.ORBassSerre.Action.Lift
