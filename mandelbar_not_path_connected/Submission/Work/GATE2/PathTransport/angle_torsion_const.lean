import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2.PathTransport

/-- **Torsion continuity.**  A continuous map of the unit interval into the `N`-torsion of the
angle group `Real.Angle` is constant at the endpoints: `f 0 = f 1`.

This is item (A0) / item "(d)" of the design `NOTES_LEAD_mandelbar_gate2transport.md` §3: the
phase integer of the gate transport is *discrete*, and discreteness together with the
connectedness of the unit interval forces the transport to be constant along a path. -/
theorem angle_torsion_const {N : ℕ} (hN : 0 < N) {f : C(unitInterval, Real.Angle)}
    (h : ∀ t, N • f t = 0) : f 0 = f 1 := by
  -- The `N`-torsion of the angle group is a finite set, hence carries the discrete topology.
  have hdisc : IsDiscrete {x : Real.Angle | N • x = 0} :=
    (AddCircle.finite_torsion (p := 2 * Real.pi) hN).isDiscrete
  -- `f` maps the (preconnected) unit interval into this discrete set, so it is constant there.
  exact IsPreconnected.constant_of_mapsTo (isPreconnected_univ) hdisc
    f.continuous.continuousOn (fun t _ => h t) trivial trivial

end Work.GATE2.PathTransport
