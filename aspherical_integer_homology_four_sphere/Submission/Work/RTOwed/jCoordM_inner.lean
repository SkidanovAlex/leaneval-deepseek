/-
# The polar (inner) branch of the junction coordinate inclusion

The junction chart `Work.RTOwed.jCoordM a v D cU k W kx δ` of the `v`-th filling piece
(`Submission/Work/RTOwed/FillBigDefs.lean`) is defined by a two-branch case split on the radial
coordinate `q 0 ≤ rJ`: below the junction it is the inverse of the *polar* chart,

  `q ↦ a.incW v (cuspInvInner v q)`

(the point of `M̂` whose filling coordinates are the pair `(p, y) = cuspInvInner v q`), and above
the junction it is the collar coordinate inclusion `cuspCoordMTop` composed with `polarToUHS`.

This file proves the statement needed to identify the *value map* of the junction chart with the
polar coordinate `Θ_v` on the inner side of the junction: if the polar coordinate `q` of a point is
the polar chart image `ThetaPolar v p w` of a filling pair `(p, y)` — where `w` are the
`w`-coordinates of `y`, i.e. `w = D.tor y` in the two torus coordinates modulo `ℤ²` — and `q` lies
in the inner region `q 0 ≤ rJ`, then `jCoordM` returns exactly that filling point:

  `jCoordM a v D cU k W kx δ q = a.incW v (p, y)`.

The content is `Cusp.cuspInvInner_ThetaPolar` (the polar chart inverse is a *left* inverse of the
chart, so it recovers `(p, y)` from `q`) together with the fact that the torus coordinates of
`a.incW v` are the `ℤ²`-class of `w` and `D.tor` identifies them with `y`.
-/
import Mathlib
import Submission.Work.RTOwed.FillBigDefs
import Submission.Work.Cusp.cuspInvInner_ThetaPolar

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

theorem jCoordM_inner (a : Work.Space.Assembly) (v : Work.Space.Cusp)
    (D : Work.Cusp.CuspGlueData a v) (p : Work.Space.SquarePt) (y : a.Torus v) (w : Work.Cusp.E2)
    (hw : ∀ i, ((w i : ℝ) : AddCircle (1 : ℝ)) = D.tor y i)
    (cU : ℝ) (k : Fin 4) (W : Set Work.Cusp.E2) (kx : Work.Cusp.E3) (δ : ℝ)
    (z : {q : Work.Cusp.E4 // q ∈ Work.RTOwed.jBox v cU k W kx δ})
    (hz : z.1 = Work.Cusp.ThetaPolar v (p : Work.Cusp.E2) w)
    (hle : z.1 0 ≤ Work.Cusp.rJ) :
    Work.RTOwed.jCoordM a v D cU k W kx δ z = a.incW v (p, y) := by
  -- The polar chart inverse recovers the filling coordinates of `q = ThetaPolar v p w`.
  have hz' : Work.Cusp.cuspInvInner v z.1 = ((p : Work.Cusp.E2), w) := by
    rw [hz, Work.Cusp.cuspInvInner_ThetaPolar]
  have h1 : (Work.Cusp.cuspInvInner v z.1).1 = (p : Work.Cusp.E2) := by rw [hz']
  have h2 : (Work.Cusp.cuspInvInner v z.1).2 = w := by rw [hz']
  -- On the inner side `q 0 ≤ rJ` the junction coordinate inclusion is the polar branch.
  unfold Work.RTOwed.jCoordM
  rw [dite_eq_left hle]
  -- The two filling points differ only in the `w`-coordinates versus their `ℤ²`-class.
  refine congrArg (a.incW v) (Prod.ext ?_ ?_)
  · exact Subtype.ext h1
  · have hfun : (fun i => (((Work.Cusp.cuspInvInner v z.1).2 i : ℝ) : AddCircle (1 : ℝ)))
        = D.tor y := by
      funext i
      rw [h2]
      exact hw i
    rw [hfun]
    exact D.tor.symm_apply_apply y

end Work.RTOwed
