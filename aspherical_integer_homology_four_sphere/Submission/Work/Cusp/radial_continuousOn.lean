/-
# Continuity of the metric radial coordinate `r` of the filling piece

`radial v p y` (`Work.Cusp.Basic`) is the metric radial coordinate of the filling piece
`W_v = Sq × (ℝ/ℤ)²` in the polar coordinates `(r,θ,w₁,w₂)` of the inner charts: it is
`2 r_J ‖p‖∞` on the core `{‖p‖∞ ≤ 1/2}` and `R₀ − log s` with the UHS height `s = collarS v p y`
of the collar `{‖p‖∞ ≥ 1/2}`.

Here we prove that `radial v` is continuous on the whole `(p,y)`-cover `E2 × E2`, with **no**
restriction on the direction `p`.  This is the standing regularity fact for the radial coordinate
of every polar chart: the *angle* coordinate `θ = 2π u(p) + …` is only continuous on one wedge at a
time (the perimeter parameter `u` jumps by `1` on the ray through the corner `(1,1)` of the square),
whereas the radial coordinate is continuous even there, because the jump is an integer multiple of
the lattice vector `σ_v ∈ ℤ³`, a period of the ceiling `β`.

The proof is local, pointwise, and rests on the chart layer already established:

* the boundary between the strata is the unit sphere in the direction variable, so when
  `‖p‖∞ ≠ 1/2` the value of `radial` is *locally* one of the two branches, which is continuous;
* on the collar `{1/2 < ‖p‖∞}` the point `p` is nonzero, so by the two-shift cover
  `wedge_cover` it lies in one of the open wedges `wedgeS c k` with `c ∈ {0, 1/8}`; there the
  first coordinate of the shifted polar chart `ThetaPolarS v c` is *by definition* `radial`, and
  `ThetaPolarS_continuousOn` (the regularity theorem for the shifted polar chart, which uses the
  lift `uS c` of `u` and the periodicity `β(x − u σ_v) = β x`) gives continuity on the whole
  wedge.  Continuity of `radial` on the wedge therefore needs no work at all beyond invoking it.

Note that no statement about `radial` at the origin `p = 0` is needed: there `‖p‖∞ = 0 < 1/2`, so
`radial` agrees with the continuous core branch `2 r_J ‖p‖∞` on the open set `{‖p‖∞ < 1/2}`.
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.ThetaPolarS_continuousOn
import Submission.Work.Cusp.wedge_cover
import Submission.Work.Cusp.isOpen_wedgeS
import Submission.Work.Cusp.nrm_continuous

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Cusp

open scoped Real InnerProductSpace Topology
open Filter

/-! ### The two local forms of `radial` -/

/-- **`radial` is continuous at every point of the core stratum.**  On the open set
`{‖p‖∞ < 1/2}` the defining case split of `radial` takes its first branch `2 r_J ‖p‖∞`, which is
continuous. -/
private lemma radial_continuousAt_of_lt_half (v : Fin 5) {z : E2 × E2} (h : nrm z.1 < 1/2) :
    ContinuousAt (fun w : E2 × E2 => radial v w.1 w.2) z := by
  have hcont : ContinuousAt (fun w : E2 × E2 => 2 * rJ * nrm w.1) z :=
    (continuous_const.mul (nrm_continuous.comp continuous_fst)).continuousAt
  refine hcont.congr ?_
  have hev : ∀ᶠ w : E2 × E2 in 𝓝 z, nrm w.1 < 1/2 :=
    (nrm_continuous.comp continuous_fst).continuousAt.eventually (isOpen_Iio.mem_nhds h)
  filter_upwards [hev] with w hw
  show 2 * rJ * nrm w.1 = radial v w.1 w.2
  rw [radial]
  exact (ite_eq_left (le_of_lt hw)).symm

/-- **`radial` is continuous at every point of a shifted wedge.**  On the open set
`{w | w.1 ∈ wedgeS c k}` the function `radial` *is* the first coordinate of the shifted polar
chart `ThetaPolarS v c`, which is continuous there (`ThetaPolarS_continuousOn`).  This is the case
that covers the collar stratum, including the rays on which the perimeter parameter `u` jumps. -/
private lemma radial_continuousAt_of_mem_wedgeS (v : Fin 5) (c : ℝ) (k : Fin 4) {z : E2 × E2}
    (hz : z.1 ∈ wedgeS c k) : ContinuousAt (fun w : E2 × E2 => radial v w.1 w.2) z := by
  have hcoord : Continuous (fun q : E4 => q 0) :=
    (continuous_apply 0).comp (PiLp.continuous_ofLp 2 (fun _ : Fin 4 => ℝ))
  have hg : ContinuousOn (fun w : E2 × E2 => (ThetaPolarS v c w.1 w.2) 0)
      {w | w.1 ∈ wedgeS c k} :=
    hcoord.continuousOn.comp (ThetaPolarS_continuousOn v c k) (fun _ _ => Set.mem_univ _)
  have hnhds : {w : E2 × E2 | w.1 ∈ wedgeS c k} ∈ 𝓝 z :=
    ((isOpen_wedgeS c k).preimage continuous_fst).mem_nhds hz
  refine (hg.continuousAt hnhds).congr ?_
  filter_upwards with w
  rfl

/-! ### The theorem -/

/-- **The metric radial coordinate `radial v p y` is continuous on the whole `(p,y)`-cover.**  If
`‖p‖∞ ≠ 1/2` the value of `radial` is locally one of its two branches; the remaining case is the
collar `{1/2 < ‖p‖∞}` with `‖p‖∞ = 1/2` excluded, i.e. `p ≠ 0`, where the two-shift cover
`wedge_cover` produces a shift `c ∈ {0, 1/8}` and a wedge `wedgeS c k` containing `p`, on which
`radial` is the first coordinate of the continuous chart `ThetaPolarS v c`
(`radial_continuousAt_of_mem_wedgeS`). -/
theorem radial_continuousOn (v : Fin 5) :
    ContinuousOn (fun z : E2 × E2 => radial v z.1 z.2) Set.univ := by
  rw [continuousOn_univ, continuous_iff_continuousAt]
  intro z
  by_cases h : nrm z.1 < 1/2
  · exact radial_continuousAt_of_lt_half v h
  · -- the collar stratum, away from the junction `‖p‖∞ = 1/2`
    have hpos : 0 < nrm z.1 := by linarith [not_lt.mp h]
    have hc := wedge_cover z.1 hpos
    rw [Set.mem_union] at hc
    rcases hc with hz | hz
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz
      exact radial_continuousAt_of_mem_wedgeS v 0 k hk
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz
      exact radial_continuousAt_of_mem_wedgeS v (1 / 8) k hk

end Work.Cusp
