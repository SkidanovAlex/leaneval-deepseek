/-
# Continuity of the outer cusp chart `ThetaOuter` on the collar wedges

`ThetaOuter v p y` (`Basic.lean`) is the *outer* chart of the filling piece of the `v`-th cusp, in
UHS coordinates

`ThetaOuter v p y = (x, s)`,  `x = cuspX v (u p) y = u p • σ_v + y₂λ₂ + y₃λ₃`,
`s = collarS v p y = collarHeight (‖p‖∞) (β (cuspX v (u p) y))`.

Every ingredient is continuous on the wedges `wedge k` of directions:

* `u p` is continuous on `wedge k` (`u_continuousOn_wedge`): the only jump of the perimeter
  parameter is on the corner ray through `(1,1)` of the square, and a wedge misses it;
* `‖p‖∞` and `cuspY v y = y₂λ₂ + y₃λ₃` are continuous;
* `β` is continuous (`beta_continuous`) and strictly positive (`beta_pos`), so the logarithms in
  `collarHeight` are continuous;
* `exp` is continuous.

As a function of the phase variable `y` the chart is continuous everywhere, so no restriction on
`z.2` is needed.  The stated source is `{z | z.1 ∈ wedge k ∧ 1/2 ≤ nrm z.1}`; we prove the stronger
statement on `{z | z.1 ∈ wedge k}` (the extra hypothesis `1/2 ≤ ‖p‖∞` is not needed for
regularity) and restrict.
-/
import Mathlib
import Submission.Work.Cusp.Basic
import Submission.Work.Cusp.Charts
import Submission.Work.Cusp.u_continuousOn_wedge
import Submission.Work.Cusp.ThetaPolarS_continuousOn
import Submission.Work.Cusp.beta_continuous
import Submission.Work.Cusp.beta_pos
import Submission.Work.Cusp.collarHeight_pos
import Submission.Work.Cusp.nrm_continuous

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Cusp

open scoped Real InnerProductSpace

/-- The `E4`-valued tuple map `w ↦ (w.1 0, w.1 1, w.1 2, w.2)`, i.e. the identification
`E3 × ℝ → E4` of the UHS coordinates `(x, s)`. -/
private lemma continuous_tupleE4 :
    Continuous (fun w : E3 × ℝ => !₂[w.1 0, w.1 1, w.1 2, w.2]) := by
  fun_prop

/-- **The outer chart `ThetaOuter v` is continuous on each wedge of directions.**  This is the
standing regularity fact for the collar chart of the cusp piece: the only discontinuity of
`ThetaOuter v p y` in `p` is the jump of the perimeter parameter `u` on the corner ray, and a wedge
misses that ray.  There is no restriction on the phase variable `y`. -/
theorem ThetaOuter_continuousOn_wedge (v : Fin 5) (k : Fin 4) :
    ContinuousOn (fun z : E2 × E2 => ThetaOuter v z.1 z.2) {z | z.1 ∈ wedge k} := by
  set s : Set (E2 × E2) := {z | z.1 ∈ wedge k} with hs
  have hpr : ContinuousOn (fun z : E2 × E2 => z.1) s :=
    continuous_fst.continuousOn.mono (Set.subset_univ s)
  have hnrm : ContinuousOn (fun z : E2 × E2 => nrm z.1) s :=
    nrm_continuous.comp_continuousOn hpr
  have hU : ContinuousOn (fun z : E2 × E2 => u z.1) s :=
    (u_continuousOn_wedge k).comp hpr (fun z hz => hz)
  have hY : ContinuousOn (fun z : E2 × E2 => cuspY v z.2) s :=
    ((continuous_cuspY v).comp continuous_snd).continuousOn
  have hx_raw : ContinuousOn (fun z : E2 × E2 => u z.1 • slope v + cuspY v z.2) s :=
    (hU.smul continuousOn_const).add hY
  have hx : ContinuousOn (fun z : E2 × E2 => cuspX v (u z.1) z.2) s :=
    hx_raw.congr (fun z _ => by simp only [cuspX])
  have hbeta : ContinuousOn (fun z : E2 × E2 => beta (cuspX v (u z.1) z.2)) s :=
    beta_continuous.comp_continuousOn hx
  have hlog : ContinuousOn (fun z : E2 × E2 => Real.log (beta (cuspX v (u z.1) z.2))) s :=
    hbeta.log (fun _ _ => ne_of_gt (beta_pos _))
  have hcolS : ContinuousOn (fun z : E2 × E2 => collarS v z.1 z.2) s := by
    have h1 : ContinuousOn (fun z : E2 × E2 =>
        (2 * nrm z.1 - 1) * Real.log (beta (cuspX v (u z.1) z.2))) s :=
      ((hnrm.const_mul 2).sub continuousOn_const).mul hlog
    have h2 : ContinuousOn (fun z : E2 × E2 => (2 - 2 * nrm z.1) * Real.log sJ) s :=
      (continuousOn_const.sub (hnrm.const_mul 2)).mul continuousOn_const
    have h3 : ContinuousOn (fun z : E2 × E2 => Real.exp
        ((2 * nrm z.1 - 1) * Real.log (beta (cuspX v (u z.1) z.2))
          + (2 - 2 * nrm z.1) * Real.log sJ)) s :=
      Real.continuous_exp.comp_continuousOn (h1.add h2)
    refine h3.congr ?_
    intro _ _
    simp only [collarS, collarHeight]
  have hpair : ContinuousOn
      (fun z : E2 × E2 => (cuspX v (u z.1) z.2, collarS v z.1 z.2)) s := hx.prodMk hcolS
  have hcomp : ContinuousOn (fun z : E2 × E2 =>
      (fun w : E3 × ℝ => !₂[w.1 0, w.1 1, w.1 2, w.2])
        (cuspX v (u z.1) z.2, collarS v z.1 z.2)) s := continuous_tupleE4.comp_continuousOn hpair
  simpa only [ThetaOuter] using hcomp

/-- **The outer chart `ThetaOuter v` is continuous on the collar wedges of the filling piece.**
This is the regularity statement used to assemble the outer cusp chart of `M̂`. -/
theorem ThetaOuter_continuousOn (v : Fin 5) (k : Fin 4) :
    ContinuousOn (fun z : E2 × E2 => ThetaOuter v z.1 z.2) {z | z.1 ∈ wedge k ∧ 1/2 ≤ nrm z.1} :=
  (ThetaOuter_continuousOn_wedge v k).mono (fun _ hz => hz.1)

end Work.Cusp
