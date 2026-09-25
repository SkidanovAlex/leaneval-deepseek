import Mathlib
import Submission.Work.BourgainPlan.Thm52.CircleLiftDefs
import Submission.Work.BourgainPlan.Maximal.iw_superset

namespace Work.BourgainPlan.Maximal

/-- **The `L^∞`-membership of `g ∘ iwRep`** — the measurability-free route to the `MemLp` hypotheses of the MST §3–§5 symbols (`mstWeyl`, `mstProf`, `mstEta`): since `iwRep = AddCircle.liftIoc 1 (-(1/2)) id`, the function `ξ ↦ g (iwRep ξ)` is literally the fundamental-domain lift `AddCircle.liftIoc 1 (-(1/2)) g`, so Mathlib's `MeasureTheory.MemLp.memLp_liftIoc` applies.  In particular a *continuous* `g` (e.g. `polyProfile P N` or `polyWeylKernel P N`) gives `MemLp ⊤` on the circle, with no measurability statement about `iwRep` needed. -/
theorem memLp_comp_iwRep {g : ℝ → ℂ}
    (hg : MeasureTheory.MemLp g ⊤
      (MeasureTheory.volume.restrict (Set.Ioc (-(1 / 2) : ℝ) (1 / 2)))) :
    MeasureTheory.MemLp (fun ξ : Work.BourgainPlan.IonescuWainger.Circle =>
      g (Work.BourgainPlan.Maximal.iwRep ξ)) ⊤ (AddCircle.haarAddCircle (T := 1)) := by
  -- Restate the hypothesis on the fundamental domain `Ioc (-1/2) (-1/2 + 1)` of `AddCircle.liftIoc`.
  have hg' : MeasureTheory.MemLp g ⊤
      (MeasureTheory.volume.restrict (Set.Ioc (-(1 / 2) : ℝ) (-(1 / 2) + 1))) := by
    convert hg using 2
    norm_num
  -- `ξ ↦ g (iwRep ξ)` is *definitionally* the lift `AddCircle.liftIoc 1 (-1/2) g` of `g`.
  have hlift := MeasureTheory.MemLp.memLp_liftIoc (T := (1 : ℝ)) (t := -(1 / 2)) hg'
  -- Transport the `volume`-membership to the Haar measure of the circle.
  exact hlift.haarAddCircle

end Work.BourgainPlan.Maximal
