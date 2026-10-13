import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.FTS.PressureOn.Defs
import Submission.Work.FTS.BSSwirl.CrossAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Connect.BoundaryTime

theorem lamb_derivWithinAt_zero {u ω : Work.FTS.PressureOn.R3 → ℝ → Work.FTS.PressureOn.R3}
    {y : Work.FTS.PressureOn.R3} {u' ω' : Work.FTS.PressureOn.R3}
    (hu : HasDerivWithinAt (fun s => u y s) u' (Set.Ici 0) 0)
    (hω : HasDerivWithinAt (fun s => ω y s) ω' (Set.Ici 0) 0) :
    HasDerivWithinAt (fun s => Work.FTS.PressureOn.lamb u ω y s)
      (Work.FTS.PressureOn.crossVec u' (ω y 0) + Work.FTS.PressureOn.crossVec (u y 0) ω')
      (Set.Ici 0) 0 := by
  -- `lamb u ω y s = u y s × ω y s` is (definitionally) the cross product, realised as the
  -- continuous bilinear map `BSSwirl.crossBilin`; the product rule for a bilinear map
  -- (`HasFDerivWithinAt.clm_apply`) therefore gives the claim, one-sided at `0`.
  have huy : HasFDerivWithinAt (fun s => u y s)
      (ContinuousLinearMap.toSpanSingleton ℝ u') (Set.Ici 0) 0 := hu.hasFDerivWithinAt
  have hωy : HasFDerivWithinAt (fun s => ω y s)
      (ContinuousLinearMap.toSpanSingleton ℝ ω') (Set.Ici 0) 0 := hω.hasFDerivWithinAt
  -- The partial application `fun s => crossBilin (u y s)` (a curve of continuous linear maps),
  -- with derivative `s ↦ crossBilin (s • u')`.
  have hc : HasFDerivWithinAt (fun s : ℝ => Work.FTS.BSSwirl.crossBilin (u y s))
      ((Work.FTS.BSSwirl.crossBilin).comp (ContinuousLinearMap.toSpanSingleton ℝ u'))
      (Set.Ici 0) 0 :=
    (Work.FTS.BSSwirl.crossBilin.hasFDerivWithinAt (s := Set.univ)).comp 0 huy
      (fun x _ => trivial)
  have hmain := hc.clm_apply hωy
  have hfin : HasDerivWithinAt (fun s : ℝ => Work.FTS.BSSwirl.crossBilin (u y s) (ω y s))
      (Work.FTS.PressureOn.crossVec (u y 0) ω' + Work.FTS.PressureOn.crossVec u' (ω y 0))
      (Set.Ici 0) 0 := by
    convert hmain.hasDerivWithinAt using 1
    simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul]
    rfl
  have hfs : (fun s : ℝ => Work.FTS.BSSwirl.crossBilin (u y s) (ω y s))
      = fun s => Work.FTS.PressureOn.lamb u ω y s := by
    funext s
    rfl
  rw [hfs] at hfin
  simpa only [add_comm] using hfin

end Work.FTS.PressureOn.Connect.BoundaryTime
