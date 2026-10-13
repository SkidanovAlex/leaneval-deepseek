import Mathlib.Basic.Real.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm
import Submission.Work.FTS.StrongPersist.IP6_lo_coeffs
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_Dth_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr

/-- The three `H^n → H^{n+1}` domination facts for a function which is `C^∞` on the open
quadrant and honestly in `ℋ^{n+1}`.

* the first conjunct is the plain monotonicity of `HkSq` in the regularity index
  (`HkIntegrand` is a sum of squares over a range that grows with `k`);
* the second is the `D_θ`-shift `HkSq α n (D_θ f) ≤ HkSq α (n+1) f`: the `(n)`-summands of
  `D_θ f` become mixed summands of `f` at level `n+1` with the heavier weight `W`;
* the third is the `D_z`-shift `HkSq α n (D_z f) ≤ HkSq α (n+1) f`, which is only needed on
  the open quadrant and hence only requires `SmoothOpen f` (via `Q0Sm (n+1) f`). -/
theorem normSub_SO {α : ℝ} {n : ℕ} {f : Work.FTS.Galerkin.Fn} (hα : 0 < α)
    (hs : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α (n + 1) f) :
    Work.Spaces.HkSq α n f ≤ Work.Spaces.HkSq α (n + 1) f ∧
      Work.Spaces.HkSq α n (Work.Spaces.Dth f) ≤ Work.Spaces.HkSq α (n + 1) f ∧
      Work.Spaces.HkSq α n (Work.Spaces.Dz f) ≤ Work.Spaces.HkSq α (n + 1) f :=
  ⟨Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (Nat.le_succ n) hm,
    Work.FTS.CoercivityStep.Norm.HkSq_Dth_le α hα n hm,
    Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm α n
      (Work.FTS.StrongPersist.q0Sm_of_smoothOpen hs (n + 1)) hm⟩

end Work.FTS.StrongEps.EpsE4Thr
