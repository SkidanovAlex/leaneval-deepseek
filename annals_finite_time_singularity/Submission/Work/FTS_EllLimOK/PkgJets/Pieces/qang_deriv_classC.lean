import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.StrongEps.classC_mixed_sup_le_four
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.hasDerivAt_integral_Itheta_K
import Submission.Work.Elliptic.L12Aux
import Submission.Work.FTS.StrongPersist.QangDiff6
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets.Pieces

/-- **The `z`-derivative of the angular moment of a class-`C` datum.**

`Qang g m z = ∫_θ K(θ)·D_z^m g(z,θ) dθ` is differentiable at every `z > 0`, with

  `∂_z (Qang g m) z = Qang g (m+1) z / z`,

as soon as `g` is `C^∞` on the open quadrant and honestly weighted-`ℋ^{m+1}`.
The identity is the `z = z` case of the primitive identity
`Qang g j z - Qang g j z₀ = ∫_{z₀}^{z} Qang g (j+1) x / x dx`
of `Work.FTS.OpenPkg.QangOpen.Qang_primitive_open`; the derivative then follows from the
continuity of the integrand `x ↦ Qang g (j+1) x / x` at `z > 0`.

Here we read it off the assembled module `Work.FTS.StrongPersist.QangDiff6`, which supplies the
identity in the exact open-quadrant class at the level `ℋ⁶` (it runs the level-`ℋ⁴` chain twice,
once for `g` and once for the `D_z²`-shift of `g`, by `Qang g (k+2) = Qang (D_z²g) k`).
The class `ClassC` carries `SmoothOpen g` and `HkMem α 7 g`, so `HkMem α 6 g` (and a fortiori
the level `ℋ^{m+1}` needed for `m ≤ 3`) is the monotonicity step
`Work.FTS.OpenPkg.HkMem_mono_open`. -/
theorem qang_deriv_classC {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.ClassC.ClassC α g) {m : ℕ} (hm : m ≤ 3) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun x => Work.Elliptic.Qang g m x) (Work.Elliptic.Qang g (m + 1) z / z) z := by
  -- the class supplies open-quadrant smoothness and `ℋ⁷`-honesty; descend to the level `ℋ⁶`
  -- at which the assembled moment calculus `QangDiff6` is stated
  have hmem6 : Work.Spaces.HkMem α 6 g :=
    Work.FTS.OpenPkg.HkMem_mono_open (k := 7) hg.reg 6 (by norm_num) hg.mem
  exact (Work.FTS.StrongPersist.QangDiff6 hg.reg hmem6).1 m (by omega) z hz

end Work.FTS_EllLimOK.PkgJets.Pieces
