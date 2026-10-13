import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_RegExport.THL.theta_holder_of_HkMem
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.StrongLWP.Basic
import Submission.Work.FTS.OpenPkg.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH.BoxAux

theorem classCThetaHolder {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
      ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        ∀ θ' ∈ Set.Ioo 0 (Real.pi / 2),
          |g z θ - g z θ'| ≤ C * Work.FTS.StrongGlobal.Xn6 α g * |θ - θ'| ^ (α / 20) := by
  -- `θ`-Hölder continuity of a class-`C` profile, uniformly in `z > 0`.
  --
  -- The trace-free Hölder leaf `THL.theta_holder_of_HkMem` at exponent `β = α` gives, for any
  -- `C^4`-function on the open quadrant which is honestly in `ℋ⁴`,
  --
  --   `|f z θ - f z θ'| ≤ C · min z 1 · |f|_{ℋ⁴} · |θ-θ'|^((γ-1)/2)`,
  --
  -- and `(γ-1)/2 = (α/10)/2 = α/20` is exactly the exponent of the claim.  A class-`C` profile has
  -- the required regularity (`ClassC.reg`) and the required honesty at *every* level up to `10`
  -- (`ClassC.mem10`), so in particular `HkMem α 4 g` and `HkMem α 6 g`.
  --
  -- It remains to remove the two superfluous factors: `min z 1 ≤ 1`, and the order-monotonicity
  -- `HkNorm α 4 g ≤ HkNorm α 6 g = Xn6 α g` of the `ℋ^k`-norm (the integrand is a sum of
  -- nonnegative slots, so increasing the order only adds terms).
  have hα1 : α ≤ 1 := by linarith
  obtain ⟨C, hC0, hmain⟩ :=
    Work.FTS_RegExport.THL.theta_holder_of_HkMem (β := α) hα hα1
  refine ⟨C + 1, by linarith, ?_⟩
  intro g hg z hz θ hθ θ' hθ'
  have hmem4 : Work.Spaces.HkMem α 4 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hg.reg 4 (by norm_num) hg.mem
  have hmem6 : Work.Spaces.HkMem α 6 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hg.reg 6 (by norm_num) hg.mem
  have h4 : ContDiffOn ℝ 4 (Function.uncurry g) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongLWP.SmoothOpen.contDiffOn_four hg.reg
  have hkey := hmain g h4 hmem4 z hz θ hθ θ' hθ'
  have hgam : (Work.Spaces.gam α - 1) / 2 = α / 20 := by
    rw [Work.Spaces.gam_sub_one]; ring
  rw [hgam] at hkey
  have hX : 0 ≤ Work.FTS.StrongGlobal.Xn6 α g := Work.Spaces.HkNorm_nonneg α 6 g
  have hB : 0 ≤ Work.Spaces.HkNorm α 4 g := Work.Spaces.HkNorm_nonneg α 4 g
  have hnorm_mono : Work.Spaces.HkNorm α 4 g ≤ Work.FTS.StrongGlobal.Xn6 α g :=
    Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 6) (k' := 4) (by norm_num) hmem6
  have hmin : min z 1 ≤ 1 := min_le_right z 1
  have hr : 0 ≤ |θ - θ'| ^ (α / 20) := Real.rpow_nonneg (abs_nonneg _) _
  have hAB : C * min z 1 * Work.Spaces.HkNorm α 4 g
      ≤ (C + 1) * Work.FTS.StrongGlobal.Xn6 α g := by
    have h1 : min z 1 * Work.Spaces.HkNorm α 4 g ≤ Work.FTS.StrongGlobal.Xn6 α g :=
      calc min z 1 * Work.Spaces.HkNorm α 4 g
          ≤ 1 * Work.Spaces.HkNorm α 4 g := mul_le_mul_of_nonneg_right hmin hB
        _ = Work.Spaces.HkNorm α 4 g := one_mul _
        _ ≤ Work.FTS.StrongGlobal.Xn6 α g := hnorm_mono
    calc C * min z 1 * Work.Spaces.HkNorm α 4 g
        = C * (min z 1 * Work.Spaces.HkNorm α 4 g) := by ring
      _ ≤ C * Work.FTS.StrongGlobal.Xn6 α g := mul_le_mul_of_nonneg_left h1 hC0
      _ ≤ (C + 1) * Work.FTS.StrongGlobal.Xn6 α g :=
          mul_le_mul_of_nonneg_right (by linarith) hX
  calc |g z θ - g z θ'|
      ≤ C * min z 1 * Work.Spaces.HkNorm α 4 g * |θ - θ'| ^ (α / 20) := hkey
    _ ≤ (C + 1) * Work.FTS.StrongGlobal.Xn6 α g * |θ - θ'| ^ (α / 20) :=
        mul_le_mul_of_nonneg_right hAB hr

end Work.FTS_EllLimOK.ProducerH.BoxAux
