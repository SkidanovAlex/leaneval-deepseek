import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Submission.Work.FTS.StrongEps.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongEps.KernAux

/-- **The shifted profile is smooth.**  If `g` is `C^n` on the open quadrant `Quad` (for every
`n`, as a function of `(z, θ)`), then for fixed `(z, θ) ∈ Quad` the two-variable function

`p ↦ g (z e^{-p₁}) (arctan (tan θ · e^{-p₂}))`

is `C^n` on all of `ℝ²`.  The reason is that the shift map
`p ↦ (zShift z p₁, thShift θ p₂)` is smooth as a map `ℝ² → ℝ²` and takes *all* of `ℝ²` into the
open quadrant `Quad` (`zShift_pos`, `thShift_mem`), which is where the hypothesis on `g` lives. -/
theorem contDiff_shift (g : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Work.FTS.StrongEps.Quad) :
    ∀ n : ℕ, ContDiff ℝ n
      (fun p : ℝ × ℝ => g (Work.FTS.StrongEps.zShift z p.1) (Work.FTS.StrongEps.thShift θ p.2)) := by
  intro n
  -- the shift map `p ↦ (zShift z p₁, thShift θ p₂)` is `C^n` on `ℝ²`:
  -- `p ↦ z e^{-p₁}` is a constant times `exp` of a linear function, and
  -- `p ↦ arctan (tan θ · e^{-p₂})` is `arctan` of a constant times `exp` of a linear function.
  have hφ : ContDiff ℝ n (fun p : ℝ × ℝ =>
      (Work.FTS.StrongEps.zShift z p.1, Work.FTS.StrongEps.thShift θ p.2)) := by
    refine ContDiff.prodMk ?_ ?_
    · have hp1 : ContDiff ℝ n (fun p : ℝ × ℝ => -p.1) := contDiff_fst.neg
      exact contDiff_const.mul (Real.contDiff_exp.comp hp1)
    · have hp2 : ContDiff ℝ n (fun p : ℝ × ℝ => -p.2) := contDiff_snd.neg
      exact Real.contDiff_arctan.comp (contDiff_const.mul (Real.contDiff_exp.comp hp2))
  -- the shift map lands in the open quadrant, where `g` is `C^n`:
  have hmem : ∀ p : ℝ × ℝ,
      (Work.FTS.StrongEps.zShift z p.1, Work.FTS.StrongEps.thShift θ p.2)
        ∈ Work.FTS.StrongEps.Quad :=
    fun p => ⟨Work.FTS.StrongEps.zShift_pos hz, Work.FTS.StrongEps.thShift_mem hθ⟩
  exact (hg n).comp_contDiff hφ hmem

end Work.FTS.StrongEps.KernAux
