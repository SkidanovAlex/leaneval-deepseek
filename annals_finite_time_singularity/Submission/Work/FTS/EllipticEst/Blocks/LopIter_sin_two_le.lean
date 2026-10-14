import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_f_bound
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.StabilityFar.Profile.exists_Fstar_add_ge

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Blocks

/-- **Divisibility of `D_θ^m (sin 2θ)` by `sin(2θ)`.**
PLACEMENT: file `Submission/Work/FTS/EllipticEst/Blocks/LopIter_sin_two_le.lean`, namespace
`Work.FTS.EllipticEst.Blocks`, so the fully qualified name is
`Work.FTS.EllipticEst.Blocks.LopIter_sin_two_le`.
There is a constant `K ≥ 0` (depending on `k`) such that for every `m ≤ k` and every
`θ ∈ (0,π/2)`,
`(LopIter m (fun θ => sin (2θ)) θ)² ≤ K · sin(2θ)²`,
where `LopIter` is the iterate of `L = sin(2θ)∂_θ` (`Work.FTS.EllipticEst.LopIter`,
`Submission/Work/FTS/EllipticEst/ThetaPoincareDefs.lean`).
RECOMMENDED ROUTE (everything is already in the workspace and sorry-free): use
`Work.FTS.EllipticEst.sd_lop_iter_sin_bound` (`Submission/Work/FTS/EllipticEst/sd_lop_iter_sin_bound.lean`),
which states `∃ C > 0, ∀ i ≤ K, ∀ θ ∈ Work.Spaces.Iθ, |LopIter i (fun θ => sin (2θ)) θ| ≤ C * sin(2θ)`.
Since `0 ≤ sin(2θ)` for `θ ∈ Iθ ⊂ (0,π/2)`, squaring gives
`(LopIter i (fun θ => sin (2θ)) θ)² ≤ C² · sin(2θ)²`, so `K := C²` works. -/
theorem LopIter_sin_two_le (k : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, m ≤ k →
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
    (Work.FTS.EllipticEst.LopIter m (fun θ => Real.sin (2 * θ)) θ) ^ 2
      ≤ K * (Real.sin (2 * θ)) ^ 2 := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.EllipticEst.sd_lop_iter_sin_bound k
  refine ⟨C ^ 2, sq_nonneg C, ?_⟩
  intro m hm θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hb := hC m hm θ hθI
  have hs : 0 ≤ Real.sin (2 * θ) := Work.FTS.EllipticEst.sin_two_nonneg hθI
  have hCs : 0 ≤ C * Real.sin (2 * θ) := mul_nonneg hCpos.le hs
  have h1 : |Work.FTS.EllipticEst.LopIter m (fun θ => Real.sin (2 * θ)) θ| ^ 2
      ≤ (C * Real.sin (2 * θ)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hb 2
  rw [mul_pow] at h1
  rwa [sq_abs] at h1

end Work.FTS.EllipticEst.Blocks
