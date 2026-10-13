import Mathlib.Analysis.Real.Sqrt
import Submission.Work.FTS.StrongEps.HkSq_four_le_of_conv
import Submission.Work.FTS.StrongEps.ConvLev0Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

theorem Xn_le_of_convLocUnif {α B C₀ : ℝ} {G : ℕ → Work.FTS.Galerkin.Fn} {f : Work.FTS.Galerkin.Fn}
    (hconv : Work.FTS.StrongEps.ConvLocUnifH6 α B G f)
    (hmem : ∀ n : ℕ, Work.Spaces.HkMem α 4 (G n))
    (hbsq : ∀ n : ℕ, Work.FTS.Nonlin.Xn α (G n) ≤ C₀ * α ^ 2) :
    Work.FTS.Nonlin.Xn α f ≤ C₀ * α ^ 2 := by
  -- `Xn` is `HkNorm α 4`, so the hypothesis is a uniform bound on the `ℋ⁴`-norms of the
  -- approximants, hence (by squaring) a uniform bound on their `ℋ⁴`-energies.
  have hC₀ : 0 ≤ C₀ * α ^ 2 :=
    le_trans (Work.Spaces.HkNorm_nonneg α 4 (G 0)) (hbsq 0)
  have hsq : ∀ n : ℕ, Work.Spaces.HkSq α 4 (G n) ≤ (C₀ * α ^ 2) ^ 2 := by
    intro n
    have hsqn : Work.Spaces.HkSq α 4 (G n) = (Work.Spaces.HkNorm α 4 (G n)) ^ 2 :=
      (Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 (G n))).symm
    rw [hsqn]
    exact pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 (G n)) (hbsq n) 2
  -- lower semicontinuity of the `ℋ⁴`-energy along the locally uniform slot convergence
  have hlim : Work.Spaces.HkSq α 4 f ≤ (C₀ * α ^ 2) ^ 2 :=
    HkSq_four_le_of_conv (B4 := (C₀ * α ^ 2) ^ 2) hconv hmem hsq
  calc Work.FTS.Nonlin.Xn α f = Real.sqrt (Work.Spaces.HkSq α 4 f) := rfl
    _ ≤ Real.sqrt ((C₀ * α ^ 2) ^ 2) := Real.sqrt_le_sqrt hlim
    _ = C₀ * α ^ 2 := Real.sqrt_sq hC₀

end Work.FTS.StrongEps
