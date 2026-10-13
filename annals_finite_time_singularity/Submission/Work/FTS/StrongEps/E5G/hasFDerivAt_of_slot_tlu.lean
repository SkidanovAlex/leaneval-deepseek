import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E5G

theorem hasFDerivAt_of_slot_tlu {W : ℕ → ℝ → ℝ → ℝ} {F R : ℝ → ℝ → ℝ}
    {L : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] ℝ)} {q : ℝ × ℝ} (hq : q ∈ Work.FTS.EllipticEst.Q0)
    (hd : ∀ n : ℕ, ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 →
      DifferentiableAt ℝ (Function.uncurry (W n)) p)
    (hW : TendstoLocallyUniformlyOn (fun n : ℕ => Function.uncurry (W n))
      (fun p : ℝ × ℝ => F p.1 p.2) Filter.atTop Work.FTS.EllipticEst.Q0)
    (hL : TendstoLocallyUniformlyOn (fun n : ℕ => fderiv ℝ (Function.uncurry (W n))) L
      Filter.atTop Work.FTS.EllipticEst.Q0)
    (heq : ∀ p ∈ Work.FTS.EllipticEst.Q0, R p.1 p.2 = F p.1 p.2) :
    HasFDerivAt (Function.uncurry R) (L q) q := by
  -- The locally uniform limit `F` of the `W n` has Fréchet derivative `L` on the quadrant.
  have hF : HasFDerivAt (fun p : ℝ × ℝ => F p.1 p.2) (L q) q :=
    hasFDerivAt_of_tendstoLocallyUniformlyOn Work.FTS.EllipticEst.isOpen_Q0 hL
      (fun n p hp => (hd n p hp).hasFDerivAt)
      (fun p hp => hW.tendsto_at hp) hq
  -- `R` agrees with `F` on a neighbourhood of `q` (the quadrant is open), so the derivative
  -- is the same.
  refine hF.congr_of_eventuallyEq ?_
  filter_upwards [Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hq] with p hp
  exact heq p hp

end Work.FTS.StrongEps.E5G
