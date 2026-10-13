import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HardyZ
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.interval_sq_le_Itheta
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllSol.VthAux.endpoint.SigmaBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.EllPkgAux.MollDom

theorem abs_interval_integral_le_sqrt_thEta {h : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn h (Set.uIcc a b))
    (hint : MeasureTheory.IntegrableOn (fun θ : ℝ => h θ ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ)
    (ha : 0 < a) (hab : a ≤ b) (hb : b < Real.pi / 2) (hlen : b - a ≤ Real.pi / 4) :
    |∫ t in a..b, h t|
      ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, h θ ^ 2 * Work.FTS.EllipticEst.thEta θ)
        * Real.sqrt (Real.pi / 4) := by
  -- On `[a,b] ⊆ (0, π/2)` the weight satisfies `thEta ≥ 1`, so `∫_a^b h² ≤ ∫_Iθ h²·thEta`
  -- (`interval_sq_le_Itheta`), and the interval length is at most `π/4`.
  have hcontIcc : ContinuousOn h (Set.Icc a b) := by rwa [Set.uIcc_of_le hab] at hcont
  have hint2 : MeasureTheory.IntegrableOn (fun x : ℝ => h x ^ 2) (Set.Icc a b) :=
    (hcontIcc.pow 2).integrableOn_compact isCompact_Icc
  -- Cauchy–Schwarz for the interval integral of `h` against the constant `1`.
  have hcs :=
    Work.FTS.EllSol.VthAux.endpoint.abs_integral_le_sqrt_mul_sqrt hab hcontIcc hint2
  have hmono : ∫ x in a..b, h x ^ 2
      ≤ ∫ θ in Work.Spaces.Iθ, h θ ^ 2 * Work.FTS.EllipticEst.thEta θ :=
    Work.FTS.EllSol.EllPkgAux.MollDom.interval_sq_le_Itheta hint ha hab hb
  have hsqrt1 : Real.sqrt (∫ x in a..b, h x ^ 2)
      ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, h θ ^ 2 * Work.FTS.EllipticEst.thEta θ) :=
    Real.sqrt_le_sqrt hmono
  have hsqrt2 : Real.sqrt (b - a) ≤ Real.sqrt (Real.pi / 4) := Real.sqrt_le_sqrt hlen
  have hstep : Real.sqrt (b - a) * Real.sqrt (∫ x in a..b, h x ^ 2)
      ≤ Real.sqrt (Real.pi / 4)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, h θ ^ 2 * Work.FTS.EllipticEst.thEta θ) :=
    mul_le_mul hsqrt2 hsqrt1 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc |∫ t in a..b, h t|
      ≤ Real.sqrt (b - a) * Real.sqrt (∫ x in a..b, h x ^ 2) := hcs
    _ ≤ Real.sqrt (Real.pi / 4)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, h θ ^ 2 * Work.FTS.EllipticEst.thEta θ) := hstep
    _ = Real.sqrt (∫ θ in Work.Spaces.Iθ, h θ ^ 2 * Work.FTS.EllipticEst.thEta θ)
          * Real.sqrt (Real.pi / 4) := by rw [mul_comm]

end Work.FTS.EllSol.EllPkgAux.MollDom
