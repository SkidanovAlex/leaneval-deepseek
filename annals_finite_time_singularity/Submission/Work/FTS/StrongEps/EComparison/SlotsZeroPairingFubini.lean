import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeKey

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set

namespace Work.FTS.StrongEps.EComparison

theorem SlotsZeroPairingFubini {α : ℝ} {Φ : ℝ → ℝ → ℝ} {ρ : ℝ → ℝ} {m : ℕ} {a b : ℝ}
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry Φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hρ : ∀ k : ℕ, ContDiff ℝ k ρ) (ha : 0 < a)
    (hsub : tsupport ρ ⊆ Set.Icc a b)
    (hΦint : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => |Φ z θ|) Work.Spaces.Iθ)
    (hEint : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, |Φ z θ|)
      (Set.Icc a b)) :
    (∫ p in Work.FTS.EllipticEst.Q0, Φ p.1 p.2
        * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
            p.1 p.2
        * Work.FTS.StrongEps.EComparison.bslWeight α p)
      = ∫ z in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ, Φ z θ
          * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
              z θ
          * (z ^ ((5 - α) / α) * Real.cos θ) := by
  -- The integrand of the left-hand side is product-measure integrable on the quadrant
  -- (`integrableOn_modeIntegrand`, fed by the box integrability of `|Φ|`).
  have hFint : MeasureTheory.Integrable (fun p : ℝ × ℝ => Φ p.1 p.2
      * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2
      * Work.FTS.StrongEps.EComparison.bslWeight α p)
      (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
        ((volume : Measure ℝ).restrict (Set.Ioo 0 (Real.pi / 2)))) := by
    rw [← Work.FTS.StrongEps.EComparison.restrict_Q0_eq_prod]
    exact Work.FTS.StrongEps.EComparison.integrableOn_modeIntegrand (α := α) (m := m)
      hsm hρ ha hsub (Work.FTS.StrongEps.EComparison.integrableOn_absPhi_box hsm hΦint hEint)
  -- Rewrite the set integral over `Q0 = (0,∞) × (0,π/2)` as an integral against the
  -- product of the two restricted measures.
  rw [show (∫ p in Work.FTS.EllipticEst.Q0, Φ p.1 p.2
        * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2
        * Work.FTS.StrongEps.EComparison.bslWeight α p)
      = ∫ p, (Φ p.1 p.2
        * Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) p.1 p.2
        * Work.FTS.StrongEps.EComparison.bslWeight α p)
        ∂(((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
          ((volume : Measure ℝ).restrict (Set.Ioo 0 (Real.pi / 2)))) from by
    rw [Work.FTS.StrongEps.EComparison.restrict_Q0_eq_prod]]
  -- Fubini.
  rw [MeasureTheory.integral_prod _ hFint]
  -- Replace the angular interval `(0,π/2)` by `Iθ = [0,π/2]` (same restricted measure),
  -- and unfold the pairing weight `bslWeight α (z,θ) = z^((5-α)/α)·cos θ`.
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  rw [Work.FTS.StrongEps.EComparison.restrict_Ioo_eq_Iθ]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
  simp [Work.FTS.StrongEps.EComparison.bslWeight]

end Work.FTS.StrongEps.EComparison
