import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open scoped Real Topology
open MeasureTheory Set Filter

/-- **Fubini for the `∂_z`-slice integrals of the angular moment, plus vanishing of the angular
integral when both `Fstar`-moments vanish.**

Since `Work.Elliptic.Fstar Ψ z = ∫_{Iθ} Ψ z θ sin θ cos²θ dθ`, the fundamental theorem of
calculus in `z` gives, for every angle `θ`,

`∫_{r}^{z₁} ∂_z Ψ z θ * sin θ cos²θ dz = (Ψ z₁ θ - Ψ r θ) * sin θ cos²θ`,

and upon integrating in `θ` the two `Fstar`-terms cancel because `Fstar Ψ r = Fstar Ψ z₁ = 0`.
The first conjunct is Tonelli/Fubini for the product measure on `Ioc r z₁ × Iθ`. -/
theorem pzSliceFubiniZero {Ψ : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {r z₁ : ℝ} (hr : 0 < r) (hrz : r < z₁)
    (hΨr : MeasureTheory.Integrable (fun θ : ℝ => Ψ r θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hΨz : MeasureTheory.Integrable (fun θ : ℝ => Ψ z₁ θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hFr : Work.Elliptic.Fstar Ψ r = 0) (hFz : Work.Elliptic.Fstar Ψ z₁ = 0)
    (hrect : MeasureTheory.Integrable
      (Function.uncurry (fun z θ : ℝ => Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.Ioc r z₁)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ))) :
    (∫ z in r..z₁, (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ))
      = (∫ θ in Work.Spaces.Iθ, ∫ z in r..z₁,
          Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) ∧
    (∫ θ in Work.Spaces.Iθ, ∫ z in r..z₁,
      Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) = 0
  := by
  have hmeasIθ : MeasurableSet Work.Spaces.Iθ := by
    rw [Work.Spaces.Iθ]; exact measurableSet_Icc
  -- Tonelli/Fubini on the product `Ioc r z₁ × Iθ`.
  have hswap : (∫ z in Set.Ioc r z₁,
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ))
      = ∫ θ in Work.Spaces.Iθ, ∫ z in Set.Ioc r z₁,
          Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ :=
    MeasureTheory.integral_integral_swap hrect
  constructor
  · have hout : (∫ z in r..z₁,
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ))
        = ∫ z in Set.Ioc r z₁,
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) :=
      intervalIntegral.integral_of_le hrz.le
    have hin : (∫ θ in Work.Spaces.Iθ, ∫ z in r..z₁,
          Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ)
        = ∫ θ in Work.Spaces.Iθ, ∫ z in Set.Ioc r z₁,
            Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ := by
      refine MeasureTheory.setIntegral_congr_ae hmeasIθ ?_
      exact Filter.Eventually.of_forall (fun θ _ => intervalIntegral.integral_of_le hrz.le)
    exact hout.trans (hswap.trans hin.symm)
  · -- The `θ`-vanishing: integrate the `z`-FTC of the slice.
    have hsin0 : Work.Elliptic.sinCos2 0 = 0 := by simp [Work.Elliptic.sinCos2]
    have hsinpi : Work.Elliptic.sinCos2 (π / 2) = 0 := by simp [Work.Elliptic.sinCos2]
    have hpt : ∀ θ ∈ Work.Spaces.Iθ,
        (∫ z in r..z₁, Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ)
          = (Ψ z₁ θ - Ψ r θ) * Work.Elliptic.sinCos2 θ := by
      intro θ hθ
      rw [intervalIntegral.integral_mul_const]
      by_cases hθi : θ ∈ Set.Ioo 0 (π / 2)
      · -- interior angle: the fundamental theorem of calculus in `z` for the slice
        have hderiv : ∀ x ∈ Set.uIcc r z₁,
            HasDerivAt (fun z' => Ψ z' θ) (Work.Spaces.pz Ψ x θ) x := by
          intro x hx
          rw [Set.uIcc_of_le hrz.le] at hx
          exact hsm.hasDerivAt_slice hθi (lt_of_lt_of_le hr hx.1)
        have hcont : ContinuousOn (fun z => Work.Spaces.pz Ψ z θ) (Set.uIcc r z₁) := by
          have hc : ContinuousOn (fun z => Work.Spaces.pz Ψ z θ) (Set.Ioi 0) :=
            ((hsm.pz).curry_z hθi).continuousOn
          refine hc.mono ?_
          intro x hx
          rw [Set.uIcc_of_le hrz.le] at hx
          exact lt_of_lt_of_le hr hx.1
        rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
      · -- endpoint angle: `sin θ cos²θ` vanishes, so both sides are zero
        have hθ' : θ = 0 ∨ θ = π / 2 := by
          rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
          rw [Set.mem_Ioo] at hθi
          by_cases h0 : 0 < θ
          · exact Or.inr (le_antisymm hθ.2 (not_lt.mp (fun hlt => hθi ⟨h0, hlt⟩)))
          · exact Or.inl (le_antisymm (not_lt.mp h0) hθ.1)
        rcases hθ' with h | h
        · rw [h, hsin0]; ring
        · rw [h, hsinpi]; ring
    have hpt_int : (∫ θ in Work.Spaces.Iθ, ∫ z in r..z₁,
          Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ)
        = ∫ θ in Work.Spaces.Iθ, (Ψ z₁ θ - Ψ r θ) * Work.Elliptic.sinCos2 θ :=
      MeasureTheory.setIntegral_congr_ae hmeasIθ (Filter.Eventually.of_forall hpt)
    have hsplit : (∫ θ in Work.Spaces.Iθ, (Ψ z₁ θ - Ψ r θ) * Work.Elliptic.sinCos2 θ)
        = (∫ θ in Work.Spaces.Iθ, Ψ z₁ θ * Work.Elliptic.sinCos2 θ)
          - (∫ θ in Work.Spaces.Iθ, Ψ r θ * Work.Elliptic.sinCos2 θ) := by
      rw [show (fun θ => (Ψ z₁ θ - Ψ r θ) * Work.Elliptic.sinCos2 θ)
            = (fun θ => Ψ z₁ θ * Work.Elliptic.sinCos2 θ - Ψ r θ * Work.Elliptic.sinCos2 θ)
          from by funext θ; ring]
      exact MeasureTheory.integral_sub hΨz hΨr
    rw [hpt_int, hsplit]
    simp only [Work.Elliptic.Fstar] at hFz hFr
    rw [hFz, hFr]
    ring

end Work.FTS.EllipticEst.remov
