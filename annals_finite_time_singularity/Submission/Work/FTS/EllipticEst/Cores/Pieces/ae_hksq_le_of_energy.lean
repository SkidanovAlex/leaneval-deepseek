import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSigmaUpgradeU
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSigma.AeHkMemU
import Submission.Work.FTS.EllipticEst.AngAWeak.aeSigmaUpgradeRho

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores.Pieces

/-- The two domains `Iz = [0,∞)` and `Ioi 0 = (0,∞)` differ by the null set `{0}`, so they carry
the same restricted Lebesgue measure. -/
theorem ae_hksq_le_of_energy_restrict_Iz :
    MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) := by
  rw [Work.Spaces.Iz]
  exact (MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))).symm

/-- `Iz` and `Ioi 0` agree almost everywhere. -/
theorem ae_hksq_le_of_energy_Iz_ae_eq :
    Work.Spaces.Iz =ᵐ[MeasureTheory.volume] Set.Ioi (0 : ℝ) := by
  have h : Set.Ioi (0 : ℝ) =ᵐ[MeasureTheory.volume] Set.Ici (0 : ℝ) :=
    MeasureTheory.Ioi_ae_eq_Ici
  rw [Work.Spaces.Iz]
  exact h.symm

/-- **Honesty transfer across the two radial domains.**  `IntegrableOn` is insensitive to the
passage from `(0,∞)` to `[0,∞)`. -/
theorem ae_hksq_le_of_energy_integrableOn_Iz_iff {f : ℝ → ℝ} :
    MeasureTheory.IntegrableOn f Work.Spaces.Iz
      ↔ MeasureTheory.IntegrableOn f (Set.Ioi (0 : ℝ)) := by
  show MeasureTheory.Integrable f (MeasureTheory.volume.restrict Work.Spaces.Iz)
      ↔ MeasureTheory.Integrable f (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
  rw [ae_hksq_le_of_energy_restrict_Iz]

/-- **The level-`0` mass bound from the angular energy.**  In the almost-everywhere class
`AeData`, the `ρ = w²σ`-weighted `L²`-mass of `u` is controlled by the *unweighted* angular
energy `∫_z w z² ∫_θ (∂_θu(z,θ))² dθ dz`: the singular angular weight `σ θ = sin(2θ)^{-η}` is
traded for a universal constant by the constrained slice `σ`-Poincaré inequality, and the
`z`-integral is then transported from `(0,∞)` to `Iz = [0,∞)` (`{0}` is null). -/
theorem ae_hksq_le_of_energy : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
    MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2)) Work.Spaces.Iz →
    Work.Spaces.HkSq α 0 u
      ≤ C * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2)) := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.EllipticEst.AngAWeak.aeSigmaUpgradeRho
  refine ⟨C, hCpos, fun α u G h hInt => ?_⟩
  -- transport the integrability hypothesis to `(0,∞)`
  have hIntIoi : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2)) (Set.Ioi (0 : ℝ)) :=
    ae_hksq_le_of_energy_integrableOn_Iz_iff.mp hInt
  have hmain := hC α u G h hIntIoi
  -- and the integral back to `Iz`
  have hconv := MeasureTheory.setIntegral_congr_set (μ := MeasureTheory.volume)
    (f := fun z => (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2))
    ae_hksq_le_of_energy_Iz_ae_eq
  rw [← hconv] at hmain
  exact hmain

end Work.FTS.EllipticEst.Cores.Pieces
