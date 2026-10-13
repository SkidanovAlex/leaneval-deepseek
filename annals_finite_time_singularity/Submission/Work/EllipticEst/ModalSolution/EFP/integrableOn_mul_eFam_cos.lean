/-
# `EFP.integrableOn_mul_eFam_cos` — one mode of a `L²(Iθ, cos θ dθ)` function is `L¹`

If `θ ↦ F z θ` is a.e. strongly measurable on `Iθ` and `θ ↦ F z θ ^ 2 * cos θ` is integrable
there (i.e. `F z · ∈ L²(Iθ, cos θ dθ)`), then for every mode `eFam m` of the angular
Gegenbauer basis the product `θ ↦ F z θ * eFam m θ * cos θ` is integrable on `Iθ`.

The point is that `eFam m` is bounded on the compact interval `Iθ` (it is `cos θ` times the
continuous function `gC (2m+1) ∘ sin`), and that `L²` on a *finite* measure space sits inside
`L¹`: writing `F z θ * eFam m θ * cos θ = (F z θ * √(cos θ)) * (eFam m θ * √(cos θ))`,
both factors lie in `L²(Iθ)` — the first because `(F z θ * √(cos θ)) ^ 2 = F z θ ^ 2 * cos θ`
on `Iθ` (where `cos θ ≥ 0`), the second because `eFam m` is bounded there — so their product
is `L¹` by Hölder.

The measurability hypothesis `hmeas` is essential: without it `IntegrableOn (F ^ 2 * cos)`
constrains only `|F|` and does not force `F` itself to be a.e. strongly measurable (see
`Work.EllipticEst.ModalSolution.eFamBasisFts_FALSE`).
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.gC_ode

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.EllipticEst.ModalSolution.EFP

theorem integrableOn_mul_eFam_cos (F : ℝ → ℝ → ℝ) (z : ℝ) (m : ℕ)
    (hmeas : MeasureTheory.AEStronglyMeasurable (fun θ => F z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hz : MeasureTheory.IntegrableOn (fun θ => F z θ ^ 2 * Real.cos θ) Work.Spaces.Iθ) :
    MeasureTheory.IntegrableOn
      (fun θ => F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ)
      Work.Spaces.Iθ := by
  -- `volume.restrict Iθ` is a finite measure: `Iθ = [0, π/2]` is compact.
  haveI hfin : IsFiniteMeasure (volume.restrict Work.Spaces.Iθ) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact isCompact_Icc.measure_lt_top
  -- The mode `eFam m` is bounded on `Iθ`.
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ θ ∈ Work.Spaces.Iθ,
      ‖Work.FTS.PhiStar.Gegenbauer.eFam m θ‖ ≤ C := by
    have hcont : Continuous (fun θ : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m θ) :=
      Real.continuous_cos.mul
        (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous).comp
          Real.continuous_sin)
    have hcomp : IsCompact (Work.Spaces.Iθ) := isCompact_Icc
    obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuousOn hcont.continuousOn
    exact ⟨C, fun θ hθ => hC θ hθ⟩
  have hCnonneg : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 Work.Spaces.zero_mem_Iθ)
  -- `F z · * √(cos ·) ∈ L²(Iθ)`.
  have haesmF : AEStronglyMeasurable (fun θ => F z θ * Real.sqrt (Real.cos θ))
      (volume.restrict Work.Spaces.Iθ) :=
    hmeas.mul ((Real.continuous_sqrt.comp Real.continuous_cos).aestronglyMeasurable)
  have hz' : Integrable (fun θ => F z θ ^ 2 * Real.cos θ)
      (volume.restrict Work.Spaces.Iθ) := hz
  have hsqF : Integrable (fun θ => (F z θ * Real.sqrt (Real.cos θ)) ^ 2)
      (volume.restrict Work.Spaces.Iθ) := by
    refine hz'.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    have hcos : 0 ≤ Real.cos θ := by
      apply Real.cos_nonneg_of_mem_Icc
      exact ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    rw [mul_pow, Real.sq_sqrt hcos]
  have hF : MemLp (fun θ => F z θ * Real.sqrt (Real.cos θ)) 2
      (volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq haesmF).mpr hsqF
  -- `eFam m · * √(cos ·) ∈ L²(Iθ)`, since `eFam m` is bounded on `Iθ` and `√(cos θ) ≤ 1` there.
  have hcontG : Continuous (fun θ : ℝ =>
      Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.sqrt (Real.cos θ)) :=
    (Real.continuous_cos.mul
      (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous).comp
        Real.continuous_sin)).mul (Real.continuous_sqrt.comp Real.continuous_cos)
  have hG : MemLp (fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.sqrt (Real.cos θ)) 2
      (volume.restrict Work.Spaces.Iθ) := by
    refine MemLp.of_bound hcontG.aestronglyMeasurable C ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
    have hsqrtle : ‖Real.sqrt (Real.cos θ)‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_one.mpr (Real.cos_le_one θ)
    calc ‖Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.sqrt (Real.cos θ)‖
        = ‖Work.FTS.PhiStar.Gegenbauer.eFam m θ‖ * ‖Real.sqrt (Real.cos θ)‖ := norm_mul _ _
      _ ≤ C * 1 := mul_le_mul (hC θ hθ) hsqrtle (norm_nonneg _) hCnonneg
      _ = C := mul_one C
  -- Hölder: a product of two `L²` functions is `L¹`.
  have hprod : MemLp ((fun θ => F z θ * Real.sqrt (Real.cos θ)) *
      (fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.sqrt (Real.cos θ))) 1
      (volume.restrict Work.Spaces.Iθ) := hF.mul hG
  have hint : IntegrableOn ((fun θ => F z θ * Real.sqrt (Real.cos θ)) *
      (fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.sqrt (Real.cos θ)))
      Work.Spaces.Iθ := MeasureTheory.memLp_one_iff_integrable.mp hprod
  -- Rewrite the product into the requested shape, using `√(cos θ) * √(cos θ) = cos θ`.
  have heq : ∀ θ ∈ Work.Spaces.Iθ,
      ((fun θ => F z θ * Real.sqrt (Real.cos θ)) *
        (fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.sqrt (Real.cos θ))) θ
      = F z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ := by
    intro θ hθ
    have hcos : 0 ≤ Real.cos θ := by
      apply Real.cos_nonneg_of_mem_Icc
      exact ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    simp only [Pi.mul_apply]
    rw [mul_mul_mul_comm, Real.mul_self_sqrt hcos]
  exact IntegrableOn.congr_fun hint heq measurableSet_Icc

end Work.EllipticEst.ModalSolution.EFP
