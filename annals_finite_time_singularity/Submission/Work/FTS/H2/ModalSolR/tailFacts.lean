import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.Series.psiTrunc_solves
import Submission.Work.FTS.PhiStar.Series.eFamEneDefs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.ModalSolR

open scoped Real
open MeasureTheory Set

/-- Every basis function `eFam m = cos · C^{(3/2)}_{2m+1}(sin ·)` is `C²`: it is the
composition of a polynomial with `sin` and `cos`. -/
lemma eFam_contDiff_two (m : ℕ) : ContDiff ℝ 2 (Work.FTS.PhiStar.Gegenbauer.eFam m) := by
  rw [show Work.FTS.PhiStar.Gegenbauer.eFam m
      = (fun θ : ℝ => Real.cos θ
          * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)) from rfl]
  refine Real.contDiff_cos.mul ?_
  exact ((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).of_le (by norm_num)).comp
    Real.contDiff_sin

/-- The tail data of a finite modal sum `θ ↦ ∑_{m ∈ s} a m · eFam m θ`: it is `C²` on `Iθ`,
it vanishes at both endpoints (each `eFam m` does), and the three weights `cos θ`, its square
and its square divided by `cos θ` of the sum, of its derivative and of `sum / cos θ` are all
integrable on `Iθ`.  (The last one is integrable because the quotient is bounded: on `Iθ`
the equality `eFam m θ = cos θ · gC (2m+1) (sin θ)` cancels the `cos θ`; where `cos θ`
vanishes — only at `θ = π/2` — both sides of the integrand are `0`.) -/
theorem tailFacts (a : ℕ → ℝ) (s : Finset ℕ) :
    ContDiffOn ℝ 2 (fun θ => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        (Set.Icc 0 (Real.pi / 2))
    ∧ (∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m 0) = 0
    ∧ (∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m (Real.pi / 2)) = 0
    ∧ MeasureTheory.IntegrableOn
        (fun θ => (∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2
          * Real.cos θ) Work.Spaces.Iθ
    ∧ MeasureTheory.IntegrableOn
        (fun θ => (deriv (fun θ' => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ')
            θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ
    ∧ MeasureTheory.IntegrableOn
        (fun θ => ((∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) / Real.cos θ) ^ 2
          * Real.cos θ) Work.Spaces.Iθ := by
  have hF : ContDiff ℝ 2
      (fun θ => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) :=
    ContDiff.sum (fun m _ => contDiff_const.mul (eFam_contDiff_two m))
  refine ⟨hF.contDiffOn, ?_, ?_, ?_, ?_, ?_⟩
  · -- vanishing at `θ = 0`
    simp only [Work.FTS.PhiStar.Series.eFam_zero, mul_zero, Finset.sum_const_zero]
  · -- vanishing at `θ = π/2`
    simp only [Work.FTS.PhiStar.Series.eFam_pi_half, mul_zero, Finset.sum_const_zero]
  · -- integrability of the `cos θ`-weighted square
    exact (((hF.continuous.pow 2).mul Real.continuous_cos).continuousOn).integrableOn_compact
      isCompact_Icc
  · -- integrability of the `cos θ`-weighted square of the derivative
    have hderiv : Continuous (deriv
        (fun θ => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)) :=
      hF.continuous_deriv (by norm_num)
    exact (((hderiv.pow 2).mul Real.continuous_cos).continuousOn).integrableOn_compact
      isCompact_Icc
  · -- integrability of the `cos θ`-weighted square of the quotient by `cos θ`
    set G : ℝ → ℝ :=
      fun θ => ∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.gC (2 * m + 1) (Real.sin θ)
      with hGdef
    have hGcont : Continuous G := by
      refine continuous_finsetSum _ (fun m _ => ?_)
      exact continuous_const.mul
        (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous).comp
          Real.continuous_sin)
    refine MeasureTheory.IntegrableOn.congr_fun
      ((((hGcont.pow 2).mul Real.continuous_cos).continuousOn).integrableOn_compact
        isCompact_Icc) ?_ measurableSet_Icc
    intro θ hθ
    change G θ ^ 2 * Real.cos θ
        = ((∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ) / Real.cos θ) ^ 2
          * Real.cos θ
    have hFG : (∑ m ∈ s, a m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        = Real.cos θ * G θ := by
      rw [hGdef, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      simp only [Work.FTS.PhiStar.Gegenbauer.eFam]
      ring
    by_cases hc : Real.cos θ = 0
    · -- the only zero of `cos` on `Iθ` is `θ = π/2`, where both sides vanish
      have hθpi : θ = Real.pi / 2 := by
        by_contra hne
        have hlt : θ < Real.pi / 2 := lt_of_le_of_ne hθ.2 hne
        have hmem : θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
          ⟨by linarith [hθ.1, Real.pi_pos], hlt⟩
        have hpos := Real.cos_pos_of_mem_Ioo hmem
        linarith [hc]
      subst hθpi
      simp only [hFG, hc, zero_mul, mul_zero]
    · rw [hFG, mul_div_cancel_left₀ _ hc]

end Work.FTS.H2.ModalSolR
