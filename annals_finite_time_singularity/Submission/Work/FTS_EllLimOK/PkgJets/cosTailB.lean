import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS_EllLimOK.PkgJets.CosTailDefs
import Submission.Work.FTS_EllLimOK.PkgJets.ctF_le_ctA
import Submission.Work.FTS_EllLimOK.PkgJets.ctG_le_ctB
import Submission.Work.FTS_EllLimOK.PkgJets.ctSmall_integral_le
import Submission.Work.FTS_EllLimOK.PkgJets.ctTail_integral_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets

open scoped Real Topology
open MeasureTheory Set

/-- `ctF` is continuous on `[π/4, T]` when `π/4 ≤ T < π/2`; hence interval integrable,
so that `∫_0^T = ∫_0^{π/4} + ∫_{π/4}^T` can be applied in the second case of the split. -/
theorem ctF_intervalIntegrable_quarter {T : ℝ} (h1 : Real.pi / 4 ≤ T) (h2 : T < Real.pi / 2) :
    IntervalIntegrable ctF MeasureTheory.volume (Real.pi / 4) T := by
  have hsin : ∀ x ∈ Set.Icc (Real.pi / 4) T, 0 < Real.sin (2 * x) := by
    intro x hx
    refine Real.sin_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hx.1], ?_⟩
    linarith [hx.2, h2]
  have hcos : ∀ x ∈ Set.Icc (Real.pi / 4) T, 0 < Real.cos x := by
    intro x hx
    refine Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hx.1], by linarith [hx.2, h2]⟩
  have hcont : ContinuousOn ctF (Set.Icc (Real.pi / 4) T) := by
    unfold ctF
    refine ContinuousOn.div ?_ (Real.continuous_cos.pow 4).continuousOn ?_
    · refine ContinuousOn.rpow_const ?_ ?_
      · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
      · intro x hx; exact Or.inl (ne_of_gt (hsin x hx))
    · intro x hx; exact pow_ne_zero 4 (ne_of_gt (hcos x hx))
  exact ContinuousOn.intervalIntegrable_of_Icc h1 hcont

/-- Second half of the `cos`-weight tail estimate: the primitive
`∫_0^T sin(2s)^{-η}/cos(s)^4 ds` diverges as `T → π/2`, but only like `(π/2 - T)^{-(3+η)}`
(with `η = 99/100`).  Intended route: on `(0, π/4]` use `sin (2s) ≥ (4/π) s` and `cos s ≥ √2/2`,
so the integrand is `≤ 4 (π/4)^η s^{-η}`, giving a finite bound `K` for `T ≤ π/4`; for
`T ∈ [π/4, π/2)` split `∫_0^T = ∫_0^{π/4} + ∫_{π/4}^T`, and for `u ∈ [π/4, T]` put
`w = π/2 - u`, where `sin(2u) = sin(2w) ≥ (4/π) w` and `cos u = sin w ≥ (2/π) w`, so
`g(u) ≤ (π/4)^η (π/2)^4 w^{-(4+η)}`; then `∫_{π/4}^T w^{-(4+η)} du = ∫_{δ}^{π/4} v^{-(4+η)} dv`
with `δ = π/2 - T ≤ π/4` (substitution `v = π/2 - u`, via
`intervalIntegral.integral_comp_sub_left`), which is `≤ δ^{-(3+η)}/(3+η)` by `integral_rpow`. -/
theorem cosTailB :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, T ∈ Set.Ioo 0 (Real.pi / 2) →
      (∫ s in (0 : ℝ)..T, (Real.sin (2 * s)) ^ (-(99 / 100 : ℝ)) / (Real.cos s) ^ (4 : ℕ))
        ≤ C * (Real.pi / 2 - T) ^ (-(3 + 99 / 100 : ℝ)) := by
  refine ⟨10 ^ 5, by norm_num, ?_⟩
  intro T hT
  change (∫ s in (0 : ℝ)..T, ctF s) ≤ 10 ^ 5 * (Real.pi / 2 - T) ^ (-(3 + 99 / 100 : ℝ))
  have hδpos : 0 < Real.pi / 2 - T := by linarith [hT.2]
  by_cases hle : T ≤ Real.pi / 4
  · -- Case `T ≤ π/4`: the integral over `(0, T]` is uniformly bounded by `1600`,
    -- while `(π/2 - T)^{-(3+η)} ≥ (π/2)^{-(3+η)} ≥ 1/16`.
    have h1 : (∫ s in (0 : ℝ)..T, ctF s) ≤ 1600 :=
      ctSmall_integral_le.2 T ⟨hT.1, hle⟩
    have hδ : Real.pi / 2 - T < Real.pi / 2 := by linarith [hT.1]
    have h2 : (Real.pi / 2) ^ (-(3 + 99 / 100 : ℝ))
        ≤ (Real.pi / 2 - T) ^ (-(3 + 99 / 100 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hδpos (le_of_lt hδ) (by norm_num)
    have h3 : (1 : ℝ) / 16 ≤ (Real.pi / 2 - T) ^ (-(3 + 99 / 100 : ℝ)) :=
      le_trans ct_sixteenth_le_pi_div_two_rpow h2
    have h4 : (1600 : ℝ) ≤ 10 ^ 5 * (Real.pi / 2 - T) ^ (-(3 + 99 / 100 : ℝ)) := by
      nlinarith [h3]
    linarith
  · -- Case `π/4 < T < π/2`: split the integral at `π/4`; the first piece is `≤ 1600`,
    -- the second is `≤ 1000 (π/2 - T)^{-(3+η)}`, and `(π/2 - T)^{-(3+η)} ≥ 1`.
    have hlt : Real.pi / 4 < T := not_le.mp hle
    have hInt0 : IntervalIntegrable ctF MeasureTheory.volume (0 : ℝ) (Real.pi / 4) :=
      ctSmall_integral_le.1
    have hInt1 : IntervalIntegrable ctF MeasureTheory.volume (Real.pi / 4) T :=
      ctF_intervalIntegrable_quarter (le_of_lt hlt) hT.2
    have hsplit : (∫ s in (0 : ℝ)..T, ctF s)
        = (∫ s in (0 : ℝ)..(Real.pi / 4), ctF s) + (∫ s in (Real.pi / 4)..T, ctF s) :=
      (intervalIntegral.integral_add_adjacent_intervals hInt0 hInt1).symm
    have h1 : (∫ s in (0 : ℝ)..(Real.pi / 4), ctF s) ≤ 1600 :=
      ctSmall_integral_le.2 (Real.pi / 4) ⟨by linarith [Real.pi_pos], le_rfl⟩
    have h2 : (∫ s in (Real.pi / 4)..T, ctF s)
        ≤ 1000 * (Real.pi / 2 - T) ^ (-(3 + 99 / 100 : ℝ)) :=
      ctTail_integral_le T ⟨hlt, hT.2⟩
    have hδle : Real.pi / 2 - T ≤ Real.pi / 4 := by linarith [hlt]
    have h2' : (Real.pi / 4) ^ (-(3 + 99 / 100 : ℝ))
        ≤ (Real.pi / 2 - T) ^ (-(3 + 99 / 100 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hδpos hδle (by norm_num)
    have h3 : (1 : ℝ) ≤ (Real.pi / 2 - T) ^ (-(3 + 99 / 100 : ℝ)) :=
      le_trans ct_one_le_pi_div_four_rpow h2'
    rw [hsplit]
    nlinarith [h1, h2, h3]

end Work.FTS_EllLimOK.PkgJets
