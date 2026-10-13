import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PressureOn.MollDefs
import Submission.Work.FTS.PressureOn.MollAux.rho_props
import Submission.Work.FTS.PressureOn.MollAux.moll_smooth_bounded

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.MollAux

open MeasureTheory

/-- The outer radius `1/(n+1)` of the mollifier bump is at most `1`. -/
theorem bump_rOut_le_one (n : ℕ) : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2 : (1 : ℝ) ≤ 1 * ((n : ℝ) + 1) := by
    have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  exact (div_le_iff₀ hpos).mpr h2

/-- The support of `rho n` lies in the closed unit ball: `rho n t ≠ 0` forces `‖t‖ ≤ 1`. -/
theorem norm_le_one_of_rho_ne_zero (n : ℕ) (t : EuclideanSpace ℝ (Fin 3))
    (ht : Work.FTS.PressureOn.rho n t ≠ 0) : ‖t‖ ≤ 1 :=
  le_trans ((rho_props n).2.2.2.2.2.1 t ht) (bump_rOut_le_one n)

/-- The integrand `t ↦ rho n t • ψ (x - t)` of the mollification `mollV n ψ x` vanishes
identically as soon as `x` is at distance `> 1` from `tsupport ψ`: the support of `rho n` lies
in the unit ball, while `tsupport ψ` stays outside it. -/
theorem rho_smul_eq_zero_of_dist_gt_one (n : ℕ) (ψ : EuclideanSpace ℝ (Fin 3) →
    EuclideanSpace ℝ (Fin 3)) (x : EuclideanSpace ℝ (Fin 3))
    (hx : ∀ b ∈ tsupport ψ, 1 < dist x b) (t : EuclideanSpace ℝ (Fin 3)) :
    Work.FTS.PressureOn.rho n t • ψ (x - t) = 0 := by
  by_cases ht : Work.FTS.PressureOn.rho n t = 0
  · rw [ht, zero_smul]
  · have hdist : dist x (x - t) = ‖t‖ := by rw [dist_eq_norm, sub_sub_cancel]
    have hnot : x - t ∉ tsupport ψ := by
      intro hmem
      have hlt := hx (x - t) hmem
      rw [hdist] at hlt
      have := norm_le_one_of_rho_ne_zero n t ht
      linarith
    rw [image_eq_zero_of_notMem_tsupport hnot, smul_zero]

theorem mollV_support_bound (n : ℕ) (ψ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (M : ℝ) (hM : ∀ y, ‖ψ y‖ ≤ M) :
    (∀ x, (∀ b ∈ tsupport ψ, 1 < dist x b) → Work.FTS.PressureOn.mollV n ψ x = 0) ∧
      (∀ x, ‖Work.FTS.PressureOn.mollV n ψ x‖ ≤ M) := by
  constructor
  · intro x hx
    rw [MollSB.mollV_eq_integral_rho]
    have hzero : (fun t => Work.FTS.PressureOn.rho n t • ψ (x - t))
        =ᵐ[volume] (fun _ => (0 : EuclideanSpace ℝ (Fin 3))) :=
      Filter.Eventually.of_forall (rho_smul_eq_zero_of_dist_gt_one n ψ x hx)
    rw [integral_congr_ae hzero]
    simp
  · intro x
    exact MollSB.norm_mollV_le n ψ M hM x

end Work.FTS.PressureOn.MollAux
