import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.ODE.ExistUnique

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.ODE

open Set Metric
open scoped NNReal Topology

/-- **Uniform local existence for a bounded linear ODE.**

Let `A : ℝ → E →L[ℝ] E` be a continuous family of bounded linear operators on a Banach space `E`
whose operator norms are bounded by a constant `M` (`‖A t‖ ≤ M` for all `t`).  Then there is a
single radius `ε ∈ (0, 1]` such that *every* initial datum `x₁` with `‖x₁‖ ≤ R` at *every* initial
time `t₁` admits a solution of the linear initial value problem
`α' = A t (α t)`, `α t₁ = x₁` on the closed interval `[t₁ - ε, t₁ + ε]`, with one-sided
derivatives at the endpoints.

The essential point is that the existence radius is uniform in `t₁` and in `x₁`: the field
`(t, x) ↦ A t x` is globally Lipschitz in `x` with constant `M`, and it is bounded by `M · (2R+1)`
on the ball of radius `R + 1` around any admissible `x₁`.  Hence the hypotheses of the
Picard–Lindelöf theorem (`IsPicardLindelof`) hold on the window `[t₁ - ε, t₁ + ε]` as soon as
`M · (2R+1) · ε ≤ 1`, and it suffices to take `ε = 1 / (M · (2R+1) + 1) ≤ 1`. -/
theorem exists_uniform_local_solution_linearODE {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {A : ℝ → E →L[ℝ] E} (hA : Continuous A) {M : NNReal}
    (hM : ∀ t, ‖A t‖ ≤ M) {R : ℝ} (hR : 0 ≤ R) :
    ∃ ε > (0 : ℝ), ε ≤ 1 ∧ ∀ (t₁ : ℝ) (x₁ : E), ‖x₁‖ ≤ R →
      ∃ α : ℝ → E, α t₁ = x₁ ∧ ∀ t ∈ Set.Icc (t₁ - ε) (t₁ + ε),
        HasDerivWithinAt α (A t (α t)) (Set.Icc (t₁ - ε) (t₁ + ε)) t := by
  classical
  -- The operator norm bound on the ball of radius `R + 1` around any admissible initial point.
  set D : ℝ := (M : ℝ) * (2 * R + 1) with hDdef
  -- The uniform existence radius.
  set ε : ℝ := 1 / (D + 1) with hεdef
  have hD : 0 ≤ D := by
    rw [hDdef]
    have h1 : (0 : ℝ) ≤ (M : ℝ) := M.coe_nonneg
    nlinarith
  have hD1 : 0 < D + 1 := by linarith
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have hεle1 : ε ≤ 1 := by
    rw [hεdef, div_le_one hD1]; linarith
  have hLε : ((M : ℝ) * (2 * R + 1)) * ε ≤ 1 := by
    rw [hεdef, hDdef, mul_one_div, div_le_one hD1]
    linarith
  refine ⟨ε, hεpos, hεle1, ?_⟩
  intro t₁ x₁ hx₁
  set tmin : ℝ := t₁ - ε with htmin
  set tmax : ℝ := t₁ + ε with htmax
  have htmin_le : tmin ≤ t₁ := by rw [htmin]; linarith
  have htmax_le : t₁ ≤ tmax := by rw [htmax]; linarith
  set t₀ : Set.Icc tmin tmax := ⟨t₁, htmin_le, htmax_le⟩ with ht₀
  -- Radii and constants for the Picard–Lindelöf theorem.
  set a : NNReal := ⟨R + 1, by linarith⟩ with hadef
  set r : NNReal := ⟨R, hR⟩ with hrdef
  set L : NNReal := ⟨(M : ℝ) * (2 * R + 1), by nlinarith [M.coe_nonneg, hR]⟩ with hLdef
  have ha_coe : ((a : NNReal) : ℝ) = R + 1 := rfl
  have hr_coe : ((r : NNReal) : ℝ) = R := rfl
  have hL_coe : ((L : NNReal) : ℝ) = (M : ℝ) * (2 * R + 1) := rfl
  have hmem : x₁ ∈ closedBall (x₁ : E) r := by
    rw [mem_closedBall, dist_self]
    exact r.coe_nonneg
  -- The field `(t, x) ↦ A t x` is `M`-Lipschitz in `x`.
  have hf_lip : ∀ t ∈ Set.Icc tmin tmax,
      LipschitzOnWith M (fun x : E => A t x) (closedBall x₁ a) := fun t _ =>
    ((A t).lipschitzWith_of_opNorm_le (hM t)).lipschitzOnWith
  -- ... it is continuous in `t` ...
  have hf_cont : ∀ x ∈ closedBall x₁ a,
      ContinuousOn (fun t : ℝ => A t x) (Set.Icc tmin tmax) := fun x _ =>
    (by fun_prop : Continuous fun t : ℝ => A t x).continuousOn
  -- ... and it is bounded by `L` on the ball of radius `R + 1`.
  have hf_norm : ∀ t ∈ Set.Icc tmin tmax, ∀ x ∈ closedBall x₁ a,
      ‖(fun t x => A t x) t x‖ ≤ L := by
    intro t _ x hx
    rw [hL_coe]
    have hx' : ‖x - x₁‖ ≤ R + 1 := by
      rw [← dist_eq_norm]
      have := hx
      rw [mem_closedBall, ha_coe] at this
      linarith
    have hxn : ‖x‖ ≤ 2 * R + 1 := by
      calc ‖x‖ = ‖(x - x₁) + x₁‖ := by rw [sub_add_cancel]
        _ ≤ ‖x - x₁‖ + ‖x₁‖ := norm_add_le _ _
        _ ≤ (R + 1) + R := by linarith
        _ = 2 * R + 1 := by ring
    calc ‖A t x‖ ≤ ‖A t‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (M : ℝ) * ‖x‖ := by gcongr; exact hM t
      _ ≤ (M : ℝ) * (2 * R + 1) := by gcongr
  -- The time constraint of the Picard–Lindelöf theorem.
  have hf_mul : L * max (tmax - (t₀ : ℝ)) (↑t₀ - tmin) ≤ a - r := by
    have ht₀val : (t₀ : ℝ) = t₁ := rfl
    rw [ht₀val, htmax, htmin]
    have hsimp : max (t₁ + ε - t₁) (t₁ - (t₁ - ε)) = ε := by
      rw [add_sub_cancel_left, sub_sub_cancel, max_self]
    rw [hsimp, ha_coe, hr_coe, hL_coe]
    linarith [hLε]
  have hPL : IsPicardLindelof (fun t x => A t x) t₀ x₁ a r L M :=
    ⟨hf_lip, hf_cont, hf_norm, hf_mul⟩
  obtain ⟨α, hα0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt hmem
  refine ⟨α, hα0, fun t ht => ?_⟩
  refine hα t ?_
  rw [htmin, htmax]
  exact ht

end Commons.Analysis.ODE