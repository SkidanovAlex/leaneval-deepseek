import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.FTS.LocData.HkFstarDefs
import Submission.Work.Spaces.c_bounds
import Submission.Work.FTS.LocData.rpow_one_add_ge_sub_sqrt
import Submission.Work.FTS.LocData.integral_sqrt_sin_mul_cos_sq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The lower bound `3/5 ≤ c(α)`

The normalisation constant of Elgindi's paper is
`c(α) = ∫_{[0,π/2]} Γ(θ)K(θ) dθ` with `Γ(θ) = (sin θ cos²θ)^{α/3}` and
`K(θ) = 3 sin θ cos²θ`; only the range `1/10 ≤ c(α) ≤ 10` is needed in the paper
(`Work.Spaces.c_bounds`), but the localisation data used in this development
needs the sharper lower bound `3/5 ≤ c(α)` for `0 < α ≤ 1`.

On `Iθ` the integrand is `Γ(θ)K(θ) = 3 s^{1+α/3}` with `s = sin θ cos²θ ∈ [0,1]`.
Since `α ≤ 1` gives `1 + α/3 ≤ 4/3` and `s ≤ 1`,
`s^{1+α/3} ≥ s^{4/3} ≥ s - √s/5` (`Work.FTS.LocData.rpow_one_add_ge_sub_sqrt`,
whose content is that `sup_{v∈[0,1]} v³(1-v²) = 6√3/(25√5) ≈ 0.186 < 1/5`).
Integrating and using the two elementary integrals
`∫_{Iθ} s dθ = 1/3` and `∫_{Iθ} √s dθ = 2/3` gives

`c(α) ≥ 3(1/3 - (1/5)(2/3)) = 3/5`.

(The sharp value is `c(1) = 3 ∫_0^{π/2} (sin θ cos²θ)^{4/3} dθ ≈ 0.6545`.)
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.LocData

/-- The elementary angular integral `∫_{[0,π/2]} sin θ cos²θ dθ = 1/3`.

This is Mathlib's `integral_sin_mul_cos_sq` transported from the interval
`0..π/2` to the set `Work.Spaces.Iθ = Set.Icc 0 (π/2)`. -/
theorem integral_sin_mul_cos_sq_Iθ :
    ∫ θ in Work.Spaces.Iθ, Real.sin θ * Real.cos θ ^ 2 = 1 / 3 := by
  rw [Work.Spaces.Iθ, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2),
      integral_sin_mul_cos_sq]
  norm_num [Real.cos_zero, Real.cos_pi_div_two]

theorem c_ge_three_fifths (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) :
    (3 : ℝ)/5 ≤ Work.Spaces.c α := by
  -- `s = sin θ cos²θ ∈ [0,1]` on `Iθ`.
  have hsq_nonneg : ∀ θ ∈ Work.Spaces.Iθ, (0 : ℝ) ≤ Real.sin θ * Real.cos θ ^ 2 := by
    intro θ hθ
    have hs : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩
    positivity
  have hsq_le_one : ∀ θ ∈ Work.Spaces.Iθ, Real.sin θ * Real.cos θ ^ 2 ≤ 1 := by
    intro θ hθ
    have hs : Real.sin θ ≤ 1 := Real.sin_le_one θ
    have hc : Real.cos θ ^ 2 ≤ 1 := by
      have h := sq_le_sq' (Real.neg_one_le_cos θ) (Real.cos_le_one θ)
      simpa using h
    have hc0 : (0 : ℝ) ≤ Real.cos θ ^ 2 := by positivity
    simpa using mul_le_mul hs hc hc0 (by norm_num : (0 : ℝ) ≤ 1)
  -- Integrability of the two pieces of the comparison function.
  have hcont_s : ContinuousOn (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) Work.Spaces.Iθ :=
    (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).continuousOn
  have hcont_sqrt :
      ContinuousOn (fun θ : ℝ => Real.sqrt (Real.sin θ * Real.cos θ ^ 2)) Work.Spaces.Iθ :=
    hcont_s.sqrt
  have hsqrt_int :
      IntegrableOn (fun θ : ℝ => Real.sqrt (Real.sin θ * Real.cos θ ^ 2)) Work.Spaces.Iθ :=
    hcont_sqrt.integrableOn_Icc
  have hK_int : IntegrableOn (fun θ : ℝ => Work.Spaces.K θ) Work.Spaces.Iθ := by
    refine ContinuousOn.integrableOn_Icc ?_
    simp only [Work.Spaces.K]
    fun_prop
  have hlb_int : IntegrableOn
      (fun θ : ℝ => Work.Spaces.K θ - (3/5) * Real.sqrt (Real.sin θ * Real.cos θ ^ 2))
      Work.Spaces.Iθ :=
    hK_int.sub (hsqrt_int.const_mul (3/5))
  -- The pointwise comparison `K θ - (3/5)√s ≤ Γ(θ)K(θ)` on `Iθ`.
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.K θ - (3/5) * Real.sqrt (Real.sin θ * Real.cos θ ^ 2)
        ≤ Work.Spaces.Gam α θ * Work.Spaces.K θ := by
    intro θ hθ
    have hA := rpow_one_add_ge_sub_sqrt (Real.sin θ * Real.cos θ ^ 2)
      (hsq_nonneg θ hθ) (hsq_le_one θ hθ) α hα hα1
    -- `Γ(θ)K(θ) = 3 s^{1+α/3}`
    have hident : Work.Spaces.Gam α θ * Work.Spaces.K θ
        = 3 * (Real.sin θ * Real.cos θ ^ 2) ^ (1 + α / 3) := by
      have h1 : (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) * (Real.sin θ * Real.cos θ ^ 2)
          = (Real.sin θ * Real.cos θ ^ 2) ^ (1 + α / 3) := by
        rw [Real.rpow_add' (hsq_nonneg θ hθ) (by positivity : 1 + α / 3 ≠ 0), Real.rpow_one]
        ring
      rw [Work.Spaces.Gam, Work.Spaces.K]
      calc (Real.sin θ * Real.cos θ ^ 2) ^ (α / 3) * (3 * Real.sin θ * Real.cos θ ^ 2)
          = 3 * ((Real.sin θ * Real.cos θ ^ 2) ^ (α / 3)
              * (Real.sin θ * Real.cos θ ^ 2)) := by ring
        _ = 3 * (Real.sin θ * Real.cos θ ^ 2) ^ (1 + α / 3) := by rw [h1]
    have hkey : 3 * (Real.sin θ * Real.cos θ ^ 2
        - Real.sqrt (Real.sin θ * Real.cos θ ^ 2) / 5)
        ≤ 3 * (Real.sin θ * Real.cos θ ^ 2) ^ (1 + α / 3) :=
      mul_le_mul_of_nonneg_left hA (by norm_num)
    have hrew : Work.Spaces.K θ - (3/5) * Real.sqrt (Real.sin θ * Real.cos θ ^ 2)
        = 3 * (Real.sin θ * Real.cos θ ^ 2
            - Real.sqrt (Real.sin θ * Real.cos θ ^ 2) / 5) := by
      rw [Work.Spaces.K]; ring
    rw [hrew, hident]
    exact hkey
  have hmono := MeasureTheory.setIntegral_mono_on hlb_int
    (Work.Spaces.CAux.integrableOn_GamK α hα) measurableSet_Icc hpt
  -- The two integrals.
  have hKval : ∫ θ in Work.Spaces.Iθ, Work.Spaces.K θ = 1 := by
    have hK_eq : (fun θ : ℝ => Work.Spaces.K θ)
        = fun θ : ℝ => 3 * (Real.sin θ * Real.cos θ ^ 2) := by
      funext θ; rw [Work.Spaces.K]; ring
    rw [hK_eq, MeasureTheory.integral_const_mul, integral_sin_mul_cos_sq_Iθ]
    norm_num
  have hsqrtval : ∫ θ in Work.Spaces.Iθ,
      (3/5) * Real.sqrt (Real.sin θ * Real.cos θ ^ 2) = 2/5 := by
    rw [MeasureTheory.integral_const_mul, integral_sqrt_sin_mul_cos_sq]
    norm_num
  have hval : ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.K θ - (3/5) * Real.sqrt (Real.sin θ * Real.cos θ ^ 2)) = 3/5 := by
    rw [MeasureTheory.integral_sub hK_int (hsqrt_int.const_mul (3/5)), hKval, hsqrtval]
    norm_num
  calc (3 : ℝ)/5 = ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.K θ - (3/5) * Real.sqrt (Real.sin θ * Real.cos θ ^ 2)) := hval.symm
    _ ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.Gam α θ * Work.Spaces.K θ := hmono
    _ = Work.Spaces.c α := rfl

end Work.FTS.LocData
