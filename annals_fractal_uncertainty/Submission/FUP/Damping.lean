import ChallengeDeps
import Submission.FUP.Cubes
import Submission.Commons.Analysis.SpecialFunctions.monotoneOn_div_log_rpow

open FractalUncertainty MeasureTheory FourierTransform Metric
open scoped ENNReal BigOperators

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-!
# Damping functions (Cohen §"Outline", Han–Schlag Definition 4.1)

This module contains the definitions of `ℓ₂`- and `ℓ₁`-damping functions and the basic
monotonicity properties that the proof of the fractal uncertainty principle uses.

Pointwise bounds on an `L²` class are formulated almost everywhere (see the discussion in
`Submission.FUP.Spec`).
-/

namespace Submission.FUP

/-- `⟨x⟩ = (1 + ‖x‖²)^{1/2}`. -/
noncomputable def bracket (x : ℝᵈ) : ℝ := Real.sqrt (1 + ‖x‖ ^ 2)

lemma bracket_pos (x : ℝᵈ) : 0 < bracket x :=
  Real.sqrt_pos.mpr (by positivity)

lemma bracket_pow (x : ℝᵈ) (s : ℝ) : bracket x ^ s = (1 + ‖x‖ ^ 2) ^ (s / 2) := by
  rw [bracket, Real.sqrt_eq_rpow,
    ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 + ‖x‖ ^ 2)]
  ring_nf

/-- The `ℓ₁` norm `|x|₁ = ∑ᵢ ‖xᵢ‖` on `ℝᵈ`. -/
noncomputable def l1norm (x : ℝᵈ) : ℝ := ∑ i : Fin d, ‖x i‖

lemma l1norm_nonneg (x : ℝᵈ) : 0 ≤ l1norm x :=
  Finset.sum_nonneg (fun i _ => norm_nonneg _)

lemma norm_apply_le_norm (x : ℝᵈ) (i : Fin d) : ‖x i‖ ≤ ‖x‖ := PiLp.norm_apply_le x i

/-- `|x|₁ ≤ √d·‖x‖`. -/
lemma l1norm_le_sqrt_mul (x : ℝᵈ) : l1norm x ≤ Real.sqrt (d : ℝ) * ‖x‖ := by
  have hsum : ∑ i : Fin d, ‖x i‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Real.norm_eq_abs, sq_abs]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
    (fun i : Fin d => ‖x i‖) (fun _ : Fin d => (1 : ℝ))
  simp only [mul_one, one_pow] at hcs
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hsum] at hcs
  simp only [nsmul_eq_mul, mul_one] at hcs
  rw [l1norm]
  have h2 : (0 : ℝ) ≤ ∑ i : Fin d, ‖x i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hsq : (∑ i : Fin d, ‖x i‖) ^ 2 ≤ (Real.sqrt (d : ℝ) * ‖x‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ d)]
    nlinarith [hcs]
  calc ∑ i : Fin d, ‖x i‖ = |∑ i : Fin d, ‖x i‖| := (abs_of_nonneg h2).symm
    _ = Real.sqrt ((∑ i : Fin d, ‖x i‖) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((Real.sqrt (d : ℝ) * ‖x‖) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = |Real.sqrt (d : ℝ) * ‖x‖| := Real.sqrt_sq_eq_abs _
    _ = Real.sqrt (d : ℝ) * ‖x‖ := abs_of_nonneg (by positivity)

lemma closedBall_subset_cube {c : ℝ} :
    closedBall (0 : ℝᵈ) c ⊆ cube (-c) c := by
  intro x hx
  rw [Metric.mem_closedBall, dist_eq_norm] at hx
  simp only [sub_zero] at hx
  rw [mem_cube]
  intro i
  have hi : |x i| ≤ c := le_trans (norm_apply_le_norm x i) hx
  exact ⟨by linarith [abs_le.mp hi], by linarith [abs_le.mp hi]⟩

lemma ball_subset_cube :
    ball (0 : ℝᵈ) 1 ⊆ cube (-1) 1 := by
  intro x hx
  rw [Metric.mem_ball, dist_eq_norm] at hx
  simp only [sub_zero] at hx
  rw [mem_cube]
  intro i
  have h : |x i| < 1 := by
    rw [← Real.norm_eq_abs]
    exact lt_of_le_of_lt (norm_apply_le_norm x i) hx
  exact ⟨by linarith [abs_le.mp (le_of_lt h)], by linarith [abs_le.mp (le_of_lt h)]⟩

/-- Cohen's `defn:damping_func_l2`.  `Y` admits an `ℓ₂`-damping function with parameters
`c₁, c₂, c₃, α` if there is `ψ ∈ L²(ℝᵈ)` with

* Fourier support in the ball `B_{c₁}`,
* `‖ψ‖_{L²(B₁)} ≥ c₂`,
* `|ψ(x)| ≤ ⟨x⟩^{-d}` for a.e. `x`,
* `|ψ(x)| ≤ exp(-c₃ |x| / (log(2+|x|))^α)` for a.e. `x ∈ Y`. -/
noncomputable def AdmitsL2Damping (Y : Set ℝᵈ) (c₁ c₂ c₃ α : ℝ) : Prop :=
  ∃ ψ : Lp ℂ 2 (volume : Measure ℝᵈ),
    (∀ᵐ ξ ∂(volume : Measure ℝᵈ), ξ ∉ closedBall (0 : ℝᵈ) c₁ →
        ((𝓕 ψ : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ = 0) ∧
    (c₂ ^ 2 ≤ ∫ x in ball (0 : ℝᵈ) 1, ‖(ψ : ℝᵈ → ℂ) x‖ ^ 2) ∧
    (∀ᵐ x ∂(volume : Measure ℝᵈ),
        ‖(ψ : ℝᵈ → ℂ) x‖ ≤ bracket x ^ (-(d : ℝ))) ∧
    (∀ᵐ x ∂(volume : Measure ℝᵈ), x ∈ Y →
        ‖(ψ : ℝᵈ → ℂ) x‖ ≤
          Real.exp (-(c₃ * ‖x‖ / (Real.log (2 + ‖x‖)) ^ α)))

/-- Han–Schlag's Definition 4.1 (Cohen `defn:damping_func_l1`): the `ℓ₁` analogue of
`AdmitsL2Damping`, with Fourier support in the cube `[-c₁,c₁]^d` and the `L²` normalisation
over `[-1,1]^d`. -/
noncomputable def AdmitsL1Damping (Y : Set ℝᵈ) (c₁ c₂ c₃ α : ℝ) : Prop :=
  ∃ ψ : Lp ℂ 2 (volume : Measure ℝᵈ),
    (∀ᵐ ξ ∂(volume : Measure ℝᵈ), ξ ∉ cube (-c₁) c₁ →
        ((𝓕 ψ : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ = 0) ∧
    (c₂ ^ 2 ≤ ∫ x in cube (-1) 1, ‖(ψ : ℝᵈ → ℂ) x‖ ^ 2) ∧
    (∀ᵐ x ∂(volume : Measure ℝᵈ),
        ‖(ψ : ℝᵈ → ℂ) x‖ ≤ bracket x ^ (-(d : ℝ))) ∧
    (∀ᵐ x ∂(volume : Measure ℝᵈ), x ∈ Y →
        ‖(ψ : ℝᵈ → ℂ) x‖ ≤
          Real.exp (-(c₃ * l1norm x / (Real.log (2 + l1norm x)) ^ α)))

/-- The pointwise comparison used for monotonicity in `c₃`. -/
private lemma exp_decay_mono {c₃ c₃' α : ℝ} (hc₃ : c₃' ≤ c₃) (x : ℝᵈ) :
    Real.exp (-(c₃ * ‖x‖ / (Real.log (2 + ‖x‖)) ^ α))
      ≤ Real.exp (-(c₃' * ‖x‖ / (Real.log (2 + ‖x‖)) ^ α)) := by
  apply Real.exp_le_exp.mpr
  have ht : 0 ≤ ‖x‖ / (Real.log (2 + ‖x‖)) ^ α := by
    refine div_nonneg (norm_nonneg x) (le_of_lt ?_)
    refine Real.rpow_pos_of_pos ?_ α
    exact lt_of_lt_of_le (Real.log_pos (x := 2) (by norm_num))
      (Real.log_le_log (x := 2) (y := 2 + ‖x‖) (by norm_num)
        (by linarith [norm_nonneg x]))
  have h : c₃' * (‖x‖ / (Real.log (2 + ‖x‖)) ^ α)
      ≤ c₃ * (‖x‖ / (Real.log (2 + ‖x‖)) ^ α) :=
    mul_le_mul_of_nonneg_right hc₃ ht
  rw [mul_div_assoc, mul_div_assoc]
  linarith

/-- The pointwise comparison used for monotonicity in `c₃` (ℓ₁ version). -/
private lemma exp_decay_mono_l1 {c₃ c₃' α : ℝ} (hc₃ : c₃' ≤ c₃) (x : ℝᵈ) :
    Real.exp (-(c₃ * l1norm x / (Real.log (2 + l1norm x)) ^ α))
      ≤ Real.exp (-(c₃' * l1norm x / (Real.log (2 + l1norm x)) ^ α)) := by
  apply Real.exp_le_exp.mpr
  have ht : 0 ≤ l1norm x / (Real.log (2 + l1norm x)) ^ α := by
    refine div_nonneg (l1norm_nonneg x) (le_of_lt ?_)
    refine Real.rpow_pos_of_pos ?_ α
    exact lt_of_lt_of_le (Real.log_pos (x := 2) (by norm_num))
      (Real.log_le_log (x := 2) (y := 2 + l1norm x) (by norm_num)
        (by linarith [l1norm_nonneg x]))
  have h : c₃' * (l1norm x / (Real.log (2 + l1norm x)) ^ α)
      ≤ c₃ * (l1norm x / (Real.log (2 + l1norm x)) ^ α) :=
    mul_le_mul_of_nonneg_right hc₃ ht
  rw [mul_div_assoc, mul_div_assoc]
  linarith

/-- `AdmitsL2Damping` is monotone: enlarging `c₁` and shrinking `c₂`, `c₃` makes the
condition easier. -/
lemma admitsL2Damping_mono {c₁ c₂ c₃ c₁' c₂' c₃' α : ℝ} {Y : Set ℝᵈ}
    (h : AdmitsL2Damping Y c₁ c₂ c₃ α) (hc₁ : c₁ ≤ c₁') (hc₂ : 0 ≤ c₂') (hc₂le : c₂' ≤ c₂)
    (hc₃ : c₃' ≤ c₃) : AdmitsL2Damping Y c₁' c₂' c₃' α := by
  obtain ⟨ψ, hsupp, hnorm, hdecay, hYdecay⟩ := h
  refine ⟨ψ, ?_, ?_, hdecay, ?_⟩
  · exact hsupp.mono (fun ξ hξ hξ' =>
      hξ (fun hmem => hξ' (closedBall_subset_closedBall hc₁ hmem)))
  · exact le_trans (pow_le_pow_left₀ hc₂ hc₂le 2) hnorm
  · exact hYdecay.mono (fun x hx hxY => le_trans (hx hxY) (exp_decay_mono hc₃ x))

/-- `AdmitsL1Damping` is monotone: enlarging `c₁` and shrinking `c₂`, `c₃` makes the
condition easier. -/
lemma admitsL1Damping_mono {c₁ c₂ c₃ c₁' c₂' c₃' α : ℝ} {Y : Set ℝᵈ}
    (h : AdmitsL1Damping Y c₁ c₂ c₃ α) (hc₁ : c₁ ≤ c₁') (hc₂ : 0 ≤ c₂') (hc₂le : c₂' ≤ c₂)
    (hc₃ : c₃' ≤ c₃) : AdmitsL1Damping Y c₁' c₂' c₃' α := by
  obtain ⟨ψ, hsupp, hnorm, hdecay, hYdecay⟩ := h
  refine ⟨ψ, ?_, ?_, hdecay, ?_⟩
  · exact hsupp.mono (fun ξ hξ hξ' =>
      hξ (fun hmem => hξ' (cube_subset (by linarith : -c₁' ≤ -c₁) hc₁ hmem)))
  · exact le_trans (pow_le_pow_left₀ hc₂ hc₂le 2) hnorm
  · exact hYdecay.mono (fun x hx hxY => le_trans (hx hxY) (exp_decay_mono_l1 hc₃ x))

/-- Cohen's comparison between `ℓ₂`- and `ℓ₁`-damping functions: an `ℓ₂` damping function with
parameters `c₁, c₂, c₃, α` is an `ℓ₁` damping function with parameters `c₁, c₂, c₃/√d, α`.
(The `√d` loss comes from `|x|₁ ≤ √d |x|₂` and the elementary monotonicity of
`t ↦ t/(log(2+t))^α`.) -/
lemma admitsL1Damping_of_admitsL2Damping {c₁ c₂ c₃ α : ℝ} {Y : Set ℝᵈ}
    (h : AdmitsL2Damping Y c₁ c₂ c₃ α) (hd : 1 ≤ d) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hc₃ : 0 ≤ c₃) : AdmitsL1Damping Y c₁ c₂ (c₃ / Real.sqrt (d : ℝ)) α := by
  obtain ⟨ψ, hsupp, hnorm, hdecay, hYdecay⟩ := h
  refine ⟨ψ, ?_, ?_, hdecay, ?_⟩
  · exact hsupp.mono (fun ξ hξ hξ' => hξ (fun hmem => hξ' (closedBall_subset_cube hmem)))
  · -- `L²` norm: enlarge `ball 0 1` to the cube `[-1,1]^d`
    refine le_trans hnorm ?_
    have hf' : Integrable (fun x : ℝᵈ => ‖(ψ : ℝᵈ → ℂ) x‖ ^ (2 : ℝ)) volume :=
      (Lp.memLp ψ).integrable_norm_rpow (by norm_num) (by norm_num)
    have hf : Integrable (fun x : ℝᵈ => ‖(ψ : ℝᵈ → ℂ) x‖ ^ 2) volume := by
      simpa [Real.rpow_natCast] using hf'
    exact setIntegral_mono_set hf.integrableOn
      (Filter.Eventually.of_forall (fun x => by positivity))
      (Filter.Eventually.of_forall (fun x hx => ball_subset_cube hx))
  · -- decay on `Y`
    have hsqd : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < d))
    have hsqd1 : (1 : ℝ) ≤ Real.sqrt (d : ℝ) := by
      rw [← Real.sqrt_one]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hd)
    refine hYdecay.mono (fun x hx hxY => le_trans (hx hxY) (Real.exp_le_exp.mpr ?_))
    have hcx : 0 ≤ c₃ / Real.sqrt (d : ℝ) := div_nonneg hc₃ (le_of_lt hsqd)
    -- monotonicity of `g t = t / (log (2+t))^α`
    have hmon := Commons.Analysis.SpecialFunctions.monotoneOn_div_log_rpow α hα1
    have hg1 : l1norm x / (Real.log (2 + l1norm x)) ^ α
        ≤ (Real.sqrt (d : ℝ) * ‖x‖) / (Real.log (2 + Real.sqrt (d : ℝ) * ‖x‖)) ^ α :=
      hmon (show l1norm x ∈ Set.Ici (0 : ℝ) from l1norm_nonneg x)
        (show Real.sqrt (d : ℝ) * ‖x‖ ∈ Set.Ici (0 : ℝ) from mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg x))
        (l1norm_le_sqrt_mul x)
    have hlogmono : Real.log (2 + ‖x‖) ≤ Real.log (2 + Real.sqrt (d : ℝ) * ‖x‖) := by
      refine Real.log_le_log (by linarith [norm_nonneg x]) (by nlinarith [norm_nonneg x, hsqd1])
    have hpos1 : 0 < Real.log (2 + ‖x‖) :=
      Real.log_pos (by linarith [norm_nonneg x])
    have hden : (Real.log (2 + ‖x‖)) ^ α ≤ (Real.log (2 + Real.sqrt (d : ℝ) * ‖x‖)) ^ α :=
      Real.rpow_le_rpow (le_of_lt hpos1) hlogmono hα0
    have hg2 : (Real.sqrt (d : ℝ) * ‖x‖) / (Real.log (2 + Real.sqrt (d : ℝ) * ‖x‖)) ^ α
        ≤ Real.sqrt (d : ℝ) * (‖x‖ / (Real.log (2 + ‖x‖)) ^ α) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hpos1 α) hden
    have hmain : (c₃ / Real.sqrt (d : ℝ)) * (l1norm x / (Real.log (2 + l1norm x)) ^ α)
        ≤ c₃ * (‖x‖ / (Real.log (2 + ‖x‖)) ^ α) := by
      calc (c₃ / Real.sqrt (d : ℝ)) * (l1norm x / (Real.log (2 + l1norm x)) ^ α)
          ≤ (c₃ / Real.sqrt (d : ℝ)) *
              ((Real.sqrt (d : ℝ) * ‖x‖) /
                (Real.log (2 + Real.sqrt (d : ℝ) * ‖x‖)) ^ α) :=
            mul_le_mul_of_nonneg_left hg1 hcx
        _ ≤ (c₃ / Real.sqrt (d : ℝ)) *
              (Real.sqrt (d : ℝ) * (‖x‖ / (Real.log (2 + ‖x‖)) ^ α)) :=
            mul_le_mul_of_nonneg_left hg2 hcx
        _ = c₃ * (‖x‖ / (Real.log (2 + ‖x‖)) ^ α) := by
            field_simp
    have hgoal : c₃ / Real.sqrt (d : ℝ) * l1norm x / (Real.log (2 + l1norm x)) ^ α
        ≤ c₃ * ‖x‖ / (Real.log (2 + ‖x‖)) ^ α := by
      rw [mul_div_assoc, mul_div_assoc]
      exact hmain
    linarith [hgoal]

end Submission.FUP
