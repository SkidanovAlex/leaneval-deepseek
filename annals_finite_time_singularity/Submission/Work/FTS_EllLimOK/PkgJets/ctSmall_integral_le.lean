import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.FTS_EllLimOK.PkgJets.CosTailDefs
import Submission.Work.FTS_EllLimOK.PkgJets.cw_integrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.PkgJets

open scoped Real Topology
open MeasureTheory Set

/-!
# The `cos`-weight integrand near `s = 0`: `∫_0^T sin(2s)^{-η}/cos(s)^4 ds ≤ 1600`

The integrand `ctF s = sin(2s)^{-η}/cos(s)^4` (`η = 99/100`) has a single integrable
singularity at `s = 0`.  On the quarter interval `[0, π/4]`:

* `cos s ≥ cos(π/4) = √2/2`, hence `1/cos(s)^4 ≤ 4`;
* Jordan's inequality `sin(2s) ≥ (4/π) s` (applied to `2s ∈ [0, π/2]`) gives, since the
  exponent `-η` is negative, `sin(2s)^{-η} ≤ (π/4)^η s^{-η}` (with `0^{-η} = 0` at `s = 0`).

So `ctF s ≤ 4 (π/4)^η s^{-η}`, and the primitive of `s^{-η}` is `s^{1-η}/(1-η) = 100 s^{1/100}`.
For `T ≤ π/4` this gives

`∫_0^T ctF ≤ 4 (π/4)^η · 100 (π/4)^{1/100} = 400 · (π/4) = 100π ≤ 1600`.

The integrability statement is inherited from `cw_integrable` (`ctF` is literally `cwG`).
-/

/-- Pointwise comparison on `[0, π/4]`: the `cos`-factor costs at most `4`, and Jordan's
inequality turns `sin(2x)^{-η}` into `(π/4)^η x^{-η}` (the case `x = 0` is `0 ≤ 0`). -/
private lemma ctF_le_aux (x : ℝ) (hx : x ∈ Set.Icc 0 (Real.pi / 4)) :
    ctF x ≤ 4 * ((Real.pi / 4) ^ (99 / 100 : ℝ) * x ^ (-(99 / 100 : ℝ))) := by
  rcases eq_or_lt_of_le hx.1 with h0 | h0
  · have hx0 : x = 0 := h0.symm
    subst hx0
    have hz : (0 : ℝ) ^ (-(99 / 100 : ℝ)) = 0 := Real.zero_rpow (by norm_num)
    simp [ctF, hz]
  · have hx4 : x ≤ Real.pi / 4 := hx.2
    -- Jordan's inequality for `2x ∈ [0, π/2]`.
    have h2x0 : 0 ≤ 2 * x := by linarith
    have h2x1 : 2 * x ≤ Real.pi / 2 := by linarith [Real.pi_pos]
    have hj : (4 / Real.pi) * x ≤ Real.sin (2 * x) := by
      have h := Real.mul_le_sin h2x0 h2x1
      rw [show 2 / Real.pi * (2 * x) = (4 / Real.pi) * x by ring] at h
      exact h
    have hpos4x : 0 < (4 / Real.pi) * x := by positivity
    -- `sin(2x)^{-η} ≤ (π/4)^η x^{-η}`.
    have key : (Real.sin (2 * x)) ^ (-(99 / 100 : ℝ)) ≤
        (Real.pi / 4) ^ (99 / 100 : ℝ) * x ^ (-(99 / 100 : ℝ)) := by
      have hkey := Real.rpow_le_rpow_of_nonpos hpos4x hj (show (-(99 / 100 : ℝ)) ≤ 0 by norm_num)
      have hcoef : (4 / Real.pi) ^ (-(99 / 100 : ℝ)) = (Real.pi / 4) ^ (99 / 100 : ℝ) := by
        rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 4 / Real.pi),
          ← Real.inv_rpow (by positivity : (0 : ℝ) ≤ 4 / Real.pi) (99 / 100 : ℝ), inv_div]
      have hmr : ((4 / Real.pi) * x) ^ (-(99 / 100 : ℝ)) =
          (Real.pi / 4) ^ (99 / 100 : ℝ) * x ^ (-(99 / 100 : ℝ)) := by
        rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 4 / Real.pi) h0.le, hcoef]
      rwa [hmr] at hkey
    -- `1/cos(x)^4 ≤ 4`.
    have hcospos : 0 < Real.cos x :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [hx4, Real.pi_pos]⟩
    have hcos45nn : 0 ≤ Real.cos (Real.pi / 4) := by rw [Real.cos_pi_div_four]; positivity
    have hcos_le : Real.cos (Real.pi / 4) ≤ Real.cos x :=
      Real.cos_le_cos_of_nonneg_of_le_pi hx.1 (by linarith [Real.pi_pos]) hx4
    have hquarter : (1 : ℝ) / 4 ≤ (Real.cos x) ^ (4 : ℕ) := by
      have hsqrt2 : (Real.sqrt 2) ^ (4 : ℕ) = 4 := by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt (by norm_num)]
        norm_num
      have hval : (Real.sqrt 2 / 2) ^ (4 : ℕ) = 1 / 4 := by
        rw [div_pow, hsqrt2]
        norm_num
      calc (1 : ℝ) / 4 = (Real.cos (Real.pi / 4)) ^ (4 : ℕ) := by
            rw [Real.cos_pi_div_four, hval]
        _ ≤ (Real.cos x) ^ (4 : ℕ) := pow_le_pow_left₀ hcos45nn hcos_le 4
    have hinv : ((Real.cos x) ^ (4 : ℕ))⁻¹ ≤ 4 := by
      have h := one_div_le_one_div_of_le (show (0 : ℝ) < 1 / 4 by norm_num) hquarter
      rw [show (1 : ℝ) / (1 / 4) = 4 by norm_num] at h
      rw [one_div] at h
      exact h
    have hcinv : 0 ≤ ((Real.cos x) ^ (4 : ℕ))⁻¹ := by positivity
    rw [ctF, div_eq_mul_inv]
    calc (Real.sin (2 * x)) ^ (-(99 / 100 : ℝ)) * ((Real.cos x) ^ (4 : ℕ))⁻¹
        ≤ ((Real.pi / 4) ^ (99 / 100 : ℝ) * x ^ (-(99 / 100 : ℝ))) * 4 :=
          mul_le_mul key hinv hcinv
            (mul_nonneg (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ Real.pi / 4) _)
              (Real.rpow_nonneg h0.le _))
      _ = 4 * ((Real.pi / 4) ^ (99 / 100 : ℝ) * x ^ (-(99 / 100 : ℝ))) := by ring

/-- `∫_0^T s^{-η} ds = 100 T^{1/100}` for `T ≥ 0` (`η = 99/100`). -/
private lemma integral_rpow_neg_eta_aux (T : ℝ) (_hT : 0 ≤ T) :
    (∫ s in (0 : ℝ)..T, s ^ (-(99 / 100 : ℝ))) = 100 * T ^ (1 / 100 : ℝ) := by
  rw [integral_rpow (r := -(99 / 100 : ℝ))
    (Or.inl (by norm_num : (-1 : ℝ) < -(99 / 100)))]
  rw [Real.zero_rpow (by norm_num : (-(99 / 100 : ℝ) + 1) ≠ 0)]
  rw [show -(99 / 100 : ℝ) + 1 = 1 / 100 by norm_num]
  rw [sub_zero, div_eq_mul_inv, show ((1 : ℝ) / 100)⁻¹ = 100 by norm_num]
  ring

theorem ctSmall_integral_le :
    IntervalIntegrable ctF MeasureTheory.volume (0 : ℝ) (Real.pi / 4) ∧
      (∀ T : ℝ, T ∈ Set.Ioc 0 (Real.pi / 4) →
        (∫ s in (0 : ℝ)..T, ctF s) ≤ 1600) := by
  have hπ4pos : (0 : ℝ) < Real.pi / 4 := by linarith [Real.pi_pos]
  have hπ4lt : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hInt : IntegrableOn ctF (Set.Ioc 0 (Real.pi / 4)) MeasureTheory.volume :=
    cwG_integrableOn (θ := Real.pi / 4) ⟨hπ4pos, hπ4lt⟩
  refine ⟨?_, ?_⟩
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hπ4pos.le]
    exact hInt
  · intro T hT
    have hT0 : (0 : ℝ) < T := hT.1
    have hTle : T ≤ Real.pi / 4 := hT.2
    have hTpi2 : T < Real.pi / 2 := by linarith [Real.pi_pos]
    have hfi : IntervalIntegrable ctF MeasureTheory.volume (0 : ℝ) T := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT0.le]
      exact cwG_integrableOn ⟨hT0, hTpi2⟩
    set A : ℝ := (Real.pi / 4) ^ (99 / 100 : ℝ) with hA
    have hpowint : IntervalIntegrable (fun s : ℝ => s ^ (-(99 / 100 : ℝ)))
        MeasureTheory.volume (0 : ℝ) T :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < -(99 / 100))
    have h1 : IntervalIntegrable (fun s : ℝ => A * s ^ (-(99 / 100 : ℝ)))
        MeasureTheory.volume (0 : ℝ) T := hpowint.const_mul A
    have hgi : IntervalIntegrable (fun s : ℝ => 4 * (A * s ^ (-(99 / 100 : ℝ))))
        MeasureTheory.volume (0 : ℝ) T := h1.const_mul 4
    have hmono : (∫ s in (0 : ℝ)..T, ctF s) ≤
        ∫ s in (0 : ℝ)..T, 4 * (A * s ^ (-(99 / 100 : ℝ))) :=
      intervalIntegral.integral_mono_on hT0.le hfi hgi
        (fun x hx => by
          have h := ctF_le_aux x ⟨hx.1, le_trans hx.2 hTle⟩
          simpa [hA] using h)
    have houter : (∫ s in (0 : ℝ)..T, 4 * (A * s ^ (-(99 / 100 : ℝ)))) =
        4 * ∫ s in (0 : ℝ)..T, A * s ^ (-(99 / 100 : ℝ)) :=
      intervalIntegral.integral_const_mul 4 (fun s : ℝ => A * s ^ (-(99 / 100 : ℝ)))
    have hinner : (∫ s in (0 : ℝ)..T, A * s ^ (-(99 / 100 : ℝ))) =
        A * ∫ s in (0 : ℝ)..T, s ^ (-(99 / 100 : ℝ)) :=
      intervalIntegral.integral_const_mul A (fun s : ℝ => s ^ (-(99 / 100 : ℝ)))
    have hval : (∫ s in (0 : ℝ)..T, 4 * (A * s ^ (-(99 / 100 : ℝ)))) =
        4 * (A * (100 * T ^ (1 / 100 : ℝ))) := by
      rw [houter, hinner, integral_rpow_neg_eta_aux T hT0.le]
    rw [hval] at hmono
    have hpow : T ^ (1 / 100 : ℝ) ≤ (Real.pi / 4) ^ (1 / 100 : ℝ) :=
      Real.rpow_le_rpow hT0.le hTle (by norm_num)
    have hAmul : A * T ^ (1 / 100 : ℝ) ≤ Real.pi / 4 := by
      rw [hA]
      calc (Real.pi / 4) ^ (99 / 100 : ℝ) * T ^ (1 / 100 : ℝ)
          ≤ (Real.pi / 4) ^ (99 / 100 : ℝ) * (Real.pi / 4) ^ (1 / 100 : ℝ) :=
            mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (by positivity) _)
        _ = Real.pi / 4 := by
            rw [← Real.rpow_add (by positivity : (0 : ℝ) < Real.pi / 4),
              show (99 / 100 : ℝ) + 1 / 100 = 1 by norm_num, Real.rpow_one]
    have hfin : 4 * (A * (100 * T ^ (1 / 100 : ℝ))) ≤ 1600 := by
      have hA100 : A * (100 * T ^ (1 / 100 : ℝ)) ≤ 100 * (Real.pi / 4) := by
        nlinarith [hAmul]
      nlinarith [hA100, Real.pi_lt_four, Real.pi_pos]
    linarith

end Work.FTS_EllLimOK.PkgJets
