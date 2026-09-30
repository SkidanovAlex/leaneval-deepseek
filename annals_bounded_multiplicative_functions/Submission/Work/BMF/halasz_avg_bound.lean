import Mathlib
import Submission.Work.BMF.halasz_defs
import Submission.Work.BMF.halasz_basic
import Submission.Work.BMF.HL.sum_inv_p_log_p_le_const
import Submission.Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open scoped BigOperators
open Finset Real

/-- `t ↦ mHalSum f x t` is continuous: it is a finite sum of the continuous functions
`t ↦ (1 - Re(f p · p^{-it}))/p` (the exponent map `t ↦ -i t` is continuous and `p > 0`). -/
private lemma continuous_mHalSum (f : ℕ → ℂ) (x : ℝ) :
    Continuous (fun t : ℝ => mHalSum f x t) := by
  unfold mHalSum
  apply continuous_finsetSum
  intro p hp
  apply Continuous.div_const
  apply Continuous.sub continuous_const
  apply Complex.continuous_re.comp
  apply Continuous.mul continuous_const
  apply Continuous.const_cpow
  · fun_prop
  · left
    exact_mod_cast (Nat.prime_of_mem_primesLE hp).ne_zero

/-- **Minimum is at most the average.**  For `1`-bounded `f` and `T ≥ 1` the window
`|t| ≤ 2T` contains the whole interval `[0,1]`, so `mHal f x (2T) ≤ mHalSum f x t` there;
integrating in `t` over `[0,1]` (a set of length `1`) gives
`mHal f x (2T) ≤ ∫_0^1 mHalSum f x t dt`. -/
lemma mHal_le_integral_mHalSum (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) (x T : ℝ) (hT : 1 ≤ T) :
    mHal f x (2 * T) ≤ ∫ t in (0:ℝ)..1, mHalSum f x t := by
  have hbdd : BddBelow (Set.range (fun u : {u : ℝ // |u| ≤ 2 * T} => mHalSum f x u.1)) :=
    ⟨0, by rintro _ ⟨u, rfl⟩; exact mHalSum_nonneg hb x u.1⟩
  have hpt : ∀ t ∈ Set.Icc (0:ℝ) 1, mHal f x (2 * T) ≤ mHalSum f x t := by
    intro t ht
    rw [Set.mem_Icc] at ht
    refine ciInf_le hbdd ⟨t, ?_⟩
    rw [abs_of_nonneg ht.1]
    linarith [ht.2, hT]
  have hint : IntervalIntegrable (fun t : ℝ => mHalSum f x t) MeasureTheory.volume (0:ℝ) 1 :=
    (continuous_mHalSum f x).intervalIntegrable 0 1
  have hcint : IntervalIntegrable (fun _ : ℝ => mHal f x (2 * T)) MeasureTheory.volume (0:ℝ) 1 :=
    intervalIntegrable_const
  have h := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1) hcint hint hpt
  simpa using h

/-- `‖∫_0^1 p^{-it} dt‖ ≤ 2/log p` for a natural number `p ≥ 2`: the antiderivative of
`t ↦ p^{-it}` is `p^{-it}/(-i log p)` and `‖p^{-it}‖ = 1` on `[0,1]`. -/
private lemma norm_integral_cpow_le (p : ℕ) (hp2 : 2 ≤ p) :
    ‖∫ t in (0:ℝ)..1, (p:ℂ)^(-(Complex.I * (t:ℂ)))‖ ≤ 2 / Real.log p := by
  have hp0nat : 0 < p := by omega
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hp0nat
  have hp1 : (1:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hlogp : 0 < Real.log p := Real.log_pos hp1
  have hpne : ((p:ℂ)) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hL : Complex.log (p:ℂ) = ((Real.log p : ℝ) : ℂ) := Complex.natCast_log.symm
  have hLne : ((Real.log p : ℝ) : ℂ) * (-Complex.I) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · exact_mod_cast (ne_of_gt hlogp)
    · exact neg_ne_zero.mpr Complex.I_ne_zero
  have hderiv : ∀ t : ℝ, HasDerivAt (fun y : ℝ => (p:ℂ)^(-(Complex.I * (y:ℂ))))
      ((p:ℂ)^(-(Complex.I * (t:ℂ))) * (((Real.log p : ℝ) : ℂ) * (-Complex.I))) t := by
    intro t
    have hf : HasDerivAt (fun w : ℂ => -(Complex.I * w)) (-Complex.I) (t:ℂ) := by
      have h := (hasDerivAt_id (t:ℂ)).const_mul Complex.I
      convert h.neg using 1
      · funext w; simp
      · simp
    have hc := (hf.const_cpow (c := (p:ℂ)) (Or.inl hpne)).comp_ofReal
    rw [hL] at hc
    convert hc using 1
    ring
  have hF : ∀ t : ℝ, HasDerivAt
      (fun y : ℝ => (p:ℂ)^(-(Complex.I * (y:ℂ))) / (((Real.log p : ℝ) : ℂ) * (-Complex.I)))
      ((p:ℂ)^(-(Complex.I * (t:ℂ)))) t := by
    intro t
    have hd := (hderiv t).div_const (((Real.log p : ℝ) : ℂ) * (-Complex.I))
    convert hd using 1
    rw [mul_div_cancel_right₀ _ hLne]
  have hint : IntervalIntegrable (fun t : ℝ => (p:ℂ)^(-(Complex.I * (t:ℂ))))
      MeasureTheory.volume (0:ℝ) 1 := by
    apply Continuous.intervalIntegrable
    apply Continuous.const_cpow
    · fun_prop
    · exact Or.inl hpne
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun y : ℝ => (p:ℂ)^(-(Complex.I * (y:ℂ))) / (((Real.log p : ℝ) : ℂ) * (-Complex.I)))
      (fun x _ => hF x) hint
  rw [h]
  have hG1 : ‖(p:ℂ)^(-(Complex.I * ((1:ℝ):ℂ)))‖ = 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp0nat]; norm_num
  have hG0 : ‖(p:ℂ)^(-(Complex.I * ((0:ℝ):ℂ)))‖ = 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hp0nat]; norm_num
  have hden : ‖(((Real.log p : ℝ) : ℂ)) * (-Complex.I)‖ = Real.log p := by
    rw [norm_mul]
    rw [show ‖(((Real.log p : ℝ) : ℂ))‖ = |Real.log p| from RCLike.norm_ofReal (Real.log p)]
    rw [show ‖(-Complex.I : ℂ)‖ = 1 from by simp]
    rw [mul_one, abs_of_pos hlogp]
  have hsub : ‖(p:ℂ)^(-(Complex.I * ((1:ℝ):ℂ))) - (p:ℂ)^(-(Complex.I * ((0:ℝ):ℂ)))‖ ≤ 2 := by
    calc ‖(p:ℂ)^(-(Complex.I * ((1:ℝ):ℂ))) - (p:ℂ)^(-(Complex.I * ((0:ℝ):ℂ)))‖
        ≤ ‖(p:ℂ)^(-(Complex.I * ((1:ℝ):ℂ)))‖ + ‖(p:ℂ)^(-(Complex.I * ((0:ℝ):ℂ)))‖ := norm_sub_le _ _
      _ = 2 := by rw [hG1, hG0]; norm_num
  have hdiff : (p:ℂ)^(-(Complex.I * ((1:ℝ):ℂ))) / (((Real.log p : ℝ) : ℂ) * (-Complex.I))
      - (p:ℂ)^(-(Complex.I * ((0:ℝ):ℂ))) / (((Real.log p : ℝ) : ℂ) * (-Complex.I))
      = ((p:ℂ)^(-(Complex.I * ((1:ℝ):ℂ))) - (p:ℂ)^(-(Complex.I * ((0:ℝ):ℂ))))
        / (((Real.log p : ℝ) : ℂ) * (-Complex.I)) := by
    rw [div_sub_div_same]
  rw [hdiff, norm_div, hden]
  rw [div_le_div_iff_of_pos_right hlogp]
  exact hsub

/-- **Averaging over the frequency window.**  For `1`-bounded `f` and `x ≥ 2`,
`∫_0^1 mHalSum f x t dt ≤ Σ_{p ≤ x} 1/p + 2 Σ_{p ≤ x} 1/(p log p)`: interchange the finite sum
with the integral, use `∫_0^1 (1 - Re(f p · p^{-it})) dt = 1 - Re(f p · ∫_0^1 p^{-it} dt)` and
`norm_integral_cpow_le`, plus `Re z ≥ -‖z‖` and `‖f p‖ ≤ 1`. -/
private lemma mHalSum_integral_le_aux (f : ℕ → ℂ) (hb : ∀ n, ‖f n‖ ≤ 1) (x : ℝ) (_hx : 2 ≤ x) :
    (∫ t in (0:ℝ)..1, mHalSum f x t)
      ≤ Zrcp x + 2 * (∑ p ∈ (⌊x⌋₊).primesLE, (1:ℝ)/((p:ℝ) * Real.log p)) := by
  have hterm : ∀ p ∈ (⌊x⌋₊).primesLE,
      (∫ t in (0:ℝ)..1, (1 - (f p * (p:ℂ)^(-(Complex.I * (t:ℂ)))).re)/p)
      ≤ 1/(p:ℝ) + 2/((p:ℝ)*Real.log p) := by
    intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primesLE hp
    have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast hpprime.pos
    have hp2 : 2 ≤ p := hpprime.two_le
    have hp1 : (1:ℝ) < (p:ℝ) := by exact_mod_cast hpprime.one_lt
    have hlogp : 0 < Real.log p := Real.log_pos hp1
    have hpne : ((p:ℂ)) ≠ 0 := by exact_mod_cast hpprime.ne_zero
    have hJ := norm_integral_cpow_le p hp2
    have hGcont : Continuous (fun t : ℝ => (p:ℂ)^(-(Complex.I * (t:ℂ)))) := by
      apply Continuous.const_cpow
      · fun_prop
      · exact Or.inl hpne
    have hFGint : IntervalIntegrable (fun t : ℝ => f p * (p:ℂ)^(-(Complex.I * (t:ℂ))))
        MeasureTheory.volume (0:ℝ) 1 :=
      (hGcont.intervalIntegrable 0 1).const_mul (f p)
    have hreint : IntervalIntegrable (fun t : ℝ => (f p * (p:ℂ)^(-(Complex.I * (t:ℂ)))).re)
        MeasureTheory.volume (0:ℝ) 1 := by
      apply Continuous.intervalIntegrable
      exact Complex.continuous_re.comp (continuous_const.mul hGcont)
    have hre : (∫ t in (0:ℝ)..1, (f p * (p:ℂ)^(-(Complex.I * (t:ℂ)))).re)
        = (∫ t in (0:ℝ)..1, f p * (p:ℂ)^(-(Complex.I * (t:ℂ)))).re :=
      intervalIntegral.intervalIntegral_re hFGint
    have hmul : (∫ t in (0:ℝ)..1, f p * (p:ℂ)^(-(Complex.I * (t:ℂ))))
        = f p * ∫ t in (0:ℝ)..1, (p:ℂ)^(-(Complex.I * (t:ℂ))) :=
      intervalIntegral.integral_const_mul (f p) _
    have hcomp : (∫ t in (0:ℝ)..1, (1 - (f p * (p:ℂ)^(-(Complex.I * (t:ℂ)))).re)/p)
        = (1 - (f p * (∫ t in (0:ℝ)..1, (p:ℂ)^(-(Complex.I * (t:ℂ))))).re)/(p:ℝ) := by
      rw [intervalIntegral.integral_div]
      congr 1
      rw [intervalIntegral.integral_sub intervalIntegrable_const hreint, hre, hmul]
      norm_num
    rw [hcomp]
    have hbound : 1 - (f p * (∫ t in (0:ℝ)..1, (p:ℂ)^(-(Complex.I * (t:ℂ))))).re
        ≤ 1 + 2/Real.log p := by
      have h1 : -(f p * (∫ t in (0:ℝ)..1, (p:ℂ)^(-(Complex.I * (t:ℂ))))).re
          ≤ ‖f p * (∫ t in (0:ℝ)..1, (p:ℂ)^(-(Complex.I * (t:ℂ))))‖ := by
        calc -(f p * (∫ t in (0:ℝ)..1, (p:ℂ)^(-(Complex.I * (t:ℂ))))).re
            ≤ |(f p * (∫ t in (0:ℝ)..1, (p:ℂ)^(-(Complex.I * (t:ℂ))))).re| := neg_le_abs _
          _ ≤ ‖f p * (∫ t in (0:ℝ)..1, (p:ℂ)^(-(Complex.I * (t:ℂ))))‖ := Complex.abs_re_le_norm _
      have h2 : ‖f p * (∫ t in (0:ℝ)..1, (p:ℂ)^(-(Complex.I * (t:ℂ))))‖ ≤ 2/Real.log p := by
        rw [norm_mul]
        calc ‖f p‖ * ‖∫ t in (0:ℝ)..1, (p:ℂ)^(-(Complex.I * (t:ℂ)))‖
            ≤ 1 * (2/Real.log p) := mul_le_mul (hb p) hJ (norm_nonneg _) (by norm_num)
          _ = 2/Real.log p := by ring
      linarith
    calc (1 - (f p * ∫ t in (0:ℝ)..1, (p:ℂ)^(-(Complex.I * (t:ℂ)))).re)/↑p
        ≤ (1 + 2/Real.log p)/↑p := div_le_div_of_nonneg_right hbound hp0.le
      _ = 1/↑p + 2/(↑p * Real.log p) := by field_simp
  calc (∫ t in (0:ℝ)..1, mHalSum f x t)
      = ∑ p ∈ (⌊x⌋₊).primesLE,
          (∫ t in (0:ℝ)..1, (1 - (f p * (p:ℂ)^(-(Complex.I * (t:ℂ)))).re)/p) := by
        unfold mHalSum
        rw [intervalIntegral.integral_finsetSum]
        intro p hp
        have hpprime : p.Prime := Nat.prime_of_mem_primesLE hp
        apply Continuous.intervalIntegrable
        apply Continuous.div_const
        apply Continuous.sub continuous_const
        apply Complex.continuous_re.comp
        exact continuous_const.mul (Continuous.const_cpow (by fun_prop)
          (Or.inl (by exact_mod_cast hpprime.ne_zero)))
    _ ≤ ∑ p ∈ (⌊x⌋₊).primesLE, (1/(p:ℝ) + 2/((p:ℝ)*Real.log p)) := Finset.sum_le_sum hterm
    _ = Zrcp x + 2 * ∑ p ∈ (⌊x⌋₊).primesLE, 1/((p:ℝ)*Real.log p) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Zrcp]
        congr 1
        apply Finset.sum_congr rfl
        intro p hp
        rw [div_eq_mul_inv, one_div]

/-- Two related elementary estimates: `Σ_{p ≤ x} 1/(p log p) = O(1)`, and the **averaging bound**
`mHal f x (2T) ≤ log log x + O(1)` obtained by averaging `Σ_{p ≤ x} Re(f p · p^{-it})/p` over
`t ∈ [1,2]` (where `‖∫_1^2 p^{-it}dt‖ ≤ 2/log p`) together with Mertens' estimate for
`Σ_{p ≤ x} 1/p`. -/
theorem halasz_avg_bound :
    (∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
        (∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / ((p : ℝ) * Real.log p)) ≤ C) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (f : ℕ → ℂ), (∀ n, ‖f n‖ ≤ 1) → ∀ x T : ℝ, 3 ≤ x → 1 ≤ T →
        Work.BMF.mHal f x (2 * T) ≤ Real.log (Real.log x) + C) := by
  refine ⟨HL.sum_inv_p_log_p_le_const, ?_⟩
  obtain ⟨C₁, hC₁pos, hC₁⟩ := HL.sum_inv_p_log_p_le_const
  obtain ⟨CM, _hCMpos, hCM⟩ := Commons.NumberTheory.Mertens.primeRecips_sub_loglog_bound
  -- `CM` is a Mertens constant: `Σ_{p ≤ x} 1/p ≤ log log x + CM` for `x ≥ 11`.
  set C : ℝ := max (CM + 2 * C₁) (Zrcp 11 + 2 * C₁) with hC
  have hCpos : 0 < C := by
    rw [hC]; exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  refine ⟨C, hCpos, ?_⟩
  intro f hb x T hx hT
  have hx2 : 2 ≤ x := by linarith
  have hS : (∑ p ∈ (⌊x⌋₊).primesLE, (1 : ℝ) / ((p : ℝ) * Real.log p)) ≤ C₁ := hC₁ x hx2
  -- `Zrcp x + 2 Σ 1/(p log p) ≤ log log x + C`
  have hbound : Zrcp x + 2 * (∑ p ∈ (⌊x⌋₊).primesLE,
      (1 : ℝ) / ((p : ℝ) * Real.log p)) ≤ Real.log (Real.log x) + C := by
    by_cases hx11 : (11:ℝ) ≤ x
    · have h := (abs_le.mp (hCM x hx11)).2
      have hZX : Zrcp x = ∑ p ∈ (⌊x⌋₊).primesLE, (1:ℝ)/p := rfl
      have h' : Zrcp x ≤ Real.log (Real.log x) + CM := by rw [hZX]; linarith
      linarith [le_max_left (CM + 2 * C₁) (Zrcp 11 + 2 * C₁)]
    · have hx11' : x < 11 := lt_of_not_ge hx11
      have hmono : Zrcp x ≤ Zrcp 11 := Zrcp_mono hx11'.le
      have hlog3 : 1 < Real.log 3 := by
        have hexp : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
        have h := Real.log_lt_log (Real.exp_pos 1) hexp
        rwa [Real.log_exp] at h
      have hlogx1 : (1:ℝ) ≤ Real.log x :=
        le_trans hlog3.le (Real.log_le_log (by norm_num) (by linarith : (3:ℝ) ≤ x))
      have hll : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hlogx1
      linarith [le_max_right (CM + 2 * C₁) (Zrcp 11 + 2 * C₁)]
  calc mHal f x (2 * T) ≤ ∫ t in (0:ℝ)..1, mHalSum f x t :=
        mHal_le_integral_mHalSum f hb x T hT
    _ ≤ Zrcp x + 2 * (∑ p ∈ (⌊x⌋₊).primesLE,
          (1 : ℝ) / ((p : ℝ) * Real.log p)) := mHalSum_integral_le_aux f hb x hx2
    _ ≤ Real.log (Real.log x) + C := hbound

end Work.BMF
