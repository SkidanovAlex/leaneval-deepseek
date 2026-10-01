/-
# The `L52Hyp` input with the explicit constant `2` (Heath-Brown Lemma 3.1, window form)

`Work.LinnikAreas.DhRepel.l52Hyp_supply` supplies Heath-Brown's Lemma 3.1 in window form, but
only with an *existential* constant `c > 0`.  The consumer in `OtherCharRepel` needs the input
with the absolute constant `c = 2` fixed, so that downstream estimates can be stated with
numerical constants.

The constant `2` is exactly the one produced by the Hadamard partial-fraction route in
`Work.LinnikAreas.DhRepel.l52Hyp_supply`: its intermediate theorem
`Work.LinnikAreas.DhRepel.shape` bounds
`-Re (L'/L)(s) + winSum χ s δ` for a primitive character of level `N` by
`(1/2) log N + (log π)/2 + (log (2 + |Im s|) + 8)/2`.
Feeding this into the arithmetic of the region `1/(L log L) ≤ Re s - 1 ≤ log L / L`,
`|Im s| ≤ 10 L` (where `L = log q`) and using `q ≥ 10 ^ 6` gives `L52Hyp χ 2 ε δ`.
-/
import Mathlib
import Submission.Work.LinnikAreas.DhRepel.l52Hyp_supply

open Complex DirichletCharacter Metric Filter
open scoped Real Topology BigOperators
noncomputable section

set_option maxHeartbeats 4000000

namespace Work.LinnikAreas.OtherCharRepel

/-- **Heath-Brown Lemma 3.1 in window form, with the explicit constant `2`.**
There is a threshold `q₀` such that for every non-principal character `χ` modulo `q ≥ q₀`
(not necessarily primitive) and all `ε, δ ∈ (0,1)`, `L52Hyp χ 2 ε δ` holds. -/
theorem l52HypTwo : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor], χ ≠ 1 →
    ∀ {ε δ : ℝ}, 0 < ε → 0 < δ → δ < 1 → Commons.NumberTheory.Linnik.L52Hyp χ 2 ε δ := by
  refine ⟨10 ^ 6, ?_⟩
  intro q hq _inst χ _instc hχ ε δ hε hδ0 hδ1
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hχ' : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, h]
    exact DirichletCharacter.changeLevel_one χ.conductor_dvd_level
  have hprim : χ.primitiveCharacter.IsPrimitive := DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hNle : χ.conductor ≤ q := Nat.le_of_dvd hqpos χ.conductor_dvd_level
  -- size of `log q`
  have hq1e6 : (10 ^ 6 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlog10 : (2 : ℝ) < Real.log 10 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 10)]
    calc Real.exp 2 = (Real.exp 1)^2 := by rw [← Real.exp_nat_mul]; norm_num
      _ < 3^2 := by nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
      _ < 10 := by norm_num
  have hlogq : (12 : ℝ) ≤ Real.log (q : ℝ) := by
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 10 ^ 6) hq1e6
    have h2 : Real.log ((10:ℝ) ^ 6) = 6 * Real.log 10 := by
      rw [Real.log_pow]; norm_num
    have h3 : (12 : ℝ) ≤ 6 * Real.log 10 := by nlinarith [hlog10]
    rw [h2] at h; linarith
  have hlogqpos : (0 : ℝ) < Real.log (q : ℝ) := by linarith
  -- the region conditions
  have hloglogqpos : 0 < Real.log (Real.log (q : ℝ)) := by
    apply Real.log_pos; linarith
  have hden : 0 < Real.log (q : ℝ) * Real.log (Real.log (q : ℝ)) := mul_pos hlogqpos hloglogqpos
  intro s hs1 hs2 hs3
  have hs1' : 1 < s.re := by
    have : 0 < 1 / (Real.log (q : ℝ) * Real.log (Real.log (q : ℝ))) := by positivity
    linarith
  have hs15 : s.re ≤ 15 := by
    have hle : Real.log (Real.log (q : ℝ)) ≤ Real.log (q : ℝ) := by
      have := Real.log_le_sub_one_of_pos hlogqpos
      linarith
    have h1 : Real.log (Real.log (q : ℝ)) / Real.log (q : ℝ) ≤ 1 := by
      rw [div_le_one hlogqpos]; exact hle
    linarith
  have hshape := Work.LinnikAreas.DhRepel.shape χ.primitiveCharacter hχ' hprim hs1' hs15 hδ0 hδ1
  have hgoal : (-(logDeriv (DirichletCharacter.LFunction χ.primitiveCharacter) s).re) +
      (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ.primitiveCharacter)
          (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
        (if ‖(1:ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ then ((1/(s-u)).re) else 0))
      ≤ (2 + ε/4) * Real.log (q : ℝ) := by
    refine le_trans hshape ?_
    have hN1 : (1 : ℝ) ≤ (χ.conductor : ℝ) := by
      have := Nat.pos_of_ne_zero (NeZero.ne χ.conductor)
      exact_mod_cast this
    have hlogN : Real.log (χ.conductor : ℝ) ≤ Real.log (q : ℝ) :=
      Real.log_le_log (by linarith) (by exact_mod_cast hNle)
    have hpi : Real.log Real.pi / 2 ≤ 1 := by
      have h1 : Real.log Real.pi ≤ Real.log 4 := Real.log_le_log Real.pi_pos (le_of_lt Real.pi_lt_four)
      have h2 : Real.log (4:ℝ) = 2 * Real.log 2 := by
        rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
      have h3 : Real.log (2:ℝ) ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
      linarith
    have hlog12 : Real.log (12:ℝ) ≤ 4 := by
      have h1 : Real.log (12:ℝ) ≤ Real.log 16 := Real.log_le_log (by norm_num) (by norm_num)
      have h2 : Real.log (16:ℝ) = 4 * Real.log 2 := by
        rw [show (16:ℝ) = 2^4 by norm_num, Real.log_pow]; norm_num
      have h3 : Real.log (2:ℝ) ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
      linarith
    have hhalf : Real.log (Real.log (q:ℝ)) ≤ (1/2) * Real.log (q:ℝ) := by
      have h4 : (4:ℝ) ≤ Real.log (q:ℝ) := by linarith
      have hspos : 0 < Real.sqrt (Real.log (q:ℝ)) := Real.sqrt_pos.mpr hlogqpos
      have hsq2 : (2:ℝ) ≤ Real.sqrt (Real.log (q:ℝ)) := by
        rw [Real.le_sqrt (by norm_num) (by linarith)]
        linarith
      have hsq : (Real.sqrt (Real.log (q:ℝ)))^2 = Real.log (q:ℝ) :=
        Real.sq_sqrt (le_of_lt hlogqpos)
      have hlog_eq : Real.log (Real.log (q:ℝ)) = 2 * Real.log (Real.sqrt (Real.log (q:ℝ))) := by
        rw [Real.log_sqrt (le_of_lt hlogqpos)]; ring
      have hbound : Real.log (Real.sqrt (Real.log (q:ℝ))) ≤ Real.sqrt (Real.log (q:ℝ)) - 1 :=
        Real.log_le_sub_one_of_pos hspos
      rw [hlog_eq]
      nlinarith [hsq2, hsq, hbound]
    have h2t : Real.log (2 + |s.im|) ≤ Real.log 12 + Real.log (Real.log (q:ℝ)) := by
      have h1 : Real.log (2 + |s.im|) ≤ Real.log (2 + 10 * Real.log (q:ℝ)) := by
        apply Real.log_le_log (by positivity)
        linarith [abs_nonneg s.im, hs3]
      have h2 : Real.log (2 + 10 * Real.log (q:ℝ)) ≤ Real.log (12 * Real.log (q:ℝ)) := by
        apply Real.log_le_log (by positivity)
        linarith
      have h3 : Real.log (12 * Real.log (q:ℝ)) = Real.log 12 + Real.log (Real.log (q:ℝ)) :=
        Real.log_mul (by norm_num) (ne_of_gt hlogqpos)
      linarith
    have hA : (1/2) * Real.log (χ.conductor : ℝ) ≤ (1/2) * Real.log (q : ℝ) := by linarith
    have hB : (1/2) * (Real.log (2 + |s.im|) + 8) ≤
        (1/2) * (Real.log 12 + (1/2) * Real.log (q:ℝ) + 8) := by linarith
    have hC : (2:ℝ) * Real.log (q : ℝ) ≤ (2 + ε/4) * Real.log (q : ℝ) := by
      have := mul_le_mul_of_nonneg_right (by linarith : (2:ℝ) ≤ 2 + ε/4) (le_of_lt hlogqpos)
      linarith
    nlinarith [hA, hB, hC, hpi, hlog12, hlogq]
  simpa only [Complex.neg_re] using hgoal

end Work.LinnikAreas.OtherCharRepel
