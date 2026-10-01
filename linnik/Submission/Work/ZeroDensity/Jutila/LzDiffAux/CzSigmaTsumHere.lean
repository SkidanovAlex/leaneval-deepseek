import Mathlib
import Submission.Work.ZeroDensity.Jutila.Bz3Defs
import Submission.Work.ZeroDensity.Jutila.sumInvSqrtBound
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.SumDivisorsIccSwap
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.MuAbsDivKapLeOne
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.SumInvSqrtMulInvLe
import Submission.Work.ZeroDensity.Jutila.LzDiffAux.ExpNegSqrtLogFloorCmp

namespace Work.ZeroDensity.Jutila.LzDiffAux

open Finset

/-!
## The elementary analytic input

`∑_{t ≤ T} exp (−c √(log (a t))) ≤ K(c) · T · exp (−c √(log (a T)))` for `a ≥ 1`, `T ≥ 1`.

The mechanism: for `t ≤ T`,
`√(log (aT)) − √(log (a t)) = w / (√log (aT) + √log (a t)) ≤ w / √log (aT)`
with `w = log (T/t)`, so the ratio of the `t`-term to the `T`-term is at most
`exp (w · c / √log (aT))`; when `log (aT) ≥ 4c²` this is at most `exp (w/2) = √(T/t)`, and
`∑_{t ≤ T} √(T/t) ≤ √T · 2√T = 2T`.  When `log (aT) < 4c²` the trivial bound `T · exp(−c√log a)`
suffices, because then `√(log (aT)) − √(log a) ≤ √(log T) ≤ 2c`.
-/

/-- `√u - √v ≤ √(u - v)` for `0 ≤ v ≤ u`. -/
lemma sqrt_sub_sqrt_le_sqrt_sub {u v : ℝ} (hv : 0 ≤ v) (hvu : v ≤ u) :
    Real.sqrt u - Real.sqrt v ≤ Real.sqrt (u - v) := by
  have h1 : Real.sqrt v ≤ Real.sqrt u := Real.sqrt_le_sqrt hvu
  have h2 : (0 : ℝ) ≤ Real.sqrt u - Real.sqrt v := sub_nonneg.mpr h1
  have h3 : (Real.sqrt u - Real.sqrt v) ^ 2 ≤ u - v := by
    have hu' := Real.sq_sqrt (le_trans hv hvu)
    have hv' := Real.sq_sqrt hv
    nlinarith [Real.sqrt_nonneg u, Real.sqrt_nonneg v]
  calc Real.sqrt u - Real.sqrt v = Real.sqrt ((Real.sqrt u - Real.sqrt v) ^ 2) :=
        (Real.sqrt_sq h2).symm
    _ ≤ Real.sqrt (u - v) := Real.sqrt_le_sqrt h3

/-- `√u - √v ≤ (u - v)/√u` for `0 ≤ v ≤ u` and `0 < u`. -/
lemma sqrt_sub_sqrt_le_div {u v : ℝ} (hv : 0 ≤ v) (hvu : v ≤ u) (hu : 0 < u) :
    Real.sqrt u - Real.sqrt v ≤ (u - v) / Real.sqrt u := by
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have hkey : (Real.sqrt u - Real.sqrt v) * (Real.sqrt u + Real.sqrt v) = u - v := by
    have hu' := Real.sq_sqrt hu.le
    have hv' := Real.sq_sqrt hv
    nlinarith [Real.sqrt_nonneg u, Real.sqrt_nonneg v]
  have h2 : (0 : ℝ) ≤ Real.sqrt u - Real.sqrt v := sub_nonneg.mpr (Real.sqrt_le_sqrt hvu)
  calc Real.sqrt u - Real.sqrt v
      = (Real.sqrt u - Real.sqrt v) * 1 := by ring
    _ ≤ (Real.sqrt u - Real.sqrt v) * ((Real.sqrt u + Real.sqrt v) / Real.sqrt u) := by
        apply mul_le_mul_of_nonneg_left _ h2
        rw [le_div_iff₀ hsu]
        linarith [Real.sqrt_nonneg v]
    _ = (u - v) / Real.sqrt u := by rw [← hkey]; ring

/-- `exp (log x / 2) = √x` for `x > 0`. -/
lemma exp_half_log_eq_sqrt (x : ℝ) (hx : 0 < x) :
    Real.exp (Real.log x / 2) = Real.sqrt x := by
  have h : Real.exp (Real.log x / 2) ^ 2 = x := by
    rw [sq, ← Real.exp_add, show Real.log x / 2 + Real.log x / 2 = Real.log x by ring,
      Real.exp_log hx]
  exact ((Real.sqrt_eq_iff_eq_sq (le_of_lt hx) (Real.exp_nonneg _)).mpr h.symm).symm

/-- `∑_{t ≤ T} √(T/t) ≤ 2T`. -/
lemma sum_sqrt_div_le_two_mul (T : ℕ) :
    (∑ t ∈ Finset.Icc 1 T, Real.sqrt ((T : ℝ) / (t : ℝ))) ≤ 2 * (T : ℝ) := by
  have hIoc : Finset.Ioc 0 T = Finset.Icc 1 T := by
    ext x; simp [Finset.mem_Ioc, Finset.mem_Icc]; omega
  have h : (∑ t ∈ Finset.Icc 1 T, Real.sqrt ((T : ℝ) / (t : ℝ)))
      = Real.sqrt (T : ℝ) * (∑ t ∈ Finset.Icc 1 T, 1 / Real.sqrt (t : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.mem_Icc] at ht
    have ht0 : (0 : ℝ) < (t : ℝ) := by
      have : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht.1
      linarith
    rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ (T : ℝ)) (t : ℝ)]
    ring
  rw [h]
  calc Real.sqrt (T : ℝ) * (∑ t ∈ Finset.Icc 1 T, 1 / Real.sqrt (t : ℝ))
      ≤ Real.sqrt (T : ℝ) * (2 * Real.sqrt (T : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        rw [← hIoc]
        exact Work.ZeroDensity.Jutila.sumInvSqrtBound T
    _ = 2 * (T : ℝ) := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (T : ℝ) by positivity),
          Real.sqrt_nonneg (T : ℝ)]

/-- **The decay sum.** For `c > 0` there is `K > 0` such that for every `a ≥ 1` and `T ≥ 1`,
`∑_{t ≤ T} exp (−c √(log (a t))) ≤ K · T · exp (−c √(log (a T)))`. -/
theorem DecaySumLe (c : ℝ) (hc : 0 < c) :
    ∃ K : ℝ, 0 < K ∧ ∀ (a : ℝ) (T : ℕ), 1 ≤ a → 1 ≤ T →
      (∑ t ∈ Finset.Icc 1 T, Real.exp (-(c * Real.sqrt (Real.log (a * (t : ℝ))))))
        ≤ K * (T : ℝ) * Real.exp (-(c * Real.sqrt (Real.log (a * (T : ℝ))))) := by
  refine ⟨max 2 (Real.exp (2 * c ^ 2)), by positivity, ?_⟩
  intro a T ha hT
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have ha1 : (1 : ℝ) ≤ a := ha
  have hT0 : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hT1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  set U : ℝ := Real.log (a * (T : ℝ)) with hU
  have hU0 : 0 ≤ U := Real.log_nonneg (by nlinarith)
  by_cases hcase : 4 * c ^ 2 ≤ U
  · -- **Case 1**: `4c² ≤ log (aT)`.
    have hUpos : 0 < U := by nlinarith [sq_nonneg c]
    have hUeq : U = Real.log (a * (T : ℝ)) := hU
    have hper : ∀ t ∈ Finset.Icc 1 T,
        Real.exp (-(c * Real.sqrt (Real.log (a * (t : ℝ)))))
          ≤ Real.exp (-(c * Real.sqrt U)) * Real.sqrt ((T : ℝ) / (t : ℝ)) := by
      intro t ht
      rw [Finset.mem_Icc] at ht
      obtain ⟨ht1, htT⟩ := ht
      have ht1' : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht1
      have htT' : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast htT
      have ht0 : (0 : ℝ) < (t : ℝ) := by linarith
      set w : ℝ := Real.log ((T : ℝ) / (t : ℝ)) with hw
      have hw0 : 0 ≤ w := by
        rw [hw]
        exact Real.log_nonneg (by rw [le_div_iff₀ ht0]; linarith)
      have hlogt : Real.log (a * (t : ℝ)) = U - w := by
        rw [hUeq, hw, Real.log_mul ha0.ne' ht0.ne', Real.log_mul ha0.ne' hT0.ne',
          Real.log_div hT0.ne' ht0.ne']
        ring
      have hlog0 : 0 ≤ Real.log (a * (t : ℝ)) := Real.log_nonneg (by nlinarith)
      have hUW0 : 0 ≤ U - w := by rw [← hlogt]; exact hlog0
      -- the exponent difference
      have hdiff : Real.sqrt U - Real.sqrt (U - w) ≤ w / Real.sqrt U := by
        have := sqrt_sub_sqrt_le_div hUW0 (by linarith) hUpos
        convert this using 2
        ring
      have hcU : c / Real.sqrt U ≤ 1 / 2 := by
        rw [div_le_iff₀ (Real.sqrt_pos.mpr hUpos)]
        have h2c : 2 * c ≤ Real.sqrt U := by
          calc 2 * c = Real.sqrt ((2 * c) ^ 2) := (Real.sqrt_sq (by positivity)).symm
            _ ≤ Real.sqrt U := Real.sqrt_le_sqrt (by nlinarith [hcase])
        linarith
      have hstep : c * (Real.sqrt U - Real.sqrt (U - w)) ≤ w / 2 := by
        calc c * (Real.sqrt U - Real.sqrt (U - w)) ≤ c * (w / Real.sqrt U) :=
              mul_le_mul_of_nonneg_left hdiff hc.le
          _ = w * (c / Real.sqrt U) := by ring
          _ ≤ w * (1 / 2) := mul_le_mul_of_nonneg_left hcU hw0
          _ = w / 2 := by ring
      rw [hlogt,
        show -(c * Real.sqrt (U - w)) = -(c * Real.sqrt U) + c * (Real.sqrt U - Real.sqrt (U - w))
          by ring,
        Real.exp_add]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      calc Real.exp (c * (Real.sqrt U - Real.sqrt (U - w)))
          ≤ Real.exp (w / 2) := Real.exp_le_exp.mpr hstep
        _ = Real.sqrt ((T : ℝ) / (t : ℝ)) := by
            rw [hw]
            exact exp_half_log_eq_sqrt _ (by positivity)
    have hsum : (∑ t ∈ Finset.Icc 1 T, Real.exp (-(c * Real.sqrt (Real.log (a * (t : ℝ))))))
        ≤ 2 * (T : ℝ) * Real.exp (-(c * Real.sqrt U)) := by
      calc (∑ t ∈ Finset.Icc 1 T, Real.exp (-(c * Real.sqrt (Real.log (a * (t : ℝ))))))
          ≤ ∑ t ∈ Finset.Icc 1 T, Real.exp (-(c * Real.sqrt U)) * Real.sqrt ((T : ℝ) / (t : ℝ)) :=
            Finset.sum_le_sum hper
        _ = Real.exp (-(c * Real.sqrt U)) * (∑ t ∈ Finset.Icc 1 T, Real.sqrt ((T : ℝ) / (t : ℝ))) := by
            rw [Finset.mul_sum]
        _ ≤ Real.exp (-(c * Real.sqrt U)) * (2 * (T : ℝ)) :=
            mul_le_mul_of_nonneg_left (sum_sqrt_div_le_two_mul T) (Real.exp_nonneg _)
        _ = 2 * (T : ℝ) * Real.exp (-(c * Real.sqrt U)) := by ring
    calc (∑ t ∈ Finset.Icc 1 T, Real.exp (-(c * Real.sqrt (Real.log (a * (t : ℝ))))))
        ≤ 2 * (T : ℝ) * Real.exp (-(c * Real.sqrt U)) := hsum
      _ ≤ max 2 (Real.exp (2 * c ^ 2)) * (T : ℝ) * Real.exp (-(c * Real.sqrt U)) := by
          have h2K : (2 : ℝ) ≤ max 2 (Real.exp (2 * c ^ 2)) := le_max_left _ _
          have hTnn : (0 : ℝ) ≤ (T : ℝ) := le_of_lt hT0
          have hexp : (0 : ℝ) ≤ Real.exp (-(c * Real.sqrt U)) := Real.exp_nonneg _
          nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2K hTnn) hexp]
      _ = max 2 (Real.exp (2 * c ^ 2)) * (T : ℝ)
            * Real.exp (-(c * Real.sqrt (Real.log (a * (T : ℝ))))) := by rw [hUeq]
  · -- **Case 2**: `log (aT) < 4c²`.
    have hKpos : (0 : ℝ) < max 2 (Real.exp (2 * c ^ 2)) := by positivity
    have hlogT0 : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg hT1
    have hlogTlt : Real.log (T : ℝ) < 4 * c ^ 2 := by
      have : Real.log (T : ℝ) ≤ U := by
        rw [hU, Real.log_mul ha0.ne' hT0.ne']; linarith [Real.log_nonneg ha1]
      linarith
    have hcmp : Real.exp (-(c * Real.sqrt (Real.log a)))
        ≤ max 2 (Real.exp (2 * c ^ 2)) * Real.exp (-(c * Real.sqrt U)) := by
      have hla0 : 0 ≤ Real.log a := Real.log_nonneg ha1
      have hlaU : Real.log a ≤ U := by
        rw [hU, Real.log_mul ha0.ne' hT0.ne']; linarith [hlogT0]
      have hdiff : Real.sqrt U - Real.sqrt (Real.log a) ≤ Real.sqrt (U - Real.log a) :=
        sqrt_sub_sqrt_le_sqrt_sub hla0 hlaU
      have hUloga : U - Real.log a = Real.log (T : ℝ) := by
        rw [hU, Real.log_mul ha0.ne' hT0.ne']; ring
      have hsT : Real.sqrt (U - Real.log a) ≤ 2 * c := by
        rw [hUloga]
        calc Real.sqrt (Real.log (T : ℝ)) ≤ Real.sqrt ((2 * c) ^ 2) :=
              Real.sqrt_le_sqrt (by rw [show (2 * c) ^ 2 = 4 * c ^ 2 by ring]; exact hlogTlt.le)
          _ = 2 * c := Real.sqrt_sq (by positivity)
      have hc2 : c * (Real.sqrt U - Real.sqrt (Real.log a)) ≤ 2 * c ^ 2 := by
        calc c * (Real.sqrt U - Real.sqrt (Real.log a))
            ≤ c * Real.sqrt (U - Real.log a) := mul_le_mul_of_nonneg_left hdiff hc.le
          _ ≤ c * (2 * c) := mul_le_mul_of_nonneg_left hsT hc.le
          _ = 2 * c ^ 2 := by ring
      have hmain : Real.exp (c * (Real.sqrt U - Real.sqrt (Real.log a)))
          ≤ max 2 (Real.exp (2 * c ^ 2)) :=
        (Real.exp_le_exp.mpr hc2).trans (le_max_right _ _)
      rw [show -(c * Real.sqrt (Real.log a))
            = -(c * Real.sqrt U) + c * (Real.sqrt U - Real.sqrt (Real.log a)) by ring,
        Real.exp_add]
      calc Real.exp (-(c * Real.sqrt U)) * Real.exp (c * (Real.sqrt U - Real.sqrt (Real.log a)))
          ≤ Real.exp (-(c * Real.sqrt U)) * max 2 (Real.exp (2 * c ^ 2)) :=
            mul_le_mul_of_nonneg_left hmain (Real.exp_nonneg _)
        _ = max 2 (Real.exp (2 * c ^ 2)) * Real.exp (-(c * Real.sqrt U)) := by ring
    have hper2 : ∀ t ∈ Finset.Icc 1 T,
        Real.exp (-(c * Real.sqrt (Real.log (a * (t : ℝ)))))
          ≤ Real.exp (-(c * Real.sqrt (Real.log a))) := by
      intro t ht
      rw [Finset.mem_Icc] at ht
      apply Real.exp_le_exp.mpr
      have ht0 : (0 : ℝ) < (t : ℝ) := by
        have : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht.1
        linarith
      have hle : Real.log a ≤ Real.log (a * (t : ℝ)) := by
        rw [Real.log_mul ha0.ne' ht0.ne']
        linarith [Real.log_nonneg (by exact_mod_cast ht.1 : (1 : ℝ) ≤ (t : ℝ))]
      have := Real.sqrt_le_sqrt hle
      nlinarith [hc.le]
    calc (∑ t ∈ Finset.Icc 1 T, Real.exp (-(c * Real.sqrt (Real.log (a * (t : ℝ))))))
        ≤ ∑ t ∈ Finset.Icc 1 T, Real.exp (-(c * Real.sqrt (Real.log a))) :=
          Finset.sum_le_sum hper2
      _ = (T : ℝ) * Real.exp (-(c * Real.sqrt (Real.log a))) := by
          rw [Finset.sum_const, Nat.card_Icc, show T + 1 - 1 = T from by omega, nsmul_eq_mul]
      _ ≤ (T : ℝ) * (max 2 (Real.exp (2 * c ^ 2)) * Real.exp (-(c * Real.sqrt U))) :=
          mul_le_mul_of_nonneg_left hcmp hT0.le
      _ = max 2 (Real.exp (2 * c ^ 2)) * (T : ℝ)
            * Real.exp (-(c * Real.sqrt (Real.log (a * (T : ℝ))))) := by rw [hU]; ring

/-- **The `σ_{-1/2}`-weighted `t`-sum against the decaying envelope.**

For `c > 0` there is `C = C(c)` with, for all `a ≥ 1` and `T ≥ 1`,
`Σ_{t ≤ T} |μ(t)|·(t/κ(t))·σ(t)·exp(−c√log(a t)) ≤ C·T·exp(−c√log(a T))`,
where `σ(t) = Σ_{d | t} d^{-1/2}` and `κ(t) = kap t = ∏_{p | t}(p+1)`.

The point of the weight is that `|μ(t)|·(t/κ(t)) ≤ 1` and `Σ_{t ≤ T} Σ_{d | t} d^{-1/2} ≤ 3T`
(with `t = d·m`): the divisor sum is exchanged with the summation over `t`, and the inner sum is
`≪ (T/d)·exp(−c√log(a·d·⌊T/d⌋)) ≪ (T/d)·exp(−c√log(aT))` by `DecaySumLe`; the remaining sum
`Σ_d d^{-3/2}` is bounded by `3`. -/
theorem CzSigmaTsumHere (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℝ) (T : ℕ), 1 ≤ a → 1 ≤ T →
      (∑ t ∈ Finset.Icc 1 T,
        |((ArithmeticFunction.moebius t : ℤ) : ℝ)| * ((t : ℝ) / Work.ZeroDensity.Jutila.kap t) *
          (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ)) *
            Real.exp (-(c * Real.sqrt (Real.log (a * (t : ℝ))))))
      ≤ C * (T : ℝ) * Real.exp (-(c * Real.sqrt (Real.log (a * (T : ℝ))))) := by
  obtain ⟨K, hKpos, hK⟩ := DecaySumLe c hc
  refine ⟨3 * K * Real.exp c, by positivity, ?_⟩
  intro a T ha hT
  set F : ℝ := Real.exp (-(c * Real.sqrt (Real.log (a * (T : ℝ))))) with hF
  have hFnn : 0 ≤ F := by rw [hF]; positivity
  -- Step 1: the pointwise weight `|μ(t)|·(t/κ(t))` is at most `1`, so the summand is dominated
  -- by `σ(t)·exp(−c√log(a t))`.
  have hstep1 : (∑ t ∈ Finset.Icc 1 T,
        |((ArithmeticFunction.moebius t : ℤ) : ℝ)| * ((t : ℝ) / Work.ZeroDensity.Jutila.kap t) *
          (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ)) *
            Real.exp (-(c * Real.sqrt (Real.log (a * (t : ℝ))))))
      ≤ ∑ t ∈ Finset.Icc 1 T, ∑ d ∈ t.divisors,
          (1 / Real.sqrt (d : ℝ)) * Real.exp (-(c * Real.sqrt (Real.log (a * (t : ℝ))))) := by
    apply Finset.sum_le_sum
    intro t ht
    have hS : (0 : ℝ) ≤ ∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ) :=
      Finset.sum_nonneg fun d _ => by positivity
    have hE : (0 : ℝ) ≤ Real.exp (-(c * Real.sqrt (Real.log (a * (t : ℝ))))) :=
      Real.exp_nonneg _
    have h1 := MuAbsDivKapLeOne t
    calc |((ArithmeticFunction.moebius t : ℤ) : ℝ)| *
            ((t : ℝ) / Work.ZeroDensity.Jutila.kap t) *
            (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ)) *
            Real.exp (-(c * Real.sqrt (Real.log (a * (t : ℝ)))))
        = (|((ArithmeticFunction.moebius t : ℤ) : ℝ)| *
              ((t : ℝ) / Work.ZeroDensity.Jutila.kap t)) *
            ((∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ)) *
              Real.exp (-(c * Real.sqrt (Real.log (a * (t : ℝ)))))) := by ring
      _ ≤ 1 * ((∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ)) *
              Real.exp (-(c * Real.sqrt (Real.log (a * (t : ℝ)))))) :=
            mul_le_mul_of_nonneg_right h1 (mul_nonneg hS hE)
      _ = (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ)) *
              Real.exp (-(c * Real.sqrt (Real.log (a * (t : ℝ))))) := by ring
      _ = ∑ d ∈ t.divisors,
            (1 / Real.sqrt (d : ℝ)) *
              Real.exp (-(c * Real.sqrt (Real.log (a * (t : ℝ))))) := by
            rw [Finset.sum_mul]
  -- Step 2: exchange the summation over `t` with the divisor sum, `t = d·m`.
  have hstep2 : (∑ t ∈ Finset.Icc 1 T, ∑ d ∈ t.divisors,
          (1 / Real.sqrt (d : ℝ)) * Real.exp (-(c * Real.sqrt (Real.log (a * (t : ℝ))))))
      = ∑ d ∈ Finset.Icc 1 T, ∑ m ∈ Finset.Icc 1 (T / d),
          (1 / Real.sqrt (d : ℝ)) *
            Real.exp (-(c * Real.sqrt (Real.log (a * ((d * m : ℕ) : ℝ))))) :=
    SumDivisorsIccSwap
      (fun d t => (1 / Real.sqrt (d : ℝ)) *
        Real.exp (-(c * Real.sqrt (Real.log (a * (t : ℝ)))))) T
  -- Step 3: for each `d ≤ T`, bound the inner sum by `K·(T/d)·e^c·F`.
  have hstep3 : ∀ d ∈ Finset.Icc 1 T,
      (∑ m ∈ Finset.Icc 1 (T / d),
          (1 / Real.sqrt (d : ℝ)) *
            Real.exp (-(c * Real.sqrt (Real.log (a * ((d * m : ℕ) : ℝ))))))
      ≤ (1 / Real.sqrt (d : ℝ)) * (K * Real.exp c * ((T : ℝ) / (d : ℝ)) * F) := by
    intro d hd
    obtain ⟨hd1, hdT⟩ := Finset.mem_Icc.mp hd
    have hd1' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
    have had : (1 : ℝ) ≤ a * (d : ℝ) := by nlinarith
    have hTd1 : 1 ≤ T / d := by
      rw [Nat.le_div_iff_mul_le (by omega : 0 < d)]
      simpa using hdT
    have hinner := hK (a * (d : ℝ)) (T / d) had hTd1
    have hcast_m : ∀ m : ℕ,
        a * ((d * m : ℕ) : ℝ) = (a * (d : ℝ)) * (m : ℝ) := by
      intro m; push_cast; ring
    have hcongr : (∑ m ∈ Finset.Icc 1 (T / d),
          Real.exp (-(c * Real.sqrt (Real.log (a * ((d * m : ℕ) : ℝ))))))
        = ∑ m ∈ Finset.Icc 1 (T / d),
          Real.exp (-(c * Real.sqrt (Real.log ((a * (d : ℝ)) * (m : ℝ))))) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [hcast_m m]
    have hinner' : (∑ m ∈ Finset.Icc 1 (T / d),
          Real.exp (-(c * Real.sqrt (Real.log (a * ((d * m : ℕ) : ℝ))))))
        ≤ K * ((T / d : ℕ) : ℝ) *
            Real.exp (-(c * Real.sqrt (Real.log (a * (d : ℝ) * ((T / d : ℕ) : ℝ))))) := by
      rw [hcongr]; exact hinner
    have hstep : K * ((T / d : ℕ) : ℝ) *
          Real.exp (-(c * Real.sqrt (Real.log (a * (d : ℝ) * ((T / d : ℕ) : ℝ)))))
        ≤ K * Real.exp c * ((T : ℝ) / (d : ℝ)) * F := by
      have hcast2 : ((T / d : ℕ) : ℝ) ≤ (T : ℝ) / (d : ℝ) := Nat.cast_div_le
      have hcmp : Real.exp (-(c * Real.sqrt (Real.log (a * (d : ℝ) * ((T / d : ℕ) : ℝ)))))
          ≤ Real.exp c * F := by
        rw [hF]
        exact ExpNegSqrtLogFloorCmp c hc a ha d T hd1 hdT
      have h1 : ((T / d : ℕ) : ℝ) *
            Real.exp (-(c * Real.sqrt (Real.log (a * (d : ℝ) * ((T / d : ℕ) : ℝ)))))
          ≤ ((T : ℝ) / (d : ℝ)) * (Real.exp c * F) :=
        mul_le_mul hcast2 hcmp (Real.exp_nonneg _) (by positivity)
      calc K * ((T / d : ℕ) : ℝ) *
              Real.exp (-(c * Real.sqrt (Real.log (a * (d : ℝ) * ((T / d : ℕ) : ℝ)))))
          = K * (((T / d : ℕ) : ℝ) *
              Real.exp (-(c * Real.sqrt (Real.log (a * (d : ℝ) * ((T / d : ℕ) : ℝ)))))) := by ring
        _ ≤ K * (((T : ℝ) / (d : ℝ)) * (Real.exp c * F)) :=
              mul_le_mul_of_nonneg_left h1 hKpos.le
        _ = K * Real.exp c * ((T : ℝ) / (d : ℝ)) * F := by ring
    calc (∑ m ∈ Finset.Icc 1 (T / d),
          (1 / Real.sqrt (d : ℝ)) *
            Real.exp (-(c * Real.sqrt (Real.log (a * ((d * m : ℕ) : ℝ))))))
        = (1 / Real.sqrt (d : ℝ)) *
            (∑ m ∈ Finset.Icc 1 (T / d),
              Real.exp (-(c * Real.sqrt (Real.log (a * ((d * m : ℕ) : ℝ)))))) := by
          rw [Finset.mul_sum]
      _ ≤ (1 / Real.sqrt (d : ℝ)) * (K * ((T / d : ℕ) : ℝ) *
            Real.exp (-(c * Real.sqrt (Real.log (a * (d : ℝ) * ((T / d : ℕ) : ℝ)))))) :=
          mul_le_mul_of_nonneg_left hinner' (by positivity)
      _ ≤ (1 / Real.sqrt (d : ℝ)) * (K * Real.exp c * ((T : ℝ) / (d : ℝ)) * F) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
  -- Step 4: factor `K e^c T F` out of the `d`-sum.
  have hfactor : (∑ d ∈ Finset.Icc 1 T,
        (1 / Real.sqrt (d : ℝ)) * (K * Real.exp c * ((T : ℝ) / (d : ℝ)) * F))
      = K * Real.exp c * (T : ℝ) * F *
          (∑ d ∈ Finset.Icc 1 T, (1 / Real.sqrt (d : ℝ)) * (1 / (d : ℝ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [div_eq_mul_one_div]
    ring
  calc (∑ t ∈ Finset.Icc 1 T,
        |((ArithmeticFunction.moebius t : ℤ) : ℝ)| * ((t : ℝ) / Work.ZeroDensity.Jutila.kap t) *
          (∑ d ∈ t.divisors, 1 / Real.sqrt (d : ℝ)) *
            Real.exp (-(c * Real.sqrt (Real.log (a * (t : ℝ))))))
      ≤ ∑ t ∈ Finset.Icc 1 T, ∑ d ∈ t.divisors,
          (1 / Real.sqrt (d : ℝ)) * Real.exp (-(c * Real.sqrt (Real.log (a * (t : ℝ))))) := hstep1
    _ = ∑ d ∈ Finset.Icc 1 T, ∑ m ∈ Finset.Icc 1 (T / d),
          (1 / Real.sqrt (d : ℝ)) *
            Real.exp (-(c * Real.sqrt (Real.log (a * ((d * m : ℕ) : ℝ))))) := hstep2
    _ ≤ ∑ d ∈ Finset.Icc 1 T,
          (1 / Real.sqrt (d : ℝ)) * (K * Real.exp c * ((T : ℝ) / (d : ℝ)) * F) :=
        Finset.sum_le_sum hstep3
    _ = K * Real.exp c * (T : ℝ) * F *
          (∑ d ∈ Finset.Icc 1 T, (1 / Real.sqrt (d : ℝ)) * (1 / (d : ℝ))) := hfactor
    _ ≤ K * Real.exp c * (T : ℝ) * F * 3 :=
        mul_le_mul_of_nonneg_left (SumInvSqrtMulInvLe T) (by positivity)
    _ = (3 * K * Real.exp c) * (T : ℝ) *
          Real.exp (-(c * Real.sqrt (Real.log (a * (T : ℝ))))) := by rw [hF]; ring


end Work.ZeroDensity.Jutila.LzDiffAux
