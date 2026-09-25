import Mathlib
import Submission.Work.RHContract.A.regionII.caK3B_defs
import Submission.Work.RHContract.A.ca_margin_lower
import Submission.Work.RHContract.A.regionII.caK3B_window
import Submission.Work.RHContract.A.regionII.caK3B_rpow_window

/-!
# `caK3B_structure` — the shape of the primes carrying a positive `caK3term`

For `ξ = ξ(ε) = caXi ε ≥ 10^5` and a prime `p ≤ ⌊√ξ⌋₊` whose `K₃` summand is **positive**,

`0 < caK3term ε p = max 0 (caYterm ε p − caXterm ε p)`,

the "loss beat the gain" inequality `caC ε · log p < p^{−(e+1)}/((e+1)(1−1/p))` (with
`e = caExpFloor ε p = ⌊log_p ξ⌋`) forces `p` into the *short window*

`ξ^{1/(e+1)} < p ≤ ξ^{1/e} < 1 + (ξ/kB ξ)^{1/(e+1)}`

where `kB ξ = ξ · kcc ξ · log ξ` and `kcc ξ` is the certified lower bound for `caC ε`.  In other
words only very few primes (at most one per value of `e`, cf. `card_le_one_prime_short`) can
contribute to `caK3`.

The three ingredients are

* the elementary `p`-adic window `ξ^{1/(e+1)} < p ≤ ξ^{1/e}` (`caK3B_rpow_window`);
* the "gain beats loss" rearrangement `(p−1)^{e+1} · kcc ξ · log ξ < 1` which, together with
  `ξ/kB ξ = 1/(kcc ξ log ξ)`, gives the upper end of the window (`caK3B_window`);
* `p ≤ √ξ ∧ 2 ≤ e` from the hypothesis `p ∈ Nat.primesLE ⌊√ξ⌋₊`.

-/

namespace Work.RHContract.A.regionII

theorem caK3B_structure (ε : ℝ) (hε : 0 < ε) (hlo : 100000 ≤ (Work.RHPlan.caXi ε : ℝ))
    (hcaC : kcc (Work.RHPlan.caXi ε : ℝ) ≤ Work.RHContract.Margin.caC ε)
    {p : ℕ} (hp : p ∈ (Nat.primesLE ⌊Real.sqrt (Work.RHPlan.caXi ε : ℝ)⌋₊).filter
        (fun q => Work.RHContract.Margin.caExpFloor ε q < ⌊Work.RHPlan.caMu q ε⌋₊))
    (hpos : 0 < Work.RHContract.A.caK3term ε p) :
    3 ≤ Nat.log p (Work.RHPlan.caXi ε) + 1 ∧
    (Work.RHPlan.caXi ε : ℝ) ^ (1/((Nat.log p (Work.RHPlan.caXi ε) + 1 : ℕ) : ℝ)) < (p:ℝ) ∧
    (p:ℝ) ≤ (Work.RHPlan.caXi ε : ℝ) ^ (1/((Nat.log p (Work.RHPlan.caXi ε) : ℕ) : ℝ)) ∧
    (p:ℝ) < 1 + ((Work.RHPlan.caXi ε : ℝ) / kB (Work.RHPlan.caXi ε : ℝ)) ^
      (1/((Nat.log p (Work.RHPlan.caXi ε) + 1 : ℕ) : ℝ)) := by
  have hξ0 : (0:ℝ) < (Work.RHPlan.caXi ε : ℝ) := by linarith
  have hp1 : p ∈ Nat.primesLE ⌊Real.sqrt (Work.RHPlan.caXi ε : ℝ)⌋₊ :=
    (Finset.mem_filter.mp hp).1
  obtain ⟨hp_le, hprime⟩ := Nat.mem_primesLE.mp hp1
  have hpR1 : (1:ℝ) < (p:ℝ) := by exact_mod_cast hprime.one_lt
  have hlogp0 : 0 < Real.log (p:ℝ) := Real.log_pos hpR1
  -- `p ≤ ξ`
  have hpm : p ≤ Work.RHPlan.caXi ε :=
    le_trans hp_le
      (Work.RHContract.A.sqrt_floor_le_caXi ε (by linarith : 1530 ≤ (Work.RHPlan.caXi ε : ℝ)))
  -- `p^2 ≤ ξ`, so the exponent `e = ⌊log_p ξ⌋` is at least `2`
  have hsq : p ^ 2 ≤ Work.RHPlan.caXi ε := by
    have h2 : (p:ℝ) ≤ Real.sqrt (Work.RHPlan.caXi ε : ℝ) :=
      le_trans (by exact_mod_cast hp_le) (Nat.floor_le (Real.sqrt_nonneg _))
    have h1 : (p:ℝ)^2 ≤ (Work.RHPlan.caXi ε : ℝ) := by
      nlinarith [Real.sq_sqrt hξ0.le, Real.sqrt_nonneg (Work.RHPlan.caXi ε : ℝ)]
    exact_mod_cast h1
  have he2 : 2 ≤ Nat.log p (Work.RHPlan.caXi ε) := Nat.le_log_of_pow_le hprime.one_lt hsq
  refine ⟨by omega, caK3B_rpow_window hprime.one_lt hpm |>.1,
    caK3B_rpow_window hprime.one_lt hpm |>.2, ?_⟩
  -- the `K₃` summand being positive: `caC ε · log p < caYterm ε p`
  have hdiff : 0 < Work.RHContract.A.caYterm ε p - Work.RHContract.A.caXterm ε p := by
    rw [Work.RHContract.A.caK3term] at hpos
    by_contra hcon
    have hle : Work.RHContract.A.caYterm ε p - Work.RHContract.A.caXterm ε p ≤ 0 :=
      le_of_not_gt hcon
    rw [max_eq_left hle] at hpos
    exact absurd hpos (lt_irrefl 0)
  have hYcaC : Work.RHContract.Margin.caC ε * Real.log (p:ℝ) <
      (p:ℝ) ^ (-(((Nat.log p (Work.RHPlan.caXi ε) : ℝ) + 1))) /
        (((Nat.log p (Work.RHPlan.caXi ε) : ℝ) + 1) * (1 - 1/(p:ℝ))) := by
    have h := hdiff
    rw [Work.RHContract.A.caYterm, Work.RHContract.A.caXterm] at h
    rw [Work.RHContract.A.caExpFloor_eq_log ε p] at h
    linarith
  have hY : kcc (Work.RHPlan.caXi ε : ℝ) * Real.log (p:ℝ) <
      (p:ℝ) ^ (-(((Nat.log p (Work.RHPlan.caXi ε) : ℝ) + 1))) /
        (((Nat.log p (Work.RHPlan.caXi ε) : ℝ) + 1) * (1 - 1/(p:ℝ))) :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcaC hlogp0.le) hYcaC
  -- `log ξ < (e+1) log p` because `ξ < p^{e+1}`
  have hpowe : ((Work.RHPlan.caXi ε : ℕ) : ℝ) <
      (p:ℝ) ^ (Nat.log p (Work.RHPlan.caXi ε) + 1) := by
    have := Nat.lt_pow_succ_log_self hprime.one_lt (Work.RHPlan.caXi ε)
    exact_mod_cast this
  have hloglt : Real.log (Work.RHPlan.caXi ε : ℝ) <
      ((Nat.log p (Work.RHPlan.caXi ε) : ℝ) + 1) * Real.log (p:ℝ) := by
    have h1 : Real.log (Work.RHPlan.caXi ε : ℝ)
        < Real.log ((p:ℝ) ^ (Nat.log p (Work.RHPlan.caXi ε) + 1)) :=
      Real.log_lt_log hξ0 hpowe
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  exact caK3B_window hlo hprime.two_le hloglt hY

end Work.RHContract.A.regionII
