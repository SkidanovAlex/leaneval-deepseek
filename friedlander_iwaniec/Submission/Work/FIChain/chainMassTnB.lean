/-
# `Work.FIChain.chainMassTnB` — the combinatorial core of the FI per-layer bound

For odd `n = 2k+1` every chain counted by the weighted `B`-delay Rosser–Iwaniec layer sum
`TnB B ν n D y` has all of its primes above the threshold

  `levC B D k = max ⌈D^{levB B k}⌉₊ 2`,  `levB B k = ρ^k/(B+1)`,  `ρ = (B-1)/(B+1)`,

whence the weighted chain sum is dominated by

  `VfB ν (levC B D k) · (windowMass ν (levC B D k) y)^{2k+1} / (2k+1)!`.

The mathematical content is `TnB_odd_le_invariant` (`Submission/Work/FIChain/TnBInvariant.lean`),
which proves the same bound with the *real* threshold `D^{levB B k}` and the mass
`Σ_{q < ⌈y⌉₊, D^{levB B k} ≤ q} ν q`.  This file is the bridge from that statement to the one
above:

* for a *prime* `q`, `D^{levB B k} ≤ q ↔ levC B D k ≤ q`: the two thresholds cut at exactly the
  same primes (`max · 2` never separates two primes, since the only prime below `2` is `2` itself);
* `VfB ν (D^{levB B k}) = VfB ν (levC B D k)`, because `VfB` only sees primes below `⌈·⌉₊` and
  there is no prime below `2`;
* the remaining range `0 ≤ D < 1` is settled directly: at odd level `≥ 3` no chain survives at all
  (the level condition reads `p^{B+1} ≤ D < 1` while `p ≥ 2`, `B ≥ 1`), and at level `1` the chain
  sum is at most the full window mass, with `levC B D 0 = 2`.

Everything here is elementary (no `sorry`, no `axiom`).
-/
import Mathlib
import Submission.Work.FIChain.PerLayerDefs
import Submission.Work.FIChain.SnB_le_window
import Submission.Work.FIChain.TnBInvariant

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## The two bridges from the real threshold `D^{levB B k}` to `levC B D k` -/

/-- There is no prime below `2`, so `Nat.primesBelow n` is empty for `n ≤ 2`. -/
lemma primesBelow_eq_empty_of_le_two {n : ℕ} (h : n ≤ 2) : Nat.primesBelow n = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.mpr (fun p hp => ?_)
  obtain ⟨hlt, hprime⟩ := Nat.mem_primesBelow.mp hp
  have := hprime.two_le
  omega

/-- Raising the cutoff of `Nat.primesBelow` to at least `2` changes nothing. -/
lemma primesBelow_max_two (n : ℕ) : Nat.primesBelow n = Nat.primesBelow (max n 2) := by
  rcases lt_or_ge n 2 with h | h
  · rw [max_eq_right (le_of_lt h), primesBelow_eq_empty_of_le_two (le_of_lt h),
      primesBelow_eq_empty_of_le_two le_rfl]
  · rw [max_eq_left h]

/-- `VfB` at the natural level `n` equals `VfB` at the level `max n 2`. -/
lemma VfB_nat_max_two (ν : ℕ → ℝ) (n : ℕ) :
    VfB ν (n : ℝ) = VfB ν ((max n 2 : ℕ) : ℝ) := by
  rw [VfB, VfB, Nat.ceil_natCast, Nat.ceil_natCast, primesBelow_max_two]

/-- `VfB ν ((⌈y⌉₊ : ℕ) : ℝ) = VfB ν y`. -/
lemma VfB_ceil_natCast (ν : ℕ → ℝ) (y : ℝ) : VfB ν ((⌈y⌉₊ : ℕ) : ℝ) = VfB ν y := by
  rw [VfB, VfB, Nat.ceil_natCast]

/-- `VfB` at the real threshold `D^{levB B k}` equals `VfB` at the natural threshold
`levC B D k = max ⌈D^{levB B k}⌉₊ 2`: both products run over the primes below `⌈D^{levB B k}⌉₊`
(nothing changes below `2`). -/
lemma VfB_levC_eq (B D : ℝ) (ν : ℕ → ℝ) (k : ℕ) :
    VfB ν (D ^ levB B k) = VfB ν ((levC B D k : ℕ) : ℝ) := by
  calc VfB ν (D ^ levB B k) = VfB ν ((⌈D ^ levB B k⌉₊ : ℕ) : ℝ) :=
        (VfB_ceil_natCast ν (D ^ levB B k)).symm
    _ = VfB ν ((max ⌈D ^ levB B k⌉₊ 2 : ℕ) : ℝ) := VfB_nat_max_two ν ⌈D ^ levB B k⌉₊

/-- For a prime `q` the two thresholds `D^{levB B k}` and `levC B D k = max ⌈D^{levB B k}⌉₊ 2`
cut at the same place: no prime lies in the half-open gap. -/
lemma le_rpow_iff_levC_le {B D : ℝ} (k : ℕ) {q : ℕ} (hq : q.Prime) :
    D ^ levB B k ≤ (q : ℝ) ↔ levC B D k ≤ q := by
  rw [levC]
  constructor
  · intro h
    exact max_le (Nat.ceil_le.mpr h) hq.two_le
  · intro h
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_left _ _) h)

/-- The window measure over the real threshold equals the window measure over `levC B D k`. -/
lemma windowMass_levC_eq (B D y : ℝ) (ν : ℕ → ℝ) (k : ℕ) :
    (∑ q ∈ (Nat.primesBelow ⌈y⌉₊).filter (fun q : ℕ => D ^ levB B k ≤ (q : ℝ)), ν q)
      = windowMass ν (levC B D k) y := by
  rw [windowMass]
  refine Finset.sum_congr ?_ (fun q _ => rfl)
  exact Finset.filter_congr
    (fun q hq => le_rpow_iff_levC_le (B := B) (D := D) k (Nat.mem_primesBelow.mp hq).2)

/-! ## Odd layers of level `≥ 3` vanish for `D ≤ 1` -/

/-- At an odd level `m ≥ 3` the level condition is `p^{B+1} ≤ D`; with `D ≤ 1` and `p ≥ 2`,
`B ≥ 1` this is impossible, so the layer sum is empty. -/
lemma TnB_eq_zero_of_three_le_odd {B D y : ℝ} (hB : 1 ≤ B) (ν : ℕ → ℝ) {m : ℕ}
    (hm : 3 ≤ m) (hmo : Odd m) (hD : D ≤ 1) : TnB B ν m D y = 0 := by
  rw [TnB_eq_sum_primes_of_odd B ν D y hm hmo]
  refine Finset.sum_eq_zero (fun p hp => ?_)
  rw [Finset.mem_filter] at hp
  obtain ⟨hpb, hcond⟩ := hp
  obtain ⟨_, hprime⟩ := Nat.mem_primesBelow.mp hpb
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
  have hB1 : (0 : ℝ) < B + 1 := by linarith
  have hgt : (1 : ℝ) < (p : ℝ) ^ (B + 1) :=
    lt_of_lt_of_le (Real.one_lt_rpow (by norm_num) hB1)
      (Real.rpow_le_rpow (by norm_num) h2 (le_of_lt hB1))
  linarith

/-! ## The target -/

theorem chainMassTnB (B : ℝ) (hB : 1 ≤ B) {ν : ℕ → ℝ}
    (hν0 : ∀ p : ℕ, p.Prime → 0 ≤ ν p) (hν1 : ∀ p : ℕ, p.Prime → ν p ≤ 1 / 2) :
    ∀ (k : ℕ) (D y : ℝ), 0 ≤ D → 2 ≤ y →
      Work.FIChain.TnB B ν (2 * k + 1) D y
        ≤ Work.FIChain.VfB ν (Work.FIChain.levC B D k : ℝ)
            * (Work.FIChain.windowMass ν (Work.FIChain.levC B D k) y) ^ (2 * k + 1)
            / ((2 * k + 1).factorial : ℝ) := by
  intro k D y hD hy
  have hν1' : ∀ p : ℕ, p.Prime → ν p ≤ 1 := fun p hp => by linarith [hν1 p hp]
  rcases lt_or_ge D 1 with hD1 | hD1
  · -- `0 ≤ D < 1`
    have hDle1 : D ≤ 1 := le_of_lt hD1
    rcases Nat.eq_zero_or_pos k with hk | hk
    · -- `k = 0`: level `1`, where `levC B D 0 = 2` and `VfB ν 2 = 1`
      subst hk
      simp only [Nat.mul_zero, Nat.zero_add]
      have hlevC2 : levC B D 0 = 2 := by
        rw [levC]
        have hlevB : levB B 0 = 1 / (B + 1) := by rw [levB]; simp
        have hγ : D ^ levB B 0 ≤ 1 := by
          rw [hlevB]
          calc D ^ (1 / (B + 1)) ≤ 1 ^ (1 / (B + 1)) :=
                Real.rpow_le_rpow hD hDle1 (by positivity)
            _ = 1 := Real.one_rpow _
        have hceil : ⌈D ^ levB B 0⌉₊ ≤ 1 := Nat.ceil_le.mpr (by simpa using hγ)
        exact max_eq_right (le_trans hceil (by norm_num))
      have hmain : TnB B ν 1 D y ≤ ∑ p ∈ Nat.primesBelow ⌈y⌉₊, ν p := by
        have hT1 : TnB B ν 1 D y
            = ∑ p ∈ (Nat.primesBelow ⌈y⌉₊).filter (fun p => TcondB B 1 D p),
                ν p * VfB ν (p : ℝ) := by
          rw [show (1 : ℕ) = 0 + 1 from rfl, TnB]
          simp [TnB]
        rw [hT1]
        calc ∑ p ∈ (Nat.primesBelow ⌈y⌉₊).filter (fun p => TcondB B 1 D p),
                ν p * VfB ν (p : ℝ)
            ≤ ∑ p ∈ (Nat.primesBelow ⌈y⌉₊).filter (fun p => TcondB B 1 D p), ν p * 1 := by
              refine Finset.sum_le_sum (fun p hp => ?_)
              have hp' : p.Prime := (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hp).1).2
              exact mul_le_mul_of_nonneg_left (VfB_le_one hν0 hν1' (p : ℝ)) (hν0 p hp')
          _ = ∑ p ∈ (Nat.primesBelow ⌈y⌉₊).filter (fun p => TcondB B 1 D p), ν p := by simp
          _ ≤ ∑ p ∈ Nat.primesBelow ⌈y⌉₊, ν p :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                (fun p hp _ => hν0 p (Nat.mem_primesBelow.mp hp).2)
      have hVf2 : VfB ν ((2 : ℕ) : ℝ) = 1 := VfB_eq_one_of_le_two ν (by norm_num)
      have hwm : windowMass ν 2 y = ∑ p ∈ Nat.primesBelow ⌈y⌉₊, ν p := by
        rw [windowMass]
        congr 1
        exact Finset.filter_true_of_mem (fun p hp => (Nat.mem_primesBelow.mp hp).2.two_le)
      rw [hlevC2, hVf2, hwm, Nat.factorial_one, Nat.cast_one, pow_one, div_one, one_mul]
      exact hmain
    · -- `k ≥ 1`: level `≥ 3`, no chain survives
      have hzero : TnB B ν (2 * k + 1) D y = 0 :=
        TnB_eq_zero_of_three_le_odd hB ν (by omega) ⟨k, by ring⟩ hDle1
      rw [hzero]
      have hnn : 0 ≤ VfB ν (levC B D k : ℝ) * (windowMass ν (levC B D k) y) ^ (2 * k + 1)
          / ((2 * k + 1).factorial : ℝ) := by
        refine div_nonneg (mul_nonneg (VfB_nonneg hν1' _) (pow_nonneg ?_ _)) (by positivity)
        rw [windowMass]
        exact Finset.sum_nonneg
          (fun p hp => hν0 p (Nat.mem_primesBelow.mp (Finset.mem_filter.mp hp).1).2)
      linarith
  · -- `1 ≤ D`: the invariant form of the chain bound, transported along the two bridges
    have hinv := (TnB_odd_le_invariant B hB ν hν0 hν1 k D y hD1).1
    rw [← VfB_levC_eq B D ν k, ← windowMass_levC_eq B D y ν k]
    exact hinv

end

end Work.FIChain
