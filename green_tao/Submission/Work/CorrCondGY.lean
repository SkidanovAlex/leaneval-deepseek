import Mathlib
import Submission.Work.TauWeight
import Submission.Commons.NumberTheory.Sieve.KPseudorandom_mean

/-!
# The correlation condition for the Goldston–Yıldırım majorant

This file reduces `Commons.NumberTheory.Sieve.CorrCond p ν m₀ CmB` for a measure `ν` to the
Green–Tao §9 *analytic* correlation bound (`hgy`): for every `1 < m ≤ m₀` and every tuple
`h : Fin m → ZMod p`,

`𝔼_x ∏_{i<m} ν(x + h_i) ≤ Ccorr m · ∑_{i<j} ( |h_i - h_j| = 0 ? (1+log p)^{c₀ m}/Ccorr m :
                                                       (∏_{p | |h_i-h_j|} (1 + p^{-1/2}))^N )`

with `N = m(m-1)/2` the number of pairs.  The passage to the correlation weight `τ` is the
"pairing / GM–AM" step of Green–Tao (`additive-weights`), and the moment bound is
`tauNat_moment_bound` (`additive-weights` again).  Everything here is `p`-uniform.
-/

namespace GYMaj

open Finset

/-- A `p`-independent witness for the arithmetic moment bound. -/
noncomputable def CwMoment (Q : ℕ) : ℝ :=
  Classical.choose (Commons.NumberTheory.Sieve.primeFactors_weight_moment Q)

lemma CwMoment_pos (Q : ℕ) : 0 < CwMoment Q :=
  (Classical.choose_spec (Commons.NumberTheory.Sieve.primeFactors_weight_moment Q)).1

lemma CwMoment_spec (Q N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ)⁻¹ * ∑ n ∈ Finset.Icc 1 N,
      (∏ p ∈ n.primeFactors, (1 + (p : ℝ) ^ (-(1 / 2 : ℝ)))) ^ Q ≤ CwMoment Q :=
  (Classical.choose_spec (Commons.NumberTheory.Sieve.primeFactors_weight_moment Q)).2 N hN

/-- **The moment bound with an explicit, `p`-independent constant.** -/
theorem tauNat_moment_bound_explicit {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p) {A : ℝ} (hA : 0 ≤ A)
    (B c q : ℕ) :
    (p : ℝ)⁻¹ * ∑ x : ZMod p, (tauNat A B c p (min x.val (p - x.val))) ^ q
      ≤ Real.exp ((c : ℝ) ^ 2 * (q : ℝ) ^ 2 + 2 * (c : ℝ) * (q : ℝ))
          + 2 * A ^ q * CwMoment (B * q) := by
  classical
  set f : ℕ → ℝ := fun d => tauNat A B c p d with hf
  set S : ℝ := ∑ d ∈ Finset.Icc 1 (p / 2), f d ^ q with hS
  have hsum : ∑ x : ZMod p, (tauNat A B c p (min x.val (p - x.val))) ^ q = f 0 ^ q + 2 * S := by
    have h := Commons.Data.ZMod.sum_dist_to_zero p hp (fun d => f d ^ q)
    rw [hS]; simpa [hf] using h
  rw [hsum]
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hf0 : f 0 = (1 + Real.log (p : ℝ)) ^ c := by simp [hf, tauNat]
  have hIcc : (p : ℝ)⁻¹ * S ≤ A ^ q * CwMoment (B * q) := by
    have hsub : Finset.Icc 1 (p / 2) ⊆ Finset.Icc 1 p := by
      intro d hd
      rw [Finset.mem_Icc] at hd ⊢
      exact ⟨hd.1, le_trans hd.2 (Nat.div_le_self p 2)⟩
    have hstep : S ≤ A ^ q * ∑ d ∈ Finset.Icc 1 p,
        (∏ p' ∈ d.primeFactors, (1 + (p' : ℝ) ^ (-(1 / 2 : ℝ)))) ^ (B * q) := by
      rw [hS]
      have hmono : ∑ d ∈ Finset.Icc 1 (p / 2), f d ^ q ≤ ∑ d ∈ Finset.Icc 1 p, f d ^ q :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun d _ _ => pow_nonneg (tauNat_nonneg hA B c p d) q)
      refine le_trans hmono (le_of_eq ?_)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mem_Icc] at hd
      have hd0 : d ≠ 0 := by omega
      have hfd : f d = A * (∏ p' ∈ d.primeFactors, (1 + (p' : ℝ) ^ (-(1 / 2 : ℝ)))) ^ B := by
        simp only [hf, tauNat, if_neg hd0]
      rw [hfd, mul_pow, ← pow_mul]
    have hbound := CwMoment_spec (B * q) p (by omega : 1 ≤ p)
    rw [inv_mul_le_iff₀ hpR] at hbound
    have hAq : (0 : ℝ) ≤ A ^ q := pow_nonneg hA q
    have := mul_le_mul_of_nonneg_left hbound hAq
    rw [inv_mul_le_iff₀ hpR]
    calc S ≤ A ^ q * ∑ d ∈ Finset.Icc 1 p,
            (∏ p' ∈ d.primeFactors, (1 + (p' : ℝ) ^ (-(1 / 2 : ℝ)))) ^ (B * q) := hstep
      _ ≤ A ^ q * ((p : ℝ) * CwMoment (B * q)) := this
      _ = (p : ℝ) * (A ^ q * CwMoment (B * q)) := by ring
  have hsplit : (p : ℝ)⁻¹ * (f 0 ^ q + 2 * S)
      = f 0 ^ q / (p : ℝ) + 2 * ((p : ℝ)⁻¹ * S) := by field_simp
  rw [hsplit]
  have hzero : f 0 ^ q / (p : ℝ)
      ≤ Real.exp ((c : ℝ) ^ 2 * (q : ℝ) ^ 2 + 2 * (c : ℝ) * (q : ℝ)) := by
    rw [hf0, ← pow_mul]
    exact rpow_log_div_le_exp (p := p) (c := c) (q := q) (by omega : 1 ≤ p)
  have h2 : 2 * ((p : ℝ)⁻¹ * S) ≤ 2 * (A ^ q * CwMoment (B * q)) :=
    mul_le_mul_of_nonneg_left hIcc (by norm_num)
  linarith [hzero, h2]

end GYMaj

namespace GYMaj

/-- `val = 0` iff the element is `0` (already in Mathlib, restated for convenience). -/
lemma zmod_val_eq_zero_iff {p : ℕ} (a : ZMod p) : a.val = 0 ↔ a = 0 := ZMod.val_eq_zero a

/-- **The correlation condition from the Green–Tao §9 analytic bound.** -/
theorem corrCond_of_gy {p : ℕ} [Fact p.Prime] (hp : 3 ≤ p) (ν : ZMod p → ℝ) (m₀ : ℕ)
    {Ccorr : ℕ → ℝ} (hCcorr0 : ∀ m, 0 < Ccorr m) {c₀ : ℕ → ℕ}
    (hgy : ∀ m, 1 < m → m ≤ m₀ → ∀ h : Fin m → ZMod p,
      (p : ℝ)⁻¹ * ∑ x : ZMod p, ∏ i, ν (x + h i)
        ≤ Ccorr m * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
            (if h i = h j then (1 + Real.log (p : ℝ)) ^ (c₀ m) / Ccorr m
             else (∏ p' ∈ (min (h i - h j).val (p - (h i - h j).val)).primeFactors,
                     (1 + (p' : ℝ) ^ (-(1 / 2 : ℝ)))) ^ (m * (m - 1) / 2))) :
    Commons.NumberTheory.Sieve.CorrCond p ν m₀
      (fun m q => Real.exp ((c₀ m : ℝ) ^ 2 * (q : ℝ) ^ 2 + 2 * (c₀ m : ℝ) * (q : ℝ))
        + 2 * (Ccorr m) ^ q * CwMoment (m * (m - 1) / 2 * q)) := by
  classical
  intro m hm1 hmm
  have hcard : (Fintype.card (ZMod p) : ℝ) = (p : ℝ) := by rw [ZMod.card]
  set N : ℕ := m * (m - 1) / 2 with hN
  set τ : ZMod p → ℝ := fun x => tauNat (Ccorr m) N (c₀ m) p (min x.val (p - x.val)) with hτ
  have hCpos : (0 : ℝ) < Ccorr m := hCcorr0 m
  refine ⟨τ, ?_, ?_, ?_⟩
  · intro x
    exact tauNat_nonneg hCpos.le N (c₀ m) p (min x.val (p - x.val))
  · intro q hq
    have := tauNat_moment_bound_explicit (p := p) hp hCpos.le N (c₀ m) q
    rw [hN] at this
    rw [hcard]
    simpa only [hτ] using this
  · intro h
    rw [hcard]
    refine le_trans (hgy m hm1 hmm h) ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hij : h i = h j
    · -- repeated entry: `τ 0 = (1 + log p)^{c₀ m}`
      have hsub : h i - h j = 0 := sub_eq_zero.mpr hij
      have hτ0 : τ (h i - h j) = (1 + Real.log (p : ℝ)) ^ (c₀ m) := by
        simp [hτ, hsub, tauNat]
      rw [if_pos hij, hτ0, ← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt hCpos)]
    · -- distinct entries: exact agreement with the analytic bound
      have hsub : h i - h j ≠ 0 := sub_ne_zero.mpr hij
      have hval : (h i - h j).val ≠ 0 := fun hc => hsub ((zmod_val_eq_zero_iff _).mp hc)
      have hlt : (h i - h j).val < p := ZMod.val_lt _
      have hmin : min (h i - h j).val (p - (h i - h j).val) ≠ 0 := by
        rw [Ne, Nat.min_eq_zero_iff]
        push Not
        exact ⟨hval, by omega⟩
      rw [if_neg hij]
      simp only [hτ, tauNat, if_neg hmin, hN]
      exact le_rfl

end GYMaj
