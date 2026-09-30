import Mathlib
import Submission.Work.BMF.mr_direct_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

open Finset

noncomputable section

/-- The finitely supported set counted by `omegaCount`: primes `q ∈ [1,N]` with `P ≤ q ≤ Q`
and `q ∣ N`. -/
private def omegaSet (P Q : ℝ) (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun q : ℕ => q.Prime ∧ P ≤ (q : ℝ) ∧ (q : ℝ) ≤ Q ∧ q ∣ N)

private lemma omegaCount_eq_card (P Q : ℝ) (N : ℕ) :
    Work.BMF.mrDirect.omegaCount P Q N = (omegaSet P Q N).card := rfl

private lemma mem_omegaSet (P Q : ℝ) (N q : ℕ) :
    q ∈ omegaSet P Q N ↔
      (1 ≤ q ∧ q ≤ N ∧ q.Prime ∧ P ≤ (q : ℝ) ∧ (q : ℝ) ≤ Q ∧ q ∣ N) := by
  simp [omegaSet, Finset.mem_Icc, and_assoc]

lemma omegaCount_mul_prime {P Q : ℝ} {p m : ℕ} (hp : p.Prime)
    (hPp : P ≤ (p : ℝ)) (hpQ : (p : ℝ) ≤ Q) :
    Work.BMF.mrDirect.omegaCount P Q (m * p) =
      Work.BMF.mrDirect.omegaCount P Q m + (if p ∣ m then 0 else 1) := by
  by_cases hm : m = 0
  · subst hm
    simp [Work.BMF.mrDirect.omegaCount]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    rw [omegaCount_eq_card P Q (m * p), omegaCount_eq_card P Q m]
    -- Every prime in `omegaSet P Q m` remains in `omegaSet P Q (m*p)`.
    have hBA : omegaSet P Q m ⊆ omegaSet P Q (m * p) := by
      intro q hq
      rw [mem_omegaSet P Q m q] at hq
      rw [mem_omegaSet P Q (m * p) q]
      obtain ⟨h1q, hqm, hqp, hPq, hqQ, hqdm⟩ := hq
      exact ⟨h1q, le_trans hqm (Nat.le_mul_of_pos_right m hp.pos), hqp, hPq, hqQ,
        dvd_mul_of_dvd_left hqdm p⟩
    -- Every prime in `omegaSet P Q (m*p)` is either already in `omegaSet P Q m`, or is `p`.
    have hAB : omegaSet P Q (m * p) ⊆ omegaSet P Q m ∪ {p} := by
      intro q hq
      rw [mem_omegaSet P Q (m * p) q] at hq
      obtain ⟨h1q, _hqmp, hqp, hPq, hqQ, hqd⟩ := hq
      rw [Finset.mem_union, Finset.mem_singleton]
      rcases (hqp.dvd_mul).mp hqd with hqm | hqdp
      · left
        rw [mem_omegaSet P Q m q]
        exact ⟨h1q, Nat.le_of_dvd hmpos hqm, hqp, hPq, hqQ, hqm⟩
      · right
        exact (Nat.prime_dvd_prime_iff_eq hqp hp).mp hqdp
    have hpA : p ∈ omegaSet P Q (m * p) := by
      rw [mem_omegaSet P Q (m * p) p]
      exact ⟨hp.one_le, Nat.le_mul_of_pos_left p hmpos, hp, hPp, hpQ, dvd_mul_left p m⟩
    have hpB_iff : p ∈ omegaSet P Q m ↔ p ∣ m := by
      rw [mem_omegaSet P Q m p]
      constructor
      · intro h; exact h.2.2.2.2.2
      · intro hpm
        exact ⟨hp.one_le, Nat.le_of_dvd hmpos hpm, hp, hPp, hpQ, hpm⟩
    by_cases hpdm : p ∣ m
    · -- If `p ∣ m` the two sets coincide.
      have hpB : p ∈ omegaSet P Q m := hpB_iff.mpr hpdm
      have hAB' : omegaSet P Q (m * p) ⊆ omegaSet P Q m := by
        intro q hq
        rcases Finset.mem_union.mp (hAB hq) with h | h
        · exact h
        · rw [Finset.mem_singleton] at h; subst h; exact hpB
      have hAeqB : omegaSet P Q (m * p) = omegaSet P Q m :=
        Finset.Subset.antisymm hAB' hBA
      rw [hAeqB]; simp [hpdm]
    · -- Otherwise `omegaSet P Q (m*p) = omegaSet P Q m ∪ {p}` with `p ∉ omegaSet P Q m`.
      have hpB : p ∉ omegaSet P Q m := fun h => hpdm (hpB_iff.mp h)
      have hBA' : omegaSet P Q m ∪ {p} ⊆ omegaSet P Q (m * p) := by
        intro q hq
        rcases Finset.mem_union.mp hq with h | h
        · exact hBA h
        · rw [Finset.mem_singleton] at h; subst h; exact hpA
      have hAeq : omegaSet P Q (m * p) = omegaSet P Q m ∪ {p} :=
        Finset.Subset.antisymm hAB hBA'
      have hcard : (omegaSet P Q (m * p)).card = (omegaSet P Q m).card + 1 := by
        rw [hAeq, Finset.union_singleton, Finset.card_insert_of_notMem hpB]
      rw [hcard]; simp [hpdm]

end

end Work.BMF.mr_direct
