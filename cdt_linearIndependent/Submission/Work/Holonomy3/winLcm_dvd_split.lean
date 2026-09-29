import Mathlib
import Submission.Work.Holonomy3.log_den_defs
import Submission.Work.Holonomy3.ppFac_pow_dvd_of_Icc
import Submission.Work.Holonomy3.prime_dvd_Lge

namespace Work.Holonomy3

open scoped BigOperators

/-- Every divisor of `lcm(1,…,l)` that is `≤ l` divides `lcmUpto l`. -/
private lemma dvd_lcmUpto_of_le {d l : ℕ} (hd : 1 ≤ d) (h : d ≤ l) :
    d ∣ Submission.CDTPlan.lcmUpto l := by
  rw [Submission.CDTPlan.lcmUpto]
  exact Finset.dvd_lcm (f := id) (b := d) (by rw [Finset.mem_Icc]; exact ⟨hd, h⟩)

/-- **The per-prime step.**  For a prime `p` dividing a nonzero element `m` of the window
`[n-D, n]`, the full prime power `p ^ (m.factorization p)` (which divides `m`) is already cleared
by `lcmUpto l · L^{≥l}_{n,D} · ppFac l n`:

* the powers `p ^ j ≤ l` come from `lcmUpto l` (exponent `min (v_p m) (log_p l)`),
* a prime `p > l` with a window multiple contributes one factor `p` inside `L^{≥l}_{n,D}`,
* all remaining powers `p ^ j`, `l < p ^ j ≤ n`, `j ≥ 2`, are distinct live levels of `ppFac l n`. -/
private lemma prime_pow_factorization_dvd {l n D m p : ℕ} (hp : p.Prime)
    (hm : m ∈ (Finset.Icc (n - D) n).erase 0) (hpm : p ∣ m) :
    p ^ (m.factorization p) ∣ Submission.CDTPlan.lcmUpto l * Submission.CDT.LcmGe.Lge l n D *
      Work.Holonomy3.ppFac l n := by
  obtain ⟨hm0, hmIcc⟩ := Finset.mem_erase.mp hm
  obtain ⟨hm1, hmn⟩ := Finset.mem_Icc.mp hmIcc
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hpmle : p ≤ m := Nat.le_of_dvd hmpos hpm
  have hpn : p ≤ n := le_trans hpmle hmn
  have hpe : p ^ (m.factorization p) ∣ m := (hp.pow_dvd_iff_le_factorization hm0).mpr le_rfl
  have hpemn : p ^ (m.factorization p) ≤ n := le_trans (Nat.le_of_dvd hmpos hpe) hmn
  have hen : m.factorization p ≤ n := by
    have h1 : m.factorization p < 2 ^ m.factorization p := Nat.lt_two_pow_self
    have h2 : 2 ^ m.factorization p ≤ p ^ m.factorization p :=
      Nat.pow_le_pow_left hp.two_le _
    omega
  -- the `lcmUpto l` part
  have hA : p ^ min (m.factorization p) (Nat.log p l) ∣ Submission.CDTPlan.lcmUpto l := by
    rcases Nat.eq_zero_or_pos (min (m.factorization p) (Nat.log p l)) with h0 | h0
    · rw [h0, pow_zero]; exact one_dvd _
    · have hLpos : 0 < Nat.log p l := lt_of_lt_of_le h0 (min_le_right _ _)
      have hlne : l ≠ 0 := by
        intro hc
        rw [hc, Nat.log_zero_right] at hLpos
        exact absurd hLpos (lt_irrefl 0)
      have hle : p ^ min (m.factorization p) (Nat.log p l) ≤ l :=
        le_trans (Nat.pow_le_pow_right hp.pos (min_le_right _ _)) (Nat.pow_log_le_self p hlne)
      exact dvd_lcmUpto_of_le (Nat.one_le_pow _ _ hp.pos) hle
  -- the `Lge` part
  have hB : p ^ (if l < p then 1 else 0) ∣ Submission.CDT.LcmGe.Lge l n D := by
    by_cases hlp : l < p
    · rw [if_pos hlp, pow_one]
      exact prime_dvd_Lge hp hlp hm hpm
    · rw [if_neg hlp, pow_zero]; exact one_dvd _
  -- the `ppFac` part
  have hC : p ^ (m.factorization p - min (m.factorization p) (Nat.log p l) -
      (if l < p then 1 else 0)) ∣ Work.Holonomy3.ppFac l n := by
    by_cases hlp : l < p
    · rw [if_pos hlp]
      have hL0 : Nat.log p l = 0 := Nat.log_eq_zero_iff.mpr (Or.inl hlp)
      have hcond : ∀ j ∈ Finset.Icc 2 (m.factorization p), l < p ^ j ∧ p ^ j ≤ n := by
        intro j hj
        rw [Finset.mem_Icc] at hj
        refine ⟨lt_of_lt_of_le hlp ?_, ?_⟩
        · simpa using Nat.pow_le_pow_right hp.pos (show 1 ≤ j by omega)
        · exact le_trans (Nat.pow_le_pow_right hp.pos hj.2) hpemn
      have hbase := ppFac_pow_dvd_of_Icc (l := l) (n := n) (p := p) (a := 2)
        (b := m.factorization p) hp hpn (le_refl 2) hen hcond
      rw [hL0, Nat.min_zero]
      convert hbase using 2
      omega
    · rw [if_neg hlp]
      have hple : p ≤ l := le_of_not_gt hlp
      have hlne : l ≠ 0 := by have hp2 : 2 ≤ p := hp.two_le; omega
      have hL1 : 1 ≤ Nat.log p l :=
        (Nat.le_log_iff_pow_le hp.one_lt hlne).mpr (by simpa using hple)
      rcases le_or_gt (m.factorization p) (Nat.log p l) with heL | hLe
      · rw [min_eq_left heL, Nat.sub_self, Nat.sub_zero]
        exact one_dvd _
      · rw [min_eq_right hLe.le, Nat.sub_zero]
        have hcond : ∀ j ∈ Finset.Icc (Nat.log p l + 1) (m.factorization p),
            l < p ^ j ∧ p ^ j ≤ n := by
          intro j hj
          rw [Finset.mem_Icc] at hj
          refine ⟨(Nat.log_lt_iff_lt_pow hp.one_lt hlne).mp (by omega), ?_⟩
          exact le_trans (Nat.pow_le_pow_right hp.pos hj.2) hpemn
        have hbase := ppFac_pow_dvd_of_Icc (l := l) (n := n) (p := p)
          (a := Nat.log p l + 1) (b := m.factorization p) hp hpn (by omega) hen hcond
        convert hbase using 2
        omega
  -- the exponents add up
  have hsum : min (m.factorization p) (Nat.log p l) + (if l < p then 1 else 0) +
      (m.factorization p - min (m.factorization p) (Nat.log p l) - (if l < p then 1 else 0))
      = m.factorization p := by
    by_cases hlp : l < p
    · rw [if_pos hlp]
      have hL0 : Nat.log p l = 0 := Nat.log_eq_zero_iff.mpr (Or.inl hlp)
      rw [hL0, Nat.min_zero]
      have he1 : 1 ≤ m.factorization p := (hp.dvd_iff_one_le_factorization hm0).mp hpm
      omega
    · rw [if_neg hlp]
      omega
  rw [← hsum, pow_add, pow_add]
  exact mul_dvd_mul (mul_dvd_mul hA hB) hC

/-- **The window lcm is cleared by `[1,…,l]·L^{≥l}·(proper prime powers)`.**
Splitting the prime powers dividing the integers of the window `[n-D, n]` at the threshold `l`:
the powers `≤ l` are accounted for by `[1,…,l]`, the primes `p > l` having a multiple in the
window by the paper's `L^{≥l}_{n,D}` of Lemma `lcm-2`, and the proper prime powers `p^j`, `j ≥ 2`,
above `l` by `ppFac l n`.  (Only used with `l = ⌊ξD⌋` and `n` the exponent of a position.) -/
theorem winLcm_dvd_split (l n D : ℕ) :
    Work.Holonomy3.winLcm n D ∣
      Submission.CDTPlan.lcmUpto l * Submission.CDT.LcmGe.Lge l n D * Work.Holonomy3.ppFac l n := by
  rw [winLcm, Finset.lcm_dvd_iff]
  intro m hm
  refine (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr ?_
  intro p k hp hpk
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · rw [hk0, pow_zero]; exact one_dvd _
  · have hm0 : m ≠ 0 := (Finset.mem_erase.mp hm).1
    have hpm : p ∣ m := dvd_trans (dvd_pow_self p (Nat.pos_iff_ne_zero.mp hkpos)) hpk
    have hke : k ≤ m.factorization p := (hp.pow_dvd_iff_le_factorization hm0).mp hpk
    exact dvd_trans (pow_dvd_pow p hke) (prime_pow_factorization_dvd hp hm hpm)

end Work.Holonomy3
