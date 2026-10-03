/-
# `Work.FIArea7.P231.ReducedDefs` — the `c`-smooth decomposition of a natural number

*FI* Prop. 23.1 removes the condition `(mn, c) = 1` from the reduced form `L∗` by writing every
`m` uniquely as `m = a·m'` with `a` `c`-smooth (`a ∣ c^∞`) and `(m', c) = 1`.  This module fixes
that decomposition and its basic arithmetic.
-/
import Mathlib
import Submission.Work.FIArea7.P231Defs

set_option autoImplicit false

namespace Work.FIArea7.P231

open Finset
open scoped BigOperators

noncomputable section

/-- `IsSmooth c a`: every prime divisor of `a` divides `c` (i.e. `a ∣ c^∞`, `a` is `c`-smooth). -/
def IsSmooth (c a : ℕ) : Prop := ∀ p, p.Prime → p ∣ a → p ∣ c

instance decidablePred_isSmooth (c : ℕ) : DecidablePred (IsSmooth c) := fun a => Classical.dec _

/-- The `c`-smooth part of `m`: the largest divisor of `m` whose prime factors all divide `c`.
Defined as `gcd m (c^m)`. -/
def cSm (c m : ℕ) : ℕ := Nat.gcd m (c ^ m)

/-- The `c`-free part of `m`: `m` divided by its `c`-smooth part. -/
def cCp (c m : ℕ) : ℕ := m / cSm c m

/-! ## Basic arithmetic of the decomposition -/

lemma isSmooth_iff_mem_factoredNumbers {c a : ℕ} (hc : c ≠ 0) :
    IsSmooth c a ↔ a ∈ Nat.factoredNumbers c.primeFactors := by
  rw [Nat.mem_factoredNumbers']
  constructor
  · intro h p hp hpa
    exact Nat.mem_primeFactors.mpr ⟨hp, h p hp hpa, hc⟩
  · intro h p hp hpa
    exact (Nat.mem_primeFactors.mp (h p hp hpa)).2.1

lemma isSmooth_one (c : ℕ) : IsSmooth c 1 :=
  fun _ hp h => absurd h hp.not_dvd_one

lemma isSmooth_mul {c a b : ℕ} (ha : IsSmooth c a) (hb : IsSmooth c b) : IsSmooth c (a*b) :=
  fun _ hp h => ((hp.dvd_mul).mp h).elim (ha _ hp) (hb _ hp)

lemma isSmooth_of_dvd {c a b : ℕ} (hab : a ∣ b) (hb : IsSmooth c b) : IsSmooth c a :=
  fun p hp hpa => hb p hp (hpa.trans hab)

lemma ne_zero_of_isSmooth {c a : ℕ} (hc : 1 ≤ c) (h : IsSmooth c a) : a ≠ 0 := by
  intro ha0
  obtain ⟨p, hpge, hpp⟩ := Nat.exists_infinite_primes (c+1)
  have hpc : p ∣ c := h p hpp (ha0 ▸ dvd_zero p)
  have : p ≤ c := Nat.le_of_dvd (by omega) hpc
  omega

lemma isSmooth_dvd_pow {c a : ℕ} (ha : a ≠ 0) (h : IsSmooth c a) : a ∣ c ^ a := by
  rcases Nat.eq_zero_or_pos c with hc0 | hcpos
  · rw [hc0, zero_pow ha]; exact dvd_zero a
  have hcne : c ≠ 0 := Nat.pos_iff_ne_zero.mp hcpos
  rw [← Nat.factorization_le_iff_dvd ha (pow_ne_zero a hcne)]
  rw [Finsupp.le_def]
  intro p
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  by_cases hp : p.Prime
  · by_cases hpc : p ∣ c
    · have h1 : 1 ≤ c.factorization p := (hp.dvd_iff_one_le_factorization hcne).mp hpc
      have hlt : a.factorization p < a := Nat.factorization_lt p ha
      calc a.factorization p ≤ a := le_of_lt hlt
        _ = a * 1 := (mul_one a).symm
        _ ≤ a * c.factorization p := Nat.mul_le_mul_left a h1
    · have hz : a.factorization p = 0 := by
        by_contra hz
        exact hpc (h p hp (Nat.dvd_of_factorization_pos hz))
      rw [hz]; exact Nat.zero_le _
  · rw [Nat.factorization_eq_zero_of_not_prime a hp]; exact Nat.zero_le _

lemma coprime_of_isSmooth_coprime {c a b : ℕ} (hc : 1 ≤ c) (ha : IsSmooth c a)
    (hb : Nat.Coprime b c) : Nat.Coprime b a :=
  (hb.pow_right a).coprime_dvd_right (isSmooth_dvd_pow (ne_zero_of_isSmooth hc ha) ha)

lemma cSm_dvd (c m : ℕ) : cSm c m ∣ m := Nat.gcd_dvd_left m (c^m)

lemma cSm_smooth (c m : ℕ) : IsSmooth c (cSm c m) :=
  fun _ hp h => hp.dvd_of_dvd_pow (h.trans (Nat.gcd_dvd_right m (c^m)))

lemma cSm_pos {c m : ℕ} (hm : m ≠ 0) : 0 < cSm c m :=
  Nat.gcd_pos_of_pos_left (c^m) (Nat.pos_of_ne_zero hm)

lemma cSm_le {c m : ℕ} (hm : m ≠ 0) : cSm c m ≤ m :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hm) (Nat.gcd_dvd_left m (c^m))

lemma cSm_mul_cCp {c m : ℕ} (hm : m ≠ 0) : cSm c m * cCp c m = m := by
  rw [cCp, Nat.mul_comm]
  change m / Nat.gcd m (c ^ m) * Nat.gcd m (c ^ m) = m
  exact Nat.div_mul_cancel (Nat.gcd_dvd_left m (c^m))

lemma cCp_dvd (c m : ℕ) : cCp c m ∣ m := by
  rw [cCp]; exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left m (c^m))

lemma cCp_ne_zero {c m : ℕ} (hm : m ≠ 0) : cCp c m ≠ 0 :=
  fun h => hm (by rw [← cSm_mul_cCp hm, h, mul_zero])

lemma cCp_coprime {c m : ℕ} (hm : m ≠ 0) : Nat.Coprime (cCp c m) c := by
  rcases Nat.eq_zero_or_pos c with hc0 | hcpos
  · subst hc0
    have hone : cCp 0 m = 1 := by
      rw [cCp]
      change m / Nat.gcd m (0 ^ m) = 1
      rw [zero_pow hm, Nat.gcd_zero_right, Nat.div_self (Nat.pos_of_ne_zero hm)]
    rw [hone]; exact Nat.coprime_one_left 0
  · have hcne : c ≠ 0 := Nat.pos_iff_ne_zero.mp hcpos
    rw [← not_not (a := Nat.Coprime (cCp c m) c)]
    intro hbad
    obtain ⟨p, hp, hpcp, hpc⟩ := Nat.Prime.not_coprime_iff_dvd.mp hbad
    have hcm0 : c ^ m ≠ 0 := pow_ne_zero m hcne
    have hgpos : 0 < cSm c m := cSm_pos hm
    have hgfac : (cSm c m).factorization p = m.factorization p := by
      have h1 : p ^ (m.factorization p) ∣ cSm c m := by
        rw [cSm]
        apply Nat.dvd_gcd
        · exact (hp.pow_dvd_iff_le_factorization hm).mpr le_rfl
        · rw [hp.pow_dvd_iff_le_factorization hcm0, Nat.factorization_pow,
            Finsupp.smul_apply, smul_eq_mul]
          have hcv : 1 ≤ c.factorization p := (hp.dvd_iff_one_le_factorization hcne).mp hpc
          have hlt : m.factorization p < m := Nat.factorization_lt p hm
          calc m.factorization p ≤ m := le_of_lt hlt
            _ = m * 1 := (mul_one m).symm
            _ ≤ m * c.factorization p := Nat.mul_le_mul_left m hcv
      have h2 : ¬ (p ^ (m.factorization p + 1) ∣ cSm c m) := by
        intro hd
        have hdm : p ^ (m.factorization p + 1) ∣ m := hd.trans (Nat.gcd_dvd_left m (c^m))
        have hle := (hp.pow_dvd_iff_le_factorization hm).mp hdm
        omega
      refine le_antisymm ?_ ((hp.pow_dvd_iff_le_factorization hgpos.ne').mp h1)
      by_contra hcon
      exact h2 ((hp.pow_dvd_iff_le_factorization hgpos.ne').mpr (by omega))
    have hdivfac : (cCp c m).factorization p = 0 := by
      rw [cCp]
      change (m / Nat.gcd m (c ^ m)).factorization p = 0
      rw [Nat.factorization_div (Nat.gcd_dvd_left m (c^m))]
      rw [Finsupp.tsub_apply]
      show m.factorization p - (cSm c m).factorization p = 0
      rw [hgfac, tsub_self]
    have h1 : 1 ≤ (cCp c m).factorization p :=
      (hp.dvd_iff_one_le_factorization (cCp_ne_zero hm)).mp hpcp
    omega

/-- The key characterisation: for `a` `c`-smooth and `m'` coprime to `c`, the smooth part of
`a·m'` is `a` (and hence the `c`-free part is `m'`). -/
lemma cSm_mul_of_smooth_coprime {c a m' : ℕ} (hc : 1 ≤ c) (ha : IsSmooth c a)
    (hm' : Nat.Coprime m' c) (hm'0 : m' ≠ 0) : cSm c (a * m') = a := by
  have ha0 : a ≠ 0 := ne_zero_of_isSmooth hc ha
  have hapos : 0 < a := Nat.pos_of_ne_zero ha0
  have ha_dvd_cam : a ∣ c ^ (a * m') :=
    (isSmooth_dvd_pow ha0 ha).trans
      (Nat.pow_dvd_pow c (Nat.le_mul_of_pos_right a (Nat.pos_of_ne_zero hm'0)))
  have h1 : a ∣ cSm c (a * m') := Nat.dvd_gcd (dvd_mul_right a m') ha_dvd_cam
  have hcop : Nat.Coprime (cSm c (a * m')) m' :=
    (coprime_of_isSmooth_coprime hc (cSm_smooth c (a * m')) hm').symm
  have h2 : cSm c (a * m') ∣ a := hcop.dvd_of_dvd_mul_right (Nat.gcd_dvd_left (a * m') (c ^ (a * m')))
  exact (Nat.dvd_antisymm h2 h1)

lemma cCp_mul_of_smooth_coprime {c a m' : ℕ} (hc : 1 ≤ c) (ha : IsSmooth c a)
    (hm' : Nat.Coprime m' c) (hm'0 : m' ≠ 0) : cCp c (a * m') = m' := by
  have ha0 : a ≠ 0 := ne_zero_of_isSmooth hc ha
  rw [cCp, cSm_mul_of_smooth_coprime hc ha hm' hm'0]
  exact Nat.mul_div_right m' (Nat.pos_of_ne_zero ha0)

/-- Coprimality factorises across the smooth/coprime decomposition. -/
lemma coprime_mul_iff_of_smooth {c a b m' n' : ℕ} (hc : 1 ≤ c) (ha : IsSmooth c a)
    (hb : IsSmooth c b) (hm' : Nat.Coprime m' c) (hn' : Nat.Coprime n' c) :
    Nat.Coprime (a * m') (b * n') ↔ Nat.Coprime a b ∧ Nat.Coprime m' n' := by
  constructor
  · intro h
    exact ⟨h.of_dvd (dvd_mul_right a m') (dvd_mul_right b n'),
      h.of_dvd (dvd_mul_left m' a) (dvd_mul_left n' b)⟩
  · rintro ⟨hab, hmn⟩
    rw [Nat.coprime_mul_iff_left]
    refine ⟨?_, ?_⟩
    · rw [Nat.coprime_mul_iff_right]
      exact ⟨hab, (coprime_of_isSmooth_coprime hc ha hn').symm⟩
    · rw [Nat.coprime_mul_iff_right]
      exact ⟨coprime_of_isSmooth_coprime hc hb hm', hmn⟩

end

end Work.FIArea7.P231
