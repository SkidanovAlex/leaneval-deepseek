import Mathlib
import Submission.Work.WilC4aP.Basic
import Submission.Work.WilC4aP.PzAlg

namespace Work.WilC4aP

/-- The coefficient of `X ^ (m - 1)` in `(X - C c) ^ m` (for `m ≥ 1`) is `-(m : ℂ) * c`.

This is the elementary computation behind the "next coefficient" test: a pure power
`(X - c) ^ m` has vanishing coefficient of `X ^ (m - 1)` only when `c = 0`. -/
lemma coeff_X_sub_C_pow (c : ℂ) {m : ℕ} (hm : 1 ≤ m) :
    ((Polynomial.X - Polynomial.C c) ^ m).coeff (m - 1) = -(m : ℂ) * c := by
  have h1 : (Polynomial.X - Polynomial.C c) = Polynomial.X + Polynomial.C (-c) := by
    rw [sub_eq_add_neg, map_neg]
  rw [h1, Polynomial.coeff_X_add_C_pow]
  have hsub : m - (m - 1) = 1 := by omega
  rw [hsub]
  have hch : m.choose (m - 1) = m := by
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0) with ⟨k, hk⟩
    subst hk
    simp [Nat.choose_succ_self_right]
  rw [hch]
  ring

/-- A monic complex polynomial `p` whose root multiplicity at `a` equals its degree is the
pure power `(X - C a) ^ p.natDegree`.

Indeed `(X - C a) ^ p.natDegree` divides `p` (`Polynomial.pow_rootMultiplicity_dvd`
together with the hypothesis), both are monic of degree `p.natDegree`, and a monic divisor
of a monic polynomial of the same degree is the polynomial itself. -/
lemma eq_X_sub_C_pow_of_rootMultiplicity_eq_natDegree {p : Polynomial ℂ} {a : ℂ}
    (hmon : p.Monic) (h : p.rootMultiplicity a = p.natDegree) :
    p = (Polynomial.X - Polynomial.C a) ^ p.natDegree := by
  have hmon' : ((Polynomial.X - Polynomial.C a) ^ p.natDegree).Monic :=
    (Polynomial.monic_X_sub_C a).pow _
  have hdvd : (Polynomial.X - Polynomial.C a) ^ p.natDegree ∣ p := by
    have hh := Polynomial.pow_rootMultiplicity_dvd p a
    rwa [h] at hh
  have hdeg : p.natDegree ≤ ((Polynomial.X - Polynomial.C a) ^ p.natDegree).natDegree := by
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
  exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon' hmon hdvd hdeg

/-- A monic complex polynomial `p` of degree `m` whose coefficient of `X ^ (m - 1)` vanishes
but which has some non-zero lower coefficient has a root `a` with `0 < p.rootMultiplicity a < m`.

Since `p` is nonconstant it has a root `a` (`IsAlgClosed.exists_root`), and its multiplicity
is `> 0`. It is `≤ m` because `(X - C a) ^ (p.rootMultiplicity a)` divides `p`. If it were
exactly `m`, then `p = (X - C a) ^ m` (previous lemma) whose coefficient of `X ^ (m - 1)` is
`-(m : ℂ) * a`; this forces `a = 0`, whence `p = X ^ m` has no non-zero lower coefficient,
against the hypothesis. -/
lemma exists_root_multiplicity_lt {m : ℕ} {p : Polynomial ℂ} (hmon : p.Monic)
    (hdeg : p.natDegree = m) (h1 : p.coeff (m - 1) = 0)
    (h2 : ∃ i : ℕ, i < m ∧ p.coeff i ≠ 0) :
    ∃ a : ℂ, 0 < p.rootMultiplicity a ∧ p.rootMultiplicity a < m := by
  obtain ⟨i, hi, hci⟩ := h2
  have hm1 : 1 ≤ m := by omega
  have hp0 : p ≠ 0 := hmon.ne_zero
  have hdegne : p.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hp0, hdeg]
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p hdegne
  have hpos : 0 < p.rootMultiplicity a := (Polynomial.rootMultiplicity_pos hp0).mpr ha
  refine ⟨a, hpos, ?_⟩
  have hcoef : ((Polynomial.X - Polynomial.C a) ^ m).coeff (m - 1) = -(m : ℂ) * a :=
    coeff_X_sub_C_pow a hm1
  have hle : p.rootMultiplicity a ≤ m := by
    have hnd : ((Polynomial.X - Polynomial.C a) ^ p.rootMultiplicity a).natDegree
        = p.rootMultiplicity a := by
      rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
    have hb := ((Polynomial.monic_X_sub_C a).pow _).natDegree_le_of_dvd hp0
        (Polynomial.pow_rootMultiplicity_dvd p a)
    rw [hnd, hdeg] at hb
    exact hb
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exfalso
    have hrootdeg : p.rootMultiplicity a = p.natDegree := by rw [hdeg, heq]
    have hpure : p = (Polynomial.X - Polynomial.C a) ^ p.natDegree :=
      eq_X_sub_C_pow_of_rootMultiplicity_eq_natDegree hmon hrootdeg
    have hc0 : ((Polynomial.X - Polynomial.C a) ^ m).coeff (m - 1) = 0 := by
      have hpm : p = (Polynomial.X - Polynomial.C a) ^ m := by rw [hpure, hdeg]
      rw [← hpm, h1]
    rw [hcoef] at hc0
    have ha0 : a = 0 := by
      have hmne : (m : ℂ) ≠ 0 := by
        simp only [ne_eq, Nat.cast_eq_zero]; omega
      have hmul : (m : ℂ) * a = 0 := by
        rw [neg_mul] at hc0
        exact neg_eq_zero.mp hc0
      exact (mul_eq_zero.mp hmul).resolve_left hmne
    have hpi : p.coeff i = 0 := by
      have hpm : p = Polynomial.X ^ m := by
        rw [hpure, hdeg, ha0]
        simp
      rw [hpm, Polynomial.coeff_X_pow]
      simp only [hi.ne, ↓reduceIte]
    exact hci hpi

theorem root_mult :
    (∀ {p : Polynomial ℂ} {a : ℂ}, p.Monic → p.rootMultiplicity a = p.natDegree →
      p = (Polynomial.X - Polynomial.C a) ^ p.natDegree) ∧
    (∀ {m : ℕ} {p : Polynomial ℂ}, p.Monic → p.natDegree = m → p.coeff (m - 1) = 0 →
      (∃ i : ℕ, i < m ∧ p.coeff i ≠ 0) →
      ∃ a : ℂ, 0 < p.rootMultiplicity a ∧ p.rootMultiplicity a < m) :=
  ⟨fun hmon h => eq_X_sub_C_pow_of_rootMultiplicity_eq_natDegree hmon h,
   fun hmon hdeg h1 h2 => exists_root_multiplicity_lt hmon hdeg h1 h2⟩

end Work.WilC4aP
