import Mathlib
import Submission.Work.HP.Defs

namespace Work.HP.FM4

open Finset

/-- Dyadic majorant for an inverse power: for `1 ≤ t ≤ 2^K` and `d ≥ 1`,
`1/t^d ≤ 2^d * ∑_{j=0}^{K} 2^{-jd}·[t ≤ 2^j]`.

Proof route: let `J` be the least `j` with `t ≤ 2^j` (exists by `htK`, and `J ≤ K`; use
`Nat.find_spec` / `Nat.find_le`). If `J = 0` then `t ≤ 1` and `t ≥ 1` force `t = 1`, so
`1/t^d = 1 ≤ 2^d` and the sum contains the term `1` at `j = 0`. If `J ≥ 1`, minimality
(`Nat.find_min`) gives `t > 2^{J-1}`, hence `1/t^d < 2^{-(J-1)d} = 2^d·2^{-Jd}`, and the sum
contains the term `2^{-Jd} = (1/2)^{Jd}` at `j = J ≤ K` (`Finset.single_le_sum`). -/
lemma inv_pow_le_dyadic (d K : ℕ) {t : ℝ} (hd : 1 ≤ d) (ht1 : 1 ≤ t) (htK : t ≤ (2:ℝ)^K) :
    1 / t ^ d ≤ (2:ℝ)^d * ∑ j ∈ Finset.range (K + 1),
      (if t ≤ (2:ℝ)^j then ((1/2 : ℝ) ^ (j * d)) else 0) := by
  have hex : ∃ j : ℕ, t ≤ (2:ℝ)^j := ⟨K, htK⟩
  obtain ⟨J, hJspec, hJmin, hJK⟩ :
      ∃ J, t ≤ (2:ℝ)^J ∧ (∀ j, j < J → ¬ (t ≤ (2:ℝ)^j)) ∧ J ≤ K :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj, Nat.find_le htK⟩
  have hFnonneg : ∀ i ∈ Finset.range (K+1),
      0 ≤ (if t ≤ (2:ℝ)^i then ((1/2:ℝ)^(i*d)) else 0) := by
    intro i hi; split_ifs with h <;> [positivity; exact le_refl 0]
  have hJmem : J ∈ Finset.range (K+1) := by rw [Finset.mem_range]; omega
  have hsingle := Finset.single_le_sum hFnonneg hJmem
  have hsingle' : (1/2:ℝ)^(J*d) ≤
      ∑ j ∈ Finset.range (K+1), (if t ≤ (2:ℝ)^j then ((1/2:ℝ)^(j*d)) else 0) := by
    rw [ite_eq_left hJspec] at hsingle; exact hsingle
  rcases Nat.eq_zero_or_pos J with hJ0 | hJpos
  · subst hJ0
    have ht_eq : t = 1 := le_antisymm (by simpa using hJspec) ht1
    have hterm0 : (1:ℝ) ≤
        ∑ j ∈ Finset.range (K+1), (if t ≤ (2:ℝ)^j then ((1/2:ℝ)^(j*d)) else 0) := by
      simpa using hsingle'
    calc 1 / t ^ d = 1 := by rw [ht_eq, one_pow, div_one]
      _ ≤ (2:ℝ)^d := one_le_pow₀ (by norm_num)
      _ = (2:ℝ)^d * 1 := by ring
      _ ≤ (2:ℝ)^d * ∑ j ∈ Finset.range (K+1),
            (if t ≤ (2:ℝ)^j then ((1/2:ℝ)^(j*d)) else 0) := by
          apply mul_le_mul_of_nonneg_left hterm0; positivity
  · have hJ1 : 1 ≤ J := hJpos
    have hprev : ¬ (t ≤ (2:ℝ)^(J-1)) := hJmin (J-1) (Nat.sub_lt hJpos (by norm_num))
    have hgt : (2:ℝ)^(J-1) < t := not_le.mp hprev
    have hpowlt : ((2:ℝ)^(J-1))^d < t^d :=
      pow_lt_pow_left₀ hgt (by positivity) (by omega)
    have hdivlt : 1 / t^d < 1 / ((2:ℝ)^(J-1))^d :=
      one_div_lt_one_div_of_lt (by positivity) hpowlt
    have heq1 : 1 / ((2:ℝ)^(J-1))^d = (1/2:ℝ)^((J-1)*d) := by
      rw [← pow_mul, ← one_div_pow]
    have hJd : J * d = (J-1)*d + d := by
      conv_lhs => rw [← Nat.sub_add_cancel hJ1]
      rw [Nat.add_mul, one_mul]
    have heq2 : (2:ℝ)^d * (1/2:ℝ)^(J*d) = (1/2:ℝ)^((J-1)*d) := by
      rw [hJd, pow_add]
      rw [← mul_assoc, mul_comm ((2:ℝ)^d) ((1/2:ℝ)^((J-1)*d)), mul_assoc, ← mul_pow]
      norm_num
    have hbound : 1 / t^d < (2:ℝ)^d * (1/2:ℝ)^(J*d) := by
      rw [heq1, ← heq2] at hdivlt
      exact hdivlt
    calc 1 / t ^ d ≤ (2:ℝ)^d * (1/2:ℝ)^(J*d) := le_of_lt hbound
      _ ≤ (2:ℝ)^d * ∑ j ∈ Finset.range (K+1),
            (if t ≤ (2:ℝ)^j then ((1/2:ℝ)^(j*d)) else 0) := by
          apply mul_le_mul_of_nonneg_left hsingle'; positivity

end Work.HP.FM4
