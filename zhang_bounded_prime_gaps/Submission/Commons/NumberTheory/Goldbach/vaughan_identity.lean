import Mathlib
import Submission.Commons.NumberTheory.ArithmeticFunction.vonMangoldt_eq_vaughan_sum

namespace Commons.NumberTheory.Goldbach

open Finset
open scoped BigOperators

/-- For `1 ≤ n`, the divisors of `n` that are `≤ U` are exactly the elements of
`Icc 1 U` dividing `n`. -/
private theorem divisors_filter_le_eq_Icc_filter (n U : ℕ) (hn : 1 ≤ n) :
    n.divisors.filter (fun d => d ≤ U) = (Finset.Icc 1 U).filter (fun d => d ∣ n) := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hdiv, _⟩, hdU⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hdiv (by omega), hdU⟩, hdiv⟩
  · rintro ⟨⟨hd1, hdU⟩, hdiv⟩
    exact ⟨⟨hdiv, by omega⟩, hdU⟩

/-- For `1 ≤ n` and `d ∣ n`, the `e ∈ Icc 1 V` with `d * e ∣ n` are exactly the
divisors of `n / d` that are `≤ V`. -/
private theorem Icc_filter_mul_dvd_eq_divisors_filter (n V d : ℕ) (hn : 1 ≤ n) (hd : d ∣ n) :
    (Finset.Icc 1 V).filter (fun e => d * e ∣ n)
      = (n / d).divisors.filter (fun e => e ≤ V) := by
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd (by omega)
  have hnd : 0 < n / d := Nat.div_pos (Nat.le_of_dvd (by omega) hd) hdpos
  ext e
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨he1, heV⟩, hde⟩
    exact ⟨⟨(Nat.dvd_div_iff_mul_dvd hd).mpr hde, hnd.ne'⟩, heV⟩
  · rintro ⟨⟨hediv, _⟩, heV⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hediv hnd, heV⟩, Nat.mul_dvd_of_dvd_div hd hediv⟩

/-- The `e ∈ Icc (V+1) m` dividing `m` are exactly the divisors of `m` that are `> V`. -/
private theorem Icc_filter_dvd_eq_divisors_filter_gt (m V : ℕ) :
    (Finset.Icc (V + 1) m).filter (fun e => e ∣ m) = m.divisors.filter (fun e => V < e) := by
  ext e
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨h1, h2⟩, hdiv⟩
    exact ⟨⟨hdiv, by omega⟩, by omega⟩
  · rintro ⟨⟨hdiv, hm0⟩, hV⟩
    exact ⟨⟨by omega, Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdiv⟩, hdiv⟩

/-- For `1 ≤ n`, the `d ∈ Icc (U+1) n` dividing `n` are exactly the divisors of `n`
that are `> U`. -/
private theorem Icc_filter_dvd_eq_divisors_filter_gt' (n U : ℕ) (hn : 1 ≤ n) :
    (Finset.Icc (U + 1) n).filter (fun d => d ∣ n) = n.divisors.filter (fun d => U < d) := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨h1, h2⟩, hdiv⟩
    exact ⟨⟨hdiv, by omega⟩, by omega⟩
  · rintro ⟨⟨hdiv, _⟩, hU⟩
    exact ⟨⟨by omega, Nat.le_of_dvd (by omega) hdiv⟩, hdiv⟩

theorem vaughan_identity (n U V : ℕ) (hn : 1 ≤ n) (hV : V < n) :
    ArithmeticFunction.vonMangoldt n
      = (∑ d ∈ (Finset.Icc 1 U).filter (fun d => d ∣ n),
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log ((n : ℝ) / (d : ℝ)))
        - (∑ d ∈ (Finset.Icc 1 U).filter (fun d => d ∣ n),
            ∑ e ∈ Finset.Icc 1 V, if d * e ∣ n then
              ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e
              else 0)
        + (∑ d ∈ Finset.Icc (U + 1) n, if d ∣ n then
              ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
                (∑ e ∈ Finset.Icc (V + 1) (n / d), if e ∣ (n / d) then
                    ArithmeticFunction.vonMangoldt e else 0)
              else 0) := by
  have key := Commons.NumberTheory.ArithmeticFunction.vonMangoldt_eq_vaughan_sum n U V hV
  rw [key]
  have hA :
      (∑ d ∈ (Finset.Icc 1 U).filter (fun d => d ∣ n),
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log ((n : ℝ) / (d : ℝ)))
      = (∑ d ∈ n.divisors.filter (fun d => d ≤ U),
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) * Real.log (((n / d : ℕ) : ℝ))) := by
    rw [← divisors_filter_le_eq_Icc_filter n U hn]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    rw [Nat.cast_div_charZero hd.1.1]
  have hB :
      (∑ d ∈ (Finset.Icc 1 U).filter (fun d => d ∣ n),
            ∑ e ∈ Finset.Icc 1 V, if d * e ∣ n then
              ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e
              else 0)
      = (∑ d ∈ n.divisors.filter (fun d => d ≤ U),
            ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ V),
              ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e) := by
    rw [← divisors_filter_le_eq_Icc_filter n U hn]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    rw [← Finset.sum_filter]
    rw [Icc_filter_mul_dvd_eq_divisors_filter n V d hn hd.1.1]
  have hC :
      (∑ d ∈ Finset.Icc (U + 1) n, if d ∣ n then
              ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
                (∑ e ∈ Finset.Icc (V + 1) (n / d), if e ∣ (n / d) then
                    ArithmeticFunction.vonMangoldt e else 0)
              else 0)
      = (∑ d ∈ n.divisors.filter (fun d => U < d),
            ∑ e ∈ (n / d).divisors.filter (fun e => V < e),
              ((ArithmeticFunction.moebius d : ℤ) : ℝ) * ArithmeticFunction.vonMangoldt e) := by
    rw [← Finset.sum_filter]
    rw [Icc_filter_dvd_eq_divisors_filter_gt' n U hn]
    apply Finset.sum_congr rfl
    intro d _
    rw [← Finset.sum_filter]
    rw [Icc_filter_dvd_eq_divisors_filter_gt (n / d) V]
    rw [Finset.mul_sum]
  rw [hA, hB, hC]

end Commons.NumberTheory.Goldbach
