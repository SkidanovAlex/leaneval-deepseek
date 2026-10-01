import Mathlib
import Submission.Work.ZeroDensity.Jutila.sieveSymbolDefs
import Submission.Work.LinnikAreas.Density4.sum_Icc_filter_dvd_reindex

namespace Work.LinnikAreas.JutilaPieces

/--
`W V l = Σ_{l ∣ d ≤ V} μ(d)/d` factors as `μ(l)/l · U(V/l, l)`, where
`U y l = Σ_{m ≤ y, (m,l)=1} μ(m)/m`.

Reindexing the sum over the multiples of `l` as `d = l·m`, the summand satisfies
`μ(l·m)/(l·m) = (μ l/l)·(μ m/m)` when `(m,l)=1` (multiplicativity of `μ`), and
`μ(l·m) = 0` otherwise (since then `l·m` has a repeated prime factor and hence is
not squarefree). Pulling out the constant `μ(l)/l` leaves exactly `U (V/l) l`.
-/
theorem W_eq (V l : ℕ) (hl : 1 ≤ l) :
    Work.ZeroDensity.Jutila.W V l
      = (ArithmeticFunction.moebius l : ℝ) / (l : ℝ) * Work.ZeroDensity.Jutila.U (V / l) l := by
  unfold Work.ZeroDensity.Jutila.W Work.ZeroDensity.Jutila.U
  rw [Work.LinnikAreas.Density4.sum_Icc_filter_dvd_reindex V l hl
        (fun d => (ArithmeticFunction.moebius d : ℝ) / (d : ℝ))]
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases h : Nat.Coprime m l
  · rw [if_pos h]
    have hmul : ArithmeticFunction.moebius (l * m)
        = ArithmeticFunction.moebius l * ArithmeticFunction.moebius m := by
      rw [mul_comm l m,
          ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h, mul_comm]
    have hcast : (ArithmeticFunction.moebius (l * m) : ℝ)
        = (ArithmeticFunction.moebius l : ℝ) * (ArithmeticFunction.moebius m : ℝ) := by
      rw [hmul, Int.cast_mul]
    rw [hcast, Nat.cast_mul, div_mul_div_comm]
  · rw [if_neg h]
    have hzero : ArithmeticFunction.moebius (l * m) = 0 := by
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree]
      intro hs
      obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd h
      have hpm : p ∣ m := hpg.trans (Nat.gcd_dvd_left m l)
      have hpl : p ∣ l := hpg.trans (Nat.gcd_dvd_right m l)
      exact (Nat.squarefree_iff_prime_squarefree.mp hs) p hp (mul_dvd_mul hpl hpm)
    rw [hzero]
    simp

end Work.LinnikAreas.JutilaPieces
