import Mathlib
import Submission.Work.HP.MDEstimates.moebius_multiples_sum

namespace Work.HP.MDEstimates

open ArithmeticFunction

/-- The `LSeries` of the constant sequence `1` at `s : ℂ` (with `s` the coercion of a real
`1 < s`) is the coercion of the real `ℕ+`-series `∑' n : ℕ+, 1 / (n : ℝ) ^ s`.

This is just the index comparison between `LSeries` (a `tsum` over `ℕ`, where the term at `0`
vanishes) and the `tsum` over the positive naturals. -/
lemma LSeries_one_eq_ofReal_tsum (s : ℝ) (hs : 1 < s) :
    LSeries (1 : ℕ → ℂ) (s : ℂ) = ((∑' n : ℕ+, 1 / (n : ℝ) ^ s : ℝ) : ℂ) := by
  have hsC : (1 : ℝ) < (s : ℂ).re := by simpa using hs
  have hsum : Summable (fun n : ℕ => LSeries.term (1 : ℕ → ℂ) (s : ℂ) n) :=
    LSeriesSummable_one_iff.mpr hsC
  have hsplit : (∑' n : ℕ, LSeries.term (1 : ℕ → ℂ) (s : ℂ) n)
      = ∑' n : ℕ, LSeries.term (1 : ℕ → ℂ) (s : ℂ) (n + 1) := by
    rw [hsum.tsum_eq_zero_add]; simp
  rw [LSeries, hsplit,
    ← tsum_pnat_eq_tsum_succ (f := fun n : ℕ => LSeries.term (1 : ℕ → ℂ) (s : ℂ) n)]
  trans ∑' n : ℕ+, ((1 / (n : ℝ) ^ s : ℝ) : ℂ)
  · apply tsum_congr; intro n
    rw [LSeries.term_of_ne_zero (by exact_mod_cast n.pos.ne'), Complex.ofReal_div,
      Complex.ofReal_one]
    congr 1
    rw [← Complex.ofReal_natCast (n : ℕ)]
    exact (Complex.ofReal_cpow (Nat.cast_nonneg (n : ℕ)) s).symm
  · exact (Complex.ofReal_tsum _).symm

/-- The `LSeries` of the Möbius function at `s : ℂ` (with `s` the coercion of a real `1 < s`)
is the coercion of the real `ℕ+`-series `∑' n : ℕ+, μ n / (n : ℝ) ^ s`.

Same index comparison as `LSeries_one_eq_ofReal_tsum`, together with the compatibility of the
complex and real casts of the integers `μ n`. -/
lemma LSeries_moebius_eq_ofReal_tsum (s : ℝ) (hs : 1 < s) :
    LSeries (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) (s : ℂ) =
      ((∑' n : ℕ+, (ArithmeticFunction.moebius (n : ℕ) : ℝ) / (n : ℝ) ^ s : ℝ) : ℂ) := by
  have hsC : (1 : ℝ) < (s : ℂ).re := by simpa using hs
  have hsum : Summable (fun n : ℕ =>
      LSeries.term (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) (s : ℂ) n) :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hsC
  have hsplit : (∑' n : ℕ,
        LSeries.term (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) (s : ℂ) n)
      = ∑' n : ℕ,
        LSeries.term (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) (s : ℂ) (n + 1) := by
    rw [hsum.tsum_eq_zero_add]; simp
  rw [LSeries, hsplit,
    ← tsum_pnat_eq_tsum_succ
      (f := fun n : ℕ =>
        LSeries.term (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ)) (s : ℂ) n)]
  trans ∑' n : ℕ+, (((ArithmeticFunction.moebius (n : ℕ) : ℝ) / (n : ℝ) ^ s : ℝ) : ℂ)
  · apply tsum_congr; intro n
    rw [LSeries.term_of_ne_zero (by exact_mod_cast n.pos.ne')]
    rw [Complex.ofReal_div]
    congr 1
    rw [← Complex.ofReal_natCast (n : ℕ)]
    exact (Complex.ofReal_cpow (Nat.cast_nonneg (n : ℕ)) s).symm
  · exact (Complex.ofReal_tsum _).symm

/-- The Dirichlet series of the Möbius function and the Riemann zeta series multiply to `1`:
`(∑' n, μ n / n^s) * (∑' n, 1 / n^s) = 1` for real `s > 1`.

Both series are here indexed by the positive naturals `ℕ+`.  Since `s` is real, the complex
`LSeries` of the constant sequence `1` and of `μ` are the coercions of these real series, and
Mathlib's identity `LSeries 1 s * LSeries ↗μ s = 1` on `re s > 1` transports along
`Complex.ofReal_injective`. -/
theorem moebius_zeta_tsum_mul (s : ℝ) (hs : 1 < s) :
    (∑' n : ℕ+, (ArithmeticFunction.moebius (n : ℕ) : ℝ) / (n : ℝ) ^ s) *
      (∑' n : ℕ+, 1 / (n : ℝ) ^ s) = 1 := by
  have hsC : (1 : ℝ) < (s : ℂ).re := by simpa using hs
  have h1 := LSeries_one_mul_Lseries_moebius (s := (s : ℂ)) hsC
  rw [LSeries_one_eq_ofReal_tsum s hs, LSeries_moebius_eq_ofReal_tsum s hs] at h1
  refine Complex.ofReal_injective ?_
  rw [Complex.ofReal_mul, Complex.ofReal_one, mul_comm]
  exact h1

end Work.HP.MDEstimates
