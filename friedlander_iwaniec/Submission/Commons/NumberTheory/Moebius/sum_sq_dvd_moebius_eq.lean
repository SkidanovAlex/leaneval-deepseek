import Mathlib
import Submission.Commons.NumberTheory.Moebius.sum_moebius_divisors
import Submission.Commons.NumberTheory.FriedlanderIwaniec.square_divisor_max_characterization

/-!
# A square-divisor identity for the Möbius function

`∑_{d | n, d² | n} μ(d) = μ(n)²`:  the only divisors `d` of `n` whose square divides `n`
are the divisors of the (divisibility-)largest square root `s` of a square divisor of `n`,
and `∑_{d | s} μ(d)` vanishes unless `s = 1`, which happens exactly when `n` is squarefree.
-/

namespace Commons.NumberTheory.Moebius

open scoped ArithmeticFunction.Moebius

theorem sum_sq_dvd_moebius_eq (n : ℕ) :
    (∑ d ∈ n.divisors, (if d ^ 2 ∣ n then ArithmeticFunction.moebius d else 0)) =
      (ArithmeticFunction.moebius n) ^ 2 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Nat.divisors_zero]
  · -- `s` is the largest `e` with `e ^ 2 ∣ n`, i.e. the square root of the largest square
    -- divisor of `n`.
    set s := ∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2) with hs_def
    obtain ⟨hsq, _hsqfree, hmax⟩ :=
      Commons.NumberTheory.FriedlanderIwaniec.square_divisor_max_characterization
        (Nat.pos_of_ne_zero hn)
    rw [← hs_def] at hsq hmax
    have hs_ne : s ≠ 0 := by
      intro hs0
      have h0 : (0 : ℕ) ∣ n := by rw [hs0] at hsq; simpa using hsq
      exact hn (Nat.zero_dvd.mp h0)
    -- The divisors `d` of `n` with `d ^ 2 ∣ n` are exactly the divisors of `s`.
    have hfilt : n.divisors.filter (fun d => d ^ 2 ∣ n) = s.divisors := by
      ext d
      rw [Finset.mem_filter, Nat.mem_divisors, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨_hdn, _hn0⟩, hdvd⟩
        exact ⟨hmax d hdvd, hs_ne⟩
      · rintro ⟨hds, _hs0⟩
        exact ⟨⟨(hds.trans (dvd_pow_self s (by norm_num))).trans hsq,
          hn⟩, (pow_dvd_pow_of_dvd hds 2).trans hsq⟩
    -- `s = 1` exactly when `n` is squarefree.
    have hs_sf : s = 1 ↔ Squarefree n := by
      constructor
      · intro hs1
        by_contra hnsf
        simp only [Squarefree] at hnsf
        push Not at hnsf
        obtain ⟨x, hxdvd, hxunit⟩ := hnsf
        have hx1 : x = 1 := Nat.dvd_one.mp (hs1 ▸ hmax x (by rw [pow_two]; exact hxdvd))
        exact hxunit (by rw [hx1]; exact isUnit_one)
      · intro hsf
        exact Nat.isUnit_iff.mp (hsf s (by simpa [pow_two] using hsq))
    rw [← Finset.sum_filter, hfilt, Commons.NumberTheory.Moebius.sum_moebius_divisors,
      ArithmeticFunction.moebius_sq]
    by_cases h : Squarefree n
    · have hs1 : s = 1 := hs_sf.mpr h
      simp [hs1, h]
    · have hs1 : s ≠ 1 := fun h1 => h (hs_sf.mp h1)
      simp [hs1, h]

end Commons.NumberTheory.Moebius
