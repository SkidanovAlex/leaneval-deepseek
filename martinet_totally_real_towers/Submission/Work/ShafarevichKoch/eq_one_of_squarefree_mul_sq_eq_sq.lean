import Mathlib

namespace Work.ShafarevichKoch

/-- If a squarefree natural number `d` satisfies `d * m ^ 2 = n ^ 2` with `m ≠ 0` (i.e. `d` is
the square of the rational number `n/m`), then `d = 1`.  Hints: from `d * m^2 = n^2` and `m ≠ 0`
one gets `d = (n/m)^2`; comparing the `p`-adic valuations (`Nat.factorization`) of `d * m^2` and
`n^2` gives `v_p(d) = 2(v_p(n) - v_p(m))` even for every prime `p`; a squarefree `d` all of whose
valuations are even equals `1`. -/
theorem eq_one_of_squarefree_mul_sq_eq_sq {d m n : ℕ} (hd : Squarefree d) (hm : m ≠ 0)
    (h : d * m ^ 2 = n ^ 2) : d = 1 := by
  -- `d ≠ 0`, being squarefree.
  have hd0 : d ≠ 0 := hd.ne_zero
  -- `n ≠ 0`, since otherwise `d * m ^ 2 = 0` with `m ≠ 0` forces `d = 0`.
  have hn0 : n ≠ 0 := by
    rintro rfl
    have h' : d * m ^ 2 = 0 := by simpa using h
    rcases Nat.mul_eq_zero.mp h' with hd' | hm'
    · exact hd0 hd'
    · exact pow_ne_zero 2 hm hm'
  -- Every `p`-adic valuation of `d` vanishes.
  have key : ∀ p : ℕ, d.factorization p = 0 := by
    intro p
    by_cases hp : Nat.Prime p
    · -- For a prime, comparing valuations of `d * m^2` and `n^2` gives
      -- `v_p(d) + 2 v_p(m) = 2 v_p(n)`, so `v_p(d)` is even; squarefreeness bounds it by `1`.
      have hfac : d.factorization p + 2 * m.factorization p = 2 * n.factorization p := by
        have h1 : (d * m ^ 2).factorization p
            = d.factorization p + 2 * m.factorization p := by
          rw [Nat.factorization_mul hd0 (pow_ne_zero 2 hm), Nat.factorization_pow,
            Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
        have h2 : (n ^ 2).factorization p = 2 * n.factorization p := by
          rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
        rw [h, h2] at h1
        exact h1.symm
      have hle : d.factorization p ≤ 1 := (Nat.squarefree_iff_factorization_le_one hd0).mp hd p
      omega
    · -- For a non-prime the valuation vanishes automatically.
      exact (Nat.factorization_eq_zero_iff d p).mpr (Or.inl hp)
  have hzero : d.factorization = 0 := Finsupp.ext key
  -- A natural number all of whose valuations vanish is `0` or `1`.
  rcases (Nat.factorization_eq_zero_iff' d).mp hzero with h0 | h1
  · exact absurd h0 hd0
  · exact h1

end Work.ShafarevichKoch
