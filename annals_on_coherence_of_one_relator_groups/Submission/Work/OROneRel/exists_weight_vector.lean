import Mathlib

set_option linter.unusedVariables false

namespace Work.OROneRel

/-- For nonzero integers `m n : ℤ`, the kernel of the map `ℤ × ℤ → ℤ`, `(x, y) ↦ x * m + y * n`,
contains a *primitive* vector `(cx, cy)` — i.e. a vector `(cx, cy)` satisfying
`cx * m + cy * n = 0` and which is unimodular, `p * cx + q * cy = 1` for suitable `p q : ℤ`.

Explicitly, with `g = gcd m n`, by `Int.exists_gcd_one` there are `m' n'` with
`m = m' * g`, `n = n' * g` and `gcd m' n' = 1`; then `(cx, cy) = (n', -m')` is such a vector,
and `p q` are read off from Bézout's identity for `m', n'`. -/
theorem exists_weight_vector {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0) :
    ∃ (cx cy p q : ℤ), cx * m + cy * n = 0 ∧ p * cx + q * cy = 1 := by
  have H : 0 < m.gcd n := Int.gcd_pos_of_ne_zero_left n hm
  obtain ⟨m', n', hgcd, hm', hn'⟩ := Int.exists_gcd_one H
  -- Make the common factor `g = gcd m n` an opaque atom, so that rewriting by `hm', hn'`
  -- does not also rewrite inside `↑(m.gcd n)`.
  set g : ℤ := (m.gcd n : ℤ)
  refine ⟨n', -m', m'.gcdB n', -(m'.gcdA n'), ?_, ?_⟩
  · rw [hm', hn']; ring
  · -- Bézout for the primitive pair `(m', n')`.
    have hbez : m' * m'.gcdA n' + n' * m'.gcdB n' = 1 := by
      have h := Int.gcd_eq_gcd_ab m' n'
      rw [hgcd] at h
      simpa using h.symm
    nlinarith [hbez]

end Work.OROneRel
