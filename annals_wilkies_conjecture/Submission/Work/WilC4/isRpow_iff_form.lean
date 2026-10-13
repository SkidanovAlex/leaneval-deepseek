import Mathlib
import Submission.Work.WilC4.Defs
import Submission.Work.WilC4.isRpow_canon
import Submission.Work.WilC4.mul_pow_toNat_eq_iff

namespace Work.WilC4

/-- **The `LRc`-form of `IsRpow`, saturated.**  For `x > 0` and `n > 0`, the relation
`IsRpow x (p / n) t` is equivalent to the *single* polynomial condition

`t ^ n * x ^ (-p).toNat = x ^ p.toNat`

(i.e. `t^n = x^p` written with nonnegative exponents, `p.toNat` and `(-p).toNat`), together with
the positivity condition `t = 0 ∨ ∃ w ≠ 0, w ^ 2 = t`.

The content is `isRpow_canon` (the relation is saturated: it holds exactly for `t^n = x^p` plus
the square condition) and the arithmetic identity `t^n * x ^ (-p).toNat = x ^ p.toNat ↔ t^n = x^p`
(`mul_pow_toNat_eq_iff`), which is just `p = p.toNat - (-p).toNat` plus `x ≠ 0`. -/
theorem isRpow_iff_form {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] {x t : M} {p : ℤ} {n : ℕ} (hn : 0 < n) (hx : 0 < x) : Work.WilC4.IsRpow x ((p : ℚ) / (n : ℚ)) t ↔ (t = 0 ∨ ∃ w : M, w ≠ 0 ∧ w ^ 2 = t) ∧ t ^ n * x ^ (-p).toNat = x ^ p.toNat := by
  rw [isRpow_canon hn hx]
  have h : t ^ n * x ^ (-p).toNat = x ^ p.toNat ↔ t ^ n = x ^ p :=
    mul_pow_toNat_eq_iff (ne_of_gt hx) p n
  exact ⟨fun ⟨hpow, hsq⟩ => ⟨hsq, h.mpr hpow⟩, fun ⟨hsq, hmul⟩ => ⟨h.mp hmul, hsq⟩⟩

end Work.WilC4
