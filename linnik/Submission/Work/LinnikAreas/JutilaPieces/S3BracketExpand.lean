import Mathlib

namespace Work.LinnikAreas.JutilaPieces

/-- **Product-level expansion for the `S₃` bracket** (Step 2 of the `S3MainTerm` bookkeeping; pure
Mathlib, no import).  If `A` is within `ε` of `a` and `B` within `ε` of `b`, then `(A − 1)(B − 1)`
is within `ε(|a−1| + |b−1| + ε)` of `(a − 1)(b − 1)`:

  `|(A − 1)(B − 1) − (a − 1)(b − 1)| ≤ ε·(|a − 1| + |b − 1| + ε)`.

Proof (about 15 lines; the reviewer compiled it in this workspace): the identity
`(A−1)(B−1) − (a−1)(b−1) = (A−a)(B−1) + (a−1)(B−b)` together with
`|B − 1| ≤ |B − b| + |b − 1| ≤ ε + |b − 1|` gives
`|·| ≤ ε(|b−1| + ε) + |a−1|·ε = ε(|a−1| + |b−1| + ε)`; the argument is uniform in `ℝ` and survives
`ε = 0`.  The `+1` in the target bracket
`(log(⌊N/(qrt)⌋t/z) − 1)(log(⌊N/(qrt)⌋r/z) − 1) + 1` cancels in the difference, so it is
intentionally absent here.

Instantiation for the caller: `A = log(⌊N/(qrt)⌋·t/z)`, `B = log(⌊N/(qrt)⌋·r/z)`,
`a = log(N/(qrt)) − log(z/t)`, `b = log(N/(qrt)) − log(z/r)`, `ε = 2·(qrt)/N`, the two closeness
hypotheses being supplied by `S3LogExpansion` (in flight, `JutilaPieces/S3LogExpansion.lean`).  The
caller must also supply `|a − 1|, |b − 1| ≲ 1 + |ℓ|` if the `O((qrt/N)(1+|ℓ_t|)(1+|ℓ_r|))` shape is
wanted: this result gives only the raw `ε(|a−1| + |b−1| + ε)`. -/
theorem S3BracketExpand {A B a b ε : ℝ} (hA : |A - a| ≤ ε) (hB : |B - b| ≤ ε) (hε : 0 ≤ ε) :
    |(A - 1) * (B - 1) - (a - 1) * (b - 1)| ≤ ε * (|a - 1| + |b - 1| + ε) := by
  have hid : (A - 1) * (B - 1) - (a - 1) * (b - 1)
      = (A - a) * (B - 1) + (a - 1) * (B - b) := by ring
  rw [hid]
  have hBnd : |B - 1| ≤ ε + |b - 1| := by
    have hsum : B - 1 = (B - b) + (b - 1) := by ring
    calc |B - 1| = |(B - b) + (b - 1)| := by rw [hsum]
      _ ≤ |B - b| + |b - 1| := abs_add_le _ _
      _ ≤ ε + |b - 1| := by linarith
  have h1 : |(A - a) * (B - 1)| ≤ ε * (ε + |b - 1|) := by
    rw [abs_mul]
    exact mul_le_mul hA hBnd (abs_nonneg _) hε
  have h2 : |(a - 1) * (B - b)| ≤ |a - 1| * ε := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hB (abs_nonneg _)
  calc |(A - a) * (B - 1) + (a - 1) * (B - b)|
      ≤ |(A - a) * (B - 1)| + |(a - 1) * (B - b)| := abs_add_le _ _
    _ ≤ ε * (ε + |b - 1|) + |a - 1| * ε := add_le_add h1 h2
    _ = ε * (|a - 1| + |b - 1| + ε) := by ring

end Work.LinnikAreas.JutilaPieces
