import Mathlib
import Submission.Work.LinnikAreas.JutilaPieces.S3BracketExpand

namespace Work.LinnikAreas.JutilaPieces

/-- **Bracket instantiation of the `S₃` assembly** (the wrapper making the product-level expansion
usable at `ε = 2·(qrt)/N` without waiting on `S3LogExpansion`).  Given `|A − a| ≤ ε`, `|B − b| ≤ ε`,
`|a − 1| ≤ K`, `|b − 1| ≤ K` with `ε, K ≥ 0`,

  `|(A − 1)(B − 1) − (a − 1)(b − 1)| ≤ ε·(2K + ε)`.

Proof (two lines): `Work.LinnikAreas.JutilaPieces.S3BracketExpand` (proved) gives
`|·| ≤ ε·(|a − 1| + |b − 1| + ε)`; `|a − 1| + |b − 1| ≤ 2K`; monotonicity in `ε ≥ 0`.  The bound is
*sharp*: at `A = a + ε = 1 + K + ε`, `B = b + ε` both sides equal `2Kε + ε²`.  (`hK` is only for
interface clarity — `ha`, `hb` already force `K ≥ 0` when satisfiable.)

Intended instantiation: `A = log(⌊N/(qrt)⌋t/z)`, `B = log(⌊N/(qrt)⌋r/z)`,
`a = log(N/(qrt)) − log(z/t)`, `b = log(N/(qrt)) − log(z/r)`, `ε = 2(qrt)/N`, the closeness
hypotheses being `S3LogExpansion`; the caller instantiates `K` to control `|a − 1|`, `|b − 1|`
(the `O((qrt/N)(1+|ℓ_t|)(1+|ℓ_r|))` shape needs those separately). -/
theorem S3BracketExpandBounded {A B a b ε K : ℝ} (hA : |A - a| ≤ ε) (hB : |B - b| ≤ ε)
    (ha : |a - 1| ≤ K) (hb : |b - 1| ≤ K) (hε : 0 ≤ ε) (hK : 0 ≤ K) :
    |(A - 1) * (B - 1) - (a - 1) * (b - 1)| ≤ ε * (2 * K + ε) := by
  have hbase := S3BracketExpand hA hB hε
  have hsum : |a - 1| + |b - 1| ≤ 2 * K := by linarith
  calc |(A - 1) * (B - 1) - (a - 1) * (b - 1)|
      ≤ ε * (|a - 1| + |b - 1| + ε) := hbase
    _ ≤ ε * (2 * K + ε) := by
        apply mul_le_mul_of_nonneg_left _ hε
        linarith

end Work.LinnikAreas.JutilaPieces
