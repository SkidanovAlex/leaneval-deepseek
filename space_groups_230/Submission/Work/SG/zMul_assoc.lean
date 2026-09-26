import Mathlib
import Submission.Work.SG.SGprelude
import Submission.Work.SG.imatOfList_inj

import Submission.Work.SG.zassoc_m9mul_assoc
import Submission.Work.SG.zassoc_m9vecZ_m9mul
import Submission.Work.SG.zassoc_m9vecZ_add
import Submission.Work.SG.zassoc_emodList_zipWith_add
import Submission.Work.SG.zassoc_emodList_zipWith_m9vecZ
import Submission.Work.SG.zassoc_zipWith_add_assoc

namespace Work.SG

/-!
# `zMul_assoc`: associativity of the integer affine product

`zMul d p q = (p.1 * q.1, (p.2 + p.1 · q.2) mod d)` is the `ℤ`-mirror (`SGprelude`) of the
affine product `sgMulPair`: pairs `(A, u)` encoding the affine map `x ↦ A x + u/d` modulo `ℤ³`.
The matrix part is automatically associative (`zassoc_m9mul_assoc`); the whole content is that
the translation part is associative modulo `d`, which is the pointwise congruence

`(u + A·v) + A·B·w ≡ u + A·((v + B·w) mod d)   (mod d)`.

The proof below reduces it to five elementary list identities about the `getD`-based flat
matrix–vector product `m9vecZ` and the componentwise reduction `emodList` (all proved in the
sibling modules), by rewriting the left-hand side into the shape of the right-hand side:

`emodList d (e₁ + A·B·w)` with `e₁ = emodList d (u + A·v)`
* `zassoc_emodList_zipWith_add` : the outer reduction absorbs the inner one,
* `zassoc_zipWith_add_assoc`      : regroup the pointwise sums,
* `zassoc_m9vecZ_m9mul`           : `A·B·w = A·(B·w)`,
* `zassoc_m9vecZ_add`             : `A·v + A·(B·w) = A·(v + B·w)` (needs `|v| = |B·w| = 3`),
* `zassoc_emodList_zipWith_m9vecZ`: the final reduction absorbs `(v + B·w) mod d`.

No hypothesis on the matrices is used.  Of the three length hypotheses only `hq` is needed:
the additivity step requires the two summands `q.2` and `m9vecZ q.1 r.2` to have the same length
(`List.zipWith` truncates), and `m9vecZ _ _` always has length `3`.  The statement really does
need it: for `d = 3`,
```
p = ([0,0,1, 1,0,0, 0,1,0], [0,0,0])   q = ([0,1,0, 0,0,1, 1,0,0], [1])   r = ([1,1,0, 0,1,0, 0,0,1], [0,1,2])
```
the two sides have translations `[0,2,2]` and `[0,2,0]`.  The hypotheses `hp`, `hr` belong to the
requested statement but are not used by this proof.
-/

/-- `m9vecZ a v` has exactly three entries (it is a `List.map` over `List.range 3`). -/
private theorem m9vecZ_length (a v : List ℤ) : (m9vecZ a v).length = 3 := by
  simp [m9vecZ]

/-- `zMul` is associative on pairs with three numerators (integer arithmetic modulo `d`). -/
theorem zMul_assoc {d : ℕ} {p q r : List ℤ × List ℤ} (hp : p.2.length = 3) (hq : q.2.length = 3)
    (hr : r.2.length = 3) : zMul d (zMul d p q) r = zMul d p (zMul d q r) := by
  apply Prod.ext
  · -- matrix components: `(p.1 * q.1) * r.1 = p.1 * (q.1 * r.1)`
    simp only [zMul]
    rw [zassoc_m9mul_assoc]
  · -- translation components
    simp only [zMul]
    rw [zassoc_emodList_zipWith_add, zassoc_zipWith_add_assoc, zassoc_m9vecZ_m9mul,
      ← zassoc_m9vecZ_add p.1 q.2 (m9vecZ q.1 r.2) (by rw [hq, m9vecZ_length]),
      ← zassoc_emodList_zipWith_m9vecZ d p.2 p.1 (List.zipWith (· + ·) q.2 (m9vecZ q.1 r.2))]

end Work.SG
