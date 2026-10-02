import Mathlib
import Submission.Work.SeedCertNum.Box
import Submission.Work.SeedCertNum.IV_mem_mul

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertNum

open Work.SeedCert

/-- Membership in `CBox.toSet` gives membership of the real part in `CBox.re` and of the
imaginary part in `CBox.im`. -/
private theorem mem_re {B : CBox} {z : ℂ} (hz : z ∈ B.toSet) : z.re ∈ (B.re).toSet :=
  ⟨hz.1, hz.2.1⟩

private theorem mem_im {B : CBox} {z : ℂ} (hz : z ∈ B.toSet) : z.im ∈ (B.im).toSet :=
  ⟨hz.2.2.1, hz.2.2.2⟩

/-- **Soundness of the complex box product** `Work.SeedCert.CBox.mul`, whose real part is the
interval `(B.re.mul C.re).sub (B.im.mul C.im)` and whose imaginary part is
`(B.re.mul C.im).add (B.im.mul C.re)` (`Work.SeedCert.IV.mul`, `.add`, `.sub`; see
`Work.SeedCert.CBox.mul`).

If `z ∈ B.toSet` and `w ∈ C.toSet` then `z * w ∈ (B.mul C).toSet`.

Proof: `(z*w).re = z.re*w.re - z.im*w.im` (`Complex.mul_re`) so it lies in the interval
`IV.sub (IV.mul B.re C.re) (IV.mul B.im C.im)` by `IV_mem_mul`, `IV.mem_sub`; and
`(z*w).im = z.re*w.im + z.im*w.re` (`Complex.mul_im`) likewise.  Unfold `CBox.mul` and
`CBox.toSet`, and use `IV.mem_toSet`. -/
theorem CBox_mem_mul {B C : Work.SeedCert.CBox} {z w : ℂ} (hz : z ∈ B.toSet)
    (hw : w ∈ C.toSet) : z * w ∈ (B.mul C).toSet := by
  have hzre : z.re ∈ (B.re).toSet := mem_re hz
  have hzim : z.im ∈ (B.im).toSet := mem_im hz
  have hwre : w.re ∈ (C.re).toSet := mem_re hw
  have hwim : w.im ∈ (C.im).toSet := mem_im hw
  -- real part: `z.re*w.re - z.im*w.im ∈ (B.re.mul C.re).sub (B.im.mul C.im)`
  have hA : z.re * w.re - z.im * w.im ∈ ((B.re.mul C.re).sub (B.im.mul C.im)).toSet :=
    IV.mem_sub (IV_mem_mul hzre hwre) (IV_mem_mul hzim hwim)
  -- imaginary part: `z.re*w.im + z.im*w.re ∈ (B.re.mul C.im).add (B.im.mul C.re)`
  have hB : z.re * w.im + z.im * w.re ∈ ((B.re.mul C.im).add (B.im.mul C.re)).toSet :=
    IV.mem_add (IV_mem_mul hzre hwim) (IV_mem_mul hzim hwre)
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ((B.re.mul C.re).sub (B.im.mul C.im)).lo.toReal ≤ (z * w).re
    rw [Complex.mul_re]
    exact hA.1
  · show (z * w).re ≤ ((B.re.mul C.re).sub (B.im.mul C.im)).hi.toReal
    rw [Complex.mul_re]
    exact hA.2
  · show ((B.re.mul C.im).add (B.im.mul C.re)).lo.toReal ≤ (z * w).im
    rw [Complex.mul_im]
    exact hB.1
  · show (z * w).im ≤ ((B.re.mul C.im).add (B.im.mul C.re)).hi.toReal
    rw [Complex.mul_im]
    exact hB.2

end Work.SeedCertNum
