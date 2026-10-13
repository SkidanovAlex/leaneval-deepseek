import Mathlib
import Submission.Work.WilC4.Defs
import Submission.Work.WilC4.valEq_mul
import Submission.Work.WilC4.valEq_zpow
import Submission.Work.WilC4.valEq_trans
import Submission.Work.WilC4.valEq_symm
import Submission.Work.WilC4.valEq_one_iff_unitVal
import Submission.Work.WilC4.valEq_iff_unitVal_div
import Submission.Work.WilC4.unitVal_mul
import Submission.Work.WilC4.unitVal_inv
import Submission.Work.WilC4.unitVal_zpow

namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

/-- Replacing the denominator-at-the-value-level `c` by any element `y` in the same Archimedean
class preserves being a unit: the two expressions
`w * c ^ N / u ^ n` and `w * y ^ N / u ^ n`
differ by the factor `(y / c) ^ N`, which is a unit because `y / c` is one (`ValEq y c` and
`valEq_iff_unitVal_div`), and units are closed under powers (`unitVal_zpow`) and products
(`unitVal_mul`). -/
theorem isUnitVal_of_valEq_mul_pow_div {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] {w u y c : M} {N : ℕ} {n : ℤ} (hc : c ≠ 0) (h : Work.WilC4.ValEq y c) (hunit : WilkiesDesign.CG.IsUnitVal (w * c ^ N / u ^ n)) : WilkiesDesign.CG.IsUnitVal (w * y ^ N / u ^ n) := by
  have hyc : IsUnitVal (y / c) := (valEq_iff_unitVal_div (x := y) (y := c) hc).mp h
  have hpow : IsUnitVal ((y / c) ^ N) := by
    simpa using unitVal_zpow hyc (N : ℤ)
  have hprod : IsUnitVal ((w * c ^ N / u ^ n) * (y / c) ^ N) := unitVal_mul hunit hpow
  have heq : (w * c ^ N / u ^ n) * (y / c) ^ N = w * y ^ N / u ^ n := by
    rw [div_pow]
    field_simp
  rwa [heq] at hprod

end Work.WilC4
