import Mathlib
import Submission.Work.LinnikAreas.DhK.TuranDefs

namespace Work.LinnikAreas.DhK

/-- For complex `a`, `b`: `Re(ab) + Re(a·conj b) = 2 Re(a) Re(b)`.
Equivalently `Re(ab) + Re(a b̄)` is twice the product of the real parts. -/
private lemma re_mul_add_re_mul_star (a b : ℂ) :
    (a * b).re + (a * star b).re = 2 * (a.re * b.re) := by
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- Pointwise form of the Fejér expansion: summing the per-term identity
`(1 + Re u^j) Re z^j = Re z^j + ½ Re (zu)^j + ½ Re (zū)^j` against the Fejér
weights `1 - j/(J+1)` gives `fejerK J z u`. -/
theorem fejerPointwise (J : ℕ) (z u : ℂ) :
    ∑ j ∈ Finset.Icc 1 J, fejerW J j * (1 + (u ^ j).re) * (z ^ j).re
      = fejerK J z u := by
  have hterm : ∀ j ∈ Finset.Icc 1 J,
      fejerW J j * (1 + (u ^ j).re) * (z ^ j).re
        = fejerW J j * (z ^ j).re + (1 / 2) * (fejerW J j * ((z * u) ^ j).re)
          + (1 / 2) * (fejerW J j * ((z * star u) ^ j).re) := by
    intro j _
    have hkey := re_mul_add_re_mul_star (z ^ j) (u ^ j)
    rw [mul_pow, mul_pow, ← star_pow]
    linear_combination (-(fejerW J j) / 2) * hkey
  calc ∑ j ∈ Finset.Icc 1 J, fejerW J j * (1 + (u ^ j).re) * (z ^ j).re
      = ∑ j ∈ Finset.Icc 1 J, (fejerW J j * (z ^ j).re
          + (1 / 2) * (fejerW J j * ((z * u) ^ j).re)
          + (1 / 2) * (fejerW J j * ((z * star u) ^ j).re)) := Finset.sum_congr rfl hterm
    _ = (∑ j ∈ Finset.Icc 1 J, fejerW J j * (z ^ j).re)
          + (1 / 2) * (∑ j ∈ Finset.Icc 1 J, fejerW J j * ((z * u) ^ j).re)
          + (1 / 2) * (∑ j ∈ Finset.Icc 1 J, fejerW J j * ((z * star u) ^ j).re) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = fejerK J z u := by rw [fejerK, fejerQ, fejerQ, fejerQ]

end Work.LinnikAreas.DhK
