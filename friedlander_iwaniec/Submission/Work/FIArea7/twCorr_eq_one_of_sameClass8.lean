import Mathlib
import Submission.Work.FIArea7.WBOmega

namespace Work.FIArea7

set_option linter.unusedVariables false

/-- `Re(z̄₁z₂) = r₁r₂ + s₁s₂` in coordinates (`zᵢ = rᵢ + i sᵢ`). -/
private lemma re_star_mul_coord (z1 z2 : GaussianInt) :
    (star z1 * z2).re = z1.re * z2.re + z1.im * z2.im := by
  simp only [Zsqrtd.re_mul, Zsqrtd.re_star, Zsqrtd.im_star]
  ring

/-- The norm `|z|²` as an integer is `r² + s²`. -/
private lemma gnorm_int_eq (z : GaussianInt) :
    ((Work.FIPlan.gnorm z : ℕ) : ℤ) = z.re * z.re + z.im * z.im := by
  rw [Work.FIPlan.gnorm, Zsqrtd.norm_def]
  have h : z.re * z.re - -1 * z.im * z.im = z.re * z.re + z.im * z.im := by ring
  rw [h]
  have hnn : (0 : ℤ) ≤ z.re * z.re + z.im * z.im := by
    nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  rw [Int.natAbs_of_nonneg hnn]

/-- **The 2-adic correction of the (17.5)-insertion is trivial on the diagonal classes mod 8.**

`Work.FIArea7.twCorr z₁ z₂ = (χ₂(Re(z̄₁z₂))·χ₂(|z₁|²))^{ν₂(|Δ(z₁,z₂)|)}` (`kronTwo` is the
Kronecker symbol `χ₂` of §20/`KronTwo.lean`) is the correction factor in the *mod 4* form of
Lemma 17.1 used by `Work.FIArea7.reflection_pair_betaPrime_general`.  For primary `z₁ ≡ z₂
(mod 8)` one has `Re(z̄₁z₂) = r₁r₂ + s₁s₂ ≡ r₁² + s₁² = |z₁|² (mod 8)`, so the base is
`χ₂(|z₁|²)² = 1` and hence `twCorr z₁ z₂ = 1` (note `kronTwo` is `±1` on odd arguments and both
entries are odd for primary inputs; `kronTwo (Re) = kronTwo (|z₁|²)` because `kronTwo` depends on
the class mod 8 only).

This is why the round-6 coefficient — which by (5.7) is supported in ONE class mod 8
(`Work.FITop4.IsBetaCoeff6`) — needs no 2-adic correction in §17, even in the general-sign
situation where the mixed-sign factor `Work.FIArea7.reflSign z₁ z₂` is `-1`. -/
theorem twCorr_eq_one_of_sameClass8 (z1 z2 : GaussianInt)
    (hP1 : Work.FIPlan.IsPrimary z1) (hP2 : Work.FIPlan.IsPrimary z2)
    (h8r : z1.re ≡ z2.re [ZMOD 8]) (h8i : z1.im ≡ z2.im [ZMOD 8]) :
    Work.FIArea7.twCorr z1 z2 = 1 := by
  -- `Re(z̄₁z₂) = r₁r₂ + s₁s₂ ≡ r₁² + s₁² = |z₁|² (mod 8)`, because `r₁ ≡ r₂` and `s₁ ≡ s₂`.
  have hkl : kronTwo ((star z1 * z2).re) = kronTwo ((Work.FIPlan.gnorm z1 : ℕ) : ℤ) := by
    apply kronTwo_eq_of_modEq
    rw [re_star_mul_coord, gnorm_int_eq]
    exact ((Int.ModEq.refl z1.re).mul h8r).symm.add ((Int.ModEq.refl z1.im).mul h8i).symm
  -- `|z₁|² = r₁² + s₁²` is odd for primary `z₁`, so `χ₂(|z₁|²)² = 1`.
  have hodd : Odd (((Work.FIPlan.gnorm z1 : ℕ) : ℤ)) := by
    rw [gnorm_int_eq]
    exact (Odd.mul hP1.1 hP1.1).add_even (hP1.2.1.mul_right z1.im)
  have hbase :
      kronTwo ((star z1 * z2).re) * kronTwo ((Work.FIPlan.gnorm z1 : ℕ) : ℤ) = 1 := by
    rw [hkl]
    exact kronTwo_mul_self_of_odd hodd
  -- Hence the base of the power is `1`, and `twCorr z₁ z₂ = 1^ν₂(|Δ|) = 1`.
  rw [twCorr, hbase, one_pow]

end Work.FIArea7
