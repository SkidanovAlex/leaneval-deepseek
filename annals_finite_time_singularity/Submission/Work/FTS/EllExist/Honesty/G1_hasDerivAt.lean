import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllExist.Honesty.G1Aux
import Submission.Work.FTS.EllExist.Honesty.G1_continuousOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllExist.Honesty

open MeasureTheory Set

/-- `G1 α m c = z ↦ z^{s⁻} · G1A α m c z` is differentiable on `(0,∞)` with derivative
`(-a·G1 z + c z)/z`, `a = G1a α m = -G1s α m`: the product rule for `z^{s⁻} · ∫_0^z c t t^{a-1}dt`
gives `s⁻ z^{s⁻-1}A(z) + z^{s⁻}c z z^{a-1} = (s⁻ z^{s⁻}A(z) + c z)/z`, and `s⁻ = -a`. -/
theorem G1_hasDerivAt {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun z => c z ^ 2 / z ^ 4) (Set.Ioo 0 1)) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.FTS.EllExist.Honesty.G1 α m c)
        ((-(Work.FTS.EllExist.Honesty.G1a α m) * Work.FTS.EllExist.Honesty.G1 α m c z + c z) / z) z := by
  intro z hz
  have hzpos : 0 < z := hz
  have hz0 : z ≠ 0 := ne_of_gt hzpos
  have hInt : IntegrableOn (G1f α m c) (Set.Ioo 0 1) := G1f_integrableOn hα m hc h0
  have hA : HasDerivAt (G1A α m c) (G1f α m c z) z := G1A_hasDerivAt hc hInt z hz
  have hpow : HasDerivAt (fun w : ℝ => w ^ (G1s α m)) (G1s α m * z ^ (G1s α m - 1)) z :=
    Real.hasDerivAt_rpow_const (x := z) (p := G1s α m) (Or.inl hz0)
  have hprod : HasDerivAt (fun w : ℝ => w ^ (G1s α m) * G1A α m c w)
      ((G1s α m * z ^ (G1s α m - 1)) * G1A α m c z + z ^ (G1s α m) * G1f α m c z) z :=
    hpow.mul hA
  change HasDerivAt (fun w : ℝ => w ^ (G1s α m) * G1A α m c w)
    ((-(G1a α m) * (z ^ (G1s α m) * G1A α m c z) + c z) / z) z
  have hgf : G1f α m c z = c z * z ^ (G1a α m - 1) := by simp only [G1f, G1a]
  have h1 : z ^ (G1s α m - 1) = z ^ (G1s α m) / z := Real.rpow_sub_one hz0 (G1s α m)
  have h2 : z ^ (G1s α m) * z ^ (G1a α m - 1) = z⁻¹ := by
    rw [← Real.rpow_add (x := z) hzpos]
    have hsum : G1s α m + (G1a α m - 1) = -1 := by rw [G1s_eq_neg_G1a]; ring
    simp only [hsum, Real.rpow_neg_one]
  have h3 : z ^ (G1s α m) * (c z * z ^ (G1a α m - 1))
      = c z * (z ^ (G1s α m) * z ^ (G1a α m - 1)) := by ring
  have heq : (G1s α m * z ^ (G1s α m - 1)) * G1A α m c z + z ^ (G1s α m) * G1f α m c z
      = (-(G1a α m) * (z ^ (G1s α m) * G1A α m c z) + c z) / z := by
    rw [h1, hgf, h3, h2, G1s_eq_neg_G1a, div_eq_mul_inv]
    ring
  rw [← heq]
  exact hprod

end Work.FTS.EllExist.Honesty
