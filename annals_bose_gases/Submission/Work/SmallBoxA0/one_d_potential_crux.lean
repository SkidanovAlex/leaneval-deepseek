import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxA0.OneDPotMainId
import Submission.Work.SmallBoxA0.OneDPotNoEventuallyNeg
import Submission.Work.SmallBoxA0.OneDPotTailTendsto
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The one-dimensional potential crux

`Work.SmallBoxA0.one_d_potential_crux`: for a radial profile `p` supported in `(0,R]`
(`R > 0`) whose one-dimensional potential energy integrand is integrable, the potential
energy is nonnegative.

Writing `f r = r^2 * p r`, `Gfun p r = ∫_s f s / max r s`, `qfun p r = ∫_s f s / s`,
`Ufun p r = ∫_0^r qfun p t dt`, the integrand is `f r * Gfun p r`, and

* `OneDPotMainId`:  `∫_{ε}^{R} f * G = ∫_{ε}^{R} qfun^2 + qfun ε * Ufun ε` (integration by parts
  using `qfun' = -f/r` and `Gfun = Ufun / r`), valid for `0 < ε < R`;
* `OneDPotTailTendsto`: `∫_{ε}^{R} f * G → ∫_{0}^{∞} f * G` as `ε → 0⁺`;
* `OneDPotNoEventuallyNeg`: the boundary term `qfun ε * Ufun ε` cannot be eventually
  bounded above by a negative constant (since `(Ufun^2)' = 2 * qfun * Ufun` and `Ufun(0)=0`).

The proof is by contradiction: if the full energy `E = ∫ f * G` were negative, then for all
small `ε` the Cauchy/kernel term `qfun ε * Ufun ε` would be `≤ E/2 < 0`, contradicting
`OneDPotNoEventuallyNeg`.
-/

namespace Work.SmallBoxA0

open MeasureTheory

theorem one_d_potential_crux {R : ℝ} (hR : 0 < R) (p : ℝ → ℝ)
    (hp : MeasureTheory.IntegrableOn (fun r : ℝ => r ^ 2 * p r) (Set.Ioo (0 : ℝ) R))
    (hp0 : ∀ r : ℝ, R ≤ r → p r = 0)
    (hint : MeasureTheory.IntegrableOn (fun r : ℝ => r ^ 2 * p r * (∫ s in Set.Ioi (0 : ℝ), (s ^ 2 * p s) / max r s)) (Set.Ioi (0 : ℝ))) :
    0 ≤ ∫ r in Set.Ioi (0 : ℝ), r ^ 2 * p r * (∫ s in Set.Ioi (0 : ℝ), (s ^ 2 * p s) / max r s) := by
  have hgoal : (fun r : ℝ => r ^ 2 * p r * (∫ s in Set.Ioi (0 : ℝ), (s ^ 2 * p s) / max r s))
      = fun r : ℝ => (r ^ 2 * p r) * Gfun p r := by
    funext r; rw [Gfun]
  rw [hgoal]
  by_contra hcon
  push Not at hcon
  set E : ℝ := ∫ r in Set.Ioi (0 : ℝ), (r ^ 2 * p r) * Gfun p r with hE
  have hEneg : E < 0 := by rw [hE]; exact hcon
  have hEE : E < E / 2 := by linarith
  have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (∫ r in Set.Ioo ε R, (r ^ 2 * p r) * Gfun p r) < E / 2 :=
    (OneDPotTailTendsto hR p hp hp0 hint).eventually ((isOpen_Iio).mem_nhds hEE)
  rw [eventually_nhdsWithin_iff] at hev
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδpos, hδ⟩ := hev
  have hbad : ∃ c : ℝ, 0 < c ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      qfun p ε * Ufun p ε ≤ -c := by
    refine ⟨-(E / 2), by linarith, min δ R, lt_min hδpos hR, ?_⟩
    intro ε hεpos hεlt
    have hεR : ε < R := lt_of_lt_of_le hεlt (min_le_right _ _)
    have hεδ : dist ε 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hεpos]
      exact lt_of_lt_of_le hεlt (min_le_left _ _)
    have hg : (∫ r in Set.Ioo ε R, (r ^ 2 * p r) * Gfun p r) < E / 2 :=
      hδ hεδ hεpos
    have hmain := OneDPotMainId hR p hp hp0 hεpos hεR
    have hq2 : 0 ≤ ∫ r in Set.Ioo ε R, (qfun p r) ^ 2 :=
      setIntegral_nonneg measurableSet_Ioo (fun r _ => sq_nonneg _)
    linarith [hmain, hg, hq2]
  exact OneDPotNoEventuallyNeg hR p hp hp0 hbad

end Work.SmallBoxA0
