import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1P.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

/-- Weighted two-variable Young (AM–GM) inequality at the *reciprocal* pair of weights
`(1 + π²)⁻¹` and `(1 + π²)`: since the weights multiply to `1`, the mixed term is exactly
`2 c a b`, and the difference of the right-hand side and the left-hand side is
`(1 + π²)⁻¹ * (a - (1 + π²) c b)² ≥ 0`. -/
private lemma two_mul_mul_le_aux (a b c : ℝ) :
    2 * c * (a * b) ≤ (1 + Real.pi ^ 2)⁻¹ * a ^ 2 + (1 + Real.pi ^ 2) * c ^ 2 * b ^ 2 := by
  have hpos : (0 : ℝ) < 1 + Real.pi ^ 2 := by positivity
  have hnn : 0 ≤ (1 + Real.pi ^ 2)⁻¹ * (a - (1 + Real.pi ^ 2) * c * b) ^ 2 :=
    mul_nonneg (le_of_lt (inv_pos.mpr hpos)) (sq_nonneg _)
  have hexp : (1 + Real.pi ^ 2)⁻¹ * (a - (1 + Real.pi ^ 2) * c * b) ^ 2
      = (1 + Real.pi ^ 2)⁻¹ * a ^ 2 - 2 * c * (a * b) + (1 + Real.pi ^ 2) * c ^ 2 * b ^ 2 := by
    field_simp
    ring
  linarith [hnn, hexp]

theorem two_mul_integral_mul_le {P : Set ℝ³} (hK : IsCompact P) {f g : ℝ³ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (c : ℝ) :
    2 * c * (∫ x in P, f x * g x)
      ≤ (1 + Real.pi ^ 2)⁻¹ * (∫ x in P, (f x) ^ 2)
        + (1 + Real.pi ^ 2) * c ^ 2 * (∫ x in P, (g x) ^ 2) := by
  have hpt : ∀ x : ℝ³, 2 * c * (f x * g x)
      ≤ (1 + Real.pi ^ 2)⁻¹ * (f x) ^ 2 + (1 + Real.pi ^ 2) * c ^ 2 * (g x) ^ 2 :=
    fun x => two_mul_mul_le_aux (f x) (g x) c
  have hfg : MeasureTheory.Integrable (fun x : ℝ³ => f x * g x)
      (MeasureTheory.volume.restrict P) :=
    (hf.continuousOn.mul hg.continuousOn).integrableOn_compact hK
  have hf2 : MeasureTheory.Integrable (fun x : ℝ³ => (f x) ^ 2)
      (MeasureTheory.volume.restrict P) :=
    (hf.continuousOn.pow 2).integrableOn_compact hK
  have hg2 : MeasureTheory.Integrable (fun x : ℝ³ => (g x) ^ 2)
      (MeasureTheory.volume.restrict P) :=
    (hg.continuousOn.pow 2).integrableOn_compact hK
  have hL : MeasureTheory.Integrable (fun x : ℝ³ => 2 * c * (f x * g x))
      (MeasureTheory.volume.restrict P) :=
    hfg.const_mul (2 * c)
  have hR1 : MeasureTheory.Integrable (fun x : ℝ³ => (1 + Real.pi ^ 2)⁻¹ * (f x) ^ 2)
      (MeasureTheory.volume.restrict P) :=
    hf2.const_mul _
  have hR2 : MeasureTheory.Integrable (fun x : ℝ³ => (1 + Real.pi ^ 2) * c ^ 2 * (g x) ^ 2)
      (MeasureTheory.volume.restrict P) :=
    hg2.const_mul _
  have hR : MeasureTheory.Integrable (fun x : ℝ³ =>
      (1 + Real.pi ^ 2)⁻¹ * (f x) ^ 2 + (1 + Real.pi ^ 2) * c ^ 2 * (g x) ^ 2)
      (MeasureTheory.volume.restrict P) :=
    hR1.add hR2
  have hmono := MeasureTheory.integral_mono hL hR hpt
  have e1 : (∫ x in P, 2 * c * (f x * g x)) = 2 * c * (∫ x in P, f x * g x) := by
    rw [MeasureTheory.integral_const_mul]
  have e2 : (∫ x in P, ((1 + Real.pi ^ 2)⁻¹ * (f x) ^ 2
        + (1 + Real.pi ^ 2) * c ^ 2 * (g x) ^ 2))
      = (1 + Real.pi ^ 2)⁻¹ * (∫ x in P, (f x) ^ 2)
        + (1 + Real.pi ^ 2) * c ^ 2 * (∫ x in P, (g x) ^ 2) := by
    rw [MeasureTheory.integral_add, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
    · exact hR1
    · exact hR2
  rw [e1, e2] at hmono
  exact hmono

end Work.BoseFixB1S
