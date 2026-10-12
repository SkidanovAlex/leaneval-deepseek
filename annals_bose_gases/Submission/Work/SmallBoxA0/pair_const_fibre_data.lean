import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SboxEB
import Submission.Work.SmallBoxA0.Final
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

open MeasureTheory
open scoped BigOperators

/-- Two nested integrals of a constant over the centred cube `acube s`: each
layer contributes the volume `s ^ 3` of the cube, so the value is `s ^ 6 * c`. -/
lemma double_const_integral {s : ℝ} (hs : 0 < s) (c : ℝ) :
    (∫ _z : EuclideanSpace ℝ (Fin 3) in Submission.BoseGases.acube s,
      ∫ _y : EuclideanSpace ℝ (Fin 3) in Submission.BoseGases.acube s, c) = s ^ 6 * c := by
  rw [Submission.BoseGases.integral_const_acube s hs c]
  rw [Submission.BoseGases.integral_const_acube s hs (c * s ^ 3)]
  ring

/-- Fibre decomposition of a box integral for a function which is constant in the
two distinguished slots `i` and `i.succAbove j'`: the two extra coordinates
contribute the factor `s ^ 6` (the volume of `acube s × acube s`), and the
integrability of the restricted function follows from the two peels of the
box integral. -/
lemma pair_const_fibre_data {p : ℕ} {s : ℝ} (hs : 0 < s) (i : Fin (p + 2)) (j' : Fin (p + 1))
    {A : Submission.BoseGases.X (p + 2) → ℝ}
    (hA : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X (p + 2) => (A x) ^ 2)
      (Submission.BoseGases.abox (p + 2) s) MeasureTheory.volume)
    (hconst : ∀ (y z : EuclideanSpace ℝ (Fin 3)) (r2 : Submission.BoseGases.X p),
      A (Submission.BoseGases.ins2 i j' y z r2) = A (Submission.BoseGases.rest2 i j' r2)) :
    MeasureTheory.IntegrableOn (fun r2 : Submission.BoseGases.X p =>
        (A (Submission.BoseGases.rest2 i j' r2)) ^ 2) (Submission.BoseGases.abox p s) MeasureTheory.volume ∧
    (∫ x in Submission.BoseGases.abox (p + 2) s, (A x) ^ 2)
      = s ^ 6 * ∫ r2 in Submission.BoseGases.abox p s, (A (Submission.BoseGases.rest2 i j' r2)) ^ 2 := by
  -- the constancy hypothesis, unfolded to the `kcInsN` presentation of `ins2`
  have hconst2 : ∀ (y z : EuclideanSpace ℝ (Fin 3)) (r2 : Submission.BoseGases.X p),
      (A (Submission.BoseGases.kcInsN (p + 1) i (y, Submission.BoseGases.kcInsN p j' (z, r2)))) ^ 2
        = (A (Submission.BoseGases.rest2 i j' r2)) ^ 2 := by
    intro y z r2
    change (A (Submission.BoseGases.ins2 i j' y z r2)) ^ 2 = (A (Submission.BoseGases.rest2 i j' r2)) ^ 2
    rw [hconst y z r2]
  -- peel the first slot
  have hG : Integrable (fun r : Submission.BoseGases.X (p + 1) =>
      ∫ y in Submission.BoseGases.acube s, (A (Submission.BoseGases.kcInsN (p + 1) i (y, r))) ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (p + 1))).restrict
        (Submission.BoseGases.abox (p + 1) s)) :=
    Submission.BoseGases.abox_peel_inner_integrable (n := p + 1) (ℓ := s) i
      (fun x => (A x) ^ 2) hA
  -- peel the second slot
  have hH := Submission.BoseGases.abox_peel_inner_integrable (n := p) (ℓ := s) j'
      (fun r : Submission.BoseGases.X (p + 1) =>
        ∫ y in Submission.BoseGases.acube s, (A (Submission.BoseGases.kcInsN (p + 1) i (y, r))) ^ 2) hG
  -- the twice-peeled function is `s ^ 6 · (A ∘ rest2)²`
  have hI1 : Integrable (fun r2 : Submission.BoseGases.X p =>
      s ^ 6 * (A (Submission.BoseGases.rest2 i j' r2)) ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X p)).restrict
        (Submission.BoseGases.abox p s)) := by
    refine hH.congr (Filter.Eventually.of_forall (fun r2 => ?_))
    simp only [hconst2]
    exact double_const_integral hs _
  constructor
  · -- integrability of `(A ∘ rest2)²` follows by dividing out `s ^ 6 ≠ 0`
    have h2 := hI1.const_mul ((s ^ 6)⁻¹)
    refine h2.congr (Filter.Eventually.of_forall (fun r2 => ?_))
    show (s ^ 6)⁻¹ * (s ^ 6 * (A (Submission.BoseGases.rest2 i j' r2)) ^ 2)
        = (A (Submission.BoseGases.rest2 i j' r2)) ^ 2
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 6 (ne_of_gt hs)), one_mul]
  · -- the value of the integral: peel twice, reduce the fibre integral to `s ^ 6·c`
    have hcongr : (fun r2 : Submission.BoseGases.X p =>
        ∫ z in Submission.BoseGases.acube s, ∫ y in Submission.BoseGases.acube s,
          (A (Submission.BoseGases.kcInsN (p + 1) i (y, Submission.BoseGases.kcInsN p j' (z, r2)))) ^ 2)
        = fun r2 : Submission.BoseGases.X p => s ^ 6 * (A (Submission.BoseGases.rest2 i j' r2)) ^ 2 := by
      funext r2
      rw [show (∫ z in Submission.BoseGases.acube s, ∫ y in Submission.BoseGases.acube s,
            (A (Submission.BoseGases.kcInsN (p + 1) i (y, Submission.BoseGases.kcInsN p j' (z, r2)))) ^ 2)
          = ∫ z in Submission.BoseGases.acube s, ∫ y in Submission.BoseGases.acube s,
            (A (Submission.BoseGases.rest2 i j' r2)) ^ 2 from by simp only [hconst2]]
      exact double_const_integral hs _
    rw [Submission.BoseGases.abox_integral_peel2 i j' (fun x => (A x) ^ 2) hA, hcongr]
    rw [MeasureTheory.integral_const_mul]

end Work.SmallBoxA0
