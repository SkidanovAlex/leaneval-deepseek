import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Submission.Work.BoseFixB1S.CoordMeanDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.integral_sq_sub_coordMean`

The **conditional variance (Pythagoras) identity** for the coordinate mean: for a finite measure
`ν` on `α`, a function `f` on the product space `(Fin (k+1) → α)` which is a.e. strongly
measurable, integrable and square integrable, and any real `c`,

`∫ (f − c)² = ∫ (f − E_j f)² + ∫ (E_j f − c)²`   (`E_j = coordMean ν j`),

i.e. `E_j f` is the `L²`-orthogonal projection of `f` onto the functions not depending on the
coordinate `j`.  The orthogonality of the cross term is the tower identity
`Work.BoseFixB1S.pi_tower_right` together with the fact that `E_j f` does not depend on the
coordinate `j` (`Work.BoseFixB1S.coordMean_indep_self`).

This is the `L²`-form of the ANOVA decomposition
(`Submission/Work/BoseFixB1S/piAnovaLeCoordMeans.lean`): the `j`-th summand of the ANOVA bound
is exactly the first term on the right, maximised over `c`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1S

theorem integral_sq_sub_coordMean {α : Type*} [MeasurableSpace α]
    (ν : MeasureTheory.Measure α) [MeasureTheory.SigmaFinite ν] [MeasureTheory.IsFiniteMeasure ν]
    (hν : 0 < (ν Set.univ).toReal) {k : ℕ} (j : Fin (k + 1))
    {f : (Fin (k + 1) → α) → ℝ}
    (hfm : MeasureTheory.AEStronglyMeasurable f (MeasureTheory.Measure.pi (fun _ : Fin (k + 1) => ν)))
    (hf1 : MeasureTheory.Integrable f (MeasureTheory.Measure.pi (fun _ : Fin (k + 1) => ν)))
    (hf2 : MeasureTheory.Integrable (fun x => (f x) ^ 2)
        (MeasureTheory.Measure.pi (fun _ : Fin (k + 1) => ν)))
    (c : ℝ) :
    ∫ x, (f x - c) ^ 2 ∂(MeasureTheory.Measure.pi (fun _ : Fin (k + 1) => ν))
      = ∫ x, (f x - Work.BoseFixB1S.coordMean ν j f x) ^ 2
          ∂(MeasureTheory.Measure.pi (fun _ : Fin (k + 1) => ν))
        + ∫ x, (Work.BoseFixB1S.coordMean ν j f x - c) ^ 2
          ∂(MeasureTheory.Measure.pi (fun _ : Fin (k + 1) => ν)) := by
  classical
  set π : Measure (Fin (k + 1) → α) := Measure.pi (fun _ : Fin (k + 1) => ν) with hπ
  set m : (Fin (k + 1) → α) → ℝ := coordMean ν j f with hm
  -- `m` does not depend on the `j`-th coordinate
  have hm_indep : ∀ x z, m (Function.update x j z) = m x :=
    fun x z => coordMean_indep_self ν j f x z
  have hm_sm : AEStronglyMeasurable m π :=
    (aestronglyMeasurable_pi_coordMean ν j hfm).const_mul (1 / (ν Set.univ).toReal)
  -- `m ∈ L²` with `∫ m² ≤ ∫ f²` (`L²`-contraction of the coordinate mean)
  have hm2 : Integrable (fun x => (m x) ^ 2) π :=
    (integrable_and_integral_sq_pi_coordMean_le ν hν j hfm hf2).1
  have hf2' : Integrable (fun x => f x * f x) π :=
    hf2.congr (Filter.Eventually.of_forall fun x => by simp only [pow_two])
  have hm2' : Integrable (fun x => m x * m x) π :=
    hm2.congr (Filter.Eventually.of_forall fun x => by simp only [pow_two])
  -- `m ∈ L¹` (finite measure, `|m| ≤ (m² + 1)/2`)
  have hm1 : Integrable m π := by
    refine Integrable.mono' (g := fun x => (m x ^ 2 + 1) / 2)
      ((hm2.add (integrable_const 1)).div_const 2) hm_sm ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (|m x| - 1), abs_nonneg (m x), sq_abs (m x)]
  -- `f * m ∈ L¹` (`|f m| ≤ (f² + m²)/2`)
  have hfm_prod : Integrable (fun x => f x * m x) π := by
    refine Integrable.mono' (g := fun x => ((f x) ^ 2 + (m x) ^ 2) / 2)
      ((hf2.add hm2).div_const 2) (hfm.mul hm_sm) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_nonneg (|f x| - |m x|), abs_nonneg (f x), abs_nonneg (m x), sq_abs (f x),
      sq_abs (m x)]
  have hFm : Integrable (fun x => f x * (m x - c)) π :=
    (hfm_prod.sub (hf1.const_mul c)).congr (Filter.Eventually.of_forall fun x => by
      show f x * m x - c * f x = f x * (m x - c)
      ring)
  have hMm : Integrable (fun x => m x * (m x - c)) π :=
    (hm2'.sub (hm1.const_mul c)).congr (Filter.Eventually.of_forall fun x => by
      show m x * m x - c * m x = m x * (m x - c)
      ring)
  have hG : Integrable (fun x => (f x - m x) * (m x - c)) π :=
    (hFm.sub hMm).congr (Filter.Eventually.of_forall fun x => by
      show f x * (m x - c) - m x * (m x - c) = (f x - m x) * (m x - c)
      ring)
  -- **the tower identity**: `∫ f (m - c) = ∫ m (m - c)`, since `m = E_j f` and `m - c` is
  -- independent of the `j`-th coordinate
  have htower : ∫ x, f x * (m x - c) ∂π = ∫ x, m x * (m x - c) ∂π := by
    have h := pi_tower_right ν hν j (u := f) (w := fun x => m x - c)
      (fun x z => by rw [hm_indep x z]) hFm
    exact h
  -- **orthogonality of the cross term**
  have horth : ∫ x, (f x - m x) * (m x - c) ∂π = 0 := by
    have hsplit : ∫ x, (f x - m x) * (m x - c) ∂π
        = ∫ x, (f x * (m x - c) - m x * (m x - c)) ∂π :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    rw [hsplit, integral_sub hFm hMm, htower, sub_self]
  have hB : Integrable (fun x => (f x - m x) ^ 2) π :=
    ((hf2'.sub (hfm_prod.const_mul 2)).add hm2').congr
      (Filter.Eventually.of_forall fun x => by
        show f x * f x - 2 * (f x * m x) + m x * m x = (f x - m x) ^ 2
        ring)
  have hD : Integrable (fun x => (m x - c) ^ 2) π :=
    ((hm2'.sub (hm1.const_mul (2 * c))).add (integrable_const (c ^ 2))).congr
      (Filter.Eventually.of_forall fun x => by
        show m x * m x - (2 * c) * m x + c ^ 2 = (m x - c) ^ 2
        ring)
  have h2G : Integrable (fun x => 2 * ((f x - m x) * (m x - c))) π := hG.const_mul 2
  have step1 : ∫ x, ((f x - m x) ^ 2 + 2 * ((f x - m x) * (m x - c)) + (m x - c) ^ 2) ∂π
      = ∫ x, ((f x - m x) ^ 2 + 2 * ((f x - m x) * (m x - c))) ∂π
        + ∫ x, (m x - c) ^ 2 ∂π :=
    integral_add (hB.add h2G) hD
  have step2 : ∫ x, ((f x - m x) ^ 2 + 2 * ((f x - m x) * (m x - c))) ∂π
      = ∫ x, (f x - m x) ^ 2 ∂π + ∫ x, 2 * ((f x - m x) * (m x - c)) ∂π :=
    integral_add hB h2G
  have step3 : ∫ x, 2 * ((f x - m x) * (m x - c)) ∂π
      = 2 * ∫ x, ((f x - m x) * (m x - c)) ∂π :=
    integral_const_mul 2 _
  have hid : ∫ x, (f x - c) ^ 2 ∂π = ∫ x, (f x - m x) ^ 2 ∂π + ∫ x, (m x - c) ^ 2 ∂π := by
    have e1 : ∫ x, (f x - c) ^ 2 ∂π
        = ∫ x, ((f x - m x) ^ 2 + 2 * ((f x - m x) * (m x - c)) + (m x - c) ^ 2) ∂π :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    rw [e1, step1, step2, step3, horth]
    ring
  exact hid

end Work.BoseFixB1S
