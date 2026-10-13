import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS_RegExport.RXT.noDecayPieces.agmonF_deriv_bnd
import Submission.Work.FTS_RegExport.RXT.noDecayPieces.le_sub_setIntegral_of_deriv_le
import Submission.Work.FTS_RegExport.RXT.noDecayPieces.false_of_log_divergence
import Submission.Work.FTS_RegExport.RXT.noDecayPieces.sq_le_of_profile_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT

/-- **Radial pointwise bound with no decay hypothesis.**

For `v : ℝ → ℝ` differentiable on `(0,∞)` with `v'` its derivative, if both weighted energies
`∫ v² w²` and `∫ (z v')² w²` are finite (`w(z) = (1+z)²/z²`), then

  `v(z)² ≤ 20 (min z 1)² (∫ v²w² + ∫ (zv')²w²)`  for every `z > 0`.

Route.  The profile `F(x) = x (v(x) w(x))²` has
`|F'| ≤ 4 (v w)² + (x v' w)²` on `(0,∞)`, so the fundamental theorem of calculus on `[z,x]`
gives `F x ≥ F z - (4 ∫(vw)² + ∫(xv'w)²)` for all `x ≥ z`.  If `F z` exceeded that constant,
`F` would be trapped above a positive constant `c` on `[z,∞)`, whence
`∫_z^X (vw)² = ∫_z^X F(x)/x ≥ c log(X/z) → ∞`, contradicting `∫_z^X (vw)² ≤ ∫ v² w² < ∞`.
So `F z ≤ 4 ∫(vw)² + ∫(xv'w)²`, and since `v(z)² = F(z) z³/(1+z)⁴` and
`z³/(1+z)⁴ ≤ (min z 1)²`, the claim follows. -/
theorem radial_noDecay_le {v v' : ℝ → ℝ}
    (hv : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt v (v' z) z)
    (hint1 : MeasureTheory.IntegrableOn (fun z => v z ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 0))
    (hint2 : MeasureTheory.IntegrableOn (fun z => (z * v' z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (Set.Ioi 0)) :
    ∀ z ∈ Set.Ioi (0 : ℝ), v z ^ 2 ≤ 20 * (min z 1) ^ 2 *
      ((∫ z in Set.Ioi 0, v z ^ 2 * (Work.Spaces.w z) ^ 2)
        + (∫ z in Set.Ioi 0, (z * v' z) ^ 2 * (Work.Spaces.w z) ^ 2)) := by
  intro z hz
  let I1 : ℝ := ∫ z in Set.Ioi (0 : ℝ), v z ^ 2 * (Work.Spaces.w z) ^ 2
  let I2 : ℝ := ∫ z in Set.Ioi (0 : ℝ), (z * v' z) ^ 2 * (Work.Spaces.w z) ^ 2
  set F : ℝ → ℝ := fun y => y * (v y * Work.Spaces.w y) ^ 2 with hF
  set F' : ℝ → ℝ := fun y => 2 * v y * (y * v' y) * (Work.Spaces.w y) ^ 2
          + (v y) ^ 2 * (Work.Spaces.w y) ^ 2 * ((y - 3) / (1 + y)) with hF'
  set G : ℝ → ℝ := fun y => 4 * (v y * Work.Spaces.w y) ^ 2
          + (y * v' y * Work.Spaces.w y) ^ 2 with hG
  have hvcont : ContinuousOn v (Set.Ioi (0 : ℝ)) :=
    fun x hx => (hv x hx).continuousAt.continuousWithinAt
  have hwcont : ContinuousOn Work.Spaces.w (Set.Ioi (0 : ℝ)) := by
    have h : (fun x : ℝ => (1 + x) ^ 2 / x ^ 2) = Work.Spaces.w := by
      funext y; rw [Work.Spaces.w]
    rw [← h]
    exact ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2) (continuousOn_id.pow 2)
      (fun x hx => pow_ne_zero 2 (ne_of_gt hx))
  have hFcont : ContinuousOn F (Set.Ioi (0 : ℝ)) := by
    rw [hF]
    exact continuousOn_id.mul ((hvcont.mul hwcont).pow 2)
  have hderivF : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt F (F' x) x := by
    intro x hx
    exact (noDecayPieces.agmonF_deriv_bnd (v := v) (v' := v') hv x hx).1
  have hmeas : AEStronglyMeasurable F' (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have hd : AEStronglyMeasurable (deriv F) (volume.restrict (Set.Ioi (0 : ℝ))) :=
      (aestronglyMeasurable_deriv F volume).restrict
    refine hd.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (hderivF x hx).deriv
  have hbd : ∀ x ∈ Set.Ioi (0 : ℝ), |F' x| ≤ G x := by
    intro x hx
    have h := (noDecayPieces.agmonF_deriv_bnd (v := v) (v' := v') hv x hx).2
    rw [hF', hG]
    exact h
  have hJ1int : IntegrableOn (fun x => (v x * Work.Spaces.w x) ^ 2) (Set.Ioi 0) :=
    MeasureTheory.IntegrableOn.congr_fun hint1 (fun x _ => by ring) measurableSet_Ioi
  have hJ2int : IntegrableOn (fun x => (x * v' x * Work.Spaces.w x) ^ 2) (Set.Ioi 0) :=
    MeasureTheory.IntegrableOn.congr_fun hint2 (fun x _ => by ring) measurableSet_Ioi
  have hG1int : IntegrableOn (fun x => 4 * (v x * Work.Spaces.w x) ^ 2) (Set.Ioi 0) :=
    Integrable.const_mul hJ1int 4
  have hG2int : IntegrableOn (fun x => (x * v' x * Work.Spaces.w x) ^ 2) (Set.Ioi 0) := hJ2int
  have hGint : IntegrableOn G (Set.Ioi 0) := by
    rw [hG]
    exact Integrable.add hG1int hG2int
  have hGnn : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] G := by
    rw [hG]
    refine Filter.Eventually.of_forall (fun x => ?_)
    show (0 : ℝ) ≤ 4 * (v x * Work.Spaces.w x) ^ 2 + (x * v' x * Work.Spaces.w x) ^ 2
    nlinarith [sq_nonneg (v x * Work.Spaces.w x), sq_nonneg (x * v' x * Work.Spaces.w x)]
  have hFlower : ∀ x, z ≤ x → F z - (∫ t in Set.Ioi 0, G t) ≤ F x :=
    noDecayPieces.le_sub_setIntegral_of_deriv_le hFcont hmeas hderivF hbd hGint hGnn hz
  have hFz_le : F z ≤ (∫ t in Set.Ioi 0, G t) := by
    by_contra hcon
    push_neg at hcon
    have hc : 0 < F z - (∫ t in Set.Ioi 0, G t) := by linarith
    refine noDecayPieces.false_of_log_divergence (g := fun x => F x / x)
      (z := z) (c := F z - (∫ t in Set.Ioi 0, G t)) hz hc ?_ ?_ ?_
    · have hEq : Set.EqOn (fun x => v x ^ 2 * (Work.Spaces.w x) ^ 2) (fun x => F x / x)
          (Set.Ioi 0) := by
        intro x hx
        rw [hF]
        rw [eq_div_iff (ne_of_gt hx)]
        ring
      exact MeasureTheory.IntegrableOn.congr_fun hint1 hEq measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      show (0 : ℝ) ≤ F x / x
      rw [hF]
      have h : x * (v x * Work.Spaces.w x) ^ 2 / x = (v x * Work.Spaces.w x) ^ 2 := by
        rw [div_eq_iff (ne_of_gt hx)]
        ring
      rw [h]
      positivity
    · intro x hzx
      have hx0 : 0 < x := lt_of_lt_of_le hz hzx
      exact div_le_div_of_nonneg_right (hFlower x hzx) hx0.le
  have hMrw : (∫ t in Set.Ioi (0 : ℝ), G t)
      = 4 * (∫ t in Set.Ioi (0 : ℝ), (v t * Work.Spaces.w t) ^ 2)
        + (∫ t in Set.Ioi (0 : ℝ), (t * v' t * Work.Spaces.w t) ^ 2) := by
    rw [hG]
    rw [MeasureTheory.integral_add hG1int hG2int, MeasureTheory.integral_const_mul]
  have hJ1 : (∫ t in Set.Ioi (0 : ℝ), (v t * Work.Spaces.w t) ^ 2)
      = (∫ z in Set.Ioi (0 : ℝ), v z ^ 2 * (Work.Spaces.w z) ^ 2) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x _ => by ring)
  have hJ2 : (∫ t in Set.Ioi (0 : ℝ), (t * v' t * Work.Spaces.w t) ^ 2)
      = (∫ z in Set.Ioi (0 : ℝ), (z * v' z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x _ => by ring)
  have hI1nn : 0 ≤ I1 :=
    MeasureTheory.integral_nonneg (f := fun z => v z ^ 2 * (Work.Spaces.w z) ^ 2)
      (fun x => by positivity)
  have hI2nn : 0 ≤ I2 :=
    MeasureTheory.integral_nonneg (f := fun z => (z * v' z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (fun x => by positivity)
  have hprof : z * (v z * Work.Spaces.w z) ^ 2 ≤ 4 * I1 + I2 := by
    have h1 := hFz_le
    rw [hF] at h1
    rw [hMrw, hJ1, hJ2] at h1
    exact h1
  have hK0 : 0 ≤ 4 * I1 + I2 := by linarith [hI1nn, hI2nn]
  have hsq : v z ^ 2 ≤ (4 * I1 + I2) * (min z 1) ^ 2 :=
    noDecayPieces.sq_le_of_profile_le hz hK0 hprof
  have hKle : 4 * I1 + I2 ≤ 20 * (I1 + I2) := by linarith [hI1nn, hI2nn]
  calc v z ^ 2 ≤ (4 * I1 + I2) * (min z 1) ^ 2 := hsq
    _ ≤ (20 * (I1 + I2)) * (min z 1) ^ 2 :=
        mul_le_mul_of_nonneg_right hKle (sq_nonneg _)
    _ = 20 * (min z 1) ^ 2 * (I1 + I2) := by ring

end Work.FTS_RegExport.RXT
