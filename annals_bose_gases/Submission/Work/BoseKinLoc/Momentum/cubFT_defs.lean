import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The moving-box Fourier symbol chapter (FS `eq:Q1Qslide`)

This module fixes the vocabulary in which the residual `Work.BoseKinLoc.MomBound` (FS's
`eq:Q1Qslide`) is proved.

`cubFT` is the `p`-convention Fourier transform of the unit cube `acube 1`, written in real
form (the sine part vanishes by the symmetry of the cube).  `cubeB` is FS's sliding symbol
`θ̂(p)θ̂(q) − θ̂(q−p)` in the unit-cube normalisation: its `u`-average is the Fourier multiplier
of the sliding mean-free box family `∫_u Q_u 1_{(d^{-2}ℓ^{-1},∞)}(√−Δ) Q_u du`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseKinLoc.Momentum

open Submission.BoseGases

set_option autoImplicit false

/-- **The unit-cube Fourier symbol** (real form): `cubFT q = ∫_{acube 1} cos ⟪q,x⟫ dx`. -/
def cubFT (q : ℝ³) : ℝ := ∫ x in acube 1, Real.cos (inner ℝ q x)

/-- **The sliding-symbol block** `B(s,p) = θ(p−s) − θ(s)θ(p)` of FS `eq:Q1Qslide`. -/
def cubeB (v w : ℝ³) : ℝ := cubFT (w - v) - cubFT v * cubFT w

lemma volume_acube_one : volume (acube 1) = 1 := by
  have h := acube_volume (1 : ℝ) (by norm_num)
  simpa using h

lemma real_volume_acube_one : Measure.real volume (acube 1) = 1 := by
  show (volume (acube 1)).toReal = 1
  rw [volume_acube_one]; simp

lemma int_one_acube : (∫ x in acube 1, (1 : ℝ)) = 1 := by
  rw [setIntegral_const, real_volume_acube_one, one_smul]

/-- `cubFT 0 = 1`. -/
lemma cubFT_zero : cubFT 0 = 1 := by
  rw [cubFT]
  rw [show (fun x : ℝ³ => Real.cos (inner ℝ (0 : ℝ³) x)) = fun _ => (1 : ℝ) from by
    funext x; simp]
  exact int_one_acube

lemma cubeB_zero_left (w : ℝ³) : cubeB 0 w = 0 := by
  simp [cubeB, cubFT_zero]

lemma cubFT_neg (q : ℝ³) : cubFT (-q) = cubFT q := by
  unfold cubFT
  refine integral_congr_ae ?_
  filter_upwards with x
  rw [inner_neg_left, Real.cos_neg]

lemma cubFT_sub_comm (v w : ℝ³) : cubFT (w - v) = cubFT (v - w) := by
  have h : v - w = -(w - v) := by abel
  rw [h, cubFT_neg]

lemma measurableSet_acube (ℓ : ℝ) : MeasurableSet (acube ℓ) := acube_measurable ℓ

/-- `|cubFT q| ≤ 1`. -/
lemma abs_cubFT_le_one (q : ℝ³) : |cubFT q| ≤ 1 := by
  have htop : volume (acube 1) < ⊤ := by rw [volume_acube_one]; exact ENNReal.one_lt_top
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := acube 1)
    (f := fun x : ℝ³ => Real.cos (inner ℝ q x)) (C := 1) htop
    (fun x _ => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  rw [real_volume_acube_one, mul_one] at h
  rw [cubFT]
  simpa using h

lemma integrableOn_cos (v : ℝ³) :
    IntegrableOn (fun x : ℝ³ => Real.cos (inner ℝ v x)) (acube 1) volume := by
  have hne : volume (acube 1) ≠ ⊤ := by rw [volume_acube_one]; exact ENNReal.one_ne_top
  refine Integrable.mono (g := fun _ : ℝ³ => (1 : ℝ))
    (integrableOn_const (C := (1 : ℝ)) hne (by norm_num)) (by fun_prop) ?_
  filter_upwards with x
  simpa using Real.abs_cos_le_one (inner ℝ v x)

lemma integrableOn_one_sub_cos (v : ℝ³) :
    IntegrableOn (fun x : ℝ³ => 1 - Real.cos (inner ℝ v x)) (acube 1) volume := by
  have hne : volume (acube 1) ≠ ⊤ := by rw [volume_acube_one]; exact ENNReal.one_ne_top
  exact (integrableOn_const (C := (1 : ℝ)) hne (by norm_num)).sub (integrableOn_cos v)

/-- `1 − cubFT v = ∫_{acube 1}(1 − cos⟪v,x⟫)`. -/
lemma one_sub_cubFT_eq (v : ℝ³) :
    1 - cubFT v = ∫ x in acube 1, (1 - Real.cos (inner ℝ v x)) := by
  have hne : volume (acube 1) ≠ ⊤ := by rw [volume_acube_one]; exact ENNReal.one_ne_top
  have hcast : cubFT v = (∫ x in acube 1, (1 : ℝ))
      - ∫ x in acube 1, (1 - Real.cos (inner ℝ v x)) := by
    rw [cubFT, ← integral_sub (integrableOn_const (C := (1 : ℝ)) hne (by norm_num))
      (integrableOn_one_sub_cos v)]
    exact integral_congr_ae (ae_of_all _ fun x => by ring)
  rw [hcast, int_one_acube]; ring

lemma one_sub_cubFT_nonneg (v : ℝ³) : 0 ≤ 1 - cubFT v := by
  rw [one_sub_cubFT_eq]
  exact setIntegral_nonneg (measurableSet_acube 1) fun x _ => by
    linarith [Real.cos_le_one (inner ℝ v x)]

/-- `|1 − cubFT v| ≤ 2`. -/
lemma abs_one_sub_cubFT_le_two (v : ℝ³) : |1 - cubFT v| ≤ 2 := by
  rw [abs_of_nonneg (one_sub_cubFT_nonneg v)]
  linarith [neg_abs_le (cubFT v), abs_cubFT_le_one v]

end Work.BoseKinLoc.Momentum
