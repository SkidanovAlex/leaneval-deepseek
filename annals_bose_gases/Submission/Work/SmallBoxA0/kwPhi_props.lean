import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxA0.kwBumpZero
import Submission.Work.SmallBoxA0.kwDirichletScaling
import Submission.Work.SmallBoxA0.kwKinWordEq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SmallBoxA0

open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators ENNReal
open Submission BoseGases
open Work.SmallBoxA0

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Properties and scaling law of the witness family (`kwBump c z = chiBase (c • z)`,
`kwLam s c = ∫ x in abox 1 s, (kwBump c (x 0))²`,
`kwPhi s c x = (Real.sqrt (kwLam s c))⁻¹ * kwBump c (x 0)`, all defined in
`Submission/Work/SmallBoxA0/KinWitnessDefs.lean`), for `0 < s` and `2/s < c`:

1. `kwPhi s c` is smooth;
2. `tsupport (kwPhi s c) ⊆ abox 1 s`;
3. `kwPhi s c` vanishes outside `‖x 0‖ ≤ 1/(2c)`;
4. `kwLam s c = (c³)⁻¹ * chiNormSq`;
5. `∫ x in abox 1 s, (kwPhi s c x)² = 1`;
6. `kinWord 1 s (kwPhi s c) = c² * (kwE / chiNormSq)`.

HINTS.  (4) `integral_abox_one_eq` (already proved in the definitions module) rewrites the box
integral over `X 1` as `∫_{acube s}`; `kwBump c` is supported in `ball 0 (1/(2c)) ⊆ acube s`
because `2/s < c`, so the set integral may be extended to `∫_{ℝ³}`; then the scaling
`∫ z, g (c • z) = (c³)⁻¹ ∫ z, g z` (`Submission.BoseGases.integral_comp_smul_left`) with
`g := fun z => (chiBase z)²` and the definition of `chiNormSq` finish.  (3) `‖c • w‖ = c‖w‖` and
`chiBase` vanishes off `ball 0 (1/2)`.  (1),(2) smoothness and support from (3) plus
`chiBase_continuous`.  (5) from (4) and `Real.sq_sqrt` with `kwLam s c > 0`.  (6) the chain rule
for `y ↦ kwBump c (y 0)` on `kcDir 1 0 k = Function.update 0 0 (kcStdBasis k)` gives
`fderiv ℝ (kwBump c) (x 0) (kcStdBasis k)`; after `Fin.sum_univ_one`/`Finset.sum` bookkeeping and
`integral_finsetSum` the claim reduces to the scaled Dirichlet energy
`∫ z, Σ k, (fderiv ℝ (fun z => chiBase (c • z)) z (kcStdBasis k))² = c⁻¹ * kwE`, which follows
from `fderiv_comp_smul` (`fderiv ℝ (fun z => chiBase (c • z)) z = c • fderiv ℝ chiBase (c • z)`)
pointwise plus `integral_comp_smul_left` and `mul_pow`; combine with (4). -/
lemma kwPhi_props {s c : ℝ} (hs : 0 < s) (hcs : 2 / s < c) :
    ContDiff ℝ ∞ (kwPhi s c) ∧ tsupport (kwPhi s c) ⊆ abox 1 s ∧
      (∀ x : X 1, 1 / (2 * c) < ‖x 0‖ → kwPhi s c x = 0) ∧
      kwLam s c = (c ^ 3)⁻¹ * chiNormSq ∧
      (∫ x in abox 1 s, (kwPhi s c x) ^ 2) = 1 ∧
      kinWord 1 s (kwPhi s c) = c ^ 2 * (kwE / chiNormSq) := by
  -- `2/s < c` with `0 < s` forces `c > 0`.
  have hc : 0 < c := lt_trans (div_pos two_pos hs) hcs
  have hcne : c ≠ 0 := ne_of_gt hc
  -- The strict margin `1/(2c) < s/2` is all that the support arguments need.
  have h12 : 1 / (2 * c) < s / 2 := by
    have hcs2 : 2 < s * c := by
      rw [div_lt_iff₀ hs] at hcs
      nlinarith
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  -- Smoothness of the scaled bump and of its one-particle avatar.
  have hbump_cont : ContDiff ℝ ∞ (kwBump c) := by
    unfold kwBump
    exact chiBase_contDiff.comp (by fun_prop)
  have hproj : ContDiff ℝ ∞ (fun x : X 1 => kwBump c (x 0)) :=
    hbump_cont.comp (ContinuousLinearMap.contDiff
      (ContinuousLinearMap.proj (0 : Fin 1) : X 1 →L[ℝ] ℝ³))
  -- (3) `kwBump c` vanishes outside the ball of radius `1/(2c)`.
  have hvan : ∀ x : X 1, 1 / (2 * c) < ‖x 0‖ → kwPhi s c x = 0 := by
    intro x hx
    have hz : kwBump c (x 0) = 0 := by
      unfold kwBump
      apply chiBase_eq_zero_of_norm_gt
      rw [norm_smul, Real.norm_of_nonneg (le_of_lt hc)]
      have hcc : c * (1 / (2 * c)) = 1 / 2 := by field_simp
      rw [← hcc]
      exact mul_lt_mul_of_pos_left hx hc
    unfold kwPhi
    rw [hz, mul_zero]
  -- (1) the normalised witness is smooth.
  have h1 : ContDiff ℝ ∞ (kwPhi s c) := by
    unfold kwPhi
    exact contDiff_const.mul hproj
  -- (4) the `L²`-mass of the scaled bump.
  have h4 : kwLam s c = (c ^ 3)⁻¹ * chiNormSq := by
    rw [kwLam]
    rw [kwBoxExtend (F := fun z : ℝ³ => (kwBump c z) ^ 2)
      (fun z hz => by rw [kwBumpZero hs hcs hz, zero_pow (by norm_num)])]
    have h := integral_comp_smul_left (g := fun w : ℝ³ => (chiBase w) ^ 2) hc
    unfold kwBump chiNormSq
    exact h
  have hΛ : 0 < kwLam s c := by
    rw [h4]
    exact mul_pos (inv_pos.mpr (pow_pos hc 3)) chiNormSq_pos
  -- (5) the witness is `L²`-normalised on the box.
  have h5 : (∫ x in abox 1 s, (kwPhi s c x) ^ 2) = 1 := by
    have hsq : (Real.sqrt (kwLam s c))⁻¹ ^ 2 = (kwLam s c)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt (le_of_lt hΛ)]
    have hInt : (∫ x in abox 1 s, (kwPhi s c x) ^ 2)
        = (Real.sqrt (kwLam s c))⁻¹ ^ 2 * (∫ x in abox 1 s, (kwBump c (x 0)) ^ 2) := by
      rw [show (∫ x in abox 1 s, (kwPhi s c x) ^ 2)
          = ∫ x in abox 1 s, ((Real.sqrt (kwLam s c))⁻¹ * kwBump c (x 0)) ^ 2 from by
            unfold kwPhi; rfl]
      rw [show (∫ x in abox 1 s, ((Real.sqrt (kwLam s c))⁻¹ * kwBump c (x 0)) ^ 2)
          = ∫ x in abox 1 s, (Real.sqrt (kwLam s c))⁻¹ ^ 2 * (kwBump c (x 0)) ^ 2 from by
            apply integral_congr_ae
            filter_upwards with x
            exact mul_pow _ _ 2]
      rw [integral_const_mul]
    rw [hInt, hsq]
    exact inv_mul_cancel₀ (ne_of_gt hΛ)
  -- The one-particle box is closed.
  have hclosed : IsClosed (abox 1 s) := by
    have hac : IsClosed (acube s) := by
      rw [show acube s = ⋂ m : Fin 3, (fun y : ℝ³ => y m) ⁻¹' Set.Icc (-s/2) (s/2) from by
        ext y; simp [acube]]
      exact isClosed_iInter fun m => isClosed_Icc.preimage (by fun_prop)
    rw [show abox 1 s = (fun x : X 1 => x 0) ⁻¹' acube s from by ext x; simp [abox]]
    exact hac.preimage (by fun_prop)
  -- (2) the topological support lies in the box: the support lies in the ball
  -- `‖x 0‖ ≤ 1/(2c) < s/2`, which is contained in the closed box.
  have h2 : tsupport (kwPhi s c) ⊆ abox 1 s := by
    unfold tsupport
    refine closure_minimal (fun x hx => ?_) hclosed
    rw [Function.mem_support] at hx
    intro i
    rw [Fin.eq_zero i]
    intro m
    have hxle : ‖x 0‖ ≤ 1 / (2 * c) := by
      by_contra h
      push Not at h
      exact hx (hvan x h)
    have h' : |(x 0) m| ≤ s / 2 :=
      le_trans (abs_coord_le_norm (x 0) m) (le_of_lt (lt_of_le_of_lt hxle h12))
    obtain ⟨h1', h2'⟩ := abs_le.mp h'
    exact ⟨by linarith [h1'], h2'⟩
  -- (6) the kinetic word is the scaled Dirichlet energy.
  have h6 : kinWord 1 s (kwPhi s c) = c ^ 2 * (kwE / chiNormSq) := by
    have hchi : chiNormSq ≠ 0 := ne_of_gt chiNormSq_pos
    rw [kwKinWordEq hs hcs, kwDirichletScaling hc, h4]
    field_simp
  exact ⟨h1, h2, hvan, h4, h5, h6⟩

end Work.SmallBoxA0
