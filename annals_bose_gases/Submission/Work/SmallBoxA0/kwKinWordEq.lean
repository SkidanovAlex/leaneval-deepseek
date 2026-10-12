import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.SmallBoxA0.kwBoxExtend
import Submission.Work.SmallBoxA0.kwFderivZero
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

/-- The scaled bump `kwBump c` is smooth. -/
private lemma kwBump_contDiff (c : ℝ) : ContDiff ℝ ∞ (kwBump c) := by
  unfold kwBump
  have h1 : ContDiff ℝ ∞ (fun z : EuclideanSpace ℝ (Fin 3) => c • z) :=
    ContinuousLinearMap.contDiff
      (c • (1 : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3)))
  exact chiBase_contDiff.comp h1

/-- Chain rule for the slot-coordinate function `y ↦ kwBump c (y 0)` on `X 1`. -/
private lemma kwBump_fderiv_comp {c : ℝ} (x : X 1) :
    fderiv ℝ (fun y : X 1 => kwBump c (y 0)) x
      = (fderiv ℝ (kwBump c) (x 0)).comp
          ((ContinuousLinearMap.proj (0 : Fin 1)) : X 1 →L[ℝ] EuclideanSpace ℝ (Fin 3)) := by
  have hkw := kwBump_contDiff c
  have hproj_cd : ContDiff ℝ ∞ (fun y : X 1 =>
      (ContinuousLinearMap.proj (0 : Fin 1) : X 1 →L[ℝ] EuclideanSpace ℝ (Fin 3)) y) :=
    ContinuousLinearMap.contDiff
      ((ContinuousLinearMap.proj (0 : Fin 1)) : X 1 →L[ℝ] EuclideanSpace ℝ (Fin 3))
  have h := fderiv_comp (𝕜 := ℝ) (x := x)
    (f := fun y : X 1 =>
      (ContinuousLinearMap.proj (0 : Fin 1) : X 1 →L[ℝ] EuclideanSpace ℝ (Fin 3)) y)
    (g := kwBump c) (hkw.contDiffAt.differentiableAt (by simp))
    (hproj_cd.contDiffAt.differentiableAt (by simp))
  rw [show (fun y : X 1 => kwBump c (y 0)) = kwBump c ∘ (fun y : X 1 =>
      (ContinuousLinearMap.proj (0 : Fin 1) : X 1 →L[ℝ] EuclideanSpace ℝ (Fin 3)) y) from rfl,
      h, ContinuousLinearMap.fderiv]
  rfl

/-- Chain rule for the witness state along the kinetic directions `kcDir 1 0 k`. -/
private lemma kwPhi_fderiv_kcDir {s c : ℝ} (x : X 1) (k : Fin 3) :
    fderiv ℝ (kwPhi s c) x (kcDir 1 0 k)
      = (Real.sqrt (kwLam s c))⁻¹ * fderiv ℝ (kwBump c) (x 0) (kcStdBasis k) := by
  have hproj_cd : ContDiff ℝ ∞ (fun y : X 1 =>
      (ContinuousLinearMap.proj (0 : Fin 1) : X 1 →L[ℝ] EuclideanSpace ℝ (Fin 3)) y) :=
    ContinuousLinearMap.contDiff
      ((ContinuousLinearMap.proj (0 : Fin 1)) : X 1 →L[ℝ] EuclideanSpace ℝ (Fin 3))
  have hdiff : DifferentiableAt ℝ (fun y : X 1 => kwBump c (y 0)) x :=
    ((kwBump_contDiff c).comp hproj_cd).contDiffAt.differentiableAt (by simp)
  have hd : fderiv ℝ (kwPhi s c) x
      = (Real.sqrt (kwLam s c))⁻¹ • fderiv ℝ (fun y : X 1 => kwBump c (y 0)) x := by
    show fderiv ℝ (fun y : X 1 => (Real.sqrt (kwLam s c))⁻¹ * kwBump c (y 0)) x = _
    exact fderiv_const_mul hdiff _
  rw [hd, kwBump_fderiv_comp x]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
  rw [show (ContinuousLinearMap.proj (0 : Fin 1) : X 1 →L[ℝ] EuclideanSpace ℝ (Fin 3))
        (kcDir 1 0 k) = kcStdBasis k from rfl]
  rfl

/-- Continuity on `X 1` of `x ↦ fderiv ℝ (kwBump c) (x 0) (kcStdBasis k)`. -/
private lemma kwBump_dir_continuous {c : ℝ} (k : Fin 3) :
    Continuous (fun x : X 1 => fderiv ℝ (kwBump c) (x 0) (kcStdBasis k)) := by
  have hproj_cd : ContDiff ℝ ∞ (fun y : X 1 =>
      (ContinuousLinearMap.proj (0 : Fin 1) : X 1 →L[ℝ] EuclideanSpace ℝ (Fin 3)) y) :=
    ContinuousLinearMap.contDiff
      ((ContinuousLinearMap.proj (0 : Fin 1)) : X 1 →L[ℝ] EuclideanSpace ℝ (Fin 3))
  have hkw_cd : ContDiff ℝ ∞ (fun y : X 1 => kwBump c (y 0)) :=
    (kwBump_contDiff c).comp hproj_cd
  have hcd := firstDir_contDiff hkw_cd (kcDir 1 0 k)
  have heq : (fun x : X 1 => fderiv ℝ (fun y : X 1 => kwBump c (y 0)) x (kcDir 1 0 k))
      = fun x : X 1 => fderiv ℝ (kwBump c) (x 0) (kcStdBasis k) := by
    funext x
    rw [kwBump_fderiv_comp x]
    simp only [ContinuousLinearMap.comp_apply]
    rw [show (ContinuousLinearMap.proj (0 : Fin 1) : X 1 →L[ℝ] EuclideanSpace ℝ (Fin 3))
          (kcDir 1 0 k) = kcStdBasis k from rfl]
  rw [← heq]
  exact hcd.continuous

/-- Reduction of the kinetic word of the witness state to the Dirichlet energy of the scaled bump:
for `0 < s` and `2/s < c` (with `Λ := kwLam s c`),
`kinWord 1 s (kwPhi s c) = Λ⁻¹ * ∫ z : ℝ³, Σ_{k : Fin 3} (fderiv ℝ (kwBump c) z (kcStdBasis k))^2`
(all names from `Submission/Work/SmallBoxA0/KinWitnessDefs.lean` and
`Submission/CentredGap.lean`).  The companion lemma `Work.SmallBoxA0.kwBoxExtend` (in
`Submission/Work/SmallBoxA0/kwBoxExtend.lean`) is available and should be imported.

HINT.
`kinWord 1 s Φ = Σ_{i : Fin 1} Σ_{k : Fin 3} ∫ x in abox 1 s, (fderiv ℝ Φ x (kcDir 1 i k))^2`
unfolds, and `Fin.sum_univ_one` collapses the particle sum to `i = 0`.

Step 1 (chain rule).  `kwPhi s c = fun x : X 1 => (√Λ)⁻¹ * kwBump c (x 0)`; `fderiv_const_mul`
plus `fderiv_comp` with the continuous linear projection `ContinuousLinearMap.proj (0 : Fin 1)`
(whose derivative is itself, `ContinuousLinearMap.fderiv`) give, using
`kcDir 1 0 k = Function.update 0 0 (kcStdBasis k)`,
`fderiv ℝ (kwPhi s c) x (kcDir 1 0 k) = (√Λ)⁻¹ * fderiv ℝ (kwBump c) (x 0) (kcStdBasis k)`.
(The same identity is being proved independently as `Work.SmallBoxA0.kwPhiFderiv`.)

Step 2 (extension to `ℝ³`).  For `z ∉ acube s` one has `1/(2c) < ‖z‖` (`z ∉ acube s` gives a
coordinate with `|z m| > s/2` and `|z m| ≤ ‖z‖`; `1/(2c) < s/2` from `0 < s`, `2/s < c`), hence
`fderiv ℝ (kwBump c) z = 0` (`kwBump c` is eventually `0` near `z`: the set
`{w | 1/(2c) < ‖w‖}` is open and `chiBase (c•w) = 0` there since `‖c•w‖ = c‖w‖ > 1/2`; then
`Filter.EventuallyEq.fderiv_eq` with the constant `0`, `fderiv_const`).  So each
`G_k z := (fderiv ℝ (kwBump c) z (kcStdBasis k))^2` vanishes for `z ∉ acube s`, and
`Work.SmallBoxA0.kwBoxExtend` turns `∫ x in abox 1 s, (fderiv ℝ (kwBump c) (x 0) (kcStdBasis k))^2`
into `∫ z : ℝ³, G_k z`.

Step 3 (algebra).  `((√Λ)⁻¹ * v)^2 = Λ⁻¹ * v^2`: `(√Λ)⁻¹ ^ 2 = ((√Λ)^2)⁻¹ = Λ⁻¹` by
`Real.sq_sqrt` with `0 ≤ Λ`.  Then `Finset.mul_sum` pulls `Λ⁻¹` out of the sum over `k : Fin 3`
and `MeasureTheory.integral_finsetSum` plus `MeasureTheory.integral_const_mul` out of the integral
(integrability of each `G_k` on the compact box from continuity of
`x ↦ (fderiv ℝ (kwBump c) x (kcStdBasis k))`; `Submission.BoseGases.integrableOn_abox_of_continuous`
is available, as is `Submission.BoseGases.firstDir_contDiff`).
(Note the identity itself, including the case `Λ = 0`, does not need `Λ > 0`.) -/
lemma kwKinWordEq {s c : ℝ} (hs : 0 < s) (hcs : 2 / s < c) :
    kinWord 1 s (kwPhi s c)
      = (kwLam s c)⁻¹ *
          ∫ z : EuclideanSpace ℝ (Fin 3), ∑ k : Fin 3, (fderiv ℝ (kwBump c) z (kcStdBasis k)) ^ 2 := by
  have hΛ : 0 ≤ kwLam s c := by
    rw [kwLam]
    exact integral_nonneg (fun x => sq_nonneg _)
  have hsq : ((Real.sqrt (kwLam s c))⁻¹) ^ 2 = (kwLam s c)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt hΛ]
  have hpw : ∀ (x : X 1) (k : Fin 3), (fderiv ℝ (kwPhi s c) x (kcDir 1 0 k)) ^ 2
      = (kwLam s c)⁻¹ * (fderiv ℝ (kwBump c) (x 0) (kcStdBasis k)) ^ 2 := by
    intro x k
    rw [kwPhi_fderiv_kcDir x k, mul_pow, hsq]
  have hint : ∀ k : Fin 3, IntegrableOn
      (fun x : X 1 => (fderiv ℝ (kwBump c) (x 0) (kcStdBasis k)) ^ 2) (abox 1 s) volume :=
    fun k => integrableOn_abox_of_continuous hs ((kwBump_dir_continuous k).pow 2)
  unfold kinWord
  rw [Fin.sum_univ_one]
  calc ∑ k : Fin 3, ∫ x in abox 1 s, (fderiv ℝ (kwPhi s c) x (kcDir 1 0 k)) ^ 2
      = ∑ k : Fin 3, (kwLam s c)⁻¹ *
          ∫ x in abox 1 s, (fderiv ℝ (kwBump c) (x 0) (kcStdBasis k)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro k _
        rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun x => hpw x k)),
            MeasureTheory.integral_const_mul]
    _ = (kwLam s c)⁻¹ * ∑ k : Fin 3,
          ∫ x in abox 1 s, (fderiv ℝ (kwBump c) (x 0) (kcStdBasis k)) ^ 2 := by
        rw [← Finset.mul_sum]
    _ = (kwLam s c)⁻¹ * ∫ x in abox 1 s,
          ∑ k : Fin 3, (fderiv ℝ (kwBump c) (x 0) (kcStdBasis k)) ^ 2 := by
        congr 1
        exact (MeasureTheory.integral_finsetSum (s := Finset.univ)
          (f := fun k : Fin 3 => fun x : X 1 =>
            (fderiv ℝ (kwBump c) (x 0) (kcStdBasis k)) ^ 2)
          (fun k _ => hint k)).symm
    _ = (kwLam s c)⁻¹ * ∫ z : EuclideanSpace ℝ (Fin 3),
          ∑ k : Fin 3, (fderiv ℝ (kwBump c) z (kcStdBasis k)) ^ 2 := by
        congr 1
        exact kwBoxExtend (s := s)
          (F := fun z : EuclideanSpace ℝ (Fin 3) =>
            ∑ k : Fin 3, (fderiv ℝ (kwBump c) z (kcStdBasis k)) ^ 2) (by
              intro z hz
              apply Finset.sum_eq_zero
              intro k _
              rw [kwFderivZero hs hcs hz, ContinuousLinearMap.zero_apply]
              ring)

end Work.SmallBoxA0
