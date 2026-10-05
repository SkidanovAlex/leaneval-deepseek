import Mathlib
import Submission.Work.RPCore.Flow.HamFlow
import Submission.Work.RPCore.Flow.flow_variational_eq
import Submission.Work.RPCore.Flow.flow_hasFDerivAt_nearId

namespace Work.RPCore.Flow

/-- Reading an endomorphism `M` of `ℝ × E` on the second factor, `snd ∘L M ∘L inr`, is a deviation
from the identity of at most `‖M - 1‖`: the projections have operator norm at most one. -/
lemma norm_snd_comp_inr_sub_one_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : ℝ × E →L[ℝ] ℝ × E) :
    ‖ContinuousLinearMap.snd ℝ ℝ E ∘L M ∘L ContinuousLinearMap.inr ℝ ℝ E - 1‖ ≤ ‖M - 1‖ := by
  have hcomp : (ContinuousLinearMap.snd ℝ ℝ E ∘L M ∘L ContinuousLinearMap.inr ℝ ℝ E) - 1
      = ContinuousLinearMap.snd ℝ ℝ E ∘L (M - 1) ∘L ContinuousLinearMap.inr ℝ ℝ E := by
    apply ContinuousLinearMap.ext
    intro v
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  rw [hcomp]
  set s := ContinuousLinearMap.snd ℝ ℝ E with hs
  set i := ContinuousLinearMap.inr ℝ ℝ E with hi
  have hs1 : ‖s‖ ≤ 1 := ContinuousLinearMap.norm_snd_le ℝ ℝ E
  have hi1 : ‖i‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun v => by
    rw [ContinuousLinearMap.inr_apply, Prod.norm_def, norm_zero,
      max_eq_right (norm_nonneg v), one_mul])
  have hM0 : 0 ≤ ‖M - 1‖ := norm_nonneg _
  calc ‖s ∘L (M - 1) ∘L i‖ ≤ ‖s‖ * ‖(M - 1) ∘L i‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖s‖ * (‖M - 1‖ * ‖i‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ 1 * (‖M - 1‖ * 1) := by
        apply mul_le_mul hs1
        · exact mul_le_mul_of_nonneg_left hi1 hM0
        · positivity
        · norm_num
    _ = ‖M - 1‖ := by ring

theorem Phi_nearId (Hh : Work.RPV.CptPerHam) {a b : ℝ} (ha : a ∈ Set.Icc (-1 : ℝ) 2)
    (hb : b ∈ Set.Icc (-1 : ℝ) 2) (x : Work.RPV.PS) :
    ‖fderiv ℝ (Work.RPCore.Phi Hh a b) x - 1‖
      ≤ Real.exp ((Work.RPCore.clampedData Hh).K * |b - a|) - 1 := by
  -- the global Grönwall bound on the derivative of the clamped flow on `ℝ × PS`
  have hglob := flow_hasFDerivAt_nearId (Work.RPCore.clampedField Hh)
    ((Work.RPCore.clampedField_contDiff_three Hh).of_le (by norm_num))
    (Work.RPCore.clampedData Hh).hK (Work.RPCore.clampFlow Hh)
    (fun _ y => ⟨fun s => Work.RPCore.clampFlow Hh s y, Work.RPCore.clampFlow_zero Hh y,
      Work.RPCore.clampFlow_curve Hh y, rfl⟩)
  obtain ⟨M, hM, hMb⟩ := hglob (b - a) (a, x)
  -- `Phi Hh a b` is `Prod.snd ∘ clampFlow Hh (b-a) ∘ (fun y => (a, y))`
  have hι : HasFDerivAt (fun y : Work.RPV.PS => ((a : ℝ), y))
      (ContinuousLinearMap.inr ℝ ℝ Work.RPV.PS) x := by
    have h1 : HasFDerivAt (fun y : Work.RPV.PS => (a : ℝ)) (0 : Work.RPV.PS →L[ℝ] ℝ) x :=
      hasFDerivAt_const (a : ℝ) x
    have h2 : HasFDerivAt (fun y : Work.RPV.PS => y)
        (1 : Work.RPV.PS →L[ℝ] Work.RPV.PS) x := hasFDerivAt_id x
    have h := h1.prodMk h2
    rwa [show (0 : Work.RPV.PS →L[ℝ] ℝ).prod (1 : Work.RPV.PS →L[ℝ] Work.RPV.PS)
        = ContinuousLinearMap.inr ℝ ℝ Work.RPV.PS from rfl] at h
  have hcomp1 : HasFDerivAt (fun y : Work.RPV.PS => Work.RPCore.clampFlow Hh (b - a) (a, y))
      (M ∘L ContinuousLinearMap.inr ℝ ℝ Work.RPV.PS) x := hM.comp x hι
  have hcomp2 := hasFDerivAt_snd.comp x hcomp1
  have hfun : (Prod.snd ∘ fun y : Work.RPV.PS => Work.RPCore.clampFlow Hh (b - a) (a, y))
      = Work.RPCore.Phi Hh a b := rfl
  rw [← hfun, hcomp2.fderiv]
  exact le_trans (norm_snd_comp_inr_sub_one_le M) hMb

end Work.RPCore.Flow
