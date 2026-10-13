import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE5.Basic
import Submission.Work.WilE5.Calc.hasFDerivAt_eaEval
import Submission.Work.WilE9.Ift.AppendCLM

namespace Work.WilE7.Aux

open WilkiesDesign WilkiesDesign.E

/-- `y ↦ Fin.append u y` (with `u` a fixed base point) is an affine map whose linear part is
`y ↦ Fin.append 0 y`, realised as the continuous linear map `appendCLM p q ∘ inr`. -/
lemma hasFDerivAt_append_const (p q : ℕ) (u : Fin p → ℝ) (y₀ : Fin q → ℝ) :
    HasFDerivAt (fun y : Fin q → ℝ => Fin.append u y)
      ((Work.WilE9.Ift.appendCLM p q).comp
        (ContinuousLinearMap.inr ℝ (Fin p → ℝ) (Fin q → ℝ))) y₀ := by
  have h1 : HasFDerivAt (fun y : Fin q → ℝ => (u, y))
      ((0 : (Fin q → ℝ) →L[ℝ] (Fin p → ℝ)).prod
        (1 : (Fin q → ℝ) →L[ℝ] (Fin q → ℝ))) y₀ :=
    (hasFDerivAt_const u y₀).prodMk (hasFDerivAt_id (𝕜 := ℝ) y₀)
  have h2 : ((0 : (Fin q → ℝ) →L[ℝ] (Fin p → ℝ)).prod
        (1 : (Fin q → ℝ) →L[ℝ] (Fin q → ℝ)))
      = ContinuousLinearMap.inr ℝ (Fin p → ℝ) (Fin q → ℝ) := rfl
  rw [h2] at h1
  have h3 := (ContinuousLinearMap.hasFDerivAt (Work.WilE9.Ift.appendCLM p q)).comp y₀ h1
  refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
  simp [Function.comp_apply, Work.WilE9.Ift.appendCLM_apply]

theorem fibreFDeriv {p q : ℕ} {j r : ℕ} (c : WilkiesDesign.E.EAChain (p + q) r)
    (h : Fin j → WilkiesDesign.E.EAPoly (p + q) r) (z : Fin (p + q) → ℝ) :
    fderiv ℝ (fun y : Fin q → ℝ => fun a : Fin j =>
        WilkiesDesign.E.eaEval c (h a) (Fin.append (WilkiesDesign.E.projFirst p q z) y))
      (WilkiesDesign.E.projSnd p q z)
      = ContinuousLinearMap.pi (fun a : Fin j => (∑ l : Fin q,
          WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c (Work.WilE5.yDir p l) (h a)) z •
            (ContinuousLinearMap.proj l : (Fin q → ℝ) →L[ℝ] ℝ))) := by
  classical
  set L : (Fin q → ℝ) →L[ℝ] (Fin (p + q) → ℝ) :=
    (Work.WilE9.Ift.appendCLM p q).comp
      (ContinuousLinearMap.inr ℝ (Fin p → ℝ) (Fin q → ℝ)) with hLdef
  have hL_apply : ∀ v : Fin q → ℝ, L v = Fin.append (0 : Fin p → ℝ) v := by
    intro v
    rw [hLdef]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      Work.WilE9.Ift.appendCLM_apply]
  have hz : Fin.append (WilkiesDesign.E.projFirst p q z) (WilkiesDesign.E.projSnd p q z) = z := by
    funext i
    refine Fin.addCases (fun i' => ?_) (fun l => ?_) i
    · simp [WilkiesDesign.E.projFirst, Fin.append_left]
    · simp [WilkiesDesign.E.projSnd, Fin.append_right]
  have hA : HasFDerivAt (fun y : Fin q → ℝ => Fin.append (WilkiesDesign.E.projFirst p q z) y) L
      (WilkiesDesign.E.projSnd p q z) := by
    rw [hLdef]
    exact hasFDerivAt_append_const p q (WilkiesDesign.E.projFirst p q z)
      (WilkiesDesign.E.projSnd p q z)
  have hG : HasFDerivAt (fun w : Fin (p + q) → ℝ => fun a : Fin j => eaEval c (h a) w)
      (ContinuousLinearMap.pi (fun a : Fin j => ∑ i : Fin (p + q),
        (eaEval c (eaD c i (h a)) z) •
          (ContinuousLinearMap.proj i : (Fin (p + q) → ℝ) →L[ℝ] ℝ))) z :=
    hasFDerivAt_pi.mpr fun a => Work.WilE5.Calc.hasFDerivAt_eaEval c (h a) z
  have hG' : HasFDerivAt (fun w : Fin (p + q) → ℝ => fun a : Fin j => eaEval c (h a) w)
      (ContinuousLinearMap.pi (fun a : Fin j => ∑ i : Fin (p + q),
        (eaEval c (eaD c i (h a)) z) •
          (ContinuousLinearMap.proj i : (Fin (p + q) → ℝ) →L[ℝ] ℝ)))
      (Fin.append (WilkiesDesign.E.projFirst p q z) (WilkiesDesign.E.projSnd p q z)) := by
    rw [hz]; exact hG
  have hcomp : HasFDerivAt
      (fun y : Fin q → ℝ => fun a : Fin j => eaEval c (h a) (Fin.append (WilkiesDesign.E.projFirst p q z) y))
      ((ContinuousLinearMap.pi (fun a : Fin j => ∑ i : Fin (p + q),
        (eaEval c (eaD c i (h a)) z) •
          (ContinuousLinearMap.proj i : (Fin (p + q) → ℝ) →L[ℝ] ℝ))).comp L)
      (WilkiesDesign.E.projSnd p q z) := by
    have h4 := hG'.comp (WilkiesDesign.E.projSnd p q z) hA
    exact h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => rfl)
  rw [hcomp.fderiv]
  ext v a
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply, hL_apply v]
  rw [ContinuousLinearMap.sum_apply, Fin.sum_univ_add]
  simp only [ContinuousLinearMap.pi_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply,
    Fin.append_left, Fin.append_right, Pi.zero_apply, mul_zero, smul_eq_mul]
  simp [Work.WilE5.yDir]

end Work.WilE7.Aux
