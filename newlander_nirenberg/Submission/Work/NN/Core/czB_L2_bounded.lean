import Mathlib
import Submission.Work.NN.Core.czB_L2_aux
import Submission.Work.NN.Core.czbL2_bound_of_smooth
import Submission.Work.NN.Core.czbL2_bound_smooth
import Submission.Work.NN.Final.bmPot_linear

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace Work.NN.Core

open Work.CR.Flat.Cauchy

/-- Pointwise linearity of `dCoord` under subtraction. -/
lemma dCoord_sub_flat {n : ℕ} (i : Fin n) (u v : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ)
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    Work.CR.Flat.dCoord i (fun w => u w - v w) z = Work.CR.Flat.dCoord i u z - Work.CR.Flat.dCoord i v z := by
  have h : fderiv ℝ (fun w => u w - v w) z = fderiv ℝ u z - fderiv ℝ v z := fderiv_sub hu hv
  simp only [Work.CR.Flat.dCoord, h, sub_apply]
  ring

/-- **The final assembly.**  From the smooth-case bound (which is what `czB_L2_bound_smooth`
provides) the target statement follows by linearity and the mollification step
`czbL2_bound_of_smooth`. -/
theorem czB_L2_bounded_of_smooth {n : ℕ} (hn : 0 < n)
    (hsmooth : ∃ C : ℝ, 0 ≤ C ∧ ∀ h : Fin n → (Fin n → ℂ) → ℂ, (∀ j, ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (h j)) →
      (∀ j, HasCompactSupport (h j)) →
      ∫⁻ z : Fin n → ℂ, (∑ k : Fin n, ENNReal.ofReal
          ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2)
        ≤ ENNReal.ofReal (C ^ 2) *
          ∫⁻ z : Fin n → ℂ, (∑ j : Fin n, ENNReal.ofReal ‖h j z‖ ^ 2))
    (hmoll : ∀ C : ℝ,
      (∀ h : Fin n → (Fin n → ℂ) → ℂ, (∀ j, ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) (h j)) →
        (∀ j, HasCompactSupport (h j)) →
        ∫⁻ z : Fin n → ℂ, (∑ k : Fin n, ENNReal.ofReal
            ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2)
          ≤ ENNReal.ofReal (C ^ 2) *
            ∫⁻ z : Fin n → ℂ, (∑ j : Fin n, ENNReal.ofReal ‖h j z‖ ^ 2)) →
      ∀ h : Fin n → (Fin n → ℂ) → ℂ, (∀ j, ContDiff ℝ 1 (h j)) →
        (∀ j, HasCompactSupport (h j)) →
        ∫⁻ z : Fin n → ℂ, (∑ k : Fin n, ENNReal.ofReal
            ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2)
          ≤ ENNReal.ofReal (C ^ 2) *
            ∫⁻ z : Fin n → ℂ, (∑ j : Fin n, ENNReal.ofReal ‖h j z‖ ^ 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f g : Fin n → (Fin n → ℂ) → ℂ),
      (∀ j, ContDiff ℝ 1 (f j)) → (∀ j, ContDiff ℝ 1 (g j)) →
      (∀ j, HasCompactSupport (f j)) → (∀ j, HasCompactSupport (g j)) →
      (∫⁻ z : Fin n → ℂ, (∑ i : Fin n, ENNReal.ofReal
          ‖Work.CR.Flat.dCoord i (bmPotential f) z
            - Work.CR.Flat.dCoord i (bmPotential g) z‖ ^ 2)
        ≤ ENNReal.ofReal (C ^ 2) *
          ∫⁻ z : Fin n → ℂ, (∑ j : Fin n, ENNReal.ofReal ‖f j z - g j z‖ ^ 2)) := by
  obtain ⟨C, hC, hsm⟩ := hsmooth
  have hb := hmoll C hsm
  refine ⟨C, hC, ?_⟩
  intro f g hf hg hfc hgc
  set h : Fin n → (Fin n → ℂ) → ℂ := fun j y => f j y - g j y with hhdef
  have hC1 : ∀ j, ContDiff ℝ 1 (h j) := fun j => (hf j).sub (hg j)
  have hcs : ∀ j, HasCompactSupport (h j) := fun j => (hfc j).sub (hgc j)
  -- `bmPotential f - bmPotential g = bmPotential h` pointwise
  have hlin : ∀ z : Fin n → ℂ, bmPotential h z
      = bmPotential f z - bmPotential g z := by
    intro z
    rw [bmPotential_eq_bmPot, bmPotential_eq_bmPot, bmPotential_eq_bmPot]
    have h0 := Work.NN.Final.bmPot_linear hn (1 : ℂ) (-1) (fun j => (hf j).continuous)
      (fun j => (hg j).continuous) (fun j => hfc j) (fun j => hgc j) z
    have hfun : (fun j : Fin n => fun y : Fin n → ℂ => (1 : ℂ) * f j y + (-1 : ℂ) * g j y)
        = fun j y => f j y - g j y := by
      funext j y; ring
    rw [hfun] at h0
    rw [hhdef]
    simpa [sub_eq_add_neg] using h0
  have hpt : ∀ (i : Fin n) (z : Fin n → ℂ),
      Work.CR.Flat.dCoord i (bmPotential f) z - Work.CR.Flat.dCoord i (bmPotential g) z
        = Work.CR.Flat.dCoord i (bmPotential h) z := by
    intro i z
    have hcs' : ∀ l, HasCompactSupport (fun x : Fin n → ℂ => Work.CR.Flat.dCoord i (f l) (z + x)) :=
      fun l => (hasCompactSupport_dCoord (hfc l) i).comp_homeomorph (Homeomorph.addLeft z)
    have hcs'' : ∀ l, HasCompactSupport (fun x : Fin n → ℂ => Work.CR.Flat.dCoord i (g l) (z + x)) :=
      fun l => (hasCompactSupport_dCoord (hgc l) i).comp_homeomorph (Homeomorph.addLeft z)
    have hcont' : ∀ l, Continuous (fun x : Fin n → ℂ => Work.CR.Flat.dCoord i (f l) (z + x)) :=
      fun l => (continuous_dCoord_of_contDiff_one (hf l) i).comp (continuous_const.add continuous_id)
    have hcont'' : ∀ l, Continuous (fun x : Fin n → ℂ => Work.CR.Flat.dCoord i (g l) (z + x)) :=
      fun l => (continuous_dCoord_of_contDiff_one (hg l) i).comp (continuous_const.add continuous_id)
    rw [bmPotential_dCoord_eq hn hf hfc i z, bmPotential_dCoord_eq hn hg hgc i z,
      bmPotential_dCoord_eq hn hC1 hcs i z, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← MeasureTheory.integral_sub (integrable_bmKernel_mul hn l (hcont' l) (hcs' l))
      (integrable_bmKernel_mul hn l (hcont'' l) (hcs'' l))]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    change bmKernel l x * Work.CR.Flat.dCoord i (f l) (z + x)
        - bmKernel l x * Work.CR.Flat.dCoord i (g l) (z + x)
      = bmKernel l x * Work.CR.Flat.dCoord i (h l) (z + x)
    rw [← mul_sub, ← dCoord_sub_flat i (f l) (g l) (z + x) ((hf l).differentiable (by simp) (z+x))
      ((hg l).differentiable (by simp) (z+x)), hhdef]
  have hmain := hb h hC1 hcs
  calc (∫⁻ z : Fin n → ℂ, (∑ i : Fin n, ENNReal.ofReal
          ‖Work.CR.Flat.dCoord i (bmPotential f) z
            - Work.CR.Flat.dCoord i (bmPotential g) z‖ ^ 2))
      = ∫⁻ z : Fin n → ℂ, (∑ i : Fin n, ENNReal.ofReal
          ‖Work.CR.Flat.dCoord i (bmPotential h) z‖ ^ 2) := by
        refine lintegral_congr fun z => ?_
        rw [Finset.sum_congr rfl (fun i _ => by rw [hpt i z])]
    _ ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ z : Fin n → ℂ, (∑ j : Fin n, ENNReal.ofReal ‖h j z‖ ^ 2) := hmain
    _ = ENNReal.ofReal (C ^ 2) * ∫⁻ z : Fin n → ℂ, (∑ j : Fin n, ENNReal.ofReal
          ‖f j z - g j z‖ ^ 2) := by
        rw [hhdef]


/-- **The `L²` bound for `∂ bmPotential` requested by the caller.** -/
theorem czB_L2_bounded {n : ℕ} (hn : 0 < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f g : Fin n → (Fin n → ℂ) → ℂ),
      (∀ j, ContDiff ℝ 1 (f j)) → (∀ j, ContDiff ℝ 1 (g j)) →
      (∀ j, HasCompactSupport (f j)) → (∀ j, HasCompactSupport (g j)) →
      (∫⁻ z : Fin n → ℂ, (∑ i : Fin n, ENNReal.ofReal
          ‖Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential f) z
            - Work.CR.Flat.dCoord i (Work.CR.Flat.Cauchy.bmPotential g) z‖ ^ 2)
        ≤ ENNReal.ofReal (C ^ 2) *
          ∫⁻ z : Fin n → ℂ, (∑ j : Fin n, ENNReal.ofReal ‖f j z - g j z‖ ^ 2)) :=
  czB_L2_bounded_of_smooth (n := n) hn (czbL2_bound_smooth hn)
    (fun _ hsm => czbL2_bound_of_smooth (n := n) hn hsm)

end Work.NN.Core
