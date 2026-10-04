import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.CompSmooth

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

open scoped Topology

lemma pdR_bound_of_support {n : ℕ} (f : (Fin n → ℝ) → ℝ) (Kc : Set (Fin n → ℝ))
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hKc : IsCompact Kc) (hs : Function.support f ⊆ Kc) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (z : Fin n → ℝ) (r : Fin n), |Work.Diff.STE.pdR r f z| ≤ M := by
  -- `fderiv` is continuous
  have hcont : Continuous (fun z : Fin n → ℝ => fderiv ℝ f z) :=
    hf.continuous_fderiv (by simp)
  -- `f` vanishes on the (open) complement of `Kc`
  have hfy : ∀ y : Fin n → ℝ, y ∉ Kc → f y = 0 := by
    intro y hy
    by_contra h
    exact hy (hs (Function.mem_support.mpr h))
  -- hence `fderiv f` vanishes there
  have hfz : ∀ z : Fin n → ℝ, z ∉ Kc → fderiv ℝ f z = 0 := by
    intro z hz
    have hmem : Kcᶜ ∈ 𝓝 z := hKc.isClosed.isOpen_compl.mem_nhds hz
    have heq : f =ᶠ[𝓝 z] (fun _ : Fin n → ℝ => (0 : ℝ)) :=
      Filter.eventuallyEq_of_mem hmem (fun y hy => hfy y hy)
    have h0 : fderiv ℝ (fun _ : Fin n → ℝ => (0 : ℝ)) z = 0 := by simp
    rw [heq.fderiv_eq, h0]
  -- so `‖fderiv f ·‖` is continuous with compact support, hence bounded
  have hgcont : Continuous (fun z : Fin n → ℝ => ‖fderiv ℝ f z‖) := hcont.norm
  obtain ⟨C, hC⟩ := (hKc.image hgcont).bddAbove
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro z r
  have hbound : |Work.Diff.STE.pdR r f z| ≤ ‖fderiv ℝ f z‖ := by
    have hpd : Work.Diff.STE.pdR r f z = fderiv ℝ f z (Pi.single r (1 : ℝ)) := rfl
    rw [hpd]
    calc |fderiv ℝ f z (Pi.single r (1 : ℝ))|
        = ‖fderiv ℝ f z (Pi.single r (1 : ℝ))‖ := by rw [Real.norm_eq_abs]
      _ ≤ ‖fderiv ℝ f z‖ * ‖(Pi.single r (1 : ℝ) : Fin n → ℝ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ f z‖ * 1 := by rw [Pi.norm_single, norm_one]
      _ = ‖fderiv ℝ f z‖ := mul_one _
  by_cases hz : z ∈ Kc
  · have hCz : ‖fderiv ℝ f z‖ ≤ C :=
      hC (Set.mem_image_of_mem (fun z : Fin n → ℝ => ‖fderiv ℝ f z‖) hz)
    exact hbound.trans (hCz.trans (le_max_left C 0))
  · have hz0 : ‖fderiv ℝ f z‖ = 0 := by rw [hfz z hz, norm_zero]
    rw [hz0] at hbound
    exact hbound.trans (le_max_right C 0)

end Work.Diff.STE.B3
