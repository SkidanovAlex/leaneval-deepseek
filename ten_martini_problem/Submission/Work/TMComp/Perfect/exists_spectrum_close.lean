import Mathlib
import Submission.Work.TMC7Core.Scale.spectral_continuity
import Submission.Work.TMComp.spectrum_perturb

namespace Work.TMComp.Perfect

set_option linter.style.haveILetI false

open LeanEval.Analysis.TenMartini

theorem exists_spectrum_close {A B : LeanEval.Analysis.TenMartini.EllTwo →L[ℂ] LeanEval.Analysis.TenMartini.EllTwo} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) {γ : ℝ} (h : ‖A - B‖ ≤ γ) :
    ∀ z ∈ spectrum ℂ A, ∃ z' ∈ spectrum ℂ B, ‖z - z'‖ ≤ γ := by
  intro z hz
  -- The spectrum of `B` is nonempty because the spectrum of `A` contains `z`.
  haveI : Nontrivial (EllTwo →L[ℂ] EllTwo) := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    haveI : Subsingleton (EllTwo →L[ℂ] EllTwo) := hnt
    rw [spectrum.of_subsingleton A] at hz
    exact absurd hz (Set.notMem_empty z)
  -- Pick the point of `spectrum B` closest to `z`.
  obtain ⟨z', hzB, hmin⟩ := (spectrum.isCompact B).exists_isMinOn (spectrum.nonempty B)
      (f := fun w : ℂ => ‖z - w‖) (by fun_prop)
  refine ⟨z', hzB, ?_⟩
  by_contra hcon
  have hcon' : γ < ‖z - z'‖ := not_le.mp hcon
  -- Apply the strict perturbation result with an intermediate radius.
  have hlt : ‖A - B‖ < (γ + ‖z - z'‖) / 2 := by linarith
  obtain ⟨w, hwB, hwle⟩ := Work.TMComp.spectrum_perturb A B hA hB hz hlt
  have h1 : ‖z - z'‖ ≤ ‖z - w‖ := hmin hwB
  linarith

end Work.TMComp.Perfect
