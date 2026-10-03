import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.iterate_diffAt

namespace Work.Repel

/-- If `φ` is holomorphic on the open domain `Dφ` and the forward orbit of `φ w` stays in the open
set `Df` where `f` is holomorphic, then `w ↦ f^[n] (φ w)` is holomorphic on `U ⊆ Dφ`
(REPEL §6, `pert_orbit_eqOn` infrastructure). -/
theorem iterate_comp_phi {f₀ : ℂ → ℂ} {D₀ : Set ℂ}
    {d : MandelDim.ParabData f₀ D₀}
    {f : ℂ → ℂ} {Df : Set ℂ} {η y₁ : ℝ} {K K' : Set ℂ} {δ : ℝ}
    (P : MandelDim.PertData d f Df η y₁ K K' δ) (hDfopen : IsOpen Df)
    (hf : DifferentiableOn ℂ f Df) {U : Set ℂ} (hUsub : U ⊆ P.Dφ)
    (hiter : ∀ w ∈ U, ∀ j : ℕ, f^[j] (P.φ w) ∈ Df) (n : ℕ) :
    DifferentiableOn ℂ (fun w => f^[n] (P.φ w)) U := by
  intro w hw
  have hφ : DifferentiableAt ℂ P.φ w :=
    (P.φ_holo w (hUsub hw)).differentiableAt (P.Dφ_open.mem_nhds (hUsub hw))
  have hf_iter : DifferentiableAt ℂ f^[n] (P.φ w) :=
    differentiableAt_iterate n (fun i _hi =>
      (hf _ (hiter w hw i)).differentiableAt (hDfopen.mem_nhds (hiter w hw i)))
  exact (hf_iter.comp w hφ).differentiableWithinAt

end Work.Repel
