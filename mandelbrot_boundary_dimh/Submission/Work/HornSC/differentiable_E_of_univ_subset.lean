import Mathlib
import Submission.Work.Interfaces.HornParts

namespace Work.HornSC

open MandelDim

/-- If `φ⁻¹(B)` is all of `ℂ` (which happens only for the degenerate/contradictory case, see
`false_of_univ_subset_Btil`) and `B` lies in the parabolic basin, then the Fatou coordinate `φ`,
the lifted horn map `E = Φ ∘ φ` and the Abel equation `E (w+1) = E w + 1` hold globally. -/
theorem differentiable_E_of_univ_subset {f₀ : ℂ → ℂ} {D₀ B : Set ℂ}
    (d : MandelDim.ParabData f₀ D₀) (h : Set.univ ⊆ MandelDim.Btil d B)
    (hBsub : B ⊆ MandelDim.ParabolicBasin f₀ D₀) :
    Differentiable ℂ d.φ ∧ Differentiable ℂ (fun w : ℂ => d.Φ (d.φ w)) ∧
      ∀ w : ℂ, d.Φ (d.φ (w + 1)) = d.Φ (d.φ w) + 1 := by
  have hD : Set.univ ⊆ d.Dφ := fun w _ => (h (Set.mem_univ w)).1
  have hphi : DifferentiableOn ℂ d.φ Set.univ := d.φ_holo.mono hD
  have hbas : ∀ w : ℂ, d.φ w ∈ MandelDim.ParabolicBasin f₀ D₀ :=
    fun w => hBsub (h (Set.mem_univ w)).2
  refine ⟨differentiableOn_univ.mp hphi, ?_, ?_⟩
  · have hcomp : DifferentiableOn ℂ (d.Φ ∘ d.φ) Set.univ :=
      d.Φ_holo.comp hphi (fun w _ => hbas w)
    exact differentiableOn_univ.mp hcomp
  · intro w
    rw [d.φ_abel w (hD (Set.mem_univ w)) (hD (Set.mem_univ (w + 1))),
      d.Φ_abel (d.φ w) (hbas w)]

end Work.HornSC
