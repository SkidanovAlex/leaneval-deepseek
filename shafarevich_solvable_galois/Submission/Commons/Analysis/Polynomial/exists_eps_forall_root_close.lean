import Mathlib
import Submission.Commons.Analysis.Polynomial.exists_root_close_with_delta
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Analysis.Polynomial

theorem exists_eps_forall_root_close {K L : Type*} [NormedField K] [NormedField L] [Algebra K L]
    [IsAlgClosed L] (h_ext : ∀ k : K, ‖algebraMap K L k‖ = ‖k‖)
    {f₁ : Polynomial K} (hf₁1 : 1 ≤ f₁.natDegree) {δ : ℝ} (hδpos : 0 < δ)
    (hδsep : ∀ ⦃γ : L⦄, γ ∈ f₁.rootSet L → ∀ ⦃γ' : L⦄, γ' ∈ f₁.rootSet L →
      γ ≠ γ' → δ ≤ ‖γ - γ'‖) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (f₂ : Polynomial K), f₂.natDegree ≤ f₁.natDegree → f₂ ≠ 0 →
      (f₂ - f₁).supNorm < ε → ∀ ⦃α : L⦄, α ∈ f₁.rootSet L →
        ∃ β : L, β ∈ (f₂.map (algebraMap K L)).roots ∧ ‖α - β‖ < δ ∧
          ∀ ⦃γ : L⦄, γ ∈ f₁.rootSet L → γ ≠ α → ‖α - β‖ < ‖α - γ‖ := by
  obtain ⟨ε, hεpos, hεmain⟩ := exists_root_close_with_delta h_ext hf₁1 hδpos
  refine ⟨ε, hεpos, ?_⟩
  intro f₂ hf₂ hf₂0 hclose α hα
  obtain ⟨β, hβ, hβδ⟩ := hεmain f₂ hf₂ hf₂0 (IsAlgClosed.splits _) hclose hα
  exact ⟨β, hβ, hβδ, fun γ hγ hγne => lt_of_lt_of_le hβδ (hδsep hα hγ hγne.symm)⟩

end Commons.Analysis.Polynomial
