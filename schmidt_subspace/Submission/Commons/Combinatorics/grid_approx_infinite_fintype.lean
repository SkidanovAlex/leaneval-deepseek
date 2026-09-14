import Mathlib
import Submission.Commons.Combinatorics.grid_approx_infinite

namespace Commons.Combinatorics

/-- The `Fin n` grid approximation lemma transported to an arbitrary finite index type. -/
theorem grid_approx_infinite_fintype {ι τ : Type*} [Fintype τ] (d : ι → τ → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (γ : ℝ) (hγ : 0 < γ) (Y : Set ι) (hY : Y.Infinite)
    (hball : ∀ i ∈ Y, ∀ t, |d i t| ≤ B) :
    ∃ dbar : τ → ℝ, (∀ t, dbar t ≤ B + γ) ∧
      {i ∈ Y | ∀ t, d i t ≤ dbar t ∧ dbar t ≤ d i t + γ}.Infinite := by
  classical
  let e : τ ≃ Fin (Fintype.card τ) := Fintype.equivFin τ
  let d' : ι → Fin (Fintype.card τ) → ℝ := fun i k => d i (e.symm k)
  have hball' : ∀ i ∈ Y, ∀ k : Fin (Fintype.card τ), |d' i k| ≤ B := by
    intro i hi k
    exact hball i hi (e.symm k)
  obtain ⟨dbar', hdbar', hinf⟩ :=
    grid_approx_infinite d' B hB γ hγ Y hY hball'
  refine ⟨fun t => dbar' (e t), ?_, ?_⟩
  · intro t
    exact hdbar' (e t)
  · refine Set.Infinite.mono ?_ hinf
    rintro i ⟨hi, h⟩
    refine ⟨hi, fun t => ?_⟩
    have ht := h (e t)
    simp only [d'] at ht
    rw [e.symm_apply_apply t] at ht
    exact ht

end Commons.Combinatorics
