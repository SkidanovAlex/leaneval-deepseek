import Mathlib
import Submission.Work.Modular.Basic

namespace Work.Modular

open UpperHalfPlane ModularForm
open scoped Manifold MatrixGroups ModularForm

/-- A holomorphic function on `ℍ` that is invariant under the slash action of `SL(2, ℤ)` of
weight `k` and bounded at `i∞` is the underlying function of a Mathlib level-one modular form
of weight `k`.  (Boundedness at the other cusps is automatic since `SL(2, ℤ)` has only one
cusp, namely `i∞`.) -/
theorem modularForm_of_slash_invariant {k : ℤ} {f : ℍ → ℂ}
    (hper : ∀ γ : SL(2, ℤ), f ∣[k] γ = f) (hhol : MDiff f) (hbdd : IsBoundedAtImInfty f) :
    ∃ g : ModularForm 𝒮ℒ k, ⇑g = f := by
  -- `𝒮ℒ` is the range of `SL(2, ℤ) → GL(2, ℝ)`, so invariance under `SL(2, ℤ)` is exactly
  -- the slash-invariance of the `SlashInvariantForm` structure.
  refine ⟨{ toSlashInvariantForm := ⟨f, ?_⟩, holo' := hhol, bdd_at_cusps' := ?_ }, rfl⟩
  · rintro γ ⟨δ, rfl⟩
    exact hper δ
  -- `SL(2, ℤ)` has a single cusp, so every cusp is the image of `∞` under some `γ`,
  -- and `f ∣[k] γ = f` is bounded at `∞` by hypothesis.
  · intro c hc
    rw [OnePoint.isBoundedAt_iff_exists_SL2Z hc]
    obtain ⟨γ, rfl⟩ := isCusp_SL2Z_iff'.mp hc
    exact ⟨γ, rfl, by rw [hper γ]; exact hbdd⟩

end Work.Modular
