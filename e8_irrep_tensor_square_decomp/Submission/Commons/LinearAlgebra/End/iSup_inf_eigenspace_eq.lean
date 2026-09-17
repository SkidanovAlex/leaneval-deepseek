import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.LinearAlgebra.End

/-- **`(⨆ p i) ⊓ eigenspace f (λ i₀) = p i₀` for an independent family of generalized
eigen-subspaces.** If `p : ι → Submodule K V` is a family of subspaces with `p i` contained in the
`λ i`-eigenspace of an endomorphism `f`, and the eigenvalues `λ i` are pairwise distinct, then the
part of the sum `⨆ i, p i` lying in the `λ i₀`-eigenspace is exactly `p i₀`.

(Proof: `Module.End.eigenspaces_iSupIndep f` gives `Disjoint (eigenspace f (λ i₀))
(⨆ (μ ≠ λ i₀), eigenspace f μ)`; the sum splits as `p i₀ ⊔ ⨆_{i ≠ i₀} p i`, and
`⨆_{i ≠ i₀} p i ≤ ⨆ (μ ≠ λ i₀), eigenspace f μ`, so `sup_inf_assoc_of_le` reduces the claim to
`p i₀ ⊔ ⊥ = p i₀`.) -/
theorem iSup_inf_eigenspace_eq {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f : Module.End K V) (lam : ι → K) (hlam : Function.Injective lam)
    (p : ι → Submodule K V) (hp : ∀ i, p i ≤ Module.End.eigenspace f (lam i)) (i₀ : ι) :
    (⨆ i, p i) ⊓ Module.End.eigenspace f (lam i₀) = p i₀ := by
  have hdisj : Disjoint (Module.End.eigenspace f (lam i₀))
      (⨆ (μ : K) (_ : μ ≠ lam i₀), Module.End.eigenspace f μ) :=
    f.eigenspaces_iSupIndep (lam i₀)
  have hQbot : (⨆ (μ : K) (_ : μ ≠ lam i₀), Module.End.eigenspace f μ) ⊓
      Module.End.eigenspace f (lam i₀) = ⊥ := by
    rw [inf_comm]; exact hdisj.eq_bot
  have hle : (⨆ i, p i) ≤ p i₀ ⊔ (⨆ (μ : K) (_ : μ ≠ lam i₀), Module.End.eigenspace f μ) := by
    refine iSup_le fun i => ?_
    by_cases hi : i = i₀
    · subst hi; exact le_sup_left
    · have hne : lam i ≠ lam i₀ := fun h => hi (hlam h)
      have h1 : Module.End.eigenspace f (lam i) ≤
          (⨆ (μ : K) (_ : μ ≠ lam i₀), Module.End.eigenspace f μ) :=
        le_iSup₂ (f := fun (μ : K) (_ : μ ≠ lam i₀) => Module.End.eigenspace f μ) (lam i) hne
      exact le_trans (hp i) (le_trans h1 le_sup_right)
  apply le_antisymm
  · calc (⨆ i, p i) ⊓ Module.End.eigenspace f (lam i₀)
        ≤ (p i₀ ⊔ (⨆ (μ : K) (_ : μ ≠ lam i₀), Module.End.eigenspace f μ)) ⊓ Module.End.eigenspace f (lam i₀) :=
          inf_le_inf hle le_rfl
      _ = p i₀ ⊔ ((⨆ (μ : K) (_ : μ ≠ lam i₀), Module.End.eigenspace f μ) ⊓ Module.End.eigenspace f (lam i₀)) :=
          sup_inf_assoc_of_le _ (hp i₀)
      _ = p i₀ := by rw [hQbot, sup_bot_eq]
  · exact le_inf (le_iSup p i₀) (hp i₀)

end Commons.LinearAlgebra.End