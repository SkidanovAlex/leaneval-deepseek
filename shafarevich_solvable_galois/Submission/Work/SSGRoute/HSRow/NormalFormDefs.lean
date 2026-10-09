import Mathlib
import Submission.Work.SSGRoute.HSRow.CokerFz
import Submission.Work.SSGRoute.HSRow.slice_mem_lcCocycles
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The normal form `Fz Φ` of a crossed homomorphism, extended off the decomposition group

`Fz Φ` (defined in `CokerFz`) is a `2`-cochain on `↥(decomp k A) → ↥(decomp k A) → M` built from a
crossed homomorphism `Φ : C = closure (zpowers σ) → Zr`; here we extend it by `0` to all of
`Gal(Ω/k) × Gal(Ω/k)` and record its basic values.
-/

open scoped Pointwise
open Classical

namespace Work.SSGRoute.HSRow

noncomputable section

/-- The normal form `Fz Φ`, extended by `0` off the decomposition group. -/
def Fzext (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (Φ : ↥(Ccl k Ω σ) → ↥(Zr p k Ω K M I)) : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M :=
  fun g h => if hg : g ∈ SSGRoute.decomp k H.A then
      (if hh : h ∈ SSGRoute.decomp k H.A then
        Fz p k Ω K M I σ H Φ ⟨g, hg⟩ ⟨h, hh⟩ else 0)
    else 0

@[simp] lemma Fzext_apply_of_mem
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (Φ : ↥(Ccl k Ω σ) → ↥(Zr p k Ω K M I)) (g h : ↥(SSGRoute.decomp k H.A)) :
    Fzext p k Ω K M I σ H Φ g h = Fz p k Ω K M I σ H Φ g h := by
  simp only [Fzext, dif_pos g.2, dif_pos h.2]

/-- **Normal form**: `Fzext Φ` vanishes in the second variable on `I`. -/
lemma Fzext_normal
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (Φ : ↥(Ccl k Ω σ) → ↥(Zr p k Ω K M I)) (hΦ1 : Φ 1 = 0)
    (g : Ω ≃ₐ[k] Ω) {n : Ω ≃ₐ[k] Ω} (hg : g ∈ SSGRoute.decomp k H.A) (hn : n ∈ I) :
    Fzext p k Ω K M I σ H Φ g n = 0 := by
  rw [Fzext, dif_pos hg, dif_pos (H.hI hn)]
  exact Fz_normal p k Ω K M I σ H Φ hΦ1 ⟨g, hg⟩ hn

/-- **The slice at `σ`**: `Fzext Φ (n, σ) = Φ σ (n)`. -/
lemma Fzext_slice
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (I : Subgroup (Ω ≃ₐ[k] Ω)) (σ : Ω ≃ₐ[k] Ω) (H : Hcx k Ω I σ)
    (Φ : ↥(Ccl k Ω σ) → ↥(Zr p k Ω K M I)) {n : Ω ≃ₐ[k] Ω} (hn : n ∈ I) :
    Fzext p k Ω K M I σ H Φ n σ = (Φ (sigC k Ω σ) : ↥I → M) ⟨n, hn⟩ := by
  rw [Fzext, dif_pos (H.hI hn), dif_pos H.hσ]
  exact Fz_slice p k Ω K M I σ H Φ hn

end

end Work.SSGRoute.HSRow
