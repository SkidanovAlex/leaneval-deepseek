import Mathlib

namespace Work.ORLocInd.Howie

theorem abstract_tietze {A B : Type*} [Group A] [Group B] (ι : A →* B) (σ : B →* A)
    (N : Subgroup B) [N.Normal] (N' : Subgroup A) [N'.Normal]
    (hσι : ∀ a : A, σ (ι a) = a) (hσN : ∀ b ∈ N, σ b ∈ N') (hιN' : ∀ a ∈ N', ι a ∈ N)
    (hcong : ∀ b : B, ι (σ b) * b⁻¹ ∈ N)
    (Φ : A ⧸ N' →* B ⧸ N) (hΦ : ∀ a : A, Φ (QuotientGroup.mk a) = QuotientGroup.mk (ι a)) :
    Function.Bijective Φ := by
  constructor
  · -- injectivity: `Φ (mk a) = Φ (mk a')` gives `ι a N = ι a' N`, and applying `σ`
    -- yields `a N' = a' N'` since `σ N ⊆ N'` and `σ ∘ ι = id`.
    intro x y hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective y
    have hxy' : (QuotientGroup.mk (ι a) : B ⧸ N) = QuotientGroup.mk (ι a') := by
      rw [← hΦ a, ← hΦ a']; exact hxy
    rw [QuotientGroup.eq] at hxy' ⊢
    have h : σ ((ι a)⁻¹ * ι a') ∈ N' := hσN _ hxy'
    rwa [map_mul, map_inv, hσι a, hσι a'] at h
  · -- surjectivity: for `b : B`, the class of `σ b` maps to `ι (σ b) N = b N`
    -- because `ι (σ b) * b⁻¹ ∈ N`.
    intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    refine ⟨QuotientGroup.mk (σ b), ?_⟩
    rw [hΦ (σ b), eq_comm, QuotientGroup.eq]
    exact (inferInstance : N.Normal).mem_comm (hcong b)

end Work.ORLocInd.Howie
