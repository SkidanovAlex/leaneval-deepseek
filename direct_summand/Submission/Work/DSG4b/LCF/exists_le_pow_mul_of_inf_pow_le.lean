import Mathlib
import Submission.Work.DSG4b.LCF.Basic

namespace Work.DSG4b.LCF

/-- Artin–Rees in the form `I ⊓ 𝔪 ^ n ≤ 𝔪 ^ (n - k) * I` for all `n ≥ k`.

This is the standard corollary of the Artin–Rees lemma
(`Ideal.exists_pow_inf_eq_pow_smul`): applied to `M = R` and the submodule `N = I`, it
gives `𝔪 ^ n • ⊤ ⊓ I = 𝔪 ^ (n - k) • (𝔪 ^ k • ⊤ ⊓ I)`, and since `𝔪 ^ m • ⊤ = 𝔪 ^ m`
and `𝔪 ^ k • ⊤ ⊓ I ≤ I`, the right-hand side is contained in `𝔪 ^ (n - k) • I = 𝔪 ^ (n - k) * I`. -/
theorem exists_le_pow_mul_of_inf_pow_le {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I 𝔪 : Ideal R) : ∃ k : ℕ, ∀ n ≥ k, I ⊓ 𝔪 ^ n ≤ 𝔪 ^ (n - k) * I := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (R := R) (M := R) 𝔪 (I : Submodule R R)
  refine ⟨k, fun n hn => ?_⟩
  -- the scalar-multiple submodules `𝔪 ^ m • ⊤` are just the ideals `𝔪 ^ m`
  have h1 : 𝔪 ^ n • (⊤ : Submodule R R) = (𝔪 ^ n : Submodule R R) := by ext x; simp
  have h2 : 𝔪 ^ k • (⊤ : Submodule R R) = (𝔪 ^ k : Submodule R R) := by ext x; simp
  have h : (𝔪 ^ n : Submodule R R) ⊓ (I : Submodule R R)
      = 𝔪 ^ (n - k) • ((𝔪 ^ k : Submodule R R) ⊓ (I : Submodule R R)) := by
    have h3 := hk n hn
    rw [h1, h2] at h3
    exact h3
  rw [← Ideal.smul_eq_mul]
  calc (I ⊓ 𝔪 ^ n : Ideal R) = (𝔪 ^ n ⊓ I : Ideal R) := inf_comm I (𝔪 ^ n)
    _ = (𝔪 ^ (n - k) • (𝔪 ^ k ⊓ I) : Ideal R) := h
    _ ≤ (𝔪 ^ (n - k) • I : Ideal R) := smul_mono_right _ inf_le_right

end Work.DSG4b.LCF
