import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.Core18ScalarActionNormalizes

/-!
# GW design pass 18, item A, A2: `S ≤ N_G(X)` for every `X ≤ F(U)` (proved from A1)

Bender p. 222 (Thm 2.10, second half), the step the printed proof leaves implicit: once every
`s ∈ S − S₀` centralizes or inverts every `O_p(U)` (the per-prime dichotomy of the first half),
every element of `S` does (elements of `S₀` are products of two elements of `S − S₀`), so
**every subgroup of `F(U)` is `S`-invariant**.  Hence `S ≤ N_G(X) ≤ M` for *every* `M ⊇ N_G(X)`
and the "bad configuration" `N_G(X) ⊔ S = ⊤` never occurs.
-/

namespace Work.GW18

open Subgroup

theorem Core18SNormalizesOfScalar {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    (hact : ∀ s ∈ (B.S : Subgroup G), s ∉ B.S0 → ∀ p : ℕ, p.Prime →
      (∀ z ∈ Work.GW2.pCoreIn p B.U, s * z * s⁻¹ = z) ∨
        (∀ z ∈ Work.GW2.pCoreIn p B.U, s * z * s⁻¹ = z⁻¹))
    (X : Subgroup G) (hX : X ≤ Work.GW2.fittingIn B.U) :
    (B.S : Subgroup G) ≤ Subgroup.normalizer (X : Set G) := by
  -- an element of `S − S₀`
  have hex : ∃ s₁ ∈ (B.S : Subgroup G), s₁ ∉ B.S0 := by
    by_contra h
    push_neg at h
    have hle : (B.S : Subgroup G) ≤ B.S0 := fun x hx => h x hx
    have h1 : B.S0.relIndex (B.S : Subgroup G) = 1 :=
      Subgroup.relIndex_eq_one.mpr hle
    rw [B.S0_index] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨s₁, hs₁, hs₁0⟩ := hex
  have hN : ∀ s ∈ (B.S : Subgroup G), s ∉ B.S0 → s ∈ Subgroup.normalizer (X : Set G) :=
    fun s hs hs0 => Core18ScalarActionNormalizes B.U s (hact s hs hs0) X hX
  intro σ hσ
  by_cases hσ0 : σ ∈ B.S0
  · -- `σ = s₁ * (s₁⁻¹ * σ)` with both factors in `S − S₀`
    have h2 : s₁⁻¹ * σ ∈ (B.S : Subgroup G) := (B.S : Subgroup G).mul_mem
      ((B.S : Subgroup G).inv_mem hs₁) hσ
    have h20 : s₁⁻¹ * σ ∉ B.S0 := by
      intro h
      apply hs₁0
      have : s₁ = σ * (s₁⁻¹ * σ)⁻¹ := by group
      rw [this]
      exact B.S0.mul_mem hσ0 (B.S0.inv_mem h)
    have : σ = s₁ * (s₁⁻¹ * σ) := by group
    rw [this]
    exact (Subgroup.normalizer (X : Set G)).mul_mem (hN s₁ hs₁ hs₁0) (hN _ h2 h20)
  · exact hN σ hσ hσ0

end Work.GW18
