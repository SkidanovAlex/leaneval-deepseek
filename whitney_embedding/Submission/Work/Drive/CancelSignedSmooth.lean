import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Whitney.CancelSigned

/-!
# The smooth-arc signed cancellation interface

`Work.Drive.HasCancelSignedSmooth` is `Work.Whitney.HasCancelSigned` with the two bigon arcs
additionally `C^∞` on `ℝ` and immersive on `[0,1]` — the hypotheses under which the *smooth*
collar push `Work.Drive.HasPushSignedSmooth` applies.

`Work.Drive.hasCancelSignedSmooth_of_hasPushSignedSmooth` is
`Work.Whitney.hasCancelSigned_of_hasPushSigned` verbatim: the arc hypotheses are simply handed to
the push, and the cancellation itself only consumes the resulting ambient push data.
-/

namespace Work.Drive

open scoped Manifold ContDiff
open Topology Work.Whitney

set_option linter.unusedVariables false

/-- **The smooth-arc signed cancellation.**  `Work.Whitney.HasCancelSigned` with the two arcs
`C^∞` on `ℝ` and immersive on `[0,1]`. -/
def HasCancelSignedSmooth (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M] : Prop :=
  ∀ (hn : 3 ≤ n) (f : M → EuclideanSpace ℝ (Fin (2 * n)))
      (hf : ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f)
      (himm : ∀ y, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) f y))
      (W : Set M) (hWopen : IsOpen W) (hWcpt : IsCompact (closure W))
      (p₁ p₂ q₁ q₂ : M)
      (hW₁ : p₁ ∈ W) (hW₂ : p₂ ∈ W) (hW₃ : q₁ ∈ W) (hW₄ : q₂ ∈ W)
      (hp₁p₂ : p₁ ≠ p₂) (hq₁q₂ : q₁ ≠ q₂)
      (hp₁q₁ : p₁ ≠ q₁) (hp₁q₂ : p₁ ≠ q₂) (hp₂q₁ : p₂ ≠ q₁) (hp₂q₂ : p₂ ≠ q₂)
      (hfp : f p₁ = f p₂) (hfq : f q₁ = f q₂)
      (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
        y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
          (y = q₂ ∧ z = q₁))
      (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
      (htransP : (mfderiv (𝓡 n) (𝓡 (2 * n)) f p₁).range ⊔
        (mfderiv (𝓡 n) (𝓡 (2 * n)) f p₂).range = ⊤)
      (htransQ : (mfderiv (𝓡 n) (𝓡 (2 * n)) f q₁).range ⊔
        (mfderiv (𝓡 n) (𝓡 (2 * n)) f q₂).range = ⊤)
      (γ₁ γ₂ : ℝ → M) (hγ₁ : Continuous γ₁) (hγ₂ : Continuous γ₂)
      (hγ₁0 : γ₁ 0 = p₁) (hγ₁1 : γ₁ 1 = q₁) (hγ₂0 : γ₂ 0 = p₂) (hγ₂1 : γ₂ 1 = q₂)
      (hγW₁ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ W)
      (hγW₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t ∈ W)
      (hγ₁inj : Set.InjOn γ₁ (Set.Icc (0 : ℝ) 1))
      (hγ₂inj : Set.InjOn γ₂ (Set.Icc (0 : ℝ) 1))
      (hγ₁smooth : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ₁) (hγ₂smooth : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ₂)
      (hγ₁imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
        Function.Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ₁ t))
      (hγ₂imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
        Function.Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ₂ t))
      (hγdisj : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
        γ₁ s = γ₂ t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
      (hγend : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
        f (γ₁ s) = f (γ₂ t) → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hsign : OppositeType f γ₁ γ₂ p₁ p₂ q₁ q₂),
    ∃ (f' : M → EuclideanSpace ℝ (Fin (2 * n))),
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ f' ∧
      (∀ y, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) f' y)) ∧
      (∀ y : M, y ∉ W → f' y = f y) ∧
      doubleSet f' = doubleSet f \ {(p₁, p₂), (p₂, p₁), (q₁, q₂), (q₂, q₁)} ∧
      (∀ (u v : M), u ∉ W → v ∉ W →
        ∀ (c₁ c₂ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))),
          u ∈ c₁.source → v ∈ c₂.source →
          pairDet f' c₁ c₂ u v = pairDet f c₁ c₂ u v)

/-- **The smooth push gives the smooth cancellation.** -/
theorem hasCancelSignedSmooth_of_hasPushSignedSmooth {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (h : HasPushSignedSmooth n M) : HasCancelSignedSmooth n M := by
  intro hn f hf himm W hWopen hWcpt p₁ p₂ q₁ q₂ hW₁ hW₂ hW₃ hW₄ hp₁p₂ hq₁q₂
    hp₁q₁ hp₁q₂ hp₂q₁ hp₂q₂ hfp hfq hclean hsep htransP htransQ γ₁ γ₂ hγ₁ hγ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1
    hγW₁ hγW₂ hγ₁inj hγ₂inj hγ₁sm hγ₂sm hγ₁imm hγ₂imm hγdisj hγend hsign
  obtain ⟨W₀, O, ψ, σ, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄, h₁₅,
    h₁₆⟩ := h hn f hf himm W hWopen hWcpt p₁ p₂ q₁ q₂ hW₁ hW₂ hW₃ hW₄ hp₁p₂ hq₁q₂
      hp₁q₁ hp₁q₂ hp₂q₁ hp₂q₂ hfp hfq hclean hsep htransP htransQ γ₁ γ₂ hγ₁ hγ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1
      hγW₁ hγW₂ hγ₁inj hγ₂inj hγ₁sm hγ₂sm hγ₁imm hγ₂imm hγdisj hγend hsign
  exact cancellation_of_pushData hn f hf himm W hWopen p₁ p₂ q₁ q₂ hW₁ hW₂ hW₃ hW₄ hclean hsep
    W₀ O ψ σ h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₂ h₁₃ h₁₀ h₁₁ h₁₄ h₁₅ h₁₆

end Work.Drive
