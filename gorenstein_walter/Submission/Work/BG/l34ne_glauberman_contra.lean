import Mathlib
import Submission.Work.BG.glaubValue
import Submission.Work.BG.hatInjCore
import Submission.Work.BG.hatInjCountAlt
import Submission.Work.BG.hatInjParity
import Submission.Work.BG.modTwoIndep
import Submission.Work.BG.CharBridge
import Submission.Work.BG.Defs
import Submission.Work.BG.glaubCorrDistinct

namespace Work.BG

open OddOrder.RepresentationTheory Work.BG in
theorem l34ne_glauberman_contra {U : Type} [Group U] [Finite U] [Fintype U]
    [Invertible (Nat.card U : ℂ)] (hU : Odd (Nat.card U)) (σ : MulAut U) (hσ : σ * σ = 1)
    [Fintype ↥(Work.BG.fixedSubgroup σ)]
    [Invertible (Nat.card ↥(Work.BG.fixedSubgroup σ) : ℂ)]
    {α₁ α₂ : ClassFunction U ℂ} (hα₁ : IsIrreducibleCharacter α₁)
    (hα₂ : IsIrreducibleCharacter α₂)
    (hinv₁ : ∀ u : U, α₁ (σ u) = α₁ u) (hinv₂ : ∀ u : U, α₂ (σ u) = α₂ u)
    (hne : α₁ ≠ α₂)
    (hcong : ∀ c : ↥(Work.BG.fixedSubgroup σ), AlgIntModTwo (α₁ (c : U) + α₂ (c : U)) 0) : False := by
  -- The hypothesis is `α₁ + α₂ ≡ 0 (mod 2)` on `C_U(σ)`: pointwise on `C_U(σ)`,
  -- `α₁ ≡ -α₂ (mod 2)`, and since `α₂ - (-α₂) = 2 α₂` with `α₂` integral there,
  -- this says `α₁ ≡ α₂ (mod 2)` on `C_U(σ)`.
  --
  -- `Work.BG.glauberman_injective` (Bender–Glauberman 1981, Lemma 1.9: the correspondence
  -- `α ↦ α*` is injective — the row structure `glauberman_two`, the column parity
  -- `hatInjParity` and the count `hatInjCountAlt`) then forces `α₁ = α₂`.
  refine hne (glauberman_injective hU σ hσ (hatInjCountAlt hU σ hσ)
    (fun β => hatInjParity hU σ hσ β) hα₁ hinv₁ hα₂ hinv₂ ?_)
  intro c
  obtain ⟨d, hd, hd'⟩ := hcong c
  exact ⟨d - α₂ (c : U),
    hd.sub (isIntegral_apply_of_isIrreducibleCharacter hα₂ (c : U)),
    by linear_combination hd'⟩

end Work.BG
