import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.atomPairG
import Submission.Work.BoseBoxFock.pairDecompPairSetGen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PotCubicLowBandAux.rowZeroSmall` — the cubic row vanishes for `n ≤ 1`

For `n ≤ 1` the label set `Submission.BoseGases.pairSet n` is empty, so the *pair* decomposition
of a rank-one slot word (`Work.BoseBoxFock.pairDecompPairSetGen`)

    `B(|w₁⟩⟨v₁|)(B(|w₂⟩⟨v₂|)Θ) − B((|w₁⟩⟨v₁|)∘(|w₂⟩⟨v₂|))Θ
        = ∑_{p ∈ pairSet n} (|w₁⟩⟨v₁|)^{(p.1)} (|w₂⟩⟨v₂|)^{(p.2)} Θ`

degenerates to `0`: there is no second particle.  Consequently the `(s,k)`-atom — the sum of the
two such words — vanishes, and with it the whole cubic row

    `potCubic (fun T => boxSlotSum e T) f g PHs E Θ = 0`     (`n ≤ 1`).

This is the small-`n` case of the assembly of `PotCubicLowBandG_holds`: there the target's
inequality reads `0 ≤ γℓ⁻²cnPlus`, and `cnPlus ≥ 0` closes it.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.PotCubicLowBandAux

open Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. `pairSet n` is empty for `n ≤ 1` -/

/-- **`pairSet n = ∅` for `n ≤ 1`**: there are no two distinct particle indices. -/
theorem pairSet_eq_empty_of_le_one {n : ℕ} (hn : n ≤ 1) :
    Submission.BoseGases.pairSet n = ∅ := by
  rw [Submission.BoseGases.pairSet, Finset.filter_eq_empty_iff]
  intro p _
  simp only [ne_eq, not_not]
  exact Fin.ext (by have h1 := p.1.isLt; have h2 := p.2.isLt; omega)

/-! ## 2. The rank-one slot word vanishes -/

/-- **The pair word vanishes for `n ≤ 1`.** -/
theorem rankOnePairWord_eq_zero_of_le_one {m n : ℕ} [NeZero m] {ℓ : ℝ}
    {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (w₁ v₁ w₂ v₂ : Fin m → ℝ) (Θ : Xn n → ℂ)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) (hn : n ≤ 1) :
    (fun x : Xn n =>
        (Work.BoseDict.boxSlotSum e (rankOnePair w₁ v₁)
            (Work.BoseDict.boxSlotSum e (rankOnePair w₂ v₂) Θ)
          - Work.BoseDict.boxSlotSum e
              ((rankOnePair w₁ v₁).comp (rankOnePair w₂ v₂)) Θ) x) = 0 := by
  have h := pairDecompPairSetGen hmeas hbdd hsupp horth w₁ v₁ w₂ v₂ Θ hΘm hΘb
  rw [pairSet_eq_empty_of_le_one hn, Finset.sum_empty] at h
  exact h

/-! ## 3. The atom and the row vanish -/

/-- The definitional decomposition of the `(s,k)`-atom into its two slot words. -/
theorem potCubicAtom_eq_two_words {m n : ℕ} [NeZero m] {Mode : Type*} [AddCommGroup Mode]
    [Fintype Mode] [DecidableEq Mode] {e : Fin m → Ω → ℂ}
    (f g : Mode → Fin m → ℝ) (s k : Mode) (Θ : Xn n → ℂ) :
    Work.BoseBoxFock.FRK.potCubicAtom (fun T => Work.BoseDict.boxSlotSum e T) f g s k Θ
      = (fun x : Xn n =>
          (Work.BoseDict.boxSlotSum e (rankOnePair (evec0 m) (f (s - k)))
              (Work.BoseDict.boxSlotSum e (rankOnePair (g s) (f k)) Θ)
            - Work.BoseDict.boxSlotSum e
                ((rankOnePair (evec0 m) (f (s - k))).comp
                  (rankOnePair (g s) (f k))) Θ) x)
        + (fun x : Xn n =>
          (Work.BoseDict.boxSlotSum e (rankOnePair (f k) (g s))
              (Work.BoseDict.boxSlotSum e (rankOnePair (f (s - k)) (evec0 m)) Θ)
            - Work.BoseDict.boxSlotSum e
                ((rankOnePair (f k) (g s)).comp
                  (rankOnePair (f (s - k)) (evec0 m))) Θ) x) := rfl

/-- **The `(s,k)`-atom vanishes for `n ≤ 1`.** -/
theorem potCubicAtom_eq_zero_of_le_one {m n : ℕ} [NeZero m] {Mode : Type*}
    [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode] {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (f g : Mode → Fin m → ℝ) (s k : Mode) (Θ : Xn n → ℂ)
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) (hn : n ≤ 1) :
    Work.BoseBoxFock.FRK.potCubicAtom (fun T => Work.BoseDict.boxSlotSum e T) f g s k Θ = 0 := by
  rw [potCubicAtom_eq_two_words f g s k Θ,
    rankOnePairWord_eq_zero_of_le_one hmeas hbdd hsupp horth
      (evec0 m) (f (s - k)) (g s) (f k) Θ hΘm hΘb hn,
    rankOnePairWord_eq_zero_of_le_one hmeas hbdd hsupp horth
      (f k) (g s) (f (s - k)) (evec0 m) Θ hΘm hΘb hn,
    add_zero]

/-- **The whole cubic row vanishes for `n ≤ 1`.** -/
theorem potCubic_eq_zero_of_le_one {m n : ℕ} [NeZero m] {Mode : Type*}
    [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode] {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : Ω, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (f g : Mode → Fin m → ℝ) (PHs : Finset Mode) (E : Work.BoseB7.Q3Env Mode)
    (Θ : Xn n → ℂ) (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) (hn : n ≤ 1) :
    Work.BoseBoxFock.potCubic (fun T => Work.BoseDict.boxSlotSum e T) f g PHs E Θ = 0 := by
  rw [Work.BoseBoxFock.FRK.potCubic_eq_sum_atom (fun T => Work.BoseDict.boxSlotSum e T)
    f g PHs E Θ]
  have hzero : (∑ s ∈ Work.BoseB7.excited Mode, ∑ k ∈ PHs,
      (E.fL s * E.W1 k) •
        Work.BoseBoxFock.FRK.potCubicAtom (fun T => Work.BoseDict.boxSlotSum e T) f g s k Θ)
      = 0 :=
    Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun k _ => by
      rw [potCubicAtom_eq_zero_of_le_one hmeas hbdd hsupp horth f g s k Θ hΘm hΘb hn,
        smul_zero]
  rw [hzero, smul_zero]

end Work.BoseBoxFock.PotCubicLowBandAux
