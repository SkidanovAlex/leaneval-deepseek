import Mathlib
import Submission.OddOrder.GroupTheory.RepresentationTheory.ColumnOrthogonality
import Submission.Work.BG.c3vbCharBridge

namespace Work.BG

open OddOrder.RepresentationTheory

/-- The **degree** of an irreducible complex character, read off as the natural number `d`
with `χ(1) = d` (the dimension of any underlying irreducible representation). -/
noncomputable def charDeg {X : Type} [Group X] (χ : IrreducibleCharacter X) : ℕ :=
  Classical.choose (irreducibleCharacter_apply_one_eq_pos_natCast χ)

theorem charDeg_spec {X : Type} [Group X] (χ : IrreducibleCharacter X) :
    ((χ : ClassFunction X ℂ) : X → ℂ) 1 = (charDeg χ : ℂ) :=
  (Classical.choose_spec (irreducibleCharacter_apply_one_eq_pos_natCast χ)).2

/-- **Burnside degree-sum identity in `ℕ`**: the sum of the squared degrees of all
irreducible characters of a finite group equals its order.  Obtained from the complex form
`sumIrreducibleDegreeSq` by pushing the `ℕ → ℂ` cast through the sum and the squares. -/
theorem sum_charDeg_sq {X : Type} [Group X] [Finite X] :
    ∑ χ : IrreducibleCharacter X, (charDeg χ) ^ 2 = Nat.card X := by
  have hc : ((∑ χ : IrreducibleCharacter X, (charDeg χ) ^ 2 : ℕ) : ℂ) = (Nat.card X : ℂ) := by
    rw [Nat.cast_sum]
    simp only [Nat.cast_pow]
    rw [← sumIrreducibleDegreeSq]
    exact Finset.sum_congr rfl (fun χ _ => by rw [charDeg_spec χ])
  exact Nat.cast_injective hc

/-- A non-real irreducible character `β` of a finite group `X` has degree `d` satisfying
`2 d² ≤ |X|`: its conjugate `β̄` is a *second* irreducible character of the same degree `d`,
and both degrees contribute `d²` to the Burnside sum `∑_{χ ∈ Irr X} χ(1)² = |X|`.

(The oddness of `|X|` and the invertibility of `|X|` in `ℂ` are not needed for the
counting argument, but are part of the requested interface.) -/
theorem degreeSqNonReal {X : Type} [Group X] [Finite X] [Fintype X] [Invertible (Nat.card X : ℂ)]
    (hodd : Odd (Nat.card X)) {β : OddOrder.RepresentationTheory.ClassFunction X ℂ}
    (hβ : OddOrder.RepresentationTheory.IsIrreducibleCharacter β)
    (hnr : ¬ OddOrder.RepresentationTheory.ClassFunction.IsReal β) :
    ∃ d : ℕ, β 1 = (d : ℂ) ∧ 2 * d ^ 2 ≤ Nat.card X := by
  classical
  -- The conjugate of an irreducible character is irreducible.
  have hχ₁_irr : IsIrreducibleCharacter β.conj := IsIrreducibleCharacter.conj hβ
  -- ... and the two are distinct precisely because `β` is not real.
  have hne : (⟨β.conj, hχ₁_irr⟩ : IrreducibleCharacter X) ≠ ⟨β, hβ⟩ := by
    intro h
    refine hnr ?_
    have h2 : (β.conj : ClassFunction X ℂ) = β := by
      simpa using congrArg (fun χ : IrreducibleCharacter X => (χ : ClassFunction X ℂ)) h
    exact h2
  -- The degree of `β`.
  obtain ⟨d, _hdpos, hd⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨β, hβ⟩ : IrreducibleCharacter X)
  have hdβ : β 1 = (d : ℂ) := hd
  refine ⟨d, hdβ, ?_⟩
  have hspec₀ : β 1 = (charDeg (⟨β, hβ⟩ : IrreducibleCharacter X) : ℂ) :=
    charDeg_spec (⟨β, hβ⟩ : IrreducibleCharacter X)
  have hspec₁ : β.conj 1 = (charDeg (⟨β.conj, hχ₁_irr⟩ : IrreducibleCharacter X) : ℂ) :=
    charDeg_spec (⟨β.conj, hχ₁_irr⟩ : IrreducibleCharacter X)
  have hdeg₀ : charDeg (⟨β, hβ⟩ : IrreducibleCharacter X) = d := by
    have h : ((charDeg (⟨β, hβ⟩ : IrreducibleCharacter X) : ℂ)) = (d : ℂ) := by
      rw [← hspec₀, hdβ]
    exact Nat.cast_injective h
  -- `β̄(1) = star (β 1) = star d = d`, so the conjugate has the same degree.
  have hdeg₁ : charDeg (⟨β.conj, hχ₁_irr⟩ : IrreducibleCharacter X) = d := by
    have h : ((charDeg (⟨β.conj, hχ₁_irr⟩ : IrreducibleCharacter X) : ℂ)) = (d : ℂ) := by
      rw [← hspec₁, ClassFunction.conj_apply, hdβ, star_natCast]
    exact Nat.cast_injective h
  -- Both degrees occur in the Burnside sum, which is `|X|`.
  have hle : (charDeg (⟨β.conj, hχ₁_irr⟩ : IrreducibleCharacter X)) ^ 2 +
      (charDeg (⟨β, hβ⟩ : IrreducibleCharacter X)) ^ 2 ≤ Nat.card X := by
    have hsub : ({⟨β.conj, hχ₁_irr⟩, ⟨β, hβ⟩} : Finset (IrreducibleCharacter X)) ⊆
        Finset.univ :=
      Finset.subset_univ _
    have h := Finset.sum_le_sum_of_subset_of_nonneg
      (f := fun χ : IrreducibleCharacter X => (charDeg χ) ^ 2) hsub
      (fun _ _ _ => Nat.zero_le _)
    rw [Finset.sum_pair hne] at h
    rwa [sum_charDeg_sq] at h
  have h2 : 2 * d ^ 2 = (charDeg (⟨β.conj, hχ₁_irr⟩ : IrreducibleCharacter X)) ^ 2 +
      (charDeg (⟨β, hβ⟩ : IrreducibleCharacter X)) ^ 2 := by
    rw [hdeg₁, hdeg₀]
    ring
  rw [h2]
  exact hle

end Work.BG
