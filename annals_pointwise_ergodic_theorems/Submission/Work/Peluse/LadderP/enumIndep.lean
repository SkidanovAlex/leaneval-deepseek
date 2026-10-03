import Mathlib
import Submission.Work.Peluse.LadderB.stepDefs
import Submission.Work.Peluse.Concat.Zbox_omegaOf_indep

/-!
# The ladder state does not depend on the enumeration of the sign patterns

The ladder state `Work.Peluse.boxLadderNorm j n M₁ c ωOf L D' N f`
(`Submission/Work/Peluse/LadderB/stepDefs.lean`) is the average over `h, h' ∈ [1,M₁]^j` of the
level-`(2^j - 1 + n)` box **norm** of `f` at the direction family
`Work.Peluse.Holds.ladderSlots j n M₁ c ωOf L D' h h'`: the first `2^j - 1` slots are the short
slots `c·((h - h')·ω)[L]`, one for each **nonzero** sign pattern `ω ∈ {0,1}^j`, and the remaining
`n` slots are the long window `c[D']`.

The nonzero sign patterns are indexed by `ωOf : Fin (2 ^ j - 1) → (Fin j → Bool)`, which by
assumption (`Function.Injective` and `∀ i, ωOf i ≠ 0`) is a *bijection* onto the set of nonzero
patterns (there are exactly `2^j - 1` of them).  The ladder state therefore does not depend on which
bijection is used: two such enumerations differ by a permutation `σ` of the slot index
(`Work.Peluse.Concat.exists_perm_of_omegaOf`), which extends to a permutation of
`Fin (2 ^ j - 1 + n)` acting on the short slots and fixing the long ones, and the box norm is
invariant under permuting the direction slots
(`Work.Peluse.BoxNorm.boxNormPow_perm`, itself a consequence of the permutation invariance of the
cube sum `Work.Peluse.Track.boxSumPow_comp_bij_proved`).

This is the lemma `Work.Peluse.LadderP.enumIndep`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.LadderP

noncomputable section

open Work.Peluse

/-! ## The permutation of the slot index set

A permutation `σ` of the short-slot index `Fin m` extends to a permutation `slotPerm σ` of
`Fin (m + n)` — through the canonical decomposition `finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)`
— which permutes the first `m` indices by `σ` and fixes the last `n` of them. -/

/-- The extension of a permutation of `Fin m` to a permutation of `Fin (m + n)`, acting by `σ` on
the first `m` indices (the short slots) and fixing the last `n` (the long slots). -/
def slotPerm {m n : ℕ} (σ : Equiv.Perm (Fin m)) : Equiv.Perm (Fin (m + n)) :=
  (finSumFinEquiv.symm.trans (Equiv.sumCongr σ (Equiv.refl (Fin n)))).trans finSumFinEquiv

lemma slotPerm_castAdd {m n : ℕ} (σ : Equiv.Perm (Fin m)) (u : Fin m) :
    slotPerm σ (Fin.castAdd n u) = Fin.castAdd n (σ u) := by
  unfold slotPerm
  rw [Equiv.trans_apply, Equiv.trans_apply]
  have h1 : finSumFinEquiv.symm (Fin.castAdd n u) = Sum.inl u := by
    rw [Equiv.symm_apply_eq]; rfl
  rw [h1]; rfl

lemma slotPerm_natAdd {m n : ℕ} (σ : Equiv.Perm (Fin m)) (w : Fin n) :
    slotPerm σ (Fin.natAdd m w) = Fin.natAdd m w := by
  unfold slotPerm
  rw [Equiv.trans_apply, Equiv.trans_apply]
  have h1 : finSumFinEquiv.symm (Fin.natAdd m w) = Sum.inr w := by
    rw [Equiv.symm_apply_eq]; rfl
  rw [h1]; rfl

/-- **A concatenated family is permuted by `slotPerm`.**  Appending the permuted head `a ∘ σ` to
the tail `b` is the same as appending `a` to `b` and permuting the result by `slotPerm σ`. -/
lemma fin_append_slotPerm {m n : ℕ} {α : Type*} (σ : Equiv.Perm (Fin m)) (a : Fin m → α)
    (b : Fin n → α) :
    (fun i => Fin.append a b (slotPerm σ i)) = Fin.append (fun i => a (σ i)) b := by
  funext i
  induction i using Fin.addCases with
  | left u => rw [slotPerm_castAdd, Fin.append_left, Fin.append_left]
  | right w => rw [slotPerm_natAdd, Fin.append_right, Fin.append_right]

/-! ## The ladder slots as a concatenation -/

/-- The slot family of the ladder state, split into its short head (the `2^j - 1` directions
`c·((h-h')·ω)[L]`, one per nonzero sign pattern) and its long tail (the `n` copies of `c[D']`). -/
lemma ladderSlots_eq_append (j n M₁ : ℕ) (c : ℤ) (ωOf : Fin (2^j - 1) → (Fin j → Bool))
    (L D' : ℕ) (h h' : Fin j → Fin M₁) :
    Holds.ladderSlots j n M₁ c ωOf L D' h h'
      = Fin.append
          (fun i : Fin (2^j - 1) =>
            arithIcc (c * Concat.dotZ (ωOf i) (Concat.tupSub h h')) L)
          (fun _ : Fin n => arithIcc c D') := by
  funext i
  induction i using Fin.addCases with
  | left u =>
      simp only [Fin.append_left]
      rw [Holds.ladderSlots, Fin.val_castAdd, dif_pos u.isLt]
  | right w =>
      simp only [Fin.append_right]
      rw [Holds.ladderSlots, dif_neg (by simp)]

/-- **The slot families of two enumerations of the nonzero patterns agree up to `slotPerm`.**  If
`ωOf (σ i) = ωOf' i` for all `i`, then the slot family built from `ωOf'` is the slot family built
from `ωOf`, permuted by `slotPerm σ`. -/
lemma ladderSlots_perm (j n M₁ : ℕ) (c : ℤ) (L D' : ℕ)
    (ωOf ωOf' : Fin (2^j - 1) → (Fin j → Bool)) (σ : Equiv.Perm (Fin (2^j - 1)))
    (hσ : ∀ i, ωOf (σ i) = ωOf' i) (h h' : Fin j → Fin M₁) :
    Holds.ladderSlots j n M₁ c ωOf' L D' h h'
      = fun i => Holds.ladderSlots j n M₁ c ωOf L D' h h' (slotPerm σ i) := by
  rw [ladderSlots_eq_append, ladderSlots_eq_append, fin_append_slotPerm]
  congr 1
  funext i
  rw [hσ i]

/-! ## The independence -/

theorem enumIndep (j n M₁ : ℕ) (c : ℤ) (L D' N : ℕ) (f : ℤ → ℂ)
    (ωOf₁ ωOf₂ : Fin (2^j - 1) → (Fin j → Bool))
    (h₁ : Function.Injective ωOf₁) (h₂ : Function.Injective ωOf₂)
    (hn₁ : ∀ i, ωOf₁ i ≠ 0) (hn₂ : ∀ i, ωOf₂ i ≠ 0) :
    Work.Peluse.boxLadderNorm j n M₁ c ωOf₁ L D' N f
      = Work.Peluse.boxLadderNorm j n M₁ c ωOf₂ L D' N f := by
  classical
  -- the two enumerations differ by a permutation of the nonzero patterns
  obtain ⟨σ, hσbij, hσ⟩ := Concat.exists_perm_of_omegaOf ωOf₁ ωOf₂ h₁ h₂ hn₁ hn₂
  let τ : Equiv.Perm (Fin (2 ^ j - 1)) := Equiv.ofBijective σ hσbij
  have hτ : ∀ i, ωOf₁ (τ i) = ωOf₂ i := fun i => hσ i
  -- the slot families with the same `h, h'` differ by the permutation `slotPerm τ`
  have hstep : ∀ h h' : Fin j → Fin M₁,
      Work.Peluse.boxNorm (2 ^ j - 1 + n) (Holds.ladderSlots j n M₁ c ωOf₂ L D' h h')
          (symIcc N) f
        = Work.Peluse.boxNorm (2 ^ j - 1 + n) (Holds.ladderSlots j n M₁ c ωOf₁ L D' h h')
          (symIcc N) f := by
    intro h h'
    have hslots := ladderSlots_perm j n M₁ c L D' ωOf₁ ωOf₂ τ hτ h h'
    have hperm := BoxNorm.boxNormPow_perm (slotPerm τ)
      (Holds.ladderSlots j n M₁ c ωOf₁ L D' h h') (symIcc N) f
    have hpow : Work.Peluse.boxNormPow (2 ^ j - 1 + n)
          (Holds.ladderSlots j n M₁ c ωOf₂ L D' h h') (symIcc N) f
        = Work.Peluse.boxNormPow (2 ^ j - 1 + n)
          (Holds.ladderSlots j n M₁ c ωOf₁ L D' h h') (symIcc N) f := by
      rw [hslots]
      exact hperm
    simpa only [Work.Peluse.boxNorm] using
      congrArg (fun z : ℝ => z ^ (1 / (2 : ℝ) ^ (2 ^ j - 1 + n))) hpow
  rw [Work.Peluse.boxLadderNorm, Work.Peluse.boxLadderNorm]
  rw [Finset.sum_congr rfl (fun h _ => Finset.sum_congr rfl (fun h' _ => hstep h h'))]

end

end Work.Peluse.LadderP
