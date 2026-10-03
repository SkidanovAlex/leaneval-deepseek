import Mathlib
import Submission.Work.Peluse.Prop36SW.endgameConst
import Submission.Work.Peluse.Prop36SW.lstateAbsAbsIff
import Submission.Work.Peluse.Prop36SW.meanPeelLeBoxNorm
import Submission.Work.Peluse.Prop36SW.roundWindowGe
import Submission.Work.Peluse.Prop36SW.roundDefs

/-!
# The base case of the round of the §5 chain: `RoundStmt 1`

`RoundStmt 1` (see `roundStmt.lean`) is the round at a slot type with a **single** slot `s₀`.
Then the ladder's conclusion has an **empty short family** (`ShortIdx s₀ kω = ∅`), so its box norm
collapses to the uniformity norm of the single long direction
`arithIcc (p s₀ a) ⌊γ'·M₁·M₂⌋`, and Jensen (the power mean) converts the average of the box norms
into the average of the box-norm powers — which is exactly the round's conclusion, with
`t s₀ := card (ConclIdx s₀ kω t') = t'` and `Lw s₀ := ⌊γ'·M₁·M₂⌋`.

The ladder is applied to the *absolute value* `|p|` of the coefficient (its positivity hypothesis
`0 < p i a` fails for the signed coefficient of the chain), and the conclusion is transferred back
with `conclDirAbs.sum_paramBox_boxNorm_conclDirG_abs`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Prop36SW

noncomputable section

open Work.Peluse.UControl

/-! ## 1. The slot type has one element: `ShortIdx` is empty -/

/-- If the index set is a singleton then the conclusion's *short* family is empty. -/
lemma isEmpty_shortIdx_of_card_one {ι : Type} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = 1) (kω : SlotSet ι (fun _ => 1) → ℕ)
    (s₀ : Slot ι (fun _ => 1)) :
    IsEmpty (ShortIdx (k := fun _ : ι => 1) kω s₀) := by
  haveI : Subsingleton ι :=
    Fintype.card_le_one_iff_subsingleton.mp (by omega)
  haveI : Subsingleton (Slot ι (fun _ => 1)) := by
    constructor
    rintro ⟨i, r⟩ ⟨j, s⟩
    rw [Subsingleton.elim i j, Subsingleton.elim r s]
  rw [isEmpty_iff]
  rintro ⟨ω, r⟩
  obtain ⟨x, hx⟩ := ω.2.1
  exact ω.2.2 (by rwa [Subsingleton.elim x s₀] at hx)

/-- The multiplicity function vanishes off the subsets containing the (unique) slot. -/
lemma kar_of_card_one {ι : Type} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = 1) (kω : SlotSet ι (fun _ => 1) → ℕ)
    (s₀ : Slot ι (fun _ => 1)) :
    ∀ ω : SlotSet ι (fun _ => 1), s₀ ∉ ω.1 → kω ω = 0 := by
  haveI : Subsingleton ι :=
    Fintype.card_le_one_iff_subsingleton.mp (by omega)
  haveI : Subsingleton (Slot ι (fun _ => 1)) := by
    constructor
    rintro ⟨i, r⟩ ⟨j, s⟩
    rw [Subsingleton.elim i j, Subsingleton.elim r s]
  intro ω hω
  obtain ⟨x, hx⟩ := ω.2
  exact absurd (show s₀ ∈ ω.1 from by rwa [Subsingleton.elim x s₀] at hx) hω

/-! ## 2. The collapse of the conclusion's family -/

/-- With an empty short family, the ladder's conclusion's direction family is the constant family
of the long direction `arithIcc (p s₀ a) ⌊γ'M₁M₂⌋`. -/
lemma conclDirG_eq_long {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (kω : SlotSet ι (fun _ => 1) → ℕ) (s₀ : Slot ι (fun _ => 1))
    (hkar : ∀ ω : SlotSet ι (fun _ => 1), s₀ ∉ ω.1 → kω ω = 0)
    (p : ι → (Fin n → ℤ) → ℤ) (M₁ M₂ : ℕ) (γ' : ℝ) (t' : ℕ)
    (a : Fin n → ℤ) (b : Slot ι (fun _ => 1) → ℤ) (z : ConclIdx s₀ kω t') :
    Work.Peluse.Prop36SW.conclDirG p M₁ M₂ γ' s₀ t' a b z
      = arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat := by
  rcases z with u | ⟨ω, r⟩
  · rfl
  · exact Fin.elim0 ((hkar ⟨ω.1, ω.2.1⟩ ω.2.2) ▸ r)

/-- With an empty short family, the conclusion's box norm is the uniformity norm of the long
direction. -/
lemma boxNorm_conclDir_eq_uNorm {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (kω : SlotSet ι (fun _ => 1) → ℕ) (s₀ : Slot ι (fun _ => 1))
    (hkar : ∀ ω : SlotSet ι (fun _ => 1), s₀ ∉ ω.1 → kω ω = 0)
    (p : ι → (Fin n → ℤ) → ℤ) (M₁ M₂ : ℕ) (γ' : ℝ) (t' : ℕ)
    (a : Fin n → ℤ) (b : Slot ι (fun _ => 1) → ℤ) (S : Finset ℤ) (X : ℤ → ℂ) :
    Work.Peluse.boxNorm (Fintype.card (ConclIdx s₀ kω t'))
      (fun i => Work.Peluse.Prop36SW.conclDirG p M₁ M₂ γ' s₀ t' a b
        ((Fintype.equivFin (ConclIdx s₀ kω t')).symm i)) S X
    = Work.Peluse.uNorm (Fintype.card (ConclIdx s₀ kω t'))
        (arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) S X := by
  have hfam : (fun i : Fin (Fintype.card (ConclIdx s₀ kω t')) =>
        Work.Peluse.Prop36SW.conclDirG p M₁ M₂ γ' s₀ t' a b
          ((Fintype.equivFin (ConclIdx s₀ kω t')).symm i))
      = fun _ : Fin (Fintype.card (ConclIdx s₀ kω t')) =>
          arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat := by
    funext i
    exact conclDirG_eq_long kω s₀ hkar p M₁ M₂ γ' t' a b _
  rw [hfam]
  rfl

/-- The level `card (Σ _ : ι, Fin L)` of the round's conclusion is `L`. -/
lemma card_sigma_fin_of_card_one {ι : Type} [Fintype ι]
    (hcard : Fintype.card ι = 1) (L : ℕ) :
    Fintype.card (Σ _ : ι, Fin L) = L := by
  rw [Fintype.card_sigma]
  simp [Finset.sum_const, Finset.card_univ, hcard]

/-! ## 4. The base case -/

end

end Work.Peluse.Prop36SW
