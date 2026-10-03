import Mathlib
import Submission.Work.Peluse.UControl.peluseLadderStrong
import Submission.Work.Peluse.Concat.Defs
import Submission.Work.Peluse.Concat.boxNormPow_iteratedPeel
import Submission.Work.Peluse.BoxNorm.boxNormPow_perm
import Submission.Work.Peluse.BoxNorm.boxNormPow_le_one
import Submission.Work.Peluse.Concat.boxNormPow_succ_ge_general
import Submission.Work.Peluse.Pairing.boxSumPow_neg_directions

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.LadderA

noncomputable section

open Work.Peluse Work.Peluse.UControl Work.Peluse.Ulower

/-! ## Reindexing the box-norm power -/

/-- Reindexing the direction family of the box-norm power along an equivalence `e : Fin m ≃ Fin m'`
(with `m' = m`). -/
theorem boxNormPow_reindex {m m' : ℕ} (h : m' = m) (e : Fin m ≃ Fin m')
    (Q : Fin m → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ) :
    boxNormPow m' (fun i => Q (e.symm i)) S f = boxNormPow m Q S f := by
  subst h
  exact BoxNorm.boxNormPow_perm e.symm Q S f

/-- **Peeling a concatenated direction family.**  The iterated peel in the `Fin.append` normal
form: peeling the `b` coordinates of `QB` leaves the `a ≥ 1` coordinates of `QA`, and the peeled
function is the iterated difference `iterDelta b` of `f` along the shifts of `QB`. -/
theorem boxNormPow_peel_append {a b : ℕ} (ha : 1 ≤ a) (QA : Fin a → Finset ℤ)
    (QB : Fin b → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ) (hf : FinSuppZ f) :
    boxNormPow (b + a) (Fin.append QB QA) S f = (∏ j : Fin b, ((QB j).card : ℝ)⁻¹ ^ 2) *
      ∑ sh : (j : Fin b) → ↥(QB j) × ↥(QB j),
        boxNormPow a QA S (iterDelta b (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) f) :=
  Concat.boxNormPow_iteratedPeel ha QB QA S f hf

lemma finSumFinEquiv_apply {m n : ℕ} (x : Fin m ⊕ Fin n) :
    finSumFinEquiv x = Sum.elim (Fin.castAdd n) (Fin.natAdd m) x := rfl

/-! ## The ladder's split of the hypothesis's index set

For a fixed slot `s₀`, the index set `FamIdx kω = Σ_{ω ∈ I'} [k_ω]` of the hypothesis's family of
direction sets is split into the `A`-part, the (nonempty subsets `ω ∋ s₀`), whose direction is
linear in the peeled parameter `a' s₀` with common coefficient `p s₀.1 a`, and the `B`-part (the
`ω ∌ s₀`), whose directions are absorbed into the differenced function `g`. -/

/-- The `A`-part: the slots of the subsets `ω ∋ s₀` (the directions containing the peeled slot). -/
abbrev AIdx {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι → ℕ)
    (kω : Work.Peluse.UControl.SlotSet ι k → ℕ) (s₀ : Work.Peluse.UControl.Slot ι k) : Type :=
  Σ ω : {ω : Work.Peluse.UControl.SlotSet ι k // s₀ ∈ ω.1}, Fin (kω ω.1)

/-- The `B`-part: the slots of the subsets `ω ∌ s₀` (the directions avoiding the peeled slot). -/
abbrev BIdx {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι → ℕ)
    (kω : Work.Peluse.UControl.SlotSet ι k → ℕ) (s₀ : Work.Peluse.UControl.Slot ι k) : Type :=
  Σ ω : {ω : Work.Peluse.UControl.SlotSet ι k // s₀ ∉ ω.1}, Fin (kω ω.1)

/-- The direction set attached to an `A`-index. -/
def qA {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι → ℕ)
    (kω : Work.Peluse.UControl.SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (M₁ : ℕ)
    (a : Fin n → ℤ) (a' : Work.Peluse.UControl.Slot ι k → ℤ)
    (s₀ : Work.Peluse.UControl.Slot ι k) (j : AIdx k kω s₀) : Finset ℤ :=
  Work.Peluse.UControl.pDir p M₁ a a' j.1.1

/-- The direction set attached to a `B`-index. -/
def qB {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι → ℕ)
    (kω : Work.Peluse.UControl.SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (M₁ : ℕ)
    (a : Fin n → ℤ) (a' : Work.Peluse.UControl.Slot ι k → ℤ)
    (s₀ : Work.Peluse.UControl.Slot ι k) (j : BIdx k kω s₀) : Finset ℤ :=
  Work.Peluse.UControl.pDir p M₁ a a' j.1.1

/-- The `B`-part family in `Fin`-normal form (the family of the hypothesis, with the direction
depending only on the subset `ω ∌ s₀`). -/
def QBfin {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι → ℕ)
    (kω : Work.Peluse.UControl.SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (M₁ : ℕ)
    (a : Fin n → ℤ) (a' : Work.Peluse.UControl.Slot ι k → ℤ)
    (s₀ : Work.Peluse.UControl.Slot ι k) : Fin (Fintype.card (BIdx k kω s₀)) → Finset ℤ :=
  fun j => qB k kω p M₁ a a' s₀ ((Fintype.equivFin (BIdx k kω s₀)).symm j)

/-- The `A`-part family in `Fin`-normal form. -/
def QAfin {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι → ℕ)
    (kω : Work.Peluse.UControl.SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (M₁ : ℕ)
    (a : Fin n → ℤ) (a' : Work.Peluse.UControl.Slot ι k → ℤ)
    (s₀ : Work.Peluse.UControl.Slot ι k) : Fin (Fintype.card (AIdx k kω s₀)) → Finset ℤ :=
  fun j => qA k kω p M₁ a a' s₀ ((Fintype.equivFin (AIdx k kω s₀)).symm j)

/-- The hypothesis's full family in `Fin`-normal form. -/
def Qfull {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι → ℕ)
    (kω : Work.Peluse.UControl.SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (M₁ : ℕ)
    (a : Fin n → ℤ) (a' : Work.Peluse.UControl.Slot ι k → ℤ) :
    Fin (Fintype.card (Work.Peluse.UControl.FamIdx kω)) → Finset ℤ :=
  fun i => Work.Peluse.UControl.pDirFam p M₁ a a'
    ((Fintype.equivFin (Work.Peluse.UControl.FamIdx kω)).symm i)


noncomputable section

open Work.Peluse Work.Peluse.UControl Work.Peluse.Ulower
open scoped BigOperators

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The `B`-index type in the form in which it occurs in `ConclIdx`. -/
abbrev BIdx' (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (s₀ : Slot ι k) : Type :=
  Σ ω : {s : Finset (Slot ι k) // s.Nonempty ∧ s₀ ∉ s}, Fin (kω ⟨ω.1, ω.2.1⟩)

/-- Regrouping the subtype. -/
private def bIdxTo (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (s₀ : Slot ι k) :
    BIdx' k kω s₀ → BIdx k kω s₀ :=
  fun y => ⟨⟨⟨y.1.1, y.1.2.1⟩, y.1.2.2⟩, y.2⟩

private def bIdxInv (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (s₀ : Slot ι k) :
    BIdx k kω s₀ → BIdx' k kω s₀ :=
  fun y => ⟨⟨y.1.1.1, y.1.1.2, y.1.2⟩, y.2⟩

def bIdxEquiv (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (s₀ : Slot ι k) :
    BIdx' k kω s₀ ≃ BIdx k kω s₀ where
  toFun := bIdxTo k kω s₀
  invFun := bIdxInv k kω s₀
  left_inv y := by rcases y with ⟨⟨s, hs, hns⟩, r⟩; rfl
  right_inv y := by rcases y with ⟨⟨ω, h⟩, r⟩; rfl

/-- The direction set attached to a `BIdx'`-index (matching `conclDir` on the second summand). -/
def qB' {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι → ℕ)
    (kω : SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (M₁ : ℕ)
    (a : Fin n → ℤ) (b : Slot ι k → ℤ) (s₀ : Slot ι k) (j : BIdx' k kω s₀) : Finset ℤ :=
  arithIcc (∑ s ∈ j.1.1, p s.1 a * b s) M₁

def QBfin' {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι → ℕ)
    (kω : SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (M₁ : ℕ)
    (a : Fin n → ℤ) (b : Slot ι k → ℤ) (s₀ : Slot ι k) :
    Fin (Fintype.card (BIdx k kω s₀)) → Finset ℤ :=
  fun j => qB k kω p M₁ a b s₀ ((Fintype.equivFin (BIdx k kω s₀)).symm j)

/-- The conclusion's index type is the `B`-part followed by the long directions. -/
def conclSplit (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (s₀ : Slot ι k) (t' : ℕ) :
    ConclIdx s₀ kω t' ≃ (Fin t' ⊕ BIdx k kω s₀) :=
  Equiv.sumCongr (Equiv.refl (Fin t')) (bIdxEquiv k kω s₀)

/-- The `Fin`-level equivalence carrying the conclusion's family to `Fin.append QBfin Long`. -/
def conclFinEquiv (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (s₀ : Slot ι k) (t' : ℕ) :
    Fin (Fintype.card (ConclIdx s₀ kω t')) ≃ Fin (Fintype.card (BIdx k kω s₀) + t') :=
  ((Fintype.equivFin (ConclIdx s₀ kω t')).symm.trans (conclSplit k kω s₀ t')).trans
    ((Equiv.sumComm (Fin t') (BIdx k kω s₀)).trans
      ((Equiv.sumCongr (Fintype.equivFin (BIdx k kω s₀)) (Equiv.refl (Fin t'))).trans
        finSumFinEquiv))

lemma conclSplit_apply (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (s₀ : Slot ι k) (t' : ℕ)
    (j : ConclIdx s₀ kω t') :
    conclSplit k kω s₀ t' j
      = Sum.map id (bIdxTo k kω s₀) j := by
  rcases j with jl | ⟨⟨s, hs, hns⟩, r⟩ <;> rfl

/-- The conclusion's family is the concatenation of the `B`-family and the long family. -/
lemma conclFamily_eq_append (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ)
    (M₁ M₂ : ℕ) (a : Fin n → ℤ) (b : Slot ι k → ℤ) (s₀ : Slot ι k) (t' : ℕ) (γ' : ℝ) :
    ∀ i, conclDir p M₁ M₂ γ' s₀ t' a b
        ((Fintype.equivFin (ConclIdx s₀ kω t')).symm i)
      = Fin.append (QBfin k kω p M₁ a b s₀)
          (fun _ : Fin t' => arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
          (conclFinEquiv k kω s₀ t' i) := by
  intro i
  have key : ∀ j : ConclIdx s₀ kω t',
      conclDir p M₁ M₂ γ' s₀ t' a b j
        = Fin.append (QBfin k kω p M₁ a b s₀)
            (fun _ : Fin t' => arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
            (conclFinEquiv k kω s₀ t' ((Fintype.equivFin (ConclIdx s₀ kω t')) j)) := by
    intro j
    have hsf : conclFinEquiv k kω s₀ t' ((Fintype.equivFin (ConclIdx s₀ kω t')) j)
        = finSumFinEquiv ((Equiv.sumCongr (Fintype.equivFin (BIdx k kω s₀)) (Equiv.refl (Fin t')))
            (Equiv.sumComm (Fin t') (BIdx k kω s₀) (conclSplit k kω s₀ t' j))) := by
      simp only [conclFinEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
    rw [hsf]
    rcases j with jl | ⟨⟨s, hs, hns⟩, r⟩
    · simp only [conclDir, conclSplit, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumComm_apply,
        Sum.swap_inl, Equiv.refl_apply, finSumFinEquiv_apply, Sum.elim_inr,
        Fin.append_right]
      simp only [Sum.map_inr, Equiv.refl_apply, Sum.elim_inr, Fin.append_right]
    · simp only [conclDir, conclSplit, bIdxEquiv, bIdxTo, Equiv.sumCongr_apply, Sum.map_inr,
        Equiv.sumComm_apply, Sum.swap_inr, Equiv.refl_apply, finSumFinEquiv_apply, Sum.elim_inl,
        Fin.append_left, QBfin, qB, Equiv.symm_apply_apply]
      simp only [Sum.map_inl, Equiv.refl_apply, Sum.elim_inl, Fin.append_left, Equiv.coe_fn_mk]
      simp only [QBfin, qB, pDir, Equiv.symm_apply_apply, bIdxTo]
  simpa only [Equiv.apply_symm_apply] using key ((Fintype.equivFin (ConclIdx s₀ kω t')).symm i)

lemma card_conclIdx (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (s₀ : Slot ι k) (t' : ℕ) :
    Fintype.card (BIdx k kω s₀) + t' = Fintype.card (ConclIdx s₀ kω t') := by
  have h := Fintype.card_congr (conclFinEquiv k kω s₀ t')
  simpa using h.symm

/-- **The peel of the conclusion's family.**  Splitting the conclusion's direction family at the
peeled slot `s₀`, the box-norm power of `f` at that family is the average, over the shifts of the
`B`-part (the directions `ω ∌ s₀`), of the box-norm power of the iterated difference `iterDelta`
of `f` at `t'` copies of the long direction `arithIcc (p s₀.1 a) ⌊γ'M₁M₂⌋`. -/
theorem concl_peel (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (M₁ M₂ : ℕ)
    (a : Fin n → ℤ) (b : Slot ι k → ℤ) (s₀ : Slot ι k) (t' : ℕ) (γ' : ℝ) (hT : 1 ≤ t')
    (S : Finset ℤ) (f : ℤ → ℂ) (hf : FinSuppZ f) :
    boxNormPow (Fintype.card (ConclIdx s₀ kω t'))
        (fun i => conclDir p M₁ M₂ γ' s₀ t' a b ((Fintype.equivFin (ConclIdx s₀ kω t')).symm i))
        S f
      = (∏ j : Fin (Fintype.card (BIdx k kω s₀)),
            ((QBfin k kω p M₁ a b s₀ j).card : ℝ)⁻¹ ^ 2) *
        ∑ sh : (j : Fin (Fintype.card (BIdx k kω s₀))) →
            ↥(QBfin k kω p M₁ a b s₀ j) × ↥(QBfin k kω p M₁ a b s₀ j),
          boxNormPow t' (fun _ : Fin t' =>
              arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) S
            (iterDelta (Fintype.card (BIdx k kω s₀))
              (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) f) := by
  rw [← boxNormPow_reindex (card_conclIdx k kω s₀ t') (conclFinEquiv k kω s₀ t')
    (fun i => conclDir p M₁ M₂ γ' s₀ t' a b
      ((Fintype.equivFin (ConclIdx s₀ kω t')).symm i)) S f]
  have hfam : (fun i => conclDir p M₁ M₂ γ' s₀ t' a b
        ((Fintype.equivFin (ConclIdx s₀ kω t')).symm
          ((conclFinEquiv k kω s₀ t').symm i)))
      = Fin.append (QBfin k kω p M₁ a b s₀)
          (fun _ : Fin t' => arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) := by
    funext i
    simpa only [Equiv.apply_symm_apply] using
      conclFamily_eq_append k kω p M₁ M₂ a b s₀ t' γ' ((conclFinEquiv k kω s₀ t').symm i)
  exact (congrArg (fun R => boxNormPow _ R S f) hfam).trans
    (boxNormPow_peel_append hT (fun _ : Fin t' =>
        arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
      (QBfin k kω p M₁ a b s₀) S f hf)

end

end

end Work.Peluse.LadderA
