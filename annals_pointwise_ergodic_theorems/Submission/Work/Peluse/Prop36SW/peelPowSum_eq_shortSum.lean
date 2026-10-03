import Mathlib
import Submission.Work.Peluse.Prop36SW.averageParamBoxPeelProj
import Submission.Work.Peluse.Prop36SW.peelParamAverage

namespace Work.Peluse.Prop36SW

noncomputable section

open Work.Peluse.UControl

/-!
# The peel's average is the ladder's short sum

`Work.Peluse.Prop36SW.peelPowSum_eq_shortSum` identifies the average, over the peeled state's
parameter type `PeelParam` and the peeled state's parameter box, of the box-norm power of the
peeled family, with the average over the original parameters of the box-norm power of the ladder's
*short* family.

The proof has three ingredients, all already available in the workspace:

* `Work.Peluse.Prop36SW.peelParamAverage` — the uniform average over the dependent sigma type
  `PeelParam` unwinds to the iterated average over `A`, the original parameter box and the shift
  block;
* `Work.Peluse.Prop36SW.averageParamBoxPeelProj` — the average over the peeled state's parameter box
  equals the average over the original box (the peel adds one free coordinate);
* `Work.Peluse.Prop36SW.boxNormPowPeelFamily` — the peeled family at a restricted box point *is*
  the ladder's short family (same directions, same level).

The remaining bookkeeping is the cancellation of the free coordinate's cardinality against the
ratio of the two box sizes and the swap of the two finite sums.

This module deliberately *does not* import `Submission.Work.Peluse.Prop36SW.lstateStepTwo` (which
contains a stub of this statement), so that the latter can be rewired to this module.
-/

/-- The type of the shifts extracted at the peeled slot `s₀` for the parameter `a`: the block
`(c[L] × c[L])^{t'}` with `c = p s₀ a` and `L = ⌊γ'M₁M₂⌋`. -/
abbrev PeelShiftQ {ι : Type} {P : Type} (p : ι → P → ℤ) (M₁ M₂ : ℕ) (γ' : ℝ)
    (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1)) (a : P) : Type :=
  ↥(Work.Peluse.arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)

/-- The direction family of the peeled state, as a function of the *old* parameter `a` and of the
new direction parameters `a'` only (it does not depend on the remaining components of
`PeelParam`). -/
def famPreQ {ι : Type} [Fintype ι] [DecidableEq ι]
    (kω : Work.Peluse.UControl.SlotSet ι (fun _ => 1) → ℕ) {P : Type} (p : ι → P → ℤ) (M₁ : ℕ)
    (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1)) (a : P)
    (a' : Work.Peluse.UControl.Slot (Work.Peluse.Prop36SW.PeelSlot s₀) (fun _ => 1) → ℤ) :
    Fin (Fintype.card (Work.Peluse.UControl.FamIdx (Work.Peluse.Prop36SW.peelKω kω s₀))) → Finset ℤ :=
  fun j => Work.Peluse.arithIcc
    (∑ s ∈ ((Fintype.equivFin
        (Work.Peluse.UControl.FamIdx (Work.Peluse.Prop36SW.peelKω kω s₀))).symm j).1.1,
      p s.1.1.1 a * a' s) M₁

/-- The iterated difference of the peel, as a function of the old parameter `a` and of the shifts
only. -/
def uPreQ {ι : Type} {P : Type} (p : ι → P → ℤ) (M₁ M₂ : ℕ) (γ' : ℝ)
    (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1)) (t' : ℕ) (g : P → ℤ → ℂ) (a : P)
    (sh : (j : Fin t') → PeelShiftQ p M₁ M₂ γ' s₀ a × PeelShiftQ p M₁ M₂ γ' s₀ a) : ℤ → ℂ :=
  Work.Peluse.Ulower.iterDelta t' (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) (g a)

/-- The box-norm power, at the ambient `symIcc N`, of the peeled state's family at the old
parameter `a`, the new direction parameters `a'` and the shifts `sh`. -/
def famPowQ {ι : Type} [Fintype ι] [DecidableEq ι]
    (kω : Work.Peluse.UControl.SlotSet ι (fun _ => 1) → ℕ) {P : Type} [DecidableEq P]
    (p : ι → P → ℤ) (M₁ M₂ N : ℕ) (γ' : ℝ) (t' : ℕ)
    (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1)) (g : P → ℤ → ℂ) (a : P)
    (a' : Work.Peluse.UControl.Slot (Work.Peluse.Prop36SW.PeelSlot s₀) (fun _ => 1) → ℤ)
    (sh : (j : Fin t') → PeelShiftQ p M₁ M₂ γ' s₀ a × PeelShiftQ p M₁ M₂ γ' s₀ a) : ℝ :=
  Work.Peluse.boxNormPow
    (Fintype.card (Work.Peluse.UControl.FamIdx (Work.Peluse.Prop36SW.peelKω kω s₀)))
    (famPreQ kω p M₁ s₀ a a') (Work.Peluse.symIcc N)
    (uPreQ p M₁ M₂ γ' s₀ t' g a sh)

/-- The box-norm power, at the ambient `symIcc N`, of the ladder's *short* family at the old
parameter `a`, the box point `b` and the shifts `sh`. -/
def shortPowQ {ι : Type} [Fintype ι] [DecidableEq ι] {P : Type}
    (kω : Work.Peluse.UControl.SlotSet ι (fun _ => 1) → ℕ) (p : ι → P → ℤ) (M₁ M₂ N : ℕ) (γ' : ℝ)
    (t' : ℕ) (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1)) (g : P → ℤ → ℂ) (a : P)
    (b : Work.Peluse.UControl.Slot ι (fun _ => 1) → ℤ)
    (sh : (j : Fin t') → PeelShiftQ p M₁ M₂ γ' s₀ a × PeelShiftQ p M₁ M₂ γ' s₀ a) : ℝ :=
  Work.Peluse.boxNormPow
    (Fintype.card (Work.Peluse.Prop36SW.ShortIdx (k := fun _ : ι => 1) kω s₀))
    (Work.Peluse.Prop36SW.shortFamG kω p M₁ a b s₀) (Work.Peluse.symIcc N)
    (Work.Peluse.Ulower.iterDelta t' (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) (g a))

/-- `famPreQ` computes the family of the peel data at `q` when `a = q.1.1.1`. -/
lemma famPreQ_eq_pDirFamG {ι : Type} [Fintype ι] [DecidableEq ι]
    (kω : Work.Peluse.UControl.SlotSet ι (fun _ => 1) → ℕ) {P : Type} [DecidableEq P]
    (p : ι → P → ℤ) (M₁ M₂ : ℕ) (A : Finset P) (γ' : ℝ) (t' : ℕ)
    (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1))
    (q : Work.Peluse.Prop36SW.PeelParam p M₁ M₂ A γ' t' s₀)
    (a' : Work.Peluse.UControl.Slot (Work.Peluse.Prop36SW.PeelSlot s₀) (fun _ => 1) → ℤ)
    (j : Fin (Fintype.card (Work.Peluse.UControl.FamIdx (Work.Peluse.Prop36SW.peelKω kω s₀)))) :
    famPreQ kω p M₁ s₀ q.1.1.1 a' j
      = Work.Peluse.Prop36SW.pDirFamG (Work.Peluse.Prop36SW.peelP p M₁ M₂ A γ' t' s₀) M₁ q a'
          ((Fintype.equivFin
            (Work.Peluse.UControl.FamIdx (Work.Peluse.Prop36SW.peelKω kω s₀))).symm j) := by
  simp only [famPreQ, Work.Peluse.Prop36SW.pDirFamG, Work.Peluse.Prop36SW.pDirG,
    Work.Peluse.Prop36SW.peelP]

/-- `uPreQ` computes the iterated difference of the peel data at `q`. -/
lemma uPreQ_eq_peelG {ι : Type} [Fintype ι] [DecidableEq ι] {P : Type} [DecidableEq P]
    (p : ι → P → ℤ) (M₁ M₂ : ℕ) (A : Finset P) (γ' : ℝ) (t' : ℕ)
    (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1)) (g : P → ℤ → ℂ)
    (q : Work.Peluse.Prop36SW.PeelParam p M₁ M₂ A γ' t' s₀) :
    uPreQ p M₁ M₂ γ' s₀ t' g q.1.1.1 q.2
      = Work.Peluse.Prop36SW.peelG p M₁ M₂ A γ' t' s₀ g q := by
  simp only [uPreQ, Work.Peluse.Prop36SW.peelG]

/-- The peeled state's box-norm power at the peel data `q` is `famPowQ` at the data of `q`. -/
lemma peel_famPowQ {ι : Type} [Fintype ι] [DecidableEq ι] {P : Type} [DecidableEq P]
    (kω : Work.Peluse.UControl.SlotSet ι (fun _ => 1) → ℕ) (p : ι → P → ℤ)
    (M₁ M₂ N : ℕ) (A : Finset P) (γ' : ℝ) (t' : ℕ)
    (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1)) (g : P → ℤ → ℂ)
    (q : Work.Peluse.Prop36SW.PeelParam p M₁ M₂ A γ' t' s₀)
    (a' : Work.Peluse.UControl.Slot (Work.Peluse.Prop36SW.PeelSlot s₀) (fun _ => 1) → ℤ) :
    Work.Peluse.boxNormPow
        (Fintype.card (Work.Peluse.UControl.FamIdx (Work.Peluse.Prop36SW.peelKω kω s₀)))
        (fun j => Work.Peluse.Prop36SW.pDirFamG
          (Work.Peluse.Prop36SW.peelP p M₁ M₂ A γ' t' s₀) M₁ q a'
          ((Fintype.equivFin
            (Work.Peluse.UControl.FamIdx (Work.Peluse.Prop36SW.peelKω kω s₀))).symm j))
        (Work.Peluse.symIcc N) (Work.Peluse.Prop36SW.peelG p M₁ M₂ A γ' t' s₀ g q)
      = famPowQ kω p M₁ M₂ N γ' t' s₀ g q.1.1.1 a' q.2 := by
  have hfam : (fun j => Work.Peluse.Prop36SW.pDirFamG
        (Work.Peluse.Prop36SW.peelP p M₁ M₂ A γ' t' s₀) M₁ q a'
        ((Fintype.equivFin
          (Work.Peluse.UControl.FamIdx (Work.Peluse.Prop36SW.peelKω kω s₀))).symm j))
      = famPreQ kω p M₁ s₀ q.1.1.1 a' :=
    funext fun j => (famPreQ_eq_pDirFamG kω p M₁ M₂ A γ' t' s₀ q a' j).symm
  have hf : Work.Peluse.Prop36SW.peelG p M₁ M₂ A γ' t' s₀ g q
      = uPreQ p M₁ M₂ γ' s₀ t' g q.1.1.1 q.2 :=
    (uPreQ_eq_peelG p M₁ M₂ A γ' t' s₀ g q).symm
  rw [famPowQ, hfam, hf]

/-- The bridge: the box-norm power of the peeled family at the direction parameters obtained by
restricting a box point `b` is the box-norm power of the ladder's short family at `b`. -/
lemma famPowQ_restrict_eq_shortPowQ {ι : Type} [Fintype ι] [DecidableEq ι] {P : Type} 
    [DecidableEq P] (kω : Work.Peluse.UControl.SlotSet ι (fun _ => 1) → ℕ) (p : ι → P → ℤ)
    (M₁ M₂ N : ℕ) (A : Finset P) (γ' : ℝ) (t' : ℕ)
    (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1)) (g : P → ℤ → ℂ) {a : P} (ha : a ∈ A)
    {b : Work.Peluse.UControl.Slot ι (fun _ => 1) → ℤ}
    (hb : b ∈ Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M₂)
    (sh : (j : Fin t') → PeelShiftQ p M₁ M₂ γ' s₀ a × PeelShiftQ p M₁ M₂ γ' s₀ a) :
    famPowQ kω p M₁ M₂ N γ' t' s₀ g a
        (fun s' : Work.Peluse.UControl.Slot (Work.Peluse.Prop36SW.PeelSlot s₀) (fun _ => 1) =>
          b s'.1.1) sh
      = shortPowQ kω p M₁ M₂ N γ' t' s₀ g a b sh := by
  have hfam : famPreQ kω p M₁ s₀ a
        (fun s' : Work.Peluse.UControl.Slot (Work.Peluse.Prop36SW.PeelSlot s₀) (fun _ => 1) =>
          b s'.1.1)
      = (fun j => Work.Peluse.Prop36SW.pDirFamG
          (Work.Peluse.Prop36SW.peelP p M₁ M₂ A γ' t' s₀) M₁ ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, sh⟩
          (fun s' : Work.Peluse.UControl.Slot (Work.Peluse.Prop36SW.PeelSlot s₀) (fun _ => 1) =>
            b s'.1.1)
          ((Fintype.equivFin
            (Work.Peluse.UControl.FamIdx (Work.Peluse.Prop36SW.peelKω kω s₀))).symm j)) :=
    funext fun j => famPreQ_eq_pDirFamG kω p M₁ M₂ A γ' t' s₀ ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, sh⟩ _ j
  simp only [famPowQ, shortPowQ]
  rw [hfam, Work.Peluse.Prop36SW.boxNormPowPeelFamily kω p M₁ M₂ A γ' t' s₀
    ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, sh⟩ (Work.Peluse.symIcc N)
    (uPreQ p M₁ M₂ γ' s₀ t' g a sh)]
  rfl

/-- The summand of the peel's average, as a function of the old parameter `a` and the (unused)
box point `b`; it does not depend on `b`. -/
def peelPhiQ {ι : Type} [Fintype ι] [DecidableEq ι]
    (kω : Work.Peluse.UControl.SlotSet ι (fun _ => 1) → ℕ) {P : Type} [DecidableEq P]
    (p : ι → P → ℤ) (M₁ M₂ N : ℕ) (γ' : ℝ) (t' : ℕ)
    (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1)) (g : P → ℤ → ℂ) (a : P)
    (_b : Work.Peluse.UControl.Slot ι (fun _ => 1) → ℤ)
    (sh : (j : Fin t') → PeelShiftQ p M₁ M₂ γ' s₀ a × PeelShiftQ p M₁ M₂ γ' s₀ a) : ℝ :=
  ((Work.Peluse.UControl.paramBox
      (k := fun _ : Work.Peluse.Prop36SW.PeelSlot s₀ => 1) M₂).card : ℝ)⁻¹ *
    ∑ a' ∈ Work.Peluse.UControl.paramBox
      (k := fun _ : Work.Peluse.Prop36SW.PeelSlot s₀ => 1) M₂,
      famPowQ kω p M₁ M₂ N γ' t' s₀ g a a' sh

/-- **The peel's inner average.**  The average of the peeled family over the peeled state's box is
the average of the ladder's short family over the state's box. -/
lemma peelPhiQ_eq_avg_shortPowQ {ι : Type} [Fintype ι] [DecidableEq ι]
    (kω : Work.Peluse.UControl.SlotSet ι (fun _ => 1) → ℕ) {P : Type} [DecidableEq P]
    (p : ι → P → ℤ) (M₁ M₂ N : ℕ) (A : Finset P) (γ' : ℝ) (t' : ℕ)
    (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1)) (g : P → ℤ → ℂ)
    (hM₂ : 1 ≤ M₂) {a : P} (ha : a ∈ A)
    (b : Work.Peluse.UControl.Slot ι (fun _ => 1) → ℤ)
    (sh : (j : Fin t') → PeelShiftQ p M₁ M₂ γ' s₀ a × PeelShiftQ p M₁ M₂ γ' s₀ a) :
    peelPhiQ kω p M₁ M₂ N γ' t' s₀ g a b sh
      = ((Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M₂).card : ℝ)⁻¹ *
        ∑ b' ∈ Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M₂,
          shortPowQ kω p M₁ M₂ N γ' t' s₀ g a b' sh := by
  show ((Work.Peluse.UControl.paramBox
        (k := fun _ : Work.Peluse.Prop36SW.PeelSlot s₀ => 1) M₂).card : ℝ)⁻¹ *
      ∑ a' ∈ Work.Peluse.UControl.paramBox
        (k := fun _ : Work.Peluse.Prop36SW.PeelSlot s₀ => 1) M₂,
        famPowQ kω p M₁ M₂ N γ' t' s₀ g a a' sh
      = ((Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M₂).card : ℝ)⁻¹ *
        ∑ b' ∈ Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M₂,
          shortPowQ kω p M₁ M₂ N γ' t' s₀ g a b' sh
  rw [averageParamBoxPeelProj s₀ M₂ hM₂
    (fun a' : Work.Peluse.UControl.Slot (Work.Peluse.Prop36SW.PeelSlot s₀) (fun _ => 1) → ℤ =>
      famPowQ kω p M₁ M₂ N γ' t' s₀ g a a' sh),
    Finset.sum_congr rfl (fun b' hb' =>
      famPowQ_restrict_eq_shortPowQ kω p M₁ M₂ N A γ' t' s₀ g ha hb' sh)]

theorem peelPowSum_eq_shortSum {ι : Type} [Fintype ι] [DecidableEq ι]
    (kω : Work.Peluse.UControl.SlotSet ι (fun _ => 1) → ℕ) {P : Type} [DecidableEq P]
    (p : ι → P → ℤ) (M₁ M₂ N : ℕ) (A : Finset P) (γ' : ℝ) (t' : ℕ)
    (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1)) (g : P → ℤ → ℂ)
    (hM₂ : 1 ≤ M₂)
    (hp : ∀ a ∈ A, p s₀.1 a ≠ 0) :
    ((Fintype.card (Work.Peluse.Prop36SW.PeelParam p M₁ M₂ A γ' t' s₀) : ℝ))⁻¹ *
        ((Work.Peluse.UControl.paramBox (k := fun _ : Work.Peluse.Prop36SW.PeelSlot s₀ => 1) M₂).card : ℝ)⁻¹ *
        ∑ q : Work.Peluse.Prop36SW.PeelParam p M₁ M₂ A γ' t' s₀,
          ∑ a' ∈ Work.Peluse.UControl.paramBox (k := fun _ : Work.Peluse.Prop36SW.PeelSlot s₀ => 1) M₂,
            Work.Peluse.boxNormPow
              (Fintype.card (Work.Peluse.UControl.FamIdx (Work.Peluse.Prop36SW.peelKω kω s₀)))
              (fun j => Work.Peluse.Prop36SW.pDirFamG
                (Work.Peluse.Prop36SW.peelP p M₁ M₂ A γ' t' s₀) M₁ q a'
                ((Fintype.equivFin (Work.Peluse.UControl.FamIdx (Work.Peluse.Prop36SW.peelKω kω s₀))).symm j))
              (Work.Peluse.symIcc N) (Work.Peluse.Prop36SW.peelG p M₁ M₂ A γ' t' s₀ g q)
      = ((A.card : ℝ))⁻¹ * ((Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M₂).card : ℝ)⁻¹ *
        (((⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat : ℝ))⁻¹ ^ (2 * t') *
        ∑ a ∈ A, ∑ b ∈ Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M₂,
          ∑ sh : (j : Fin t') → ↥(Work.Peluse.arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) ×
                            ↥(Work.Peluse.arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat),
            Work.Peluse.boxNormPow
              (Fintype.card (Work.Peluse.Prop36SW.ShortIdx (k := fun _ : ι => 1) kω s₀))
              (Work.Peluse.Prop36SW.shortFamG kω p M₁ a b s₀) (Work.Peluse.symIcc N)
              (Work.Peluse.Ulower.iterDelta t' (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) (g a)) := by
  classical
  -- Step 1: the average over `PeelParam` of the box-average of the peeled family.
  have h1 : ((Fintype.card (Work.Peluse.Prop36SW.PeelParam p M₁ M₂ A γ' t' s₀) : ℝ))⁻¹ *
        ((Work.Peluse.UControl.paramBox
            (k := fun _ : Work.Peluse.Prop36SW.PeelSlot s₀ => 1) M₂).card : ℝ)⁻¹ *
        ∑ q : Work.Peluse.Prop36SW.PeelParam p M₁ M₂ A γ' t' s₀,
          ∑ a' ∈ Work.Peluse.UControl.paramBox
            (k := fun _ : Work.Peluse.Prop36SW.PeelSlot s₀ => 1) M₂,
            Work.Peluse.boxNormPow
              (Fintype.card (Work.Peluse.UControl.FamIdx (Work.Peluse.Prop36SW.peelKω kω s₀)))
              (fun j => Work.Peluse.Prop36SW.pDirFamG
                (Work.Peluse.Prop36SW.peelP p M₁ M₂ A γ' t' s₀) M₁ q a'
                ((Fintype.equivFin
                  (Work.Peluse.UControl.FamIdx (Work.Peluse.Prop36SW.peelKω kω s₀))).symm j))
              (Work.Peluse.symIcc N) (Work.Peluse.Prop36SW.peelG p M₁ M₂ A γ' t' s₀ g q)
      = ((Fintype.card (Work.Peluse.Prop36SW.PeelParam p M₁ M₂ A γ' t' s₀) : ℝ))⁻¹ *
        ∑ q : Work.Peluse.Prop36SW.PeelParam p M₁ M₂ A γ' t' s₀,
          peelPhiQ kω p M₁ M₂ N γ' t' s₀ g q.1.1.1 q.1.2.1 q.2 := by
    rw [mul_assoc, Finset.mul_sum]
    congr 1
  -- Step 2: `peelParamAverage` unwinds the average over `PeelParam`.
  have h2 := peelParamAverage p M₁ M₂ A γ' t' s₀ hp (peelPhiQ kω p M₁ M₂ N γ' t' s₀ g)
  rw [h1, h2]
  -- Step 3: the box average of the peeled family is the short average of the ladder's family.
  change ((A.card : ℝ))⁻¹ *
      ((Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M₂).card : ℝ)⁻¹ *
      (((⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat : ℝ))⁻¹ ^ (2 * t') *
      (∑ a ∈ A, ∑ b ∈ Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M₂,
        ∑ sh : (j : Fin t') →
            PeelShiftQ p M₁ M₂ γ' s₀ a × PeelShiftQ p M₁ M₂ γ' s₀ a,
          peelPhiQ kω p M₁ M₂ N γ' t' s₀ g a b sh)
    = ((A.card : ℝ))⁻¹ *
      ((Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M₂).card : ℝ)⁻¹ *
      (((⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat : ℝ))⁻¹ ^ (2 * t') *
      (∑ a ∈ A, ∑ b ∈ Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M₂,
        ∑ sh : (j : Fin t') →
            PeelShiftQ p M₁ M₂ γ' s₀ a × PeelShiftQ p M₁ M₂ γ' s₀ a,
          shortPowQ kω p M₁ M₂ N γ' t' s₀ g a b sh)
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  -- the inner double sum: replace `peelPhiQ` by the short average and cancel the cardinality
  have hBpos : 0 < (Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M₂).card := by
    refine Finset.card_pos.mpr ⟨fun _ => 0, ?_⟩
    rw [Work.Peluse.UControl.paramBox, Fintype.mem_piFinset]
    intro x
    rw [Finset.mem_Ioo]
    omega
  have hBne : ((Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M₂).card : ℝ) ≠ 0 := by
    exact_mod_cast hBpos.ne'
  have h3 : (∑ b ∈ Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M₂,
        ∑ sh : (j : Fin t') → PeelShiftQ p M₁ M₂ γ' s₀ a × PeelShiftQ p M₁ M₂ γ' s₀ a,
          peelPhiQ kω p M₁ M₂ N γ' t' s₀ g a b sh)
      = ∑ _b ∈ Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M₂,
          ∑ sh : (j : Fin t') → PeelShiftQ p M₁ M₂ γ' s₀ a × PeelShiftQ p M₁ M₂ γ' s₀ a,
            ((Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M₂).card : ℝ)⁻¹ *
              ∑ b' ∈ Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M₂,
                shortPowQ kω p M₁ M₂ N γ' t' s₀ g a b' sh := by
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro sh _
    exact peelPhiQ_eq_avg_shortPowQ kω p M₁ M₂ N A γ' t' s₀ g hM₂ ha b sh
  rw [h3]
  -- pull the constant out of the `b`-sum: the summand does not depend on `b`
  have h4 : (∑ _b ∈ Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M₂,
        ∑ sh : (j : Fin t') → PeelShiftQ p M₁ M₂ γ' s₀ a × PeelShiftQ p M₁ M₂ γ' s₀ a,
          ((Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M₂).card : ℝ)⁻¹ *
            ∑ b' ∈ Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M₂,
              shortPowQ kω p M₁ M₂ N γ' t' s₀ g a b' sh)
      = ((Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M₂).card : ℝ) *
        (((Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M₂).card : ℝ)⁻¹ *
          (∑ sh : (j : Fin t') → PeelShiftQ p M₁ M₂ γ' s₀ a × PeelShiftQ p M₁ M₂ γ' s₀ a,
            ∑ b' ∈ Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M₂,
              shortPowQ kω p M₁ M₂ N γ' t' s₀ g a b' sh)) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    congr 1
    exact (Finset.mul_sum (s := Finset.univ)
      (f := fun sh : (j : Fin t') → PeelShiftQ p M₁ M₂ γ' s₀ a × PeelShiftQ p M₁ M₂ γ' s₀ a =>
        ∑ b' ∈ Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M₂,
          shortPowQ kω p M₁ M₂ N γ' t' s₀ g a b' sh)
      (((Work.Peluse.UControl.paramBox (k := fun _ : ι => 1) M₂).card : ℝ)⁻¹)).symm
  rw [h4]
  -- cancel the cardinality and swap the two sums
  rw [← mul_assoc, mul_inv_cancel₀ hBne, one_mul]
  rw [Finset.sum_comm]

end

end Work.Peluse.Prop36SW
