import Mathlib
import Submission.Work.Peluse.ladderA_peel

/-!
# Splitting the peel at the peeled slot

The ladder's peel (`Work.Peluse.LadderA.boxNormPow_peel_append`) applies to a direction family in
the `Fin.append` normal form.  The hypothesis of `Work.Peluse.UControl.PeluseLadder` is indexed by
the sigma type `FamIdx kω = Σ_{ω ∈ I'} [k_ω]`, whose directions `pDir p M₁ a a' ω` see `a'` only
through the slots of `ω`.  The two results below perform that identification for each of the two
families of the ladder: the hypothesis family `pDirFam` (split into the `B`-part `ω ∌ s₀`, which is
peeled, and the `A`-part `ω ∋ s₀`, which survives in `QAfin`) and the conclusion family `conclDir`
(for which `Work.Peluse.LadderA.concl_peel` already supplies the `Fin.append` form; the only
correction needed is that the `B`-part of the conclusion is indexed with `a''` rather than with the
updated family, an equality that holds because a direction sees only the slots of `ω`).

The mathematical content is therefore purely bookkeeping: (i) the split of `FamIdx kω` into
`BIdx k kω s₀ ⊕ AIdx k kω s₀` along the predicate `s₀ ∈ ω`, an equivalence whose `.symm` sends
`Fin.castAdd _ i` to `QBfin i` and `Fin.natAdd _ j` to `QAfin j`; (ii) the observation that a
direction `pDir p M₁ a a' ω` is unchanged by updating `a'` at a slot outside `ω`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.LadderA

noncomputable section

open Work.Peluse Work.Peluse.UControl Work.Peluse.Ulower

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## 0. A direction family only sees the slots it contains -/

omit [Fintype ι] in
/-- The direction `pDir p M₁ a a' ω` depends on `a'` only through the slots of `ω`: updating `a'`
at a slot `s₀ ∉ ω` leaves it unchanged. -/
lemma pDir_update_of_not_mem (k : ι → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (M₁ : ℕ) (a : Fin n → ℤ)
    (a' : Slot ι k → ℤ) (s₀ : Slot ι k) {ω : SlotSet ι k} (h : s₀ ∉ ω.1) (c : ℤ) :
    pDir p M₁ a (Function.update a' s₀ c) ω = pDir p M₁ a a' ω := by
  unfold pDir
  congr 1
  refine Finset.sum_congr rfl (fun s hs => ?_)
  rw [Function.update_of_ne (fun hss => by rw [hss] at hs; exact h hs)]

/-! ## 1. Splitting the index set `FamIdx kω` along the peeled slot -/

/-- The split of the ladder's index set into the `B`-part (the subsets `ω ∌ s₀`) and the `A`-part
(the subsets `ω ∋ s₀`). -/
def famSplitFun (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (s₀ : Slot ι k) :
    FamIdx kω → (BIdx k kω s₀ ⊕ AIdx k kω s₀) :=
  fun j => if h : s₀ ∈ j.1.1 then Sum.inr ⟨⟨j.1, h⟩, j.2⟩ else Sum.inl ⟨⟨j.1, h⟩, j.2⟩

/-- The inverse of the split: a `B`-index is the pair of its subset and its slot index, and
similarly for the `A`-part. -/
def famSplitInv (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (s₀ : Slot ι k) :
    (BIdx k kω s₀ ⊕ AIdx k kω s₀) → FamIdx kω :=
  fun x => match x with
    | Sum.inl y => ⟨y.1.1, y.2⟩
    | Sum.inr y => ⟨y.1.1, y.2⟩

/-- **The split of the ladder's index set.** -/
def famSplitEquiv (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (s₀ : Slot ι k) :
    FamIdx kω ≃ (BIdx k kω s₀ ⊕ AIdx k kω s₀) where
  toFun := famSplitFun k kω s₀
  invFun := famSplitInv k kω s₀
  left_inv := by
    intro j
    by_cases h : s₀ ∈ j.1.1
    · rw [famSplitFun, dif_pos h]; simp [famSplitInv]
    · rw [famSplitFun, dif_neg h]; simp [famSplitInv]
  right_inv := by
    intro x
    rcases x with ⟨⟨ω, h⟩, r⟩ | ⟨⟨ω, h⟩, r⟩
    · rw [famSplitInv, famSplitFun, dif_neg h]
    · rw [famSplitInv, famSplitFun, dif_pos h]

lemma famSplitEquiv_apply (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (s₀ : Slot ι k)
    (j : FamIdx kω) : (famSplitEquiv k kω s₀) j = famSplitFun k kω s₀ j := rfl

lemma famSplitEquiv_symm_apply (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (s₀ : Slot ι k)
    (x : BIdx k kω s₀ ⊕ AIdx k kω s₀) :
    (famSplitEquiv k kω s₀).symm x = famSplitInv k kω s₀ x := rfl

lemma famSplitEquiv_apply_of_not_mem (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (s₀ : Slot ι k)
    (ω : SlotSet ι k) (h : s₀ ∉ ω.1) (r : Fin (kω ω)) :
    (famSplitEquiv k kω s₀) ⟨ω, r⟩ = Sum.inl (⟨⟨ω, h⟩, r⟩ : BIdx k kω s₀) := by
  rw [famSplitEquiv_apply, famSplitFun, dif_neg h]

lemma famSplitEquiv_apply_of_mem (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (s₀ : Slot ι k)
    (ω : SlotSet ι k) (h : s₀ ∈ ω.1) (r : Fin (kω ω)) :
    (famSplitEquiv k kω s₀) ⟨ω, r⟩ = Sum.inr (⟨⟨ω, h⟩, r⟩ : AIdx k kω s₀) := by
  rw [famSplitEquiv_apply, famSplitFun, dif_pos h]

/-- The split transported to `Fin`-indexing: the `B`-part first (with `Fintype.equivFin`), then
the `A`-part. -/
def splitNatEquiv (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (s₀ : Slot ι k) :
    FamIdx kω ≃ Fin (Fintype.card (BIdx k kω s₀) + Fintype.card (AIdx k kω s₀)) :=
  (famSplitEquiv k kω s₀).trans
    ((Equiv.sumCongr (Fintype.equivFin (BIdx k kω s₀)) (Fintype.equivFin (AIdx k kω s₀))).trans
      finSumFinEquiv)

/-- The equivalence reindexing the hypothesis's family `Fin (card (FamIdx kω))` into the
`Fin.append` normal form `Fin (card (BIdx k kω s₀) + card (AIdx k kω s₀))`. -/
def splitFinEquiv (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (s₀ : Slot ι k) :
    Fin (Fintype.card (BIdx k kω s₀) + Fintype.card (AIdx k kω s₀)) ≃
      Fin (Fintype.card (FamIdx kω)) :=
  (splitNatEquiv k kω s₀).symm.trans (Fintype.equivFin (FamIdx kω))

lemma splitFinEquiv_symm_apply_of_not_mem (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (s₀ : Slot ι k)
    (ω : SlotSet ι k) (h : s₀ ∉ ω.1) (r : Fin (kω ω)) :
    (splitFinEquiv k kω s₀).symm ((Fintype.equivFin (FamIdx kω)) ⟨ω, r⟩)
      = Fin.castAdd (Fintype.card (AIdx k kω s₀))
          ((Fintype.equivFin (BIdx k kω s₀)) ⟨⟨ω, h⟩, r⟩) := by
  simp only [splitFinEquiv, Equiv.symm_trans_apply, Equiv.symm_symm_apply, Equiv.symm_apply_apply,
    splitNatEquiv, Equiv.trans_apply, famSplitEquiv_apply, famSplitFun, dif_neg h,
    Equiv.sumCongr_apply, Sum.map, finSumFinEquiv_apply, Sum.elim_inl, Function.comp_apply]

lemma splitFinEquiv_symm_apply_of_mem (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (s₀ : Slot ι k)
    (ω : SlotSet ι k) (h : s₀ ∈ ω.1) (r : Fin (kω ω)) :
    (splitFinEquiv k kω s₀).symm ((Fintype.equivFin (FamIdx kω)) ⟨ω, r⟩)
      = Fin.natAdd (Fintype.card (BIdx k kω s₀))
          ((Fintype.equivFin (AIdx k kω s₀)) ⟨⟨ω, h⟩, r⟩) := by
  simp only [splitFinEquiv, Equiv.symm_trans_apply, Equiv.symm_symm_apply, Equiv.symm_apply_apply,
    splitNatEquiv, Equiv.trans_apply, famSplitEquiv_apply, famSplitFun, dif_pos h,
    Equiv.sumCongr_apply, Sum.map, finSumFinEquiv_apply, Sum.elim_inr, Function.comp_apply]

/-- The index set of the hypothesis splits evenly: `card (FamIdx kω) = card (BIdx) + card (AIdx)`. -/
lemma card_famIdx (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (s₀ : Slot ι k) :
    Fintype.card (FamIdx kω) = Fintype.card (BIdx k kω s₀) + Fintype.card (AIdx k kω s₀) := by
  rw [← Fintype.card_congr (famSplitEquiv k kω s₀).symm, Fintype.card_sum]

/-- The `B`-family of the peel is insensitive to the value of the peeled parameter: `QBfin` is
built from directions `ω ∌ s₀`. -/
lemma QBfin_update_eq (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (M₁ : ℕ)
    (a : Fin n → ℤ) (a'' : Slot ι k → ℤ) (s₀ : Slot ι k) (a₀ : ℤ)
    (j : Fin (Fintype.card (BIdx k kω s₀))) :
    QBfin k kω p M₁ a (Function.update a'' s₀ a₀) s₀ j = QBfin k kω p M₁ a a'' s₀ j := by
  simp only [QBfin, qB]
  exact pDir_update_of_not_mem k p M₁ a a'' s₀
    ((Fintype.equivFin (BIdx k kω s₀)).symm j).1.2 a₀

/-- **The hypothesis's family is the concatenation of the peeled `B`-family and the surviving
`A`-family.** -/
lemma famIdx_append_eq (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (M₁ : ℕ)
    (a : Fin n → ℤ) (a'' : Slot ι k → ℤ) (s₀ : Slot ι k) (a₀ : ℤ) :
    (fun j : Fin (Fintype.card (FamIdx kω)) =>
        pDirFam p M₁ a (Function.update a'' s₀ a₀) ((Fintype.equivFin (FamIdx kω)).symm j))
      = fun i => Fin.append (QBfin k kω p M₁ a (Function.update a'' s₀ a₀) s₀)
          (QAfin k kω p M₁ a (Function.update a'' s₀ a₀) s₀)
          ((splitFinEquiv k kω s₀).symm i) := by
  funext i
  obtain ⟨j, rfl⟩ := (Fintype.equivFin (FamIdx kω)).surjective i
  rw [Equiv.symm_apply_apply]
  rcases j with ⟨ω, r⟩
  by_cases h : s₀ ∈ ω.1
  · rw [splitFinEquiv_symm_apply_of_mem k kω s₀ ω h r, Fin.append_right]
    simp only [pDirFam, QAfin, qA, pDir, Equiv.symm_apply_apply]
  · rw [splitFinEquiv_symm_apply_of_not_mem k kω s₀ ω h r, Fin.append_left]
    simp only [pDirFam, QBfin, qB, pDir, Equiv.symm_apply_apply]

/-- **Reindexing the hypothesis's box-norm power into the `Fin.append` normal form.** -/
lemma boxNormPow_famIdx_split (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ)
    (M₁ : ℕ) (a : Fin n → ℤ) (a'' : Slot ι k → ℤ) (s₀ : Slot ι k) (a₀ : ℤ)
    (S : Finset ℤ) (f : ℤ → ℂ) :
    boxNormPow (Fintype.card (FamIdx kω))
        (fun j => pDirFam p M₁ a (Function.update a'' s₀ a₀)
          ((Fintype.equivFin (FamIdx kω)).symm j)) S f
      = boxNormPow (Fintype.card (BIdx k kω s₀) + Fintype.card (AIdx k kω s₀))
          (Fin.append (QBfin k kω p M₁ a (Function.update a'' s₀ a₀) s₀)
            (QAfin k kω p M₁ a (Function.update a'' s₀ a₀) s₀)) S f := by
  rw [famIdx_append_eq k kω p M₁ a a'' s₀ a₀]
  exact boxNormPow_reindex (card_famIdx k kω s₀) (splitFinEquiv k kω s₀) _ S f

/-! ## 2. The peel with a possibly different `B`-family on the two sides -/

/-- The sum over the shift tuples of a family of direction sets is insensitive to replacing the
family, provided the sets are equal pointwise: this is what allows the peel's two sides to use
different (but equal) expressions for the `B`-family. -/
lemma sum_shiftTuple_congr {b : ℕ} {Q Q' : Fin b → Finset ℤ} (hQ : ∀ j, Q j = Q' j)
    {M : Type*} [AddCommMonoid M] (G : ((j : Fin b) → ℤ × ℤ) → M) :
    (∑ sh : (j : Fin b) → ↥(Q j) × ↥(Q j), G (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))))
      = ∑ sh : (j : Fin b) → ↥(Q' j) × ↥(Q' j),
          G (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) := by
  refine Fintype.sum_equiv
    (Equiv.piCongrRight (fun j => Equiv.prodCongr (Equiv.subtypeEquivRight (fun x => by rw [hQ j]))
      (Equiv.subtypeEquivRight (fun x => by rw [hQ j])))) _ _ (fun x => ?_)
  congr 1

/-- **The peel with the peeled `B`-family written in an equivalent form.** -/
lemma boxNormPow_peel_append' {a b : ℕ} (ha : 1 ≤ a) (QA : Fin a → Finset ℤ)
    (QB QB' : Fin b → Finset ℤ) (hQB : ∀ j, QB j = QB' j) (S : Finset ℤ) (f : ℤ → ℂ)
    (hf : FinSuppZ f) :
    boxNormPow (b + a) (Fin.append QB QA) S f = (∏ j : Fin b, ((QB' j).card : ℝ)⁻¹ ^ 2) *
      ∑ sh : (j : Fin b) → ↥(QB' j) × ↥(QB' j),
        boxNormPow a QA S (iterDelta b (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) f) := by
  have hsum : (∑ sh : (j : Fin b) → ↥(QB j) × ↥(QB j),
        boxNormPow a QA S (iterDelta b (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) f))
      = ∑ sh : (j : Fin b) → ↥(QB' j) × ↥(QB' j),
          boxNormPow a QA S (iterDelta b (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) f) :=
    sum_shiftTuple_congr hQB (fun v : (j : Fin b) → ℤ × ℤ => boxNormPow a QA S (iterDelta b v f))
  rw [boxNormPow_peel_append ha QA QB S f hf,
    show (∏ j : Fin b, ((QB j).card : ℝ)⁻¹ ^ 2) = ∏ j : Fin b, ((QB' j).card : ℝ)⁻¹ ^ 2
      from Finset.prod_congr rfl (fun j _ => by rw [hQB j]),
    hsum]

/-! ## 3. The two conjuncts -/

/-- **The hypothesis side of the split.** -/
lemma peel_hyp_conj (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (M₁ : ℕ)
    (a : Fin n → ℤ) (a'' : Slot ι k → ℤ) (s₀ : Slot ι k)
    (hA : 1 ≤ Fintype.card (AIdx k kω s₀)) (S : Finset ℤ) (f : ℤ → ℂ) (hf : FinSuppZ f)
    (a₀ : ℤ) :
    boxNormPow (Fintype.card (FamIdx kω))
        (fun j => pDirFam p M₁ a (Function.update a'' s₀ a₀)
          ((Fintype.equivFin (FamIdx kω)).symm j)) S f
      = (∏ j : Fin (Fintype.card (BIdx k kω s₀)),
            ((QBfin k kω p M₁ a a'' s₀ j).card : ℝ)⁻¹ ^ 2) *
        ∑ sh : (j : Fin (Fintype.card (BIdx k kω s₀))) →
            ↥(QBfin k kω p M₁ a a'' s₀ j) × ↥(QBfin k kω p M₁ a a'' s₀ j),
          boxNormPow (Fintype.card (AIdx k kω s₀))
            (QAfin k kω p M₁ a (Function.update a'' s₀ a₀) s₀) S
            (iterDelta (Fintype.card (BIdx k kω s₀))
              (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) f) := by
  rw [boxNormPow_famIdx_split k kω p M₁ a a'' s₀ a₀ S f]
  exact boxNormPow_peel_append' hA (QAfin k kω p M₁ a (Function.update a'' s₀ a₀) s₀)
    (QBfin k kω p M₁ a (Function.update a'' s₀ a₀) s₀) (QBfin k kω p M₁ a a'' s₀)
    (fun j => QBfin_update_eq k kω p M₁ a a'' s₀ a₀ j) S f hf

/-- **The conclusion side of the split.** -/
lemma peel_concl_conj (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (M₁ M₂ : ℕ)
    (a : Fin n → ℤ) (a'' : Slot ι k → ℤ) (s₀ : Slot ι k) (tbig : ℕ) (γ' : ℝ) (hT : 1 ≤ tbig)
    (S : Finset ℤ) (f : ℤ → ℂ) (hf : FinSuppZ f) (b₀ : ℤ) :
    boxNormPow (Fintype.card (ConclIdx s₀ kω tbig))
        (fun j => conclDir p M₁ M₂ γ' s₀ tbig a (Function.update a'' s₀ b₀)
          ((Fintype.equivFin (ConclIdx s₀ kω tbig)).symm j)) S f
      = (∏ j : Fin (Fintype.card (BIdx k kω s₀)),
            ((QBfin k kω p M₁ a a'' s₀ j).card : ℝ)⁻¹ ^ 2) *
        ∑ sh : (j : Fin (Fintype.card (BIdx k kω s₀))) →
            ↥(QBfin k kω p M₁ a a'' s₀ j) × ↥(QBfin k kω p M₁ a a'' s₀ j),
          boxNormPow tbig (fun _ : Fin tbig =>
              arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) S
            (iterDelta (Fintype.card (BIdx k kω s₀))
              (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) f) := by
  have hsum : (∑ sh : (j : Fin (Fintype.card (BIdx k kω s₀))) →
          ↥(QBfin k kω p M₁ a (Function.update a'' s₀ b₀) s₀ j) ×
            ↥(QBfin k kω p M₁ a (Function.update a'' s₀ b₀) s₀ j),
        boxNormPow tbig (fun _ : Fin tbig =>
            arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) S
          (iterDelta (Fintype.card (BIdx k kω s₀))
            (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) f))
      = ∑ sh : (j : Fin (Fintype.card (BIdx k kω s₀))) →
            ↥(QBfin k kω p M₁ a a'' s₀ j) × ↥(QBfin k kω p M₁ a a'' s₀ j),
          boxNormPow tbig (fun _ : Fin tbig =>
              arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) S
            (iterDelta (Fintype.card (BIdx k kω s₀))
              (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) f) :=
    sum_shiftTuple_congr (fun j => QBfin_update_eq k kω p M₁ a a'' s₀ b₀ j)
      (fun v : (j : Fin (Fintype.card (BIdx k kω s₀))) → ℤ × ℤ =>
        boxNormPow tbig (fun _ : Fin tbig =>
            arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) S
          (iterDelta (Fintype.card (BIdx k kω s₀)) v f))
  rw [concl_peel k kω p M₁ M₂ a (Function.update a'' s₀ b₀) s₀ tbig γ' hT S f hf,
    show (∏ j : Fin (Fintype.card (BIdx k kω s₀)),
        ((QBfin k kω p M₁ a (Function.update a'' s₀ b₀) s₀ j).card : ℝ)⁻¹ ^ 2)
      = ∏ j : Fin (Fintype.card (BIdx k kω s₀)),
          ((QBfin k kω p M₁ a a'' s₀ j).card : ℝ)⁻¹ ^ 2
      from Finset.prod_congr rfl (fun j _ => by rw [QBfin_update_eq k kω p M₁ a a'' s₀ b₀ j]),
    hsum]

theorem peel_split_pair {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (k : ι → ℕ)
    (kω : Work.Peluse.UControl.SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (M₁ M₂ : ℕ)
    (a : Fin n → ℤ) (a'' : Work.Peluse.UControl.Slot ι k → ℤ)
    (s₀ : Work.Peluse.UControl.Slot ι k) (tbig : ℕ) (γ' : ℝ) (hT : 1 ≤ tbig)
    (hA : 1 ≤ Fintype.card (Work.Peluse.LadderA.AIdx k kω s₀)) (S : Finset ℤ) (f : ℤ → ℂ)
    (hf : Work.Peluse.FinSuppZ f) (a₀ b₀ : ℤ) :
    (Work.Peluse.boxNormPow (Fintype.card (Work.Peluse.UControl.FamIdx kω))
        (fun j => Work.Peluse.UControl.pDirFam p M₁ a (Function.update a'' s₀ a₀)
          ((Fintype.equivFin (Work.Peluse.UControl.FamIdx kω)).symm j)) S f
      = (∏ j : Fin (Fintype.card (Work.Peluse.LadderA.BIdx k kω s₀)),
            ((Work.Peluse.LadderA.QBfin k kω p M₁ a a'' s₀ j).card : ℝ)⁻¹ ^ 2) *
        ∑ sh : (j : Fin (Fintype.card (Work.Peluse.LadderA.BIdx k kω s₀))) →
            ↥(Work.Peluse.LadderA.QBfin k kω p M₁ a a'' s₀ j) ×
              ↥(Work.Peluse.LadderA.QBfin k kω p M₁ a a'' s₀ j),
          Work.Peluse.boxNormPow (Fintype.card (Work.Peluse.LadderA.AIdx k kω s₀))
            (Work.Peluse.LadderA.QAfin k kω p M₁ a (Function.update a'' s₀ a₀) s₀) S
            (Work.Peluse.Ulower.iterDelta (Fintype.card (Work.Peluse.LadderA.BIdx k kω s₀))
              (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) f)) ∧
    (Work.Peluse.boxNormPow (Fintype.card (Work.Peluse.UControl.ConclIdx s₀ kω tbig))
        (fun j => Work.Peluse.UControl.conclDir p M₁ M₂ γ' s₀ tbig a (Function.update a'' s₀ b₀)
          ((Fintype.equivFin (Work.Peluse.UControl.ConclIdx s₀ kω tbig)).symm j)) S f
      = (∏ j : Fin (Fintype.card (Work.Peluse.LadderA.BIdx k kω s₀)),
            ((Work.Peluse.LadderA.QBfin k kω p M₁ a a'' s₀ j).card : ℝ)⁻¹ ^ 2) *
        ∑ sh : (j : Fin (Fintype.card (Work.Peluse.LadderA.BIdx k kω s₀))) →
            ↥(Work.Peluse.LadderA.QBfin k kω p M₁ a a'' s₀ j) ×
              ↥(Work.Peluse.LadderA.QBfin k kω p M₁ a a'' s₀ j),
          Work.Peluse.boxNormPow tbig (fun _ : Fin tbig =>
              Work.Peluse.arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) S
            (Work.Peluse.Ulower.iterDelta (Fintype.card (Work.Peluse.LadderA.BIdx k kω s₀))
              (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) f)) := by
  constructor
  · exact peel_hyp_conj k kω p M₁ a a'' s₀ hA S f hf a₀
  · exact peel_concl_conj k kω p M₁ M₂ a a'' s₀ tbig γ' hT S f hf b₀

end

end Work.Peluse.LadderA
