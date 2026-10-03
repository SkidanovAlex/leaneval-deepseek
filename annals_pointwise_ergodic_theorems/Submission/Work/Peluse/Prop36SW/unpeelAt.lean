import Mathlib
import Submission.Work.Peluse.Prop36SW.lstatePeelFin

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Prop36SW

noncomputable section

open Work.Peluse.UControl

/-!
# The per-parameter unpeel identity of the §5 chain round

`unpeelAt` is the *per-parameter* half of the unpeel step of the §5 chain round: the identity

`‖g a‖^{2^{Σ_s t s}}_{□_{∏_s (p s a)[Lw s]}(S)}
  = (L₀^{-2})^{t'} ∑_{sh : (c[L₀] × c[L₀])^{t'}}
      ‖Δ'_{sh} (g a)‖^{2^{Σ_s trest s}}_{□_{∏_{s ≠ s₀}(p s a)[Lrest s]}(S)`

with `c = p s₀ a ≠ 0`, i.e. `Concat.boxNormPow_iteratedPeel` after reindexing the direction family
of the left-hand side along the splitting

`Σ s : ι, Fin (t s) ≃ Fin t' ⊕ Σ s : PeelSlot s₀, Fin (trest s)`

of the direction index set at the peeled slot `s₀` (whose window is `L₀` and whose multiplicity is
`t'`, while the remaining slots carry the multiplicities `trest` and the windows `Lrest`).

The work is entirely combinatorial:

* `unpeelSplitEquiv` is the splitting equivalence;
* `unpeelSplitEquiv_symm_inl` / `unpeelSplitEquiv_symm_inr` record what it does to the two summands;
* the factor `(L₀^{-1})^{2t'}` is `∏_{j : Fin t'} (c[L₀]).card^{-2}` with `(c[L₀]).card = L₀`
  (`unpeelAt_arithIcc_card`, which uses `c ≠ 0`);
* `boxNormPow_peelSum` is the general statement of the identity for an arbitrary sum-type index set.
-/

/-! ## 1. Elementary arithmetic -/

/-- The cardinality of the arithmetic progression `c[L] = {c, 2c, …, Lc}` for `c ≠ 0`. -/
lemma unpeelAt_arithIcc_card {c : ℤ} (hc : c ≠ 0) (L : ℕ) :
    (Work.Peluse.arithIcc c L).card = L := by
  rw [Work.Peluse.arithIcc, Finset.card_image_of_injOn]
  · simp
  · intro a _ b _ hab
    have h : (a : ℤ) = (b : ℤ) := mul_left_cancel₀ hc hab
    exact_mod_cast h

/-! ## 2. The splitting of the direction index set -/

/-- The equivalence between the slots different from `s₀.1` and the peeled slots
`PeelSlot s₀ = {s : Slot ι 1 // s ≠ s₀}`. -/
def unpeelSlotEquiv {ι : Type} (s₀ : Slot ι (fun _ => 1)) :
    {s : ι // s ≠ s₀.1} ≃ PeelSlot s₀ where
  toFun s := ⟨⟨s.1, 0⟩, fun h => s.2 (congrArg Sigma.fst h)⟩
  invFun s' := ⟨s'.1.1, fun h => s'.2 (Sigma.ext h (heq_of_eq (Subsingleton.elim _ _)))⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Sigma.ext rfl (heq_of_eq (Subsingleton.elim _ _)))

/-- The equivalence identifying the index block of the slots `≠ s₀.1` of `Σ s : ι, Fin (t s)` with
the peeled index type `Σ s : PeelSlot s₀, Fin (trest s)`, using `t s.1.1 = trest s`. -/
def unpeelRestEquiv {ι : Type} (s₀ : Slot ι (fun _ => 1)) (trest : PeelSlot s₀ → ℕ)
    (t : ι → ℕ) (ht : ∀ s : PeelSlot s₀, t s.1.1 = trest s) :
    {x : (Σ s : ι, Fin (t s)) // x.1 ≠ s₀.1} ≃ (Σ s : PeelSlot s₀, Fin (trest s)) :=
  (Equiv.subtypeSigmaEquiv (fun s : ι => Fin (t s)) (fun s => s ≠ s₀.1)).trans
    (Equiv.sigmaCongr (unpeelSlotEquiv s₀) (fun s => finCongr (ht (unpeelSlotEquiv s₀ s))))

/-- **The splitting of the box-norm family's direction index set at the peeled slot `s₀`**:
the `t'` copies of the slot `s₀` (whose multiplicity is `t s₀.1 = t'`) are separated from the
remaining slots `s ≠ s₀`, whose multiplicities are `trest`. -/
def unpeelSplitEquiv {ι : Type} (s₀ : Slot ι (fun _ => 1)) (trest : PeelSlot s₀ → ℕ)
    (t : ι → ℕ) (t' : ℕ) (ht0 : t s₀.1 = t') (ht : ∀ s : PeelSlot s₀, t s.1.1 = trest s) :
    (Σ s : ι, Fin (t s)) ≃ (Fin t' ⊕ Σ s : PeelSlot s₀, Fin (trest s)) := by
  classical
  exact (((Equiv.sumCompl (fun x : (Σ s : ι, Fin (t s)) => x.1 = s₀.1)).symm.trans
      (Equiv.sumCongr (Equiv.sigmaSubtype s₀.1) (Equiv.refl _))).trans
      (Equiv.sumCongr (finCongr ht0) (Equiv.refl _))).trans
    (Equiv.sumCongr (Equiv.refl (Fin t')) (unpeelRestEquiv s₀ trest t ht))

/-- The inverse of `unpeelSplitEquiv` on the `s₀`-block: the `j`-th copy of `s₀`. -/
lemma unpeelSplitEquiv_symm_inl {ι : Type} (s₀ : Slot ι (fun _ => 1))
    (trest : PeelSlot s₀ → ℕ) (t : ι → ℕ) (t' : ℕ) (ht0 : t s₀.1 = t')
    (ht : ∀ s : PeelSlot s₀, t s.1.1 = trest s) (j : Fin t') :
    (unpeelSplitEquiv s₀ trest t t' ht0 ht).symm (Sum.inl j) = ⟨s₀.1, Fin.cast ht0.symm j⟩ := by
  simp only [unpeelSplitEquiv, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.sumCongr_symm,
    Equiv.sumCongr_apply, Sum.map_inl, Equiv.refl_symm, Equiv.coe_refl, id_eq, finCongr_symm,
    finCongr_apply, Equiv.sumCompl_apply_inl]
  rfl

/-- The inverse of `unpeelSplitEquiv` on the remaining block. -/
lemma unpeelSplitEquiv_symm_inr {ι : Type} (s₀ : Slot ι (fun _ => 1))
    (trest : PeelSlot s₀ → ℕ) (t : ι → ℕ) (t' : ℕ) (ht0 : t s₀.1 = t')
    (ht : ∀ s : PeelSlot s₀, t s.1.1 = trest s)
    (y : Σ s : PeelSlot s₀, Fin (trest s)) :
    ((unpeelSplitEquiv s₀ trest t t' ht0 ht).symm (Sum.inr y)).1 = y.1.1.1 := by
  simp only [unpeelSplitEquiv, unpeelRestEquiv, unpeelSlotEquiv, Equiv.symm_trans_apply,
    Equiv.symm_symm, Equiv.sumCongr_symm, Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_symm,
    Equiv.coe_refl, id_eq, Equiv.sumCompl_apply_inr, Equiv.sigmaCongr]
  rfl

/-! ## 3. The general peel identity for a sum-type index set -/

/-- **The iterated peel of a family indexed by a sum type.**  If `β` is the index set of the
un-peeled directions and the peeled block consists of `m` copies of the set `A`, then
`boxNormPow` over the disjoint union `Fin m ⊕ β` of the family
`Sum.elim (fun _ => A) P` is the `|A|⁻²`-weighted average, over all tuples of pairs of shifts from
`A`, of the box-norm power of the iterated difference `iterDelta m` of `f` at the family `P`.

This is `Concat.boxNormPow_iteratedPeel` after identifying `Fin m ⊕ β` (enumerated by
`Fintype.equivFin`) with `Fin (m + card β)` (enumerated by `finSumFinEquiv ∘ sumCongr`). -/
theorem boxNormPow_peelSum {m : ℕ} {β : Type} [Fintype β] (hm : 1 ≤ Fintype.card β)
    (A : Finset ℤ) (P : β → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ)
    (hf : Work.Peluse.FinSuppZ f) :
    Work.Peluse.boxNormPow (Fintype.card (Fin m ⊕ β))
        (fun i => Sum.elim (fun _ : Fin m => A) P ((Fintype.equivFin (Fin m ⊕ β)).symm i)) S f
      = ((A.card : ℝ))⁻¹ ^ (2 * m) *
        ∑ sh : (j : Fin m) → ↥A × ↥A,
          Work.Peluse.boxNormPow (Fintype.card β)
            (fun i => P ((Fintype.equivFin β).symm i)) S
            (Work.Peluse.Ulower.iterDelta m
              (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) f) := by
  classical
  -- the standard enumeration of `Fin m ⊕ β` by `Fin (m + card β)`
  have hsum : Fintype.card (Fin m ⊕ β) = m + Fintype.card β := by
    rw [Fintype.card_sum, Fintype.card_fin]
  set Ae : (Fin m ⊕ β) ≃ Fin (m + Fintype.card β) :=
    (Equiv.sumCongr (Equiv.refl (Fin m)) (Fintype.equivFin β)).trans finSumFinEquiv with hAe
  -- the enumeration of `Fin m ⊕ β` by `Fin (card (Fin m ⊕ β))` induced by `Ae`
  set eM : (Fin m ⊕ β) ≃ Fin (Fintype.card (Fin m ⊕ β)) :=
    Ae.trans (finCongr hsum.symm) with heM
  -- (1) change the enumeration of `Fin m ⊕ β` from `Fintype.equivFin` to `eM`
  have h1 : Work.Peluse.boxNormPow (Fintype.card (Fin m ⊕ β))
        (fun i => Sum.elim (fun _ : Fin m => A) P ((Fintype.equivFin (Fin m ⊕ β)).symm i)) S f
      = Work.Peluse.boxNormPow (Fintype.card (Fin m ⊕ β))
        (fun i => Sum.elim (fun _ : Fin m => A) P (eM.symm i)) S f := by
    have h := Work.Peluse.BoxNorm.boxNormPow_perm
      (eM.symm.trans (Fintype.equivFin (Fin m ⊕ β)))
      (fun i => Sum.elim (fun _ : Fin m => A) P ((Fintype.equivFin (Fin m ⊕ β)).symm i)) S f
    simpa only [Equiv.trans_apply, Equiv.symm_apply_apply] using h.symm
  -- (2) reindex to the explicit enumeration `Ae` of `Fin (m + card β)`
  have h2 : Work.Peluse.boxNormPow (Fintype.card (Fin m ⊕ β))
        (fun i => Sum.elim (fun _ : Fin m => A) P (eM.symm i)) S f
      = Work.Peluse.boxNormPow (m + Fintype.card β)
        (fun j => Sum.elim (fun _ : Fin m => A) P (Ae.symm j)) S f :=
    LadderA.boxNormPow_reindex hsum (finCongr hsum).symm
      (fun j : Fin (m + Fintype.card β) => Sum.elim (fun _ : Fin m => A) P (Ae.symm j)) S f
  -- (3) the family is the concatenation of the peeled block and `P`
  have h3 : (fun j : Fin (m + Fintype.card β) => Sum.elim (fun _ : Fin m => A) P (Ae.symm j))
      = Fin.append (fun _ : Fin m => A)
          (fun i : Fin (Fintype.card β) => P ((Fintype.equivFin β).symm i)) := by
    funext j
    refine Fin.addCases (motive := fun j => Sum.elim (fun _ : Fin m => A) P (Ae.symm j)
      = Fin.append (fun _ : Fin m => A)
          (fun i : Fin (Fintype.card β) => P ((Fintype.equivFin β).symm i)) j) ?_ ?_ j
    · intro i
      rw [Fin.append_left]
      have h : Ae.symm (Fin.castAdd (Fintype.card β) i) = Sum.inl i := by
        rw [Equiv.symm_apply_eq]
        simp only [hAe, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.refl_apply,
          LadderA.finSumFinEquiv_apply, Sum.elim_inl]
      rw [h]
      rfl
    · intro i
      rw [Fin.append_right]
      have h : Ae.symm (Fin.natAdd m i) = Sum.inr ((Fintype.equivFin β).symm i) := by
        rw [Equiv.symm_apply_eq]
        simp only [hAe, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inr,
          LadderA.finSumFinEquiv_apply, Sum.elim_inr, Equiv.apply_symm_apply]
      rw [h]
      rfl
  rw [h1, h2, h3]
  rw [LadderA.boxNormPow_peel_append hm
    (fun i : Fin (Fintype.card β) => P ((Fintype.equivFin β).symm i))
    (fun _ : Fin m => A) S f hf]
  have hconst : (∏ j : Fin m, (((fun _ : Fin m => A) j).card : ℝ)⁻¹ ^ 2)
      = ((A.card : ℝ))⁻¹ ^ (2 * m) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  rw [hconst]

/-! ## 4. The per-parameter unpeel identity -/

theorem unpeelAt {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (p : ι → (Fin n → ℤ) → ℤ) (s₀ : Work.Peluse.UControl.Slot ι (fun _ => 1))
    (trest : Work.Peluse.Prop36SW.PeelSlot s₀ → ℕ)
    (Lrest : Work.Peluse.Prop36SW.PeelSlot s₀ → ℕ)
    (t : ι → ℕ) (Lw : ι → ℕ) (t' : ℕ) (L₀ : ℕ)
    (ht0 : t s₀.1 = t') (hL0 : Lw s₀.1 = L₀)
    (ht : ∀ s : Work.Peluse.Prop36SW.PeelSlot s₀, t s.1.1 = trest s)
    (hLw : ∀ s : Work.Peluse.Prop36SW.PeelSlot s₀, Lw s.1.1 = Lrest s)
    (hm : 1 ≤ Fintype.card (Σ s : Work.Peluse.Prop36SW.PeelSlot s₀, Fin (trest s)))
    (g : (Fin n → ℤ) → ℤ → ℂ) (a : Fin n → ℤ) (S : Finset ℤ)
    (hgood : p s₀.1 a ≠ 0) (hfin : Work.Peluse.FinSuppZ (g a)) :
    Work.Peluse.boxNormPow (Fintype.card (Σ s : ι, Fin (t s)))
        (fun i => Work.Peluse.arithIcc
          (p ((Fintype.equivFin (Σ s : ι, Fin (t s))).symm i).1 a)
          (Lw ((Fintype.equivFin (Σ s : ι, Fin (t s))).symm i).1)) S (g a)
      = ((L₀ : ℝ))⁻¹ ^ (2 * t') *
        ∑ sh : (j : Fin t') →
            ↥(Work.Peluse.arithIcc (p s₀.1 a) L₀) ×
              ↥(Work.Peluse.arithIcc (p s₀.1 a) L₀),
          Work.Peluse.boxNormPow (Fintype.card (Σ s : Work.Peluse.Prop36SW.PeelSlot s₀, Fin (trest s)))
            (fun i => Work.Peluse.arithIcc
              (p ((Fintype.equivFin (Σ s : Work.Peluse.Prop36SW.PeelSlot s₀, Fin (trest s))).symm i).1.1.1 a)
              (Lrest ((Fintype.equivFin (Σ s : Work.Peluse.Prop36SW.PeelSlot s₀, Fin (trest s))).symm i).1)) S
            (Work.Peluse.Ulower.iterDelta t'
              (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) (g a)) := by
  classical
  -- Step 1: reindex the left-hand side along the splitting equivalence.
  have step1 : Work.Peluse.boxNormPow (Fintype.card (Σ s : ι, Fin (t s)))
        (fun i => Work.Peluse.arithIcc
          (p ((Fintype.equivFin (Σ s : ι, Fin (t s))).symm i).1 a)
          (Lw ((Fintype.equivFin (Σ s : ι, Fin (t s))).symm i).1)) S (g a)
      = Work.Peluse.boxNormPow
          (Fintype.card (Fin t' ⊕ Σ s : Work.Peluse.Prop36SW.PeelSlot s₀, Fin (trest s)))
        (fun i => Sum.elim (fun _ : Fin t' => Work.Peluse.arithIcc (p s₀.1 a) L₀)
          (fun x : Σ s : Work.Peluse.Prop36SW.PeelSlot s₀, Fin (trest s) =>
            Work.Peluse.arithIcc (p x.1.1.1 a) (Lrest x.1))
          ((Fintype.equivFin (Fin t' ⊕ Σ s : Work.Peluse.Prop36SW.PeelSlot s₀, Fin (trest s))).symm i))
        S (g a) := by
    have hΦ := boxNormPow_family_equiv (unpeelSplitEquiv s₀ trest t t' ht0 ht)
      (fun x : (Σ s : ι, Fin (t s)) => Work.Peluse.arithIcc (p x.1 a) (Lw x.1))
      (Fintype.equivFin (Σ s : ι, Fin (t s)))
      (Fintype.equivFin (Fin t' ⊕ Σ s : Work.Peluse.Prop36SW.PeelSlot s₀, Fin (trest s)))
      (Fintype.card_congr (unpeelSplitEquiv s₀ trest t t' ht0 ht)) S (g a)
    have hfam : (fun i : Fin (Fintype.card
          (Fin t' ⊕ Σ s : Work.Peluse.Prop36SW.PeelSlot s₀, Fin (trest s))) =>
        Work.Peluse.arithIcc
          (p ((unpeelSplitEquiv s₀ trest t t' ht0 ht).symm
              ((Fintype.equivFin (Fin t' ⊕ Σ s : Work.Peluse.Prop36SW.PeelSlot s₀,
                Fin (trest s))).symm i)).1 a)
          (Lw ((unpeelSplitEquiv s₀ trest t t' ht0 ht).symm
              ((Fintype.equivFin (Fin t' ⊕ Σ s : Work.Peluse.Prop36SW.PeelSlot s₀,
                Fin (trest s))).symm i)).1))
      = (fun i => Sum.elim (fun _ : Fin t' => Work.Peluse.arithIcc (p s₀.1 a) L₀)
          (fun x : Σ s : Work.Peluse.Prop36SW.PeelSlot s₀, Fin (trest s) =>
            Work.Peluse.arithIcc (p x.1.1.1 a) (Lrest x.1))
          ((Fintype.equivFin (Fin t' ⊕ Σ s : Work.Peluse.Prop36SW.PeelSlot s₀,
            Fin (trest s))).symm i)) := by
      funext i
      obtain ⟨z, hz⟩ : ∃ z : Fin t' ⊕ Σ s : Work.Peluse.Prop36SW.PeelSlot s₀, Fin (trest s),
          (Fintype.equivFin (Fin t' ⊕ Σ s : Work.Peluse.Prop36SW.PeelSlot s₀,
            Fin (trest s))).symm i = z := ⟨_, rfl⟩
      rw [hz]
      rcases z with j | y
      · show Work.Peluse.arithIcc
            (p ((unpeelSplitEquiv s₀ trest t t' ht0 ht).symm (Sum.inl j)).1 a)
            (Lw ((unpeelSplitEquiv s₀ trest t t' ht0 ht).symm (Sum.inl j)).1)
          = Work.Peluse.arithIcc (p s₀.1 a) L₀
        rw [unpeelSplitEquiv_symm_inl s₀ trest t t' ht0 ht j, hL0]
      · show Work.Peluse.arithIcc
            (p ((unpeelSplitEquiv s₀ trest t t' ht0 ht).symm (Sum.inr y)).1 a)
            (Lw ((unpeelSplitEquiv s₀ trest t t' ht0 ht).symm (Sum.inr y)).1)
          = Work.Peluse.arithIcc (p y.1.1.1 a) (Lrest y.1)
        rw [unpeelSplitEquiv_symm_inr s₀ trest t t' ht0 ht y, hLw y.1]
    rw [hfam] at hΦ
    exact hΦ
  -- Step 2: peel, using the general identity.
  have hG := boxNormPow_peelSum (m := t')
    (β := Σ s : Work.Peluse.Prop36SW.PeelSlot s₀, Fin (trest s)) hm
    (Work.Peluse.arithIcc (p s₀.1 a) L₀)
    (fun x : Σ s : Work.Peluse.Prop36SW.PeelSlot s₀, Fin (trest s) =>
      Work.Peluse.arithIcc (p x.1.1.1 a) (Lrest x.1)) S (g a) hfin
  rw [step1, hG, unpeelAt_arithIcc_card hgood L₀]

end

end Work.Peluse.Prop36SW
