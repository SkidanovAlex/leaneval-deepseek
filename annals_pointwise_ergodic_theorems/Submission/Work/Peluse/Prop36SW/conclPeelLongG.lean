import Mathlib
import Submission.Work.Peluse.Prop36SW.GenDefs
import Submission.Work.Peluse.ladderA_defs

namespace Work.Peluse.Prop36SW

open Work.Peluse.UControl

/-!
# Peeling the long directions of the ladder's conclusion

`ConclIdx s₀ kω t' = Sum (Fin t') (ShortIdx k kω s₀)`: the conclusion's index type is the `t'` long
directions `arithIcc (p s₀.1 a) ⌊γ'M₁M₂⌋` followed by the "short" directions
`arithIcc (∑_{s ∈ ω} p s.1 a · b s) M₁` of the subsets `ω ∌ s₀`.

`conclPeelLongG` is the iterated peel `Work.Peluse.Concat.boxNormPow_iteratedPeel` applied to the
*long* coordinates of that family (the first `t'` of them): it expresses the `2^{t'+card ShortIdx}`-th
box-norm power of `f` at the conclusion's family as the `|arithIcc …|⁻²`-weighted average, over all
tuples of pairs of shifts from the long directions, of the `2^{card ShortIdx}`-th box-norm power of
the iterated difference `iterDelta t'` of `f` at the *short* family `shortFamG`.
-/

noncomputable section

/-- **The conclusion's family as a concatenation.**  Reading the conclusion's index type as
`Fin t' ⊕ ShortIdx` (via `Fintype.equivFin` on the short part) and then as `Fin (t' + card ShortIdx)`
(via `finSumFinEquiv`), the family `conclDirG` is the concatenation of the constant long family
`arithIcc (p s₀.1 a) ⌊γ'M₁M₂⌋` and the short family `shortFamG`. -/
lemma conclDirG_eq_append {ι : Type} [Fintype ι] [DecidableEq ι] {k : ι → ℕ}
    (kω : SlotSet ι k → ℕ) {P : Type} (p : ι → P → ℤ) (M₁ M₂ : ℕ) (γ' : ℝ)
    (s₀ : Slot ι k) (t' : ℕ) (a : P) (b : Slot ι k → ℤ) (j : ConclIdx s₀ kω t') :
    conclDirG p M₁ M₂ γ' s₀ t' a b j
      = Fin.append (fun _ : Fin t' =>
            Work.Peluse.arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
          (shortFamG kω p M₁ a b s₀)
          (finSumFinEquiv (Equiv.sumCongr (Equiv.refl (Fin t'))
            (Fintype.equivFin (ShortIdx k kω s₀)) j)) := by
  rcases j with jl | x
  · simp only [conclDirG, Equiv.sumCongr_apply, Sum.map_inl, LadderA.finSumFinEquiv_apply,
      Sum.elim_inl, Fin.append_left]
  · simp only [conclDirG, Equiv.sumCongr_apply, Sum.map_inr, LadderA.finSumFinEquiv_apply,
      Sum.elim_inr, Fin.append_right, shortFamG, Equiv.symm_apply_apply]

theorem conclPeelLongG {ι : Type} [Fintype ι] [DecidableEq ι] {k : ι → ℕ} (kω : Work.Peluse.UControl.SlotSet ι k → ℕ)
    {P : Type} (p : ι → P → ℤ) (M₁ M₂ : ℕ) (γ' : ℝ) (s₀ : Work.Peluse.UControl.Slot ι k) (t' : ℕ) (hT : 1 ≤ t')
    (hB : 1 ≤ Fintype.card (Work.Peluse.Prop36SW.ShortIdx k kω s₀))
    (a : P) (b : Work.Peluse.UControl.Slot ι k → ℤ) (S : Finset ℤ) (f : ℤ → ℂ) (hf : Work.Peluse.FinSuppZ f) :
    Work.Peluse.boxNormPow (Fintype.card (Work.Peluse.UControl.ConclIdx s₀ kω t'))
        (fun i => Work.Peluse.Prop36SW.conclDirG p M₁ M₂ γ' s₀ t' a b ((Fintype.equivFin (Work.Peluse.UControl.ConclIdx s₀ kω t')).symm i)) S f
      = (∏ j : Fin t', (((Work.Peluse.arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat).card : ℝ))⁻¹ ^ 2) *
        ∑ sh : (j : Fin t') → ↥(Work.Peluse.arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) ×
            ↥(Work.Peluse.arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat),
          Work.Peluse.boxNormPow (Fintype.card (Work.Peluse.Prop36SW.ShortIdx k kω s₀))
            (Work.Peluse.Prop36SW.shortFamG kω p M₁ a b s₀) S
            (Work.Peluse.Ulower.iterDelta t' (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) f) := by
  -- The conclusion's index type is `Fin t' ⊕ ShortIdx`, so its cardinality is `t' + card ShortIdx`.
  have hcard : t' + Fintype.card (ShortIdx k kω s₀) = Fintype.card (ConclIdx s₀ kω t') := by
    show t' + Fintype.card (ShortIdx k kω s₀)
      = Fintype.card (Sum (Fin t') (ShortIdx k kω s₀))
    simp [Fintype.card_sum]
  -- The reindexing carrying `Fin (card (ConclIdx …))` to `Fin (t' + card ShortIdx)`.
  let e : Fin (Fintype.card (ConclIdx s₀ kω t')) ≃ Fin (t' + Fintype.card (ShortIdx k kω s₀)) :=
    ((Fintype.equivFin (ConclIdx s₀ kω t')).symm.trans
      (Equiv.sumCongr (Equiv.refl (Fin t')) (Fintype.equivFin (ShortIdx k kω s₀)))).trans
      finSumFinEquiv
  rw [← LadderA.boxNormPow_reindex hcard e
    (fun i => conclDirG p M₁ M₂ γ' s₀ t' a b
      ((Fintype.equivFin (ConclIdx s₀ kω t')).symm i)) S f]
  -- Reindexed, the conclusion's family is the concatenation of the long and the short families.
  have hfam : (fun i : Fin (t' + Fintype.card (ShortIdx k kω s₀)) =>
        conclDirG p M₁ M₂ γ' s₀ t' a b
          ((Fintype.equivFin (ConclIdx s₀ kω t')).symm (e.symm i)))
      = Fin.append (fun _ : Fin t' =>
            Work.Peluse.arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
          (shortFamG kω p M₁ a b s₀) := by
    funext i
    rw [show (Fintype.equivFin (ConclIdx s₀ kω t')).symm (e.symm i)
        = (Equiv.sumCongr (Equiv.refl (Fin t')) (Fintype.equivFin (ShortIdx k kω s₀))).symm
            (finSumFinEquiv.symm i) from by
      simp only [e, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.symm_apply_apply]]
    rw [conclDirG_eq_append]
    exact congrArg (Fin.append _ _)
      (by rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply])
  -- Peel the long coordinates with the iterated peel.
  rw [hfam, LadderA.boxNormPow_peel_append hB (shortFamG kω p M₁ a b s₀)
    (fun _ : Fin t' =>
      Work.Peluse.arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) S f hf]

end

end Work.Peluse.Prop36SW
