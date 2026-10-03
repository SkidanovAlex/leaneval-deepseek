import Mathlib
import Submission.Work.OROneRel.mmStepData_of_expsum_zero
import Submission.Work.OROneRel.HNNStep
import Submission.Work.OROneRel.magnusMap_injective_range
import Submission.Work.OROneRel.weinbaumDefs
import Submission.Work.OROneRel.magRewRel_pow
import Submission.Work.OROneRel.rewriteAux_append

namespace Work.OROneRel

universe u

/-! ### Two word-level inputs

The proof below rests on two elementary facts about the Magnus rewriting `rewrite`/`rewriteAux` of
words.  They are stated here (privately) so that this file is self-contained; the same statements
are being developed as standalone lemmas
(`Submission.Work.OROneRel.rewriteAux_add_const` and
`Submission.Work.OROneRel.rewrite_flatten_replicate_block`).
-/

/-- Shifting the starting index of the Magnus rewriting adds a constant to every decoration. -/
private theorem rewriteAux_add_const {α : Type u} (t : α) (c i : ℤ) (L : List (α × Bool)) :
    rewriteAux t (c + i) L =
      (rewriteAux t i L).map (fun p => ((p.1.1, p.1.2 + c), p.2)) := by
  classical
  induction L generalizing i with
  | nil =>
    rw [rewriteAux.eq_1, rewriteAux.eq_1]
    rfl
  | cons p L ih =>
    rw [rewriteAux.eq_def, rewriteAux.eq_def]
    by_cases h : p.1 = t
    · simp only [h, dif_pos]
      rw [Int.add_assoc]
      exact ih (i + (if p.2 then (1 : ℤ) else -1))
    · simp only [h, dif_neg, not_false_eq_true, List.map_cons]
      rw [ih i, Int.add_comm c i]

/-- The exponent sum of a letter in a concatenation of two words is the sum of the exponent sums. -/
private theorem sigmaList_append_aux {α : Type u} (t : α) (L₁ L₂ : List (α × Bool)) :
    sigmaList t (L₁ ++ L₂) = sigmaList t L₁ + sigmaList t L₂ := by
  simp only [sigmaList, List.map_append, List.sum_append]

/-- **The Magnus rewriting of a power, split along a subword.**  If a word `V` occurs as the
contiguous block `L₁ ++ V ++ L₂` of the `k`-fold concatenation of a word `W` of exponent sum zero in
the letter `z`, then the Magnus rewriting of that concatenation splits along `V`: the rewriting of
the block `V` is `rewriteAux z (sigmaList z L₁) V`, i.e. the rewriting of `V` with every decoration
shifted by the exponent sum of `z` in the part of the word preceding `V`. -/
private theorem rewrite_flatten_replicate_block {α : Type u} (z : α) (W : List (α × Bool)) (k : ℕ)
    (L₁ V L₂ : List (α × Bool)) (h0 : sigmaList z W = 0)
    (h : (List.replicate k W).flatten = L₁ ++ V ++ L₂) :
    (List.replicate k (rewrite z W)).flatten =
      rewrite z L₁ ++ rewriteAux z (sigmaList z L₁) V ++
        rewriteAux z (sigmaList z L₁ + sigmaList z V) L₂ := by
  have h1 : rewriteAux z 0 (List.replicate k W).flatten
      = (List.replicate k (rewrite z W)).flatten := by
    rw [rewriteAux_flatten_replicate z W h0 k]
    rfl
  have hσ : sigmaList z (L₁ ++ V) = sigmaList z L₁ + sigmaList z V :=
    sigmaList_append_aux z L₁ V
  rw [← h1, h, rewriteAux_append, hσ, rewriteAux_append]
  simp only [zero_add]
  rfl

/-- The reduced word of the `k`-th power of the class of a cyclically reduced word `L` is the
`k`-fold concatenation of `L`: no cancellation occurs at the junctions of the copies. -/
private theorem toWord_pow_mk_of_isCyclicallyReduced {γ : Type u} [DecidableEq γ] {L : List (γ × Bool)}
    (hL : FreeGroup.IsCyclicallyReduced L) (k : ℕ) :
    FreeGroup.toWord ((FreeGroup.mk L) ^ k) = (List.replicate k L).flatten := by
  rw [FreeGroup.toWord_pow]
  have hred : FreeGroup.IsReduced (List.replicate k L).flatten := (hL.flatten_replicate k).1
  rw [FreeGroup.toWord_mk, hL.isReduced.reduce_eq, hred.reduce_eq]

/-- **Localisation of the Magnus rewriting of a subword.**  Let `R` be a cyclically reduced word with
`eps z R = 0` (the exponent sum of `z` in `R` vanishes) and let `v` be a subword of a power `R^k` of
`R`.  Then the Magnus rewriting of `v` with respect to `z`, whose decorations may be shifted because
the rewriting is taken relative to the beginning of the arc `v` in the cyclic word of `R`, is -- after
a single overall shift `j` of the decorations -- a subword of a power of the Magnus rewriting of `R`
itself, viewed in the decorated alphabet `mmBeta z R`; and its length is the number of letters of `v`
different from `z`.  The shift `j` is the exponent sum of `z` in the part of `R^k` preceding the arc. -/
theorem magRew_block_subword_mmBeta {β : Type u} (R : FreeGroup β) (z : β) {k : ℕ} {v : FreeGroup β}
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator R) (hz : Work.OROneRel.eps z R = 0)
    (hsub : Work.OROneRel.IsSubwordOf v (R ^ k)) :
    ∃ (j : ℤ) (u : FreeGroup (Work.OROneRel.mmBeta z R)),
      Work.OROneRel.IsSubwordOf u ((Work.OROneRel.mmW z R) ^ k) ∧
      FreeGroup.map (fun p : Work.OROneRel.mmBeta z R => ((p.1.1, p.1.2) : ({x : β // x ≠ z} × ℤ))) u
        = magShiftAut z j (Work.OROneRel.magRewRel z v) ∧
      (FreeGroup.toWord u).length = Work.OROneRel.letterCountNot z v := by
  classical
  -- unfold the subword hypothesis: `v` is the block `L₁ ++ V ++ L₂` of the reduced word of `R ^ k`
  obtain ⟨L₁, L₂, hsubfac⟩ := hsub
  -- `W` and `V` are the reduced words of `R` and `v`
  set W : List (β × Bool) := FreeGroup.toWord R with hW
  set V : List (β × Bool) := FreeGroup.toWord v with hV
  have hWcyc : FreeGroup.IsCyclicallyReduced W := hcyc
  have hW0 : sigmaList z W = 0 := by
    rw [hW, sigmaList_eq_wordEps]
    exact hz
  -- the reduced word of `R ^ k` is the `k`-fold concatenation of `W`
  have hRk : FreeGroup.toWord (R ^ k) = (List.replicate k W).flatten := by
    have hRm : R = FreeGroup.mk W := by rw [hW, FreeGroup.mk_toWord]
    rw [hRm, toWord_pow_mk_of_isCyclicallyReduced hWcyc k]
  have hfac : (List.replicate k W).flatten = L₁ ++ V ++ L₂ := by
    rw [← hRk, hV]
    exact hsubfac
  -- the Magnus rewriting of `R` (over the decorated alphabet `MMAlpha z`)
  set M : List (MMAlpha z × Bool) := rewrite z W with hMdef
  have hMlist : mmList z R = M := by
    rw [hMdef, mmList, magRew_zero_eq_rewrite, ← hW]
  -- the rewriting of the `k`-fold concatenation, split along the block `V`
  have hblock : (List.replicate k M).flatten =
      rewrite z L₁ ++ rewriteAux z (sigmaList z L₁) V ++
        rewriteAux z (sigmaList z L₁ + sigmaList z V) L₂ := by
    rw [hMdef, rewrite_flatten_replicate_block z W k L₁ V L₂ hW0 hfac]
  set A : List (MMAlpha z × Bool) := rewrite z L₁ with hA
  set B : List (MMAlpha z × Bool) := rewriteAux z (sigmaList z L₁) V with hB
  set Cz : List (MMAlpha z × Bool) :=
    rewriteAux z (sigmaList z L₁ + sigmaList z V) L₂ with hC
  have hblock' : (List.replicate k M).flatten = A ++ B ++ Cz := by
    rw [hblock, hA, hB, hC]
  -- the lift of the decorations into the decorated alphabet `mmBeta z R`
  set f : MMAlpha z × Bool → (mmBeta z R × Bool) := fun p => (mmBetaOf z R p.1, p.2) with hf
  have hMWL : mmWL z R = M.map f := by
    rw [show mmWL z R = (mmList z R).map f from rfl, ← hMlist]
  have hMβ : (List.replicate k (mmWL z R)).flatten = (List.replicate k (M.map f)).flatten :=
    congrArg (fun L => (List.replicate k L).flatten) hMWL
  have hAβ : (List.replicate k (mmWL z R)).flatten = A.map f ++ B.map f ++ Cz.map f := by
    rw [hMβ]
    have hmap := congrArg (List.map f) hblock'
    simp only [List.map_append, List.map_flatten, List.map_replicate] at hmap
    exact hmap
  have hamb : FreeGroup.IsReduced (List.replicate k (mmWL z R)).flatten :=
    (mmWL_isCyclicallyReduced z R hcyc hz).flatten_replicate k |>.isReduced
  have hBred : FreeGroup.IsReduced (B.map f) :=
    FreeGroup.IsReduced.infix hamb ⟨A.map f, Cz.map f, hAβ.symm⟩
  have hu_tw : FreeGroup.toWord (FreeGroup.mk (B.map f)) = B.map f := by
    rw [FreeGroup.toWord_mk, hBred.reduce_eq]
  -- every letter of the block lies in the decoration set of `R`
  have hBmem : ∀ p ∈ B, p.1 ∈ mmDecSet z R := by
    intro p hp
    have hp' : p ∈ (List.replicate k M).flatten := by
      rw [hblock']
      exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hp)))
    rw [List.mem_flatten] at hp'
    obtain ⟨l, hl, hpl⟩ := hp'
    rw [List.mem_replicate] at hl
    exact mmList_mem_decSet z R (p := p.1) (b := p.2) (by rw [hMlist]; exact hl.2 ▸ hpl)
  refine ⟨sigmaList z L₁, FreeGroup.mk (B.map f), ?_, ?_, ?_⟩
  · -- the block is a subword of the `k`-th power of the rewritten relator
    refine ⟨A.map f, Cz.map f, ?_⟩
    rw [hu_tw, ← hAβ]
    rw [show mmW z R = FreeGroup.mk (mmWL z R) from rfl]
    rw [toWord_pow_mk_of_isCyclicallyReduced (mmWL_isCyclicallyReduced z R hcyc hz) k]
  · -- the projection of the lifted block is the shifted rewriting of `v`
    have hproj : List.map (fun x : mmBeta z R × Bool => (x.1.val, x.2)) (B.map f) = B := by
      have h1 : List.map (fun x : mmBeta z R × Bool => (x.1.val, x.2)) (B.map f)
          = B.map id := by
        rw [List.map_map]
        refine List.map_congr_left ?_
        intro p hp
        show (↑(mmBetaOf z R p.1), p.2) = p
        rw [mmBetaOf_val z R (hBmem p hp)]
      rw [h1, List.map_id]
    have hshift : (B : List (MMAlpha z × Bool)) =
        (rewrite z V).map (fun p : MMAlpha z × Bool => ((p.1.1, p.1.2 + sigmaList z L₁), p.2)) := by
      rw [hB]
      have h := rewriteAux_add_const z (sigmaList z L₁) (0 : ℤ) V
      rw [Int.add_zero] at h
      exact h
    have hRHS : magShiftAut z (sigmaList z L₁) (magRewRel z v) =
        FreeGroup.mk ((rewrite z V).map (fun p : MMAlpha z × Bool =>
          ((p.1.1, p.1.2 + sigmaList z L₁), p.2))) := by
      rw [show (magShiftAut z (sigmaList z L₁)) (magRewRel z v)
          = FreeGroup.map (magShiftBy z (sigmaList z L₁)) (magRewRel z v) from rfl]
      rw [show magRewRel z v = FreeGroup.mk (rewrite z (FreeGroup.toWord v)) from rfl]
      rw [← hV, FreeGroup.map.mk]
      congr 1
    rw [FreeGroup.map.mk]
    show FreeGroup.mk (List.map (fun x : mmBeta z R × Bool => (x.1.val, x.2)) (B.map f))
      = magShiftAut z (sigmaList z L₁) (magRewRel z v)
    rw [hproj, hRHS, hshift]
  · -- the length of the block is the number of letters of `v` different from `z`
    rw [hu_tw, List.length_map]
    have hlc : letterCountNot z v = (V.filter (fun p => decide (p.1 ≠ z))).length := by
      rw [hV, letterCountNot, List.countP_eq_length_filter]
    rw [hlc, hB, rewriteAux_length]

end Work.OROneRel
