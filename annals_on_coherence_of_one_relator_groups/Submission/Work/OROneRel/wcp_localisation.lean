import Mathlib
import Submission.Work.OROneRel.mmStepData_of_expsum_zero
import Submission.Work.OROneRel.HNNStep
import Submission.Work.OROneRel.magnusMap_injective_range
import Submission.Work.OROneRel.weinbaumDefs
import Submission.Work.OROneRel.rewriteAux_append
import Submission.Work.OROneRel.rewrite_isReduced
import Submission.Work.OROneRel.rewrite_length_lt
import Submission.Work.OROneRel.magRewRel_pow

/-!
# Localisation of the Magnus rewriting of a subword

`Work.OROneRel.wcp_localisation` is the localisation of the Magnus rewriting used by the
exponent-sum-zero step of Weinbaum's theorem (`Work.OROneRel.sigma_step_aux`): if `R` is cyclically
reduced with `eps z R = 0` and `v` is a subword of a power `R ^ k` of `R`, then, after a single
overall shift `j` of the decorations, the Magnus rewriting `magRewRel z v` of `v` is a subword of a
power of the Magnus rewriting `mmW z R` of `R`, with the same number of letters as `v` has letters
different from `z`.

The proof is a list computation.  Write `W = toWord R` and `V = toWord v`; since `R` is cyclically
reduced, `toWord (R ^ k) = W ^ k` (the `k`-fold concatenation) and the hypothesis
`IsSubwordOf v (R ^ k)` says that `W ^ k = A ++ V ++ C` for words `A`, `C`.  Because the exponent sum
of `z` in `W` vanishes,

`rewriteAux z 0 (W ^ k) = (rewriteAux z 0 W) ^ k`

(`Work.OROneRel.rewriteAux_flatten_replicate`), whereas the additive property of `rewriteAux`
(`Work.OROneRel.rewriteAux_append`) computes the same word as

`rewriteAux z 0 A ++ rewriteAux z (sigmaList z A) V ++ rewriteAux z _ C`.

So the block `blk = rewriteAux z (sigmaList z A) V` is a contiguous factor of the `k`-fold
concatenation of `mmList z R = rewriteAux z 0 W`.  Every one of its letters therefore lies in the
"strip" `mmDecSet z R` (so that the inclusion `mmBeta z R` is an identity on them), and the element
`u` of `F (mmBeta z R)` with word `blk` is a subword of `(mmW z R) ^ k`.  Finally
`rewriteAux z j V = (rewriteAux z 0 V).map (shift j)` (`wcp_rewriteAux_shift`), so forgetting the
strip turns `u` into `magShiftAut z j (magRewRel z v)`.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ### The decoration shift

Shifting every decoration index of a rewritten word by `j` is multiplication by `magShiftHom t j`,
so it commutes with `FreeGroup.mk`. -/

/-- The decoration shift by `i`, on a rewritten letter. -/
def wcpShiftL (t : α) (i : ℤ) (p : ({x : α // x ≠ t} × ℤ) × Bool) :
    ({x : α // x ≠ t} × ℤ) × Bool :=
  ((p.1.1, p.1.2 + i), p.2)

theorem wcpShiftL_zero (t : α) (p : ({x : α // x ≠ t} × ℤ) × Bool) : wcpShiftL t 0 p = p := by
  obtain ⟨⟨x, m⟩, b⟩ := p
  simp [wcpShiftL]

theorem wcpShiftL_comp (t : α) (i j : ℤ) (p : ({x : α // x ≠ t} × ℤ) × Bool) :
    wcpShiftL t i (wcpShiftL t j p) = wcpShiftL t (i + j) p := by
  obtain ⟨⟨x, m⟩, b⟩ := p
  have h : m + j + i = m + (i + j) := by ring
  show ((x, m + j + i), b) = ((x, m + (i + j)), b)
  rw [h]

theorem wcpShiftL_eq_magShiftBy (t : α) (i : ℤ) (p : ({x : α // x ≠ t} × ℤ) × Bool) :
    wcpShiftL t i p = (magShiftBy t i p.1, p.2) := rfl

/-- Shifting the decorations of a rewritten word commutes with the Magnus rewriting: the rewriting
of a word with starting exponent sum `i` is the rewriting with starting exponent sum `0`, with every
decoration index shifted by `i`. -/
theorem wcp_rewriteAux_shift (t : α) (L : List (α × Bool)) (i : ℤ) :
    rewriteAux t i L = (rewriteAux t 0 L).map (wcpShiftL t i) := by
  induction L generalizing i with
  | nil => rw [rewriteAux_nil, rewriteAux_nil]; rfl
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    by_cases hp : a = t
    · rw [rewriteAux_cons_of_eq t i L hp, rewriteAux_cons_of_eq t 0 L hp,
        ih (i + (if b then 1 else -1)), ih (0 + (if b then 1 else -1)), List.map_map]
      congr 1
      funext q
      rw [Function.comp_apply, zero_add, wcpShiftL_comp]
    · rw [rewriteAux_cons_of_ne t i L hp, rewriteAux_cons_of_ne t 0 L hp, ih i, List.map_cons]
      simp [wcpShiftL]

/-- The decoration shift and `FreeGroup.mk`: the element of the free group represented by the
shifted rewriting is the image of the (unshifted) rewriting under `magShiftAut t i`. -/
theorem wcp_mk_rewriteAux_shift (t : α) (L : List (α × Bool)) (i : ℤ) :
    FreeGroup.mk (rewriteAux t i L) = magShiftAut t i (FreeGroup.mk (rewriteAux t 0 L)) := by
  have h : (rewriteAux t 0 L).map (fun x => (magShiftBy t i x.1, x.2))
      = (rewriteAux t 0 L).map (wcpShiftL t i) :=
    List.map_congr_left fun x _ => rfl
  rw [wcp_rewriteAux_shift t L i, ← h, ← FreeGroup.map.mk]
  rfl

/-! ### Flattening a repeated map -/

theorem wcp_map_flatten_replicate {γ δ : Type*} (f : γ → δ) (L : List γ) (k : ℕ) :
    (List.replicate k (L.map f)).flatten = ((List.replicate k L).flatten).map f := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ, List.flatten_cons, List.replicate_succ, List.flatten_cons,
        List.map_append, ih]

/-! ### The localisation -/

theorem wcp_localisation {β : Type u} (R : FreeGroup β) (z : β) {k : ℕ} {v : FreeGroup β}
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator R) (hz : Work.OROneRel.eps z R = 0)
    (hsub : Work.OROneRel.IsSubwordOf v (R ^ k)) :
    ∃ (j : ℤ) (u : FreeGroup (Work.OROneRel.mmBeta z R)),
      Work.OROneRel.IsSubwordOf u ((Work.OROneRel.mmW z R) ^ k) ∧
      FreeGroup.map (fun p : Work.OROneRel.mmBeta z R => ((p.1.1, p.1.2) : ({x : β // x ≠ z} × ℤ))) u
        = magShiftAut z j (Work.OROneRel.magRewRel z v) ∧
      (FreeGroup.toWord u).length = Work.OROneRel.letterCountNot z v := by
  classical
  -- the subword decomposition
  obtain ⟨A, C, hAC⟩ := hsub
  -- the word of `R ^ k` is the `k`-fold concatenation of the word of `R`
  have hWcyc : FreeGroup.IsCyclicallyReduced (FreeGroup.toWord R) := hcyc
  have hVred : FreeGroup.IsReduced (FreeGroup.toWord v) := FreeGroup.isReduced_toWord
  have hflat : FreeGroup.toWord (R ^ k)
      = (List.replicate k (FreeGroup.toWord R)).flatten := by
    rw [FreeGroup.toWord_pow,
      FreeGroup.IsReduced.reduce_eq
        (FreeGroup.IsCyclicallyReduced.flatten_replicate hWcyc k).isReduced]
  have hmain : (List.replicate k (FreeGroup.toWord R)).flatten
      = A ++ FreeGroup.toWord v ++ C := by
    rw [← hflat]
    exact hAC
  -- the exponent sum of `z` in the word of `R` vanishes
  have hzW : sigmaList z (FreeGroup.toWord R) = 0 := by
    rw [sigmaList_eq_wordEps]
    exact hz
  -- the rewriting of the `k`-fold concatenation is the `k`-fold concatenation of the rewritings
  have hrep : rewriteAux z 0 ((List.replicate k (FreeGroup.toWord R)).flatten)
      = (List.replicate k (rewriteAux z 0 (FreeGroup.toWord R))).flatten :=
    rewriteAux_flatten_replicate z (FreeGroup.toWord R) hzW k
  -- and it is also the rewriting of `A`, followed by the block, followed by the rewriting of `C`
  have hsplit : rewriteAux z 0 ((List.replicate k (FreeGroup.toWord R)).flatten)
      = rewriteAux z 0 A ++ rewriteAux z (sigmaList z A) (FreeGroup.toWord v ++ C) := by
    conv_lhs => rw [hmain, List.append_assoc, rewriteAux_append, zero_add]
  have hsplit2 : rewriteAux z (sigmaList z A) (FreeGroup.toWord v ++ C)
      = rewriteAux z (sigmaList z A) (FreeGroup.toWord v)
        ++ rewriteAux z (sigmaList z A + sigmaList z (FreeGroup.toWord v)) C :=
    rewriteAux_append z (sigmaList z A) (FreeGroup.toWord v) C
  -- the element of `F (mmBeta z R)` carried by the block
  set j : ℤ := sigmaList z A with hj
  set blk : List (({x : β // x ≠ z} × ℤ) × Bool) := rewriteAux z j (FreeGroup.toWord v) with hblk
  -- every letter of the block lies in the strip `mmDecSet z R`
  have hmem_blk : ∀ p ∈ blk, p.1 ∈ mmDecSet z R := by
    intro p hp
    have h1 : p ∈ (List.replicate k (rewriteAux z 0 (FreeGroup.toWord R))).flatten := by
      rw [← hrep, hsplit, hsplit2]
      simp only [List.mem_append]
      tauto
    have h2 : p ∈ rewriteAux z 0 (FreeGroup.toWord R) := by
      rw [List.mem_flatten] at h1
      obtain ⟨l, hl, hpl⟩ := h1
      rw [List.mem_replicate] at hl
      obtain ⟨-, rfl⟩ := hl
      exact hpl
    have h3 : p ∈ mmList z R := by
      rw [show mmList z R = magRew z 0 (FreeGroup.toWord R) from rfl, magRew_zero_eq_rewrite]
      exact h2
    exact mmList_mem_decSet z R h3
  -- the rewriting of a subword has the right length
  have hlen_blk : blk.length = letterCountNot z v := by
    rw [hblk, wcp_rewriteAux_shift, List.length_map, rewriteAux_length,
      ← List.countP_eq_length_filter]
    unfold letterCountNot
    rfl
  -- the element `u` of `F (mmBeta z R)` carried by the block
  set gm : ({x : β // x ≠ z} × ℤ) × Bool → (mmBeta z R) × Bool :=
    fun p => (mmBetaOf z R p.1, p.2) with hgm
  set u : FreeGroup (mmBeta z R) := FreeGroup.mk (blk.map gm) with hu
  have hblkred : FreeGroup.IsReduced blk := by
    rw [hblk]; exact rewriteAux_isReduced z (FreeGroup.toWord v) hVred j
  have hgmred : FreeGroup.IsReduced (blk.map gm) := by
    refine (isReduced_map_subtype (f := fun p : ({x : β // x ≠ z} × ℤ) => mmBetaOf z R p)
      (g := fun q : mmBeta z R => q.1) ?_).mpr hblkred
    intro p hp
    exact mmBetaOf_val z R (hmem_blk p hp)
  have htwu : FreeGroup.toWord u = blk.map gm := by
    rw [hu, FreeGroup.toWord_mk, hgmred.reduce_eq]
  -- the projection of `u` back to the decorated alphabet is the shifted rewriting
  have hproj : FreeGroup.map (fun p : mmBeta z R => ((p.1.1, p.1.2) : ({x : β // x ≠ z} × ℤ))) u
      = FreeGroup.mk blk := by
    rw [hu, FreeGroup.map.mk]
    congr 1
    rw [hgm, List.map_map]
    refine (List.map_congr_left (g := id) ?_).trans (List.map_id blk)
    intro p hp
    obtain ⟨⟨x, m⟩, b⟩ := p
    simp only [Function.comp_apply, id_eq]
    rw [mmBetaOf_val z R (hmem_blk ((x, m), b) hp)]
  -- the word of `mmW z R` is `mmWL z R`
  have htoWord_mmW : FreeGroup.toWord (mmW z R) = mmWL z R := by
    rw [mmW, FreeGroup.toWord_mk, (mmWL_isReduced z R hcyc hz).reduce_eq]
  have hmmWL : mmWL z R = (mmList z R).map gm := rfl
  have hmmList : mmList z R = rewriteAux z 0 (FreeGroup.toWord R) := by
    rw [show mmList z R = magRew z 0 (FreeGroup.toWord R) from rfl, magRew_zero_eq_rewrite]
    rfl
  -- the word of `(mmW z R) ^ k` is the `k`-fold concatenation of `mmWL z R`
  have htoW : FreeGroup.toWord ((mmW z R) ^ k) = (List.replicate k (mmWL z R)).flatten := by
    rw [FreeGroup.toWord_pow, FreeGroup.IsReduced.reduce_eq
      (FreeGroup.IsCyclicallyReduced.flatten_replicate (mmW_isCyclicallyReduced hcyc hz) k).isReduced,
      htoWord_mmW]
  -- the block is a factor of that concatenation
  have hdec : (List.replicate k (rewriteAux z 0 (FreeGroup.toWord R))).flatten
      = rewriteAux z 0 A ++ blk ++ rewriteAux z (j + sigmaList z (FreeGroup.toWord v)) C := by
    rw [← hrep, hsplit, hsplit2, List.append_assoc]
  have hsubu : IsSubwordOf u ((mmW z R) ^ k) := by
    refine ⟨(rewriteAux z 0 A).map gm,
      (rewriteAux z (j + sigmaList z (FreeGroup.toWord v)) C).map gm, ?_⟩
    rw [htoW, hmmWL, hmmList,
      wcp_map_flatten_replicate gm (rewriteAux z 0 (FreeGroup.toWord R)) k,
      hdec, List.map_append, List.map_append, htwu]
  -- the shift produces the Magnus rewriting of `v`
  have hmagRew : magRewRel z v = FreeGroup.mk (rewriteAux z 0 (FreeGroup.toWord v)) := rfl
  refine ⟨j, u, hsubu, ?_, ?_⟩
  · rw [hproj, hblk, hmagRew, wcp_mk_rewriteAux_shift]
  · rw [htwu, List.length_map, hlen_blk]

end Work.OROneRel
