import Mathlib
import Submission.Work.OROneRel.padDefs
import Submission.Work.OROneRel.exists_complement_of_isSubwordOf_pow
import Submission.Work.OROneRel.relatorNorm_padHom

/-!
# The padded relator is longer than the padding of a short subword

If `r` is a cyclically reduced relator and `v` is a subword of `r ^ k` with `|v| < |r|`, then
padding with `padHom c` makes `v` strictly shorter than `r`:

`relatorNorm (padHom c v) < relatorNorm (padRel c r)`.

The point is that the reduced word of `padHom c u` is the concatenation of the blocks
`a z ^ (c a) a` (this is `toWord_padHom`), so its length is the sum of the block lengths
`2 + |c a|`; and a window of length `< |r|` of the periodic word `r r r …` contains no more
occurrences of any letter than one period `r` does.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ### Transferring between `DecidableEq` instances

`FreeGroup.toWord` takes the `DecidableEq α` instance as an argument, while the noncomputable
definitions of this development (`IsSubwordOf`, `IsCyclicallyReducedRelator`, `relatorNorm`, …)
elaborate with the `Classical` instance.  As `Decidable _` is a subsingleton, the instances --
and hence `toWord` itself -- do not depend on the choice. -/

/-- Any two `DecidableEq` instances agree (`Decidable _` is a subsingleton). -/
theorem decEq_eq (i j : DecidableEq α) : i = j :=
  Subsingleton.elim _ _

theorem toWord_eq_of_decEq (i j : DecidableEq α) (x : FreeGroup α) :
    @FreeGroup.toWord α i x = @FreeGroup.toWord α j x := by rw [decEq_eq i j]

/-- `wordOf` is the reduced word at any chosen `DecidableEq` instance. -/
theorem wordOf_eq_toWord (d : DecidableEq α) (x : FreeGroup α) :
    wordOf x = @FreeGroup.toWord α d x :=
  toWord_eq_of_decEq (Classical.decEq α) d x

/-- `relatorNorm` is the length of the reduced word, at any chosen instance. -/
theorem relatorNorm_eq_length (d : DecidableEq α) (x : FreeGroup α) :
    relatorNorm x = (@FreeGroup.toWord α d x).length := by
  rw [show relatorNorm x = (@FreeGroup.toWord α (Classical.decEq α) x).length from rfl,
    toWord_eq_of_decEq (Classical.decEq α) d x]

theorem isCyclicallyReducedRelator_toWord (d : DecidableEq α) (r : FreeGroup α)
    (h : IsCyclicallyReducedRelator r) :
    FreeGroup.IsCyclicallyReduced (@FreeGroup.toWord α d r) := by
  rw [show @FreeGroup.toWord α d r = wordOf r from toWord_eq_of_decEq d (Classical.decEq α) r]
  exact h

/-! ### Windows of a cyclic word

A window of the periodic word `W W W …` contains no more occurrences of any element than one
period `W` does: it is a sublist of a rotation of `W`, and a rotation is a permutation of `W`. -/

open List in
theorem sublist_sum_le {l₁ l₂ : List ℕ} (h : l₁ <+ l₂) : l₁.sum ≤ l₂.sum := by
  induction h with
  | slnil => simp
  | cons a _ ih => simp only [List.sum_cons]; omega
  | cons_cons a _ ih => simp only [List.sum_cons]; omega

theorem sum_take_rotate_le {β : Type*} (W : List β) (g : β → ℕ) (i m : ℕ) :
    (((W.rotate i).take m).map g).sum ≤ (W.map g).sum := by
  calc (((W.rotate i).take m).map g).sum
      = (((W.rotate i).map g).take m).sum := congrArg List.sum List.map_take
    _ ≤ ((W.rotate i).map g).sum := sublist_sum_le (List.take_sublist m _)
    _ = (W.map g).sum := (List.rotate_perm W i).map g |>.sum_eq

/-! ### The sum bound for subwords of powers -/

/-- The sum bound at a chosen `DecidableEq` instance: the reduced word of a short subword of a
power of a cyclically reduced relator is an initial segment of a rotation of the reduced word of the
relator, whence the bound on weightings. -/
theorem map_sum_le_of_isSubwordOf_pow_aux {α : Type u} [d : DecidableEq α] (r v : FreeGroup α)
    (k : ℕ) (g : α → ℕ)
    (hcyc : IsCyclicallyReducedRelator r)
    (hsub : IsSubwordOf v (r ^ k))
    (hlen : (@FreeGroup.toWord α d v).length < (@FreeGroup.toWord α d r).length) :
    ((@FreeGroup.toWord α d v).map (fun p : α × Bool => g p.1)).sum ≤
      ((@FreeGroup.toWord α d r).map (fun p : α × Bool => g p.1)).sum := by
  obtain ⟨L₁, L₂, hL⟩ := hsub
  have hL' : @FreeGroup.toWord α d (r ^ k) = L₁ ++ @FreeGroup.toWord α d v ++ L₂ := by
    rw [toWord_eq_of_decEq d (Classical.decEq α) (r ^ k),
      toWord_eq_of_decEq d (Classical.decEq α) v]
    exact hL
  have hcyc' : FreeGroup.IsCyclicallyReduced (@FreeGroup.toWord α d r) :=
    isCyclicallyReducedRelator_toWord d r hcyc
  have hflat : @FreeGroup.toWord α d (r ^ k) =
      (List.replicate k (@FreeGroup.toWord α d r)).flatten := by
    rw [FreeGroup.toWord_pow]
    exact (FreeGroup.isReduced_iff_reduce_eq).mp (hcyc'.flatten_replicate k).isReduced
  have hmain : (List.replicate k (@FreeGroup.toWord α d r)).flatten =
      L₁ ++ @FreeGroup.toWord α d v ++ L₂ := by rw [← hflat]; exact hL'
  have htake := eq_rotate_take_of_flatten_replicate_eq hmain (le_of_lt hlen)
  calc ((@FreeGroup.toWord α d v).map (fun p : α × Bool => g p.1)).sum
      = ((((@FreeGroup.toWord α d r).rotate L₁.length).take
            (@FreeGroup.toWord α d v).length).map (fun p : α × Bool => g p.1)).sum := by
          conv_lhs => rw [htake]
    _ ≤ ((@FreeGroup.toWord α d r).map (fun p : α × Bool => g p.1)).sum :=
        sum_take_rotate_le _ _ L₁.length (@FreeGroup.toWord α d v).length

/-- **A subword of a power of a cyclically reduced relator is no heavier than the relator.**
If `v` is a subword of `r ^ k` with `|v| < |r|`, then any letter-weighting of `v` is bounded by the
weighting of `r`. -/
theorem map_sum_le_of_isSubwordOf_pow (r v : FreeGroup α) (k : ℕ) (g : α → ℕ)
    (hcyc : IsCyclicallyReducedRelator r)
    (hsub : IsSubwordOf v (r ^ k))
    (hlen : relatorNorm v < relatorNorm r) :
    ((wordOf v).map (fun p : α × Bool => g p.1)).sum ≤
      ((wordOf r).map (fun p : α × Bool => g p.1)).sum := by
  have h := map_sum_le_of_isSubwordOf_pow_aux (d := Classical.decEq α) r v k g hcyc hsub ?_
  · rw [wordOf_eq_toWord (Classical.decEq α) v, wordOf_eq_toWord (Classical.decEq α) r]
    exact h
  · rw [← relatorNorm_eq_length (Classical.decEq α) v,
      ← relatorNorm_eq_length (Classical.decEq α) r]
    exact hlen

/-! ### The length of the padding

The reduced length of `padHom c u` is the sum of the block lengths `2 + |c a|` over the letters of
the reduced word of `u`; this is `relatorNorm_padHom`. -/

/-- The sum defining the padded length splits into twice the number of letters plus the weights. -/
theorem sum_map_two_add (L : List (α × Bool)) (h : α × Bool → ℕ) :
    (L.map (fun p : α × Bool => 2 + h p)).sum = 2 * L.length + (L.map h).sum := by
  induction L with
  | nil => simp
  | cons p L ih =>
    rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons, List.length_cons]
    ring

theorem pad_length_lt {α : Type u} (r v : FreeGroup α) (c : α → ℤ) (k : ℕ)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator r)
    (hsub : Work.OROneRel.IsSubwordOf v (r ^ k))
    (hlen : Work.OROneRel.relatorNorm v < Work.OROneRel.relatorNorm r) :
    Work.OROneRel.relatorNorm (Work.OROneRel.padHom c v) <
      Work.OROneRel.relatorNorm (Work.OROneRel.padRel c r) := by
  classical
  have hV : relatorNorm v = (wordOf v).length := relatorNorm_eq_length (Classical.decEq α) v
  have hR : relatorNorm r = (wordOf r).length := relatorNorm_eq_length (Classical.decEq α) r
  have hlen' : (wordOf v).length < (wordOf r).length := by rw [← hV, ← hR]; exact hlen
  have hsum := map_sum_le_of_isSubwordOf_pow r v k (fun a => (c a).natAbs) hcyc hsub hlen
  rw [padRel, relatorNorm_padHom, relatorNorm_padHom,
    sum_map_two_add (wordOf v) (fun p : α × Bool => (c p.1).natAbs),
    sum_map_two_add (wordOf r) (fun p : α × Bool => (c p.1).natAbs)]
  omega

end Work.OROneRel
