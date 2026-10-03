import Mathlib
import Submission.Work.OROneRel.padDefs
import Submission.Work.OROneRel.weinbaumDefs
import Submission.Work.OROneRel.exists_complement_of_isSubwordOf_pow

/-!
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The number of occurrences of a letter in a short subword of a power of a cyclically reduced
relator

Let `r` be a cyclically reduced relator, i.e. the reduced word `W = r.toWord` is cyclically reduced.
Then the reduced word of `r ^ k` is the concatenation `W ++ W ++ ⋯ ++ W` of `k` copies of `W`
(Mathlib's `FreeGroup.IsCyclicallyReduced.flatten_replicate`).  Let `v` be a subword of `r ^ k`
whose reduced word `V` is no longer than `W`.  The window `V` of the periodic word `W^∞` then meets
each residue class modulo `|W|` at most once, so it contains no more occurrences of a given letter
`a` than a full period `W` does:

`#{letters (a, ·) in V} ≤ #{letters (a, ·) in W}`.

Formally, `V` is an initial segment of a rotation of `W` (the existing lemma
`eq_rotate_take_of_flatten_replicate_eq`), and counting in `V` is bounded by counting in that
rotation, which by `List.rotate_perm` agrees with counting in `W`.

The only subtlety is a formal one: `FreeGroup.toWord` takes the `DecidableEq α` instance as an
argument, while the noncomputable definitions of this development (`IsSubwordOf`,
`IsCyclicallyReducedRelator`, …) unfold with the `Classical` instance.  The lemma
`toWord_eq_of_decEq` shows that `toWord` is independent of the instance, so the two may be used
interchangeably.
-/

namespace Work.OROneRel

universe u

/-! ## `FreeGroup.toWord` does not depend on the `DecidableEq` instance -/

/-- Any two `DecidableEq` instances on a type are equal: `Decidable _` is a subsingleton, so the
functions `(a b : α) → Decidable (a = b)` agree by functional extensionality. -/
theorem decEq_eq {α : Type u} (i j : DecidableEq α) : i = j :=
  funext fun _ => funext fun _ => Subsingleton.elim _ _

/-- `FreeGroup.toWord` does not depend on the `DecidableEq α` instance. -/
theorem toWord_eq_of_decEq {α : Type u} (i j : DecidableEq α) (x : FreeGroup α) :
    @FreeGroup.toWord α i x = @FreeGroup.toWord α j x := by
  rw [decEq_eq i j]

/-! ## The counting bound -/

/-- **The counting bound.**  If `r` is a cyclically reduced relator, `v` is a subword of `r ^ k`
and the reduced word of `v` is no longer than that of `r`, then any given letter occurs in `v` no
more often than in `r`.  The predicate `q` on letters is arbitrary.

The statement is phrased with the `DecidableEq α` instance named `d`, so that the same instance
can be used both inside the noncomputable definitions (`IsSubwordOf`, `IsCyclicallyReducedRelator`,
…) and in the conclusion; `toWord_eq_of_decEq` converts between that instance and the `Classical`
one used by those definitions. -/
theorem occ_le_of_isSubwordOf_pow_aux {α : Type u} [d : DecidableEq α] (r v : FreeGroup α) (k : ℕ)
    (q : (α × Bool) → Bool) (hcyc : IsCyclicallyReducedRelator r)
    (hsub : IsSubwordOf v (r ^ k))
    (hlen : (@FreeGroup.toWord α d v).length ≤ (@FreeGroup.toWord α d r).length) :
    (@FreeGroup.toWord α d v).countP q ≤ (@FreeGroup.toWord α d r).countP q := by
  obtain ⟨L₁, L₂, hL⟩ := hsub
  -- `hL` is the decomposition of the reduced word of `r ^ k` at the `Classical` instance;
  -- convert it to the current instance `d`
  have hL' : @FreeGroup.toWord α d (r ^ k) = L₁ ++ @FreeGroup.toWord α d v ++ L₂ := by
    rw [toWord_eq_of_decEq d (Classical.decEq α) (r ^ k),
      toWord_eq_of_decEq d (Classical.decEq α) v]
    exact hL
  -- cyclic reducedness, likewise transported to `d`
  have hcycC : FreeGroup.IsCyclicallyReduced (@FreeGroup.toWord α (Classical.decEq α) r) := hcyc
  have hcyc' : FreeGroup.IsCyclicallyReduced (@FreeGroup.toWord α d r) := by
    rw [toWord_eq_of_decEq d (Classical.decEq α) r]
    exact hcycC
  -- the reduced word of `r ^ k` is the concatenation of `k` copies of that of `r`
  have hflat : @FreeGroup.toWord α d (r ^ k) =
      (List.replicate k (@FreeGroup.toWord α d r)).flatten := by
    rw [FreeGroup.toWord_pow]
    exact (FreeGroup.isReduced_iff_reduce_eq).mp (hcyc'.flatten_replicate k).isReduced
  have hmain : (List.replicate k (@FreeGroup.toWord α d r)).flatten =
      L₁ ++ @FreeGroup.toWord α d v ++ L₂ := by
    rw [← hflat]
    exact hL'
  -- hence the reduced word of `v` is an initial segment of the rotation of `W` at `L₁.length`
  have htake : @FreeGroup.toWord α d v =
      ((@FreeGroup.toWord α d r).rotate L₁.length).take
        (@FreeGroup.toWord α d v).length :=
    eq_rotate_take_of_flatten_replicate_eq hmain hlen
  -- counting in a prefix of a rotation of `W` is bounded by counting in `W`
  calc (@FreeGroup.toWord α d v).countP q
      = (((@FreeGroup.toWord α d r).rotate L₁.length).take
          (@FreeGroup.toWord α d v).length).countP q := by
        conv_lhs => rw [htake]
    _ ≤ ((@FreeGroup.toWord α d r).rotate L₁.length).countP q :=
        List.Sublist.countP_le (List.take_sublist _ _)
    _ = (@FreeGroup.toWord α d r).countP q :=
        List.Perm.countP_eq q (List.rotate_perm _ _)

/-! ## The requested statement -/

theorem occ_le_of_isSubwordOf_pow {α : Type u} [DecidableEq α] (r v : FreeGroup α) (k : ℕ) (a : α)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator r)
    (hsub : Work.OROneRel.IsSubwordOf v (r ^ k)) (hlen : (v.toWord).length ≤ (r.toWord).length) :
    (v.toWord.countP (fun p : α × Bool => p.1 = a)) ≤
      (r.toWord.countP (fun p : α × Bool => p.1 = a)) :=
  occ_le_of_isSubwordOf_pow_aux r v k (fun p : α × Bool => p.1 = a) hcyc hsub hlen

end Work.OROneRel
