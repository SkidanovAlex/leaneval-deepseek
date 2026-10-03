import Mathlib
import Submission.Work.OROneRel.Basic

/-!
# Taking roots preserves cyclic reducedness

A relator whose *reduced word* is cyclically reduced ("no cancellation at the wrap-around") remains
so after taking roots: if `u ^ l` is cyclically reduced for some `l ≥ 1`, then `u` is cyclically
reduced.

The mathematics is standard: any word `L` decomposes as `L = c ++ v ++ invRev c`, where `v` is its
cyclic reduction and `c` the conjugator (`FreeGroup.reduceCyclically`), a list equality valid for
every `L` (`conj_conjugator_reduceCyclically`).  For `l ≥ 1` the reduced word of `u ^ l` is exactly

`c ++ (replicate l v).flatten ++ invRev c`

(`reduce_flatten_replicate_succ`).  If `c` were nonempty, then in the *doubling*
`(u ^ l).toWord ++ (u ^ l).toWord` the middle block `invRev c ++ c` would be a contiguous subword,
hence reduced; but `reduce (invRev c ++ c) = []` for every `c` (`reduce_invRev_left_cancel`), so
`invRev c ++ c = []`, forcing `c = []`.  Thus `u.toWord = v` is the cyclic reduction of `u.toWord`,
which is cyclically reduced by construction.

The only characterization used is `IsCyclicallyReduced L ↔ IsReduced (L ++ L)`, immediate from
`List.isChain_append`.
-/

namespace Work.OROneRel

universe u

/-- A word is cyclically reduced exactly when its "doubling" `L ++ L` is reduced: by
`List.isChain_append` the chain condition on `L ++ L` is the conjunction of the chain conditions on
the two copies together with the wrap-around condition, which is precisely the second conjunct in
the definition of `FreeGroup.IsCyclicallyReduced`. -/
theorem isCyclicallyReduced_iff_isReduced_append_self {α : Type u} {L : List (α × Bool)} :
    FreeGroup.IsCyclicallyReduced L ↔ FreeGroup.IsReduced (L ++ L) := by
  simp only [FreeGroup.IsCyclicallyReduced, FreeGroup.IsReduced]
  rw [List.isChain_append]
  tauto

/-- **Roots of cyclically reduced words are cyclically reduced.**  If a positive concatenation of
copies of a reduced word `L` reduces to a cyclically reduced word, then `L` itself is cyclically
reduced. -/
theorem isCyclicallyReduced_of_reduce_replicate_flatten {α : Type u} [DecidableEq α]
    {L : List (α × Bool)} {l : ℕ} (hL : FreeGroup.IsReduced L) (hl : 1 ≤ l)
    (h : FreeGroup.IsCyclicallyReduced (FreeGroup.reduce (List.replicate l L).flatten)) :
    FreeGroup.IsCyclicallyReduced L := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : l ≠ 0)
  have hW := FreeGroup.reduceCyclically.reduce_flatten_replicate_succ hL n
  rw [hW] at h
  have hLL : FreeGroup.IsReduced
      ((FreeGroup.reduceCyclically.conjugator L ++
          (List.replicate (n + 1) (FreeGroup.reduceCyclically L)).flatten ++
          FreeGroup.invRev (FreeGroup.reduceCyclically.conjugator L))
        ++ (FreeGroup.reduceCyclically.conjugator L ++
          (List.replicate (n + 1) (FreeGroup.reduceCyclically L)).flatten ++
          FreeGroup.invRev (FreeGroup.reduceCyclically.conjugator L))) :=
    isCyclicallyReduced_iff_isReduced_append_self.mp h
  have hinf : FreeGroup.IsReduced
      (FreeGroup.invRev (FreeGroup.reduceCyclically.conjugator L) ++
        FreeGroup.reduceCyclically.conjugator L) :=
    hLL.infix ⟨FreeGroup.reduceCyclically.conjugator L ++
        (List.replicate (n + 1) (FreeGroup.reduceCyclically L)).flatten,
      (List.replicate (n + 1) (FreeGroup.reduceCyclically L)).flatten ++
        FreeGroup.invRev (FreeGroup.reduceCyclically.conjugator L),
      by simp [List.append_assoc]⟩
  have hempty : FreeGroup.invRev (FreeGroup.reduceCyclically.conjugator L) ++
      FreeGroup.reduceCyclically.conjugator L = [] := by
    rw [← FreeGroup.IsReduced.reduce_eq hinf]
    exact FreeGroup.reduce_invRev_left_cancel
  have hc : FreeGroup.reduceCyclically.conjugator L = [] :=
    (List.append_eq_nil_iff.mp hempty).2
  have hv : FreeGroup.reduceCyclically L = L := by
    have hd := FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically L
    rw [hc] at hd
    simpa using hd
  rw [← hv]
  exact FreeGroup.reduceCyclically.isCyclicallyReduced hL

theorem isCyclicallyReducedRelator_of_pow {β : Type u} (u : FreeGroup β) {l : ℕ} (hl : 1 ≤ l)
    (h : Work.OROneRel.IsCyclicallyReducedRelator (u ^ l)) :
    Work.OROneRel.IsCyclicallyReducedRelator u := by
  classical
  unfold Work.OROneRel.IsCyclicallyReducedRelator at *
  rw [FreeGroup.toWord_pow] at h
  exact isCyclicallyReduced_of_reduce_replicate_flatten (FreeGroup.isReduced_toWord) hl h

end Work.OROneRel
