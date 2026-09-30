import Mathlib
import Submission.Work.Certificates.Sparse

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Certificates.SVec

/-- Pointwise unfolding of `toFun` on a cons: the head contributes `p.2` exactly at the index
`p.1`, and the tail contributes its own value. -/
private theorem toFun_cons_apply {n : ℕ} (p : Fin n × ℤ) (l : SVec n) (i : Fin n) :
    toFun (p :: l) i = (if p.1 = i then p.2 else 0) + toFun l i := by
  simp [toFun, List.map_cons, List.sum_cons]

/-- General form of the certificate conversion lemma: for a list `l` of *pairwise distinct*
indices, the sparse vector obtained by keeping only the nonzero entries `(i, g i)` represents
`g` on the indices occurring in `l` and `0` elsewhere.  The distinctness hypothesis is what
rules out an index occurring twice and its coefficient being counted twice. -/
private theorem toFun_filterMap_eq_ite {n : ℕ} (l : List (Fin n)) :
    l.Nodup → ∀ (g : Fin n → ℤ) (i : Fin n),
      toFun (l.filterMap (fun j => if g j = 0 then none else some (j, g j))) i
        = if i ∈ l then g i else 0 := by
  induction l with
  | nil =>
    intro _ g i
    simp [toFun]
  | cons a l ih =>
    intro hl g i
    rw [List.nodup_cons] at hl
    obtain ⟨ha, hl⟩ := hl
    have hih := ih hl g i
    rw [List.filterMap_cons]
    by_cases hg : g a = 0
    · rw [ite_eq_left hg, hih]
      by_cases hia : i = a
      · subst hia; simp [ha, hg]
      · simp [hia]
    · rw [ite_eq_right hg, toFun_cons_apply, hih]
      by_cases hia : i = a
      · subst hia; simp [ha]
      · have hai : a ≠ i := fun h => hia h.symm
        simp [hia, hai]

/-- The sparse vector whose entries are the nonzero coordinates of `g`, listed in the order of
`Fin n`, represents exactly `g`.  Since `List.finRange n` has no repeated index, every
coordinate of `g` contributes at most once, and the coordinates dropped by `filterMap` are
exactly the zeros. -/
theorem toFun_filterMap_finRange (n : ℕ) (g : Fin n → ℤ) :
    toFun ((List.finRange n).filterMap (fun i => if g i = 0 then none else some (i, g i))) = g := by
  funext i
  rw [toFun_filterMap_eq_ite (List.finRange n) (List.nodup_finRange n) g i]
  simp

end Work.Certificates.SVec
