import Mathlib
import Submission.Work.OROneRel.HNNCoreBounds
import Submission.Work.OROneRel.finite_relatorLetters

universe u

namespace Work.OROneRel

/-- The reduced word of an element of a free group does not depend on which `DecidableEq`
instance on the generators is used. -/
theorem toWord_inst_irrel {α : Type u} (i1 i2 : DecidableEq α) :
    (@FreeGroup.toWord α i1 : FreeGroup α → List (α × Bool)) = @FreeGroup.toWord α i2 := by
  rw [Subsingleton.elim i1 i2]

/-- **The extremal `x`-decorations of the Magnus rewriting.**  If the reduced word of `r` begins
with the letter `x ≠ t`, then the set of integers `k` with `(⟨x,htx⟩,k) ∈ relatorLetters
(magRewRel t r)` is finite and nonempty (it contains `0` by `rewrite_zero_index`), so it has a least
element `i` and a greatest element `j`, and `i ≤ 0 ≤ j`. -/
private theorem decoration_bounds_of_head_aux {α : Type u} [DecidableEq α] (r : FreeGroup α)
    (t x : α) (htx : x ≠ t)
    (hhead : r.toWord.head? = some (x, true) ∨ r.toWord.head? = some (x, false)) :
    ∃ i j : ℤ,
      (⟨x, htx⟩, i) ∈ relatorLetters (magRewRel t r) ∧
      (⟨x, htx⟩, j) ∈ relatorLetters (magRewRel t r) ∧
      (∀ k : ℤ, (⟨x, htx⟩, k) ∈ relatorLetters (magRewRel t r) → i ≤ k ∧ k ≤ j) ∧
      i ≤ 0 ∧ 0 ≤ j := by
  classical
  letI : DecidableEq α := fun a b => Classical.propDecidable (a = b)
  letI : DecidableEq ({a : α // a ≠ t} × ℤ) := fun a b => Classical.propDecidable (a = b)
  have hhead' : (@FreeGroup.toWord α (fun a b => Classical.propDecidable (a = b)) r).head? =
        some (x, true) ∨
      (@FreeGroup.toWord α (fun a b => Classical.propDecidable (a = b)) r).head? =
        some (x, false) := by
    have h := hhead
    rw [toWord_inst_irrel] at h
    exact h
  have hredr : FreeGroup.IsReduced
      (@FreeGroup.toWord α (fun a b => Classical.propDecidable (a = b)) r) :=
    FreeGroup.isReduced_toWord
  have hredw : FreeGroup.IsReduced
      (rewrite t (@FreeGroup.toWord α (fun a b => Classical.propDecidable (a = b)) r)) :=
    rewrite_isReduced t hredr
  have htoWord : (magRewRel t r).toWord =
      rewrite t (@FreeGroup.toWord α (fun a b => Classical.propDecidable (a = b)) r) := by
    rw [magRewRel, FreeGroup.toWord_mk, hredw.reduce_eq]
  have hmem : ∀ p : {a : α // a ≠ t} × ℤ,
      p ∈ relatorLetters (magRewRel t r) ↔ ∃ c : Bool, (p, c) ∈
        rewrite t (@FreeGroup.toWord α (fun a b => Classical.propDecidable (a = b)) r) := by
    intro p
    show (∃ c : Bool, (p, c) ∈ (magRewRel t r).toWord) ↔ _
    rw [htoWord]
  have h0 : (⟨x, htx⟩, (0 : ℤ)) ∈ relatorLetters (magRewRel t r) := by
    rcases hhead' with h | h
    · obtain ⟨p, hp1, hp2, hpmem⟩ := rewrite_zero_index t x htx true h
      refine (hmem ((⟨x, htx⟩, (0 : ℤ)) : {a : α // a ≠ t} × ℤ)).mpr ⟨p.2, ?_⟩
      have hpeq : p = ((⟨x, htx⟩, (0 : ℤ)), p.2) := by
        refine Prod.ext ?_ rfl
        exact Prod.ext hp1 hp2
      rwa [hpeq] at hpmem
    · obtain ⟨p, hp1, hp2, hpmem⟩ := rewrite_zero_index t x htx false h
      refine (hmem ((⟨x, htx⟩, (0 : ℤ)) : {a : α // a ≠ t} × ℤ)).mpr ⟨p.2, ?_⟩
      have hpeq : p = ((⟨x, htx⟩, (0 : ℤ)), p.2) := by
        refine Prod.ext ?_ rfl
        exact Prod.ext hp1 hp2
      rwa [hpeq] at hpmem
  have hfin : ({k : ℤ | (⟨x, htx⟩, k) ∈ relatorLetters (magRewRel t r)}).Finite := by
    apply Set.Finite.subset ((finite_relatorLetters (magRewRel t r)).image Prod.snd)
    intro k hk
    exact ⟨(⟨x, htx⟩, k), hk, rfl⟩
  have hs0 : (0 : ℤ) ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset]; exact h0
  have hne : hfin.toFinset.Nonempty := ⟨0, hs0⟩
  refine ⟨hfin.toFinset.min' hne, hfin.toFinset.max' hne, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Set.Finite.mem_toFinset hfin).mp (Finset.min'_mem _ hne)
  · exact (Set.Finite.mem_toFinset hfin).mp (Finset.max'_mem _ hne)
  · intro k hk
    exact ⟨Finset.min'_le _ _ ((Set.Finite.mem_toFinset hfin).mpr hk),
      Finset.le_max' _ _ ((Set.Finite.mem_toFinset hfin).mpr hk)⟩
  · exact Finset.min'_le _ _ hs0
  · exact Finset.le_max' _ _ hs0

/-- **The HNN step of the Freiheitssatz, extremal form.**  For a cyclically reduced relator `r` with
`σ_t r = 1` whose reduced word begins with the letter `x ≠ t`, the extremal `x`-decorations `i ≤ 0 ≤
j` of the Magnus rewriting `magRewRel t r` exist and carry an HNN decomposition of `⟨α | r⟩` with
stable letter `t` over the one-relator group `⟨(α \ {t}) × ℤ | magRewRel t r⟩`. -/
theorem hnn_step_core_exists {α : Type u} [DecidableEq α] (r : FreeGroup α) (t x : α)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator r)
    (ht : t ∈ Work.OROneRel.relatorLetters r) (hx : x ∈ Work.OROneRel.relatorLetters r)
    (htx : x ≠ t) (ht0 : Work.OROneRel.sigma t r = 1)
    (hhead : r.toWord.head? = some (x, true) ∨ r.toWord.head? = some (x, false))
    (IH : ∀ (β : Type u) (s : FreeGroup β),
      Work.OROneRel.relatorNorm s < Work.OROneRel.relatorNorm (Work.OROneRel.magRewRel t r) + 1 →
      Work.OROneRel.FreiheitssatzAt s) :
    ∃ i j : ℤ,
      (⟨x, htx⟩, i) ∈ Work.OROneRel.relatorLetters (Work.OROneRel.magRewRel t r) ∧
      (⟨x, htx⟩, j) ∈ Work.OROneRel.relatorLetters (Work.OROneRel.magRewRel t r) ∧
      (∀ k : ℤ, (⟨x, htx⟩, k) ∈ Work.OROneRel.relatorLetters (Work.OROneRel.magRewRel t r) →
        i ≤ k ∧ k ≤ j) ∧
      i ≤ 0 ∧ 0 ≤ j ∧ Nonempty (Work.OROneRel.HNNStepCore r t x i j) := by
  obtain ⟨i, j, hi, hj, hb, hi0, h0j⟩ := decoration_bounds_of_head_aux r t x htx hhead
  refine ⟨i, j, hi, hj, hb, hi0, h0j, ?_⟩
  exact core_of_bounds r t x hcyc htx ht0 i j hi hj hb hi0 h0j
    (IH ({a : α // a ≠ t} × ℤ) (magRewRel t r) (Nat.lt_succ_self _))

end Work.OROneRel
