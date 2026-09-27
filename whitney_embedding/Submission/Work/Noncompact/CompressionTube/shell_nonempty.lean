import Mathlib

/-!
# Non-degeneracy of a shell of a nested exhaustion

The level step `exists_level_arc_data` needs `(interior (K (n+1)) \ K n).Nonempty` (in the
application `n = j+2`): the level-`(j+1)` arcs must *end* in `interior (K (j+3)) \ K (j+2)`, and the
review of that lemma produced counterexamples (`M = S²`, `K i = ∅` up to some index and `M`
afterwards, `L = Lprev = M`, `U = ∅`) in which that shell is empty.

The correct hypothesis is `(K n).Nonempty` (not merely "j large"): it gives
`interior (K (n+1)) ⊇ K n ≠ ∅`, and it is automatic at every level that actually carries a strand
(`n = j+2 ≥ levK b` for an active or newly active `b`).  For `K n = ∅` with the exhaustion still
trivial at that height, the shell *is* empty, so the hypothesis cannot be dropped.

Proof: if `interior (K (n+1)) \ K n = ∅` then `interior (K (n+1)) ⊆ K n`, and with
`K n ⊆ interior (K (n+1))` this makes `K n` clopen (open as an interior, closed as a compact set in a
T2 space); a connected space has no non-trivial clopen set, so `K n = ∅` (excluded by the
hypothesis) or `K n = univ`, which makes `M` compact (excluded).
-/

set_option linter.unusedSectionVars false
set_option autoImplicit false

/-- **A shell with a non-empty inner level is non-empty.** -/
theorem exists_shell_nonempty {M : Type*} [TopologicalSpace M] [T2Space M] [ConnectedSpace M]
    (hM : ¬ CompactSpace M) {K : ℕ → Set M} (hKc : ∀ i, IsCompact (K i))
    (hKsub : ∀ i, K i ⊆ interior (K (i+1))) (n : ℕ) (hne : (K n).Nonempty) :
    (interior (K (n+1)) \ K n).Nonempty := by
  by_contra h
  have hsub : interior (K (n+1)) ⊆ K n := by
    intro x hx
    by_contra hxK
    exact h ⟨x, hx, hxK⟩
  have hEq : interior (K (n+1)) = K n := le_antisymm hsub (hKsub n)
  have hcl : IsClopen (K n) := ⟨(hKc n).isClosed, hEq ▸ isOpen_interior⟩
  rcases isClopen_iff.mp hcl with hE | hU
  · exact hne.ne_empty hE
  · exact hM ⟨hU ▸ hKc n⟩
