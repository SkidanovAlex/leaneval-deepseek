import Mathlib

namespace Work.Drive.PushDisc

/-- Swapping the last two blocks of an independent `Fin.append`-built tuple preserves
linear independence: if `Fin.append (Fin.append a b) c` is independent then so is
`Fin.append (Fin.append a c) b`. (Both tuples are the same family of vectors, read in a different
order, so this is a reindexing statement.) -/
theorem tupleLiSwap {F : Type*} [AddCommGroup F] [Module ℝ F] {r k : ℕ}
    (a : Fin r → F) (b : Fin k → F) (c : Fin k → F)
    (h : LinearIndependent ℝ (Fin.append (Fin.append a b) c)) :
    LinearIndependent ℝ (Fin.append (Fin.append a c) b) := by
  -- The common index set of the two tuples is `Fin ((r + k) + k)`; identify it with
  -- `((Fin r ⊕ Fin k) ⊕ Fin k)` — the `a`-, `b`- and `c`-blocks made explicit.
  let P : ((Fin r ⊕ Fin k) ⊕ Fin k) ≃ Fin ((r + k) + k) :=
    (Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin k))).trans finSumFinEquiv
  -- The involution that swaps the last two blocks (`b` and `c`), leaving the `a`-block alone.
  let S : ((Fin r ⊕ Fin k) ⊕ Fin k) ≃ ((Fin r ⊕ Fin k) ⊕ Fin k) :=
    (Equiv.sumAssoc (Fin r) (Fin k) (Fin k)).trans
      ((Equiv.sumCongr (Equiv.refl (Fin r)) (Equiv.sumComm (Fin k) (Fin k))).trans
        (Equiv.sumAssoc (Fin r) (Fin k) (Fin k)).symm)
  -- Pointwise, the second tuple is the first one precomposed with the block swap.
  have key : (Fin.append (Fin.append a c) b) ∘ ⇑P
      = (Fin.append (Fin.append a b) c) ∘ (⇑P ∘ ⇑S) := by
    funext x
    rcases x with (y | j)
    · rcases y with (i | j') <;> simp [P, S]
    · simp [P, S]
  have h1 : LinearIndependent ℝ ((Fin.append (Fin.append a b) c) ∘ (⇑P ∘ ⇑S)) :=
    h.comp (⇑P ∘ ⇑S) (P.injective.comp S.injective)
  have hmid : LinearIndependent ℝ ((Fin.append (Fin.append a c) b) ∘ ⇑P) := by
    rw [key]; exact h1
  have h2 : LinearIndependent ℝ (((Fin.append (Fin.append a c) b) ∘ ⇑P) ∘ ⇑P.symm) :=
    hmid.comp ⇑P.symm P.symm.injective
  have he : ((Fin.append (Fin.append a c) b) ∘ ⇑P) ∘ ⇑P.symm
      = Fin.append (Fin.append a c) b := by
    ext x; simp
  rwa [he] at h2

end Work.Drive.PushDisc
