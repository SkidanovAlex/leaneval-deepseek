import Mathlib
import Submission.Work.WilVP.Defs

set_option autoImplicit false

namespace Work.WilVP

/-- The reindexing `f : Fin (k+2) → Fin (k+1) ⊕ Fin 1` sending the two "variable" coordinates of
the context `Fin (k+2)` (`0 = x`, `1 = y`) to the `Fin 1`-block (`y`) and the first coordinate of
the `Fin (k+1)`-block (`x`), and the parameter coordinates `i+2` to the remaining coordinates
`i+1` of the `Fin (k+1)`-block.

Concretely `f 0 = Sum.inl 0`, `f 1 = Sum.inr 0`, `f (i+2) = Sum.inl (i+1)`. -/
def projIdx (k : ℕ) : Fin (k + 2) → Fin (k + 1) ⊕ Fin 1 :=
  Fin.cases (Sum.inl (0 : Fin (k + 1)))
    (Fin.cases (Sum.inr (0 : Fin 1)) (fun i : Fin k => Sum.inl i.succ))

/-- Reindexing a `(Fin (k+1) ⊕ Fin 1)`-tuple along `projIdx k` turns the sum-decomposition
`v ⊕ u` (`v` on the `Fin (k+1)` block, `u` on the `Fin 1` block) into the `cons`-decomposition
`Fin.cons (v 0) (Fin.cons (u 0) (Fin.tail v))`, i.e. `(x, y, c)`. -/
lemma comp_projIdx {k : ℕ} (v : Fin (k + 1) → ℝ) (u : Fin 1 → ℝ) :
    (Sum.elim v u) ∘ projIdx k = Fin.cons (v 0) (Fin.cons (u 0) (Fin.tail v)) := by
  rw [← Fin.cons_self_tail ((Sum.elim v u) ∘ projIdx k)]
  have h0 : ((Sum.elim v u) ∘ projIdx k) 0 = v 0 := rfl
  have htail : Fin.tail ((Sum.elim v u) ∘ projIdx k) = Fin.cons (u 0) (Fin.tail v) := by
    rw [← Fin.cons_self_tail (Fin.tail ((Sum.elim v u) ∘ projIdx k))]
    have h1 : Fin.tail ((Sum.elim v u) ∘ projIdx k) 0 = u 0 := by
      show (Sum.elim v u) (projIdx k (Fin.succ (0 : Fin (k + 1)))) = u 0
      rw [projIdx, Fin.cases_succ, Fin.cases_zero]; rfl
    have h2 : Fin.tail (Fin.tail ((Sum.elim v u) ∘ projIdx k)) = Fin.tail v := by
      funext m
      show (Sum.elim v u) (projIdx k (Fin.succ (Fin.succ m))) = v m.succ
      rw [projIdx, Fin.cases_succ, Fin.cases_succ]; rfl
    rw [h1, h2]
  rw [h0, htail]

/-- The domain family `Work.WilVP.DomFam Y = {(x,c) | ∃ y, (x,y,c) ∈ Y}` is `∅`-definable when
`Y` is.  It is the projection of `Y` (pulled back along the reindexing
`f : Fin (k+2) → Fin (k+1) ⊕ Fin 1` with `f 0 = Sum.inl 0`, `f 1 = Sum.inr 0`,
`f (i+2) = Sum.inl (i+1)`) along a quantifier over the finite block `Fin 1`
(`Set.Definable.preimage_comp`, `Set.Definable.exists_of_finite`). -/
theorem domFam_definable {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (Work.WilVP.DomFam Y) := by
  -- Reindex `Y` onto the context `Fin (k+1) ⊕ Fin 1`, where the `Fin 1`-block is the value
  -- coordinate `y`.
  have h1 : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc
      ((fun g : Fin (k + 1) ⊕ Fin 1 → ℝ => g ∘ projIdx k) ⁻¹' Y) :=
    hY.preimage_comp (projIdx k)
  -- Existentially quantify the finite block `Fin 1`.
  have h2 := h1.exists_of_finite
  -- The result is exactly the domain family.
  have heq : Work.WilVP.DomFam Y =
      {v : Fin (k + 1) → ℝ | ∃ u : Fin 1 → ℝ,
        Sum.elim v u ∈ ((fun g : Fin (k + 1) ⊕ Fin 1 → ℝ => g ∘ projIdx k) ⁻¹' Y)} := by
    ext v
    simp only [Work.WilVP.DomFam, Set.mem_ofPred_eq, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨fun _ => y, ?_⟩
      rw [comp_projIdx v (fun _ => y)]
      simpa using hy
    · rintro ⟨u, hu⟩
      refine ⟨u 0, ?_⟩
      rw [comp_projIdx v u] at hu
      exact hu
  rw [heq]
  exact h2

end Work.WilVP
