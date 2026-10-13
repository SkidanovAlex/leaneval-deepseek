import Mathlib
import Submission.Work.WilC4.Defs

namespace Work.WilC4

/-- Elements of the left parameter set are definable: if `x ∈ S` then the singleton `{x}` is
`LRc`-definable with parameters in `S ∪ A` (via the constant symbol for `x`).  This is the
`S ⊆ Dcl S A` half of the definable closure being an extension of its parameters. -/
theorem definableElt_of_mem_left {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M] (S A : Set M) {x : M} (hx : x ∈ S) : DefinableElt S A x := by
  rw [DefinableElt]
  have h : (S ∪ A).Definable WilkiesDesign.CG.LRc {v : Fin 1 → M | v 0 ∈ ({x} : Set M)} :=
    Set.Definable.singleton_of_mem WilkiesDesign.CG.LRc (Set.mem_union_left A hx)
  have hset : {v : Fin 1 → M | v 0 ∈ ({x} : Set M)} = {fun _ : Fin 1 => x} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hv
      funext i
      rw [Fin.eq_zero i]
      exact hv
    · intro hv
      rw [hv]
  rw [hset] at h
  exact h

end Work.WilC4
