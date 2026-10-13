import Mathlib
import Submission.Work.WilC4.Defs

open FirstOrder FirstOrder.Language
open WilkiesDesign WilkiesDesign.CG

namespace Work.WilC4

/-- The `Fin 1`-singleton built out of a point: the set of `v : Fin 1 → M` with `v 0 ∈ {x}` is
the singleton of the constant tuple `fun _ => x`.  This is the only place where the two
formulations of "`{x}` is definable" (the `Set.Definable` one and the one with an explicit
tuple) have to be compared. -/
theorem singleton_setOf_eq {M : Type} (x : M) :
    ({v : Fin 1 → M | v 0 ∈ ({x} : Set M)} : Set (Fin 1 → M)) = {fun _ : Fin 1 => x} := by
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    funext i
    rw [Subsingleton.elim i 0]
    exact h
  · intro h
    rw [h]

/-- The definable closure of an elementary substructure (with no extra parameters) is the
substructure itself: an elementary substructure is `dcl`-closed.  Both inclusions are
straightforward: an element of `S` is definable from `S` by the parameter `x` itself
(`Set.Definable.singleton_of_mem`), while a definable element of `S` lies in it because an
elementary substructure meets every nonempty definable set
(`ElementarySubstructure.meetsDefinable`). -/
theorem dcl_elementary {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M] (S : WilkiesDesign.CG.LRc.ElementarySubstructure M) : Dcl (S : Set M) ∅ = (S : Set M) := by
  ext x
  constructor
  · -- `x` is definable from `S`, so the nonempty `S`-definable set `{x}` meets `S`.
    intro hx
    have hD : (S : Set M).Definable₁ LRc {x} := by
      rw [Set.Definable₁, singleton_setOf_eq x]
      simpa only [Dcl, DefinableElt, Set.mem_ofPred_eq, Set.union_empty] using hx
    obtain ⟨y, hy1, hy2⟩ := S.meetsDefinable {x} ⟨x, rfl⟩ hD
    rwa [Set.mem_singleton_iff.mp hy1] at hy2
  · -- `x ∈ S` is definable from the parameter `x ∈ S`.
    intro hx
    have hS : x ∈ (S : Set M) ∪ ∅ := by simpa using hx
    have hD := Set.Definable.singleton_of_mem LRc hS
    rw [Set.Definable₁, singleton_setOf_eq x] at hD
    simpa only [Dcl, DefinableElt, Set.mem_ofPred_eq] using hD

end Work.WilC4
