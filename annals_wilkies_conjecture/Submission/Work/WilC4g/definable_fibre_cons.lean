import Mathlib
import Submission.Work.WilC4.Defs

namespace Work.WilC4g

theorem definable_fibre_cons {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M] {k : ℕ} {A : Set M} {B : Set (Fin (k + 1) → M)} (hB : A.Definable WilkiesDesign.CG.LRc B) (c : Fin k → M) : (A ∪ Set.range c).Definable WilkiesDesign.CG.LRc {u : Fin 1 → M | Fin.cons (u 0) c ∈ B} := by
  have hB' : (A ∪ Set.range c).Definable WilkiesDesign.CG.LRc B := hB.mono Set.subset_union_left
  refine Set.Definable.preimage_map ?_ hB'
  intro i
  refine Fin.cases (motive := fun i => (A ∪ Set.range c).DefinableFun WilkiesDesign.CG.LRc
    (fun v : Fin 1 → M => (Fin.cons (v 0) c : Fin (k + 1) → M) i)) ?_ ?_ i
  · simpa using (Set.DefinableFun.proj (L := WilkiesDesign.CG.LRc) (A := A ∪ Set.range c)
      (i := (0 : Fin 1)))
  · intro j
    have h : (fun v : Fin 1 → M => (Fin.cons (v 0) c : Fin (k + 1) → M) (Fin.succ j)) =
        fun _ : Fin 1 → M => c j := by
      funext v
      rw [Fin.cons_succ]
    rw [h]
    exact FirstOrder.Language.definableFun_const WilkiesDesign.CG.LRc (Fin 1)
      (Or.inr (Set.mem_range_self j))

end Work.WilC4g
