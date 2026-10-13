import Mathlib
import Submission.Work.WilVP.Defs
import Submission.Work.WilC4g.finiteDefinable_subset_T
import Submission.Work.WilC4.dcl_elementary
import Submission.Work.WilC4g.definable_fibre_cons

namespace Work.WilVP

/-- Finite fibres of `∅`-definable families at `S`-parameters lie in `S`.  We know
`{x | (x,c) ∈ P}.encard ≤ N`, hence that fibre is finite; it is definable over `S` (the formula
has the parameters `c ∈ S`, via `Work.WilC4g.definable_fibre_cons` with `{range c} ⊆ S`), so
`Work.WilC4g.finiteDefinable_subset_T` (with `T := S`, using `Work.WilC4.dcl_elementary` for
`T = Dcl T ∅`) gives `p ∈ S`. -/
theorem finite_fibre_mem {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    [FirstOrder.Language.Theory.Model M WilkiesDesign.CG.TR]
    (S : WilkiesDesign.CG.LRc.ElementarySubstructure M) {k : ℕ} {c : Fin k → M}
    (hc : ∀ i, c i ∈ (S : Set M)) {P : Set (Fin (k + 1) → M)}
    (hP : (∅ : Set M).Definable WilkiesDesign.CG.LRc P) {N : ℕ}
    (hfin : {x : M | Fin.cons x c ∈ P}.encard ≤ N) {p : M} (hp : Fin.cons p c ∈ P) :
    p ∈ (S : Set M) := by
  -- `S` is `dcl`-closed: `Work.WilC4.dcl_elementary` identifies the definable closure of `S`
  -- with `S` itself.
  have hSdcl : ∀ x : M, Work.WilC4.DefinableElt (S : Set M) ∅ x ↔ x ∈ (S : Set M) :=
    fun x => Set.ext_iff.mp (Work.WilC4.dcl_elementary S) x
  -- The fibre `{x | (x,c) ∈ P}` is definable over `S`: it is definable over `range c`, and
  -- `range c ⊆ S` by hypothesis.
  have hdef : (S : Set M).Definable₁ WilkiesDesign.CG.LRc {x : M | Fin.cons x c ∈ P} :=
    (Work.WilC4g.definable_fibre_cons (A := (∅ : Set M)) (B := P) hP c).mono (by
      intro a ha
      rcases ha with h | h
      · exact absurd h (Set.notMem_empty a)
      · obtain ⟨i, rfl⟩ := h
        exact hc i)
  -- A fibre of `encard ≤ N` (a natural number) is finite.
  have hfin' : ({x : M | Fin.cons x c ∈ P} : Set M).Finite := by
    rw [← Set.encard_lt_top_iff]
    exact lt_of_le_of_lt hfin (ENat.natCast_lt_top N)
  -- A finite `S`-definable set consists of elements of `S` alone.
  exact Work.WilC4g.finiteDefinable_subset_T (inferInstance) hSdcl hdef hfin' hp

end Work.WilVP
