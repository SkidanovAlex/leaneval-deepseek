import Mathlib
import Submission.Work.ThomBordism.KeyLocal._assAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option linter.unusedVariables false

namespace Work.ThomBordism.BSUG

open Work.Tubular

/-- **A point of the tube over `x` with zero normal component is `E.e x`.**  If `y` is a point of
the tube whose foot is `x` and whose normal foot `C.inv y` has zero norm, then `C.inv y` is the
zero vector over `x`, hence `y = tubeMap E (x, 0) = E.e x`.  Contrapositively: a point of the tube
over `x` distinct from `E.e x` has a nonzero normal component. -/
theorem tubeMap_inv_eq_embedding {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε)
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (i : Work.ThomBordism.PontryaginThom.CoverIdx V k) (x : V.pt)
    {y : ↥(Work.ThomBordism.KeyLocal.tubeBaseSet E C ND i)}
    (h : Work.ThomBordism.KeyLocal.tubeFoot E C (y : ↥C.U) = x)
    (hnorm : normalNorm E (C.inv (y : Work.Tubular.Euc (8 + k))) = 0) :
    (y : Work.Tubular.Euc (8 + k)) = E.e x := by
  have hvec : NormalTotal.vec (C.inv (y : Work.Tubular.Euc (8 + k))) = 0 := by
    have h2 := hnorm
    rw [normalNorm] at h2
    exact norm_eq_zero.mp h2
  have hproj : NormalTotal.proj (C.inv (y : Work.Tubular.Euc (8 + k))) = x := h
  simp only [NormalTotal.proj] at hproj
  simp only [NormalTotal.vec] at hvec
  have ht : tubeMap E (C.inv (y : Work.Tubular.Euc (8 + k))) = E.e x := by
    show E.e (C.inv (y : Work.Tubular.Euc (8 + k))).1.1
        + (C.inv (y : Work.Tubular.Euc (8 + k))).1.2 = E.e x
    rw [hproj, hvec, add_zero]
  rw [← C.tubeMap_inv (y : Work.Tubular.Euc (8 + k)) y.1.2]
  exact ht

theorem tubeUnionMem {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε)
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    (i : Work.ThomBordism.PontryaginThom.CoverIdx V k) (x : V.pt)
    (hx : x ∈ ND.D.baseSet i)
    {y : ↥(Work.ThomBordism.KeyLocal.tubeBaseSet E C ND i)}
    (hy : (y : Work.Tubular.Euc (8 + k)) ≠ E.e x) :
    y ∈ Work.ThomBordism.KeyLocal.tubeFootPunct E C ND i x
      ∪ Work.ThomBordism.KeyLocal.tubeBaseSetPunct E C ND i := by
  rw [Set.mem_union]
  by_cases h : Work.ThomBordism.KeyLocal.tubeFoot E C (y : ↥C.U) = x
  · refine Or.inr ?_
    by_contra hz
    have hnorm : normalNorm E (C.inv (y : Work.Tubular.Euc (8 + k))) = 0 := by
      by_contra hne
      exact hz (Work.Tubular.mem_normalNonzero.2 hne)
    exact hy (tubeMap_inv_eq_embedding E C ND i x h hnorm)
  · exact Or.inl h

end Work.ThomBordism.BSUG
