import Mathlib
import Submission.Work.ThomBordism.orientedFibreGen
import Submission.Work.ThomBordism.nfRes_span_top_of_generator
import Submission.Work.ThomBordism.nfRelCohIso
import Submission.Work.ThomBordism.fibreRes_localDegreeClass_eq_nfGen
import Submission.Work.ThomBordism.TubeLocalDegree

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism

/-- **The fibre restriction determines a generator of the Thom pair.**

`Work.ThomBordism.nfRes E x k : H^k(ν, ν∖0;ℤ) → H^k(ν_x, ν_x∖0;ℤ)` is the restriction to the fibre
over `x`.  The fibre module is `ℤ` (`Work.ThomBordism.nfRelCohIso`), and the restriction of a
generator of the Thom pair generates it (`Work.ThomBordism.nfRes_span_top_of_generator`).  Hence if
`U` and `W` both generate `H^k(ν, ν∖0;ℤ)` and have the same fibre restriction, they are equal: write
`W = m • U`, apply `nfRes`, and cancel the nonzero element `nfRes U` of the torsion-free module
`H^k(ν_x, ν_x∖0;ℤ)`.

This is exactly `Work.ThomBordism.branchSign_core` with `s = 1`. -/
theorem nfRes_eq_of_span {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (hk : 1 ≤ k) (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (x : V.pt)
    {U W : Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E)}
    (hU : Submodule.span ℤ ({U} : Set (Work.Thom.RelCoh ℤ k
      (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E))) = ⊤)
    (hW : Submodule.span ℤ ({W} : Set (Work.Thom.RelCoh ℤ k
      (TopCat.of (Work.Tubular.NormalTotal E)) (Work.Tubular.normalNonzero E))) = ⊤)
    (h : Work.ThomBordism.nfRes E x k U = Work.ThomBordism.nfRes E x k W) : U = W := by
  obtain ⟨e⟩ := nfRelCohIso hk E ND x
  have hWU : W = (1 : ℤ) • U :=
    branchSign_core (nfRes E x k) U W (nfRes E x k U) 1 hU ⟨e⟩
      (nfRes_span_top_of_generator (k := k) hk E ND x hU)
      (by rw [← h, one_smul]) rfl
  have : W = U := by simpa using hWU
  exact this.symm

end Work.ThomBordism
