import Submission.Work.Tubular.contractibleSpace_onePointNonzero
import Submission.Work.Cohomology.onePoint_cokernel_pi_compl_point_bijective

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# The vanishing of the homology of `A = (ν ∖ 0) ∪ {∞}`, and the first half of (B2)

`A = Work.Tubular.onePointNonzero E` — the complement of the zero section in the one-point
compactification of the normal bundle of an embedding `E : V ↪ ℝ^{8+k}` — is contractible
(`Work.Tubular.contractibleSpace_onePointNonzero`), so its positive-degree singular homology
vanishes:

* `Work.Tubular.isZero_homology_onePointNonzero`;
* `Work.Tubular.bijective_homologyMap_onePoint_compl_zero` — with the long exact sequence of the
  pair `(ν⁺, A)` (`Work.Cohomology.homologyMap_cokernel_pi_bijective_of_isZero`) this gives the
  **first half of (B2)**: `H_{k+8}(ν⁺) ≅ H_{k+8}(ν⁺, A)`.

The remaining half — the excision of `{∞}` identifying `H_{k+8}(ν⁺,A)` with
`H_{k+8}(ν, ν∖0)` — is `Work.Tubular.nonempty_homologyIso_onePoint_relChains`.
-/

open CategoryTheory Limits

open Work.ThomBordism.PontryaginThom (EmbeddingData)

namespace Work.Tubular

noncomputable section

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- **The positive-degree homology of `A = (ν ∖ 0) ∪ {∞}` vanishes** (it is contractible). -/
theorem isZero_homology_onePointNonzero (E : EmbeddingData V (8 + k)) (n : ℕ) (hn : 0 < n) :
    IsZero ((Work.Cohomology.singularChains ℤ
      (TopCat.of (onePointNonzero E))).homology n) := by
  have hc : ContractibleSpace ↥(onePointNonzero E) := contractibleSpace_onePointNonzero E
  haveI := hc
  exact Work.Cohomology.homologyContractible n hn

/-- **The first half of (B2)**: the map `H_{k+8}(ν⁺) → H_{k+8}(ν⁺, A)` of the pair `(ν⁺, A)` is
bijective, because the two neighbouring terms `H_{k+8}(A)` and `H_{k+7}(A)` of the long exact
sequence vanish. -/
theorem bijective_homologyMap_onePoint_compl_zero (E : EmbeddingData V (8 + k)) :
    Function.Bijective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains
        (TopCat.of (OnePoint (NormalTotal E)))
        (OnePoint.some '' {p : NormalTotal E | normalNorm E p ≠ 0} ∪ {OnePoint.infty}))) (k + 8))) := by
  have h := Work.Cohomology.homologyMap_cokernel_pi_bijective_of_isZero
    (TopCat.of (OnePoint (NormalTotal E))) (onePointNonzero E) (k + 8) (by omega)
    (isZero_homology_onePointNonzero E (k + 8) (by omega))
    (isZero_homology_onePointNonzero E ((k + 8) - 1) (by omega))
  exact h

end

end Work.Tubular
