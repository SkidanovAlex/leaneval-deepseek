import Mathlib
import Submission.Work.Pi6.SQM.SIG.sigmaNaturalDefs
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Naturality of the connecting homomorphism of the pair for the path fibration

For a continuous map `h : C(K,L)` and a base point `k₀ : K`, the map on based path spaces
`pathMap K L k₀ h : PK K k₀ → PK L (h k₀)` is a map of pairs `(PK K, fibre K) → (PK L, fibre L)`.
The connecting homomorphisms `pairδ` of the long exact sequences of the pair are natural with
respect to such a map of pairs, which is the statement proved here (the form needed for the
naturality of the cohomology suspension `σ`).
-/

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicTopology Work.Cohomology
open scoped Simplicial

namespace Work.Pi6.SQM.SIG

noncomputable section

/-- The map of pairs `(PK K, fibre K) → (PK L, fibre L)` induced by `h`, as a morphism of short
exact sequences of relative/absolute/restricted cochain complexes
`0 → C^*(PL, fibre L) → C^*(PL) → C^*(fibre L) → 0`
`↓          ↓          ↓          ↓`
`0 → C^*(PK, fibre K) → C^*(PK) → C^*(fibre K) → 0`. -/
def pathPairShortMap (K L : Type) [TopologicalSpace K] [TopologicalSpace L] (k₀ : K)
    (h : C(K, L)) :
    Work.Cohomology.pairShort Work.Pi6.SQ.F2 (TopCat.of (PK L (h k₀))) (fibreSet L (h k₀)) ⟶
      Work.Cohomology.pairShort Work.Pi6.SQ.F2 (TopCat.of (PK K k₀)) (fibreSet K k₀) :=
  { τ₁ := pathPairMap K L k₀ h
    τ₂ := dualChainMap Work.Pi6.SQ.F2 (TopCat.of (PK K k₀)) (TopCat.of (PK L (h k₀)))
      (PKmap K L k₀ h)
    τ₃ := dualChainMap Work.Pi6.SQ.F2 (TopCat.of ↥(fibreSet K k₀))
      (TopCat.of ↥(fibreSet L (h k₀))) (fibreMap K L k₀ h)
    comm₁₂ := lmCompRelIncl _ _ _ _ _
    comm₂₃ := dualChainMap_restr_comp _ _ _ _ _ }

/-- **Naturality of the connecting homomorphism of the pair under the map of pairs induced by
`h`.**  The two ways round the square

`H^{n+1}(fibre L) --δ--> H^{n+2}(PL, fibre L)`
`      |                            |`
`  fibreMap*                   pathPairMap*`
`      v                            v`
`H^{n+1}(fibre K) --δ--> H^{n+2}(PK, fibre K)`

agree. -/
theorem pairDeltaNatural (K L : Type) [TopologicalSpace K] [TopologicalSpace L] (k₀ : K) (h : C(K, L)) (n : ℕ) : CategoryTheory.CategoryStruct.comp (Work.Cohomology.pairδ Work.Pi6.SQ.F2 (TopCat.of (Work.Pi6.SQM.SIG.PK L (h k₀))) (Work.Pi6.SQM.SIG.fibreSet L (h k₀)) (n + 1)) (HomologicalComplex.homologyMap (Work.Pi6.SQM.SIG.pathPairMap K L k₀ h) (n + 2)) = CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (Work.Cohomology.dualChainMap Work.Pi6.SQ.F2 (TopCat.of ↥(Work.Pi6.SQM.SIG.fibreSet K k₀)) (TopCat.of ↥(Work.Pi6.SQM.SIG.fibreSet L (h k₀))) (Work.Pi6.SQM.SIG.fibreMap K L k₀ h)) (n + 1)) (Work.Cohomology.pairδ Work.Pi6.SQ.F2 (TopCat.of (Work.Pi6.SQM.SIG.PK K k₀)) (Work.Pi6.SQM.SIG.fibreSet K k₀) (n + 1)) := by
  have hrel : (ComplexShape.up ℕ).Rel (n + 1) (n + 2) := ComplexShape.up_mk _ _ rfl
  have hnat := HomologicalComplex.HomologySequence.δ_naturality (pathPairShortMap K L k₀ h)
      (Work.Cohomology.pairShort_shortExact Work.Pi6.SQ.F2 (TopCat.of (PK L (h k₀)))
        (fibreSet L (h k₀)))
      (Work.Cohomology.pairShort_shortExact Work.Pi6.SQ.F2 (TopCat.of (PK K k₀))
        (fibreSet K k₀))
      (n + 1) (n + 2) hrel
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro w
  have hw := congrArg (fun (g :
      (Work.Cohomology.pairShort Work.Pi6.SQ.F2 (TopCat.of (PK L (h k₀)))
          (fibreSet L (h k₀))).X₃.homology (n + 1) ⟶
        (Work.Cohomology.pairShort Work.Pi6.SQ.F2 (TopCat.of (PK K k₀))
          (fibreSet K k₀)).X₁.homology (n + 2)) => ModuleCat.Hom.hom g w) hnat
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hw ⊢
  exact hw

end

end Work.Pi6.SQM.SIG
