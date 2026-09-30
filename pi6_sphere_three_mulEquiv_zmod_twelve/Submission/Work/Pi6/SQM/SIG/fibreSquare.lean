import Mathlib
import Submission.Work.Pi6.SQM.SIG.sigmaNaturalDefs
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# `fibreSquare` — naturality of the identification `H^*(fibre) ≅ H^*(ΩK)`

For a based continuous map `h : (K,k₀) → (L,h k₀)` (with a chosen lift `Ωh` of `h` to the loop
spaces, i.e. a continuous map `ΩK → ΩL` satisfying `(Ωh γ)(t) = h (γ t)`), the two ways of getting
from `H^n(fibre (evalOne L) (h k₀))` to `H^n(ΩK)` — restrict along the induced map of fibres and
then transport across `fibre ≅ ΩK`, or transport to `H^n(ΩL)` first and then pull back along `Ωh`
— coincide.  Both composites are the pullback along the single map `ΩK → fibre L`, `γ ↦ h ∘ γ`, so
the square commutes on the nose; the only input is the pointwise agreement `hΩh`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicTopology Work.Cohomology
open scoped Simplicial

namespace Work.Pi6.SQM.SIG

noncomputable section

/-- The two maps `ΩK ⟶ fibre (evalOne L) (h k₀)` — `γ ↦ fibreMap (fibreSetHomeo.symm γ)` and
`γ ↦ fibreSetHomeo.symm (Ωh γ)` — agree, because both send `γ` to the path `h ∘ γ`. -/
theorem fibreSquare_aux (K L : Type) [TopologicalSpace K] [TopologicalSpace L] (k₀ : K)
    (h : C(K, L)) (Ωh : C(Path k₀ k₀, Path (h k₀) (h k₀))) (hΩh : ∀ γ t, Ωh γ t = h (γ t)) :
    TopCat.ofHom (⟨(fibreSetHomeo K k₀).symm.toFun,
        (fibreSetHomeo K k₀).symm.continuous_toFun⟩ : C(Path k₀ k₀, ↥(fibreSet K k₀))) ≫
      fibreMap K L k₀ h
    = TopCat.ofHom Ωh ≫
      TopCat.ofHom (⟨(fibreSetHomeo L (h k₀)).symm.toFun,
        (fibreSetHomeo L (h k₀)).symm.continuous_toFun⟩ :
          C(Path (h k₀) (h k₀), ↥(fibreSet L (h k₀)))) := by
  apply TopCat.ext
  intro γ
  simp only [CategoryTheory.comp_apply, TopCat.hom_ofHom, fibreMap, relMapSub, PKmap, pathMap]
  apply Subtype.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  exact (hΩh γ t).symm

theorem fibreSquare (K L : Type) [TopologicalSpace K] [TopologicalSpace L] (k₀ : K) (h : C(K, L)) (Ωh : C(Path k₀ k₀, Path (h k₀) (h k₀))) (hΩh : ∀ γ t, Ωh γ t = h (γ t)) (n : ℕ) : CategoryTheory.CategoryStruct.comp (HomologicalComplex.homologyMap (Work.Cohomology.dualChainMap Work.Pi6.SQ.F2 (TopCat.of ↥(Work.Pi6.SQM.SIG.fibreSet K k₀)) (TopCat.of ↥(Work.Pi6.SQM.SIG.fibreSet L (h k₀))) (Work.Pi6.SQM.SIG.fibreMap K L k₀ h)) n) ((Work.Pi6.SQM.SIG.fibreCohIso K k₀ n).inv) = CategoryTheory.CategoryStruct.comp ((Work.Pi6.SQM.SIG.fibreCohIso L (h k₀) n).inv) (Work.Pi6.cmap Work.Pi6.SQ.F2 Ωh n) := by
  have H1 : (fibreCohIso K k₀ n).inv = singularCohomologyMap F2 (TopCat.of (Path k₀ k₀))
      (TopCat.of ↥(fibreSet K k₀)) (TopCat.ofHom
        (⟨(fibreSetHomeo K k₀).symm.toFun, (fibreSetHomeo K k₀).symm.continuous_toFun⟩ :
          C(Path k₀ k₀, ↥(fibreSet K k₀)))) n := by
    simp only [fibreCohIso, homeoSSet, Iso.symm_inv, asIso_hom]
  have H2 : (fibreCohIso L (h k₀) n).inv = singularCohomologyMap F2 (TopCat.of (Path (h k₀) (h k₀)))
      (TopCat.of ↥(fibreSet L (h k₀))) (TopCat.ofHom
        (⟨(fibreSetHomeo L (h k₀)).symm.toFun, (fibreSetHomeo L (h k₀)).symm.continuous_toFun⟩ :
          C(Path (h k₀) (h k₀), ↥(fibreSet L (h k₀))))) n := by
    simp only [fibreCohIso, homeoSSet, Iso.symm_inv, asIso_hom]
  rw [H1, H2]
  change singularCohomologyMap F2 (TopCat.of ↥(fibreSet K k₀)) (TopCat.of ↥(fibreSet L (h k₀)))
      (fibreMap K L k₀ h) n ≫
      singularCohomologyMap F2 (TopCat.of (Path k₀ k₀)) (TopCat.of ↥(fibreSet K k₀))
        (TopCat.ofHom (⟨(fibreSetHomeo K k₀).symm.toFun,
          (fibreSetHomeo K k₀).symm.continuous_toFun⟩ : C(Path k₀ k₀, ↥(fibreSet K k₀)))) n
    = singularCohomologyMap F2 (TopCat.of (Path (h k₀) (h k₀)))
        (TopCat.of ↥(fibreSet L (h k₀)))
        (TopCat.ofHom (⟨(fibreSetHomeo L (h k₀)).symm.toFun,
          (fibreSetHomeo L (h k₀)).symm.continuous_toFun⟩ :
            C(Path (h k₀) (h k₀), ↥(fibreSet L (h k₀))))) n ≫
      singularCohomologyMap F2 (TopCat.of (Path k₀ k₀)) (TopCat.of (Path (h k₀) (h k₀)))
        (TopCat.ofHom Ωh) n
  rw [← singularCohomologyMap_comp (R := F2)
    (f := (TopCat.ofHom (⟨(fibreSetHomeo K k₀).symm.toFun,
      (fibreSetHomeo K k₀).symm.continuous_toFun⟩ : C(Path k₀ k₀, ↥(fibreSet K k₀)))))
    (g := fibreMap K L k₀ h) (n := n)]
  rw [← singularCohomologyMap_comp (R := F2)
    (f := (TopCat.ofHom Ωh)) (g := (TopCat.ofHom (⟨(fibreSetHomeo L (h k₀)).symm.toFun,
        (fibreSetHomeo L (h k₀)).symm.continuous_toFun⟩ :
        C(Path (h k₀) (h k₀), ↥(fibreSet L (h k₀)))))) (n := n)]
  congr 1
  exact fibreSquare_aux K L k₀ h Ωh hΩh

end

end Work.Pi6.SQM.SIG
