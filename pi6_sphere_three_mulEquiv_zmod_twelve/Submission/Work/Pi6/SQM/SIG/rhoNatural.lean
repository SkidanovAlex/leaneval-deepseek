import Mathlib
import Submission.Work.Pi6.SQM.SIG.sigmaNaturalDefs
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# SQM / SIG — naturality of `ρ : H^{n+2}(K) → H^{n+2}(K,{k₀})`

`ρ_K` is the inverse of the homology map of the inclusion `relIncl : C^*(K,{k₀}) → C^*(K)` of the
relative into the absolute cochain complex (valid because a point has no positive-degree
cohomology).  Naturality of `ρ` with respect to a based continuous map `h : K → L` follows from the
naturality of `relIncl` — the chain-level square
`basePairMap h ≫ relIncl_K = relIncl_L ≫ dualChainMap h`, proved as `lmCompRelIncl` — together with
the two section/retraction identities `relIncl_rhoLM` (`ρ ≫ relIncl = id`) and `rhoLM_relIncl`
(`relIncl ≫ ρ = id`).
-/

open CategoryTheory Limits AlgebraicTopology Work.Cohomology
open scoped Simplicial

namespace Work.Pi6.SQM.SIG

noncomputable section

/-- The chain-level naturality square for the inclusion `relIncl` of the relative into the
absolute cochain complex, in the exact form needed for `rhoNatural`. -/
theorem basePairMap_relIncl (K L : Type) [TopologicalSpace K] [TopologicalSpace L] (k₀ : K)
    (h : C(K, L)) :
    CategoryTheory.CategoryStruct.comp (basePairMap K L k₀ h)
        (relIncl Work.Pi6.SQ.F2 (TopCat.of K) ({k₀} : Set K)) =
      CategoryTheory.CategoryStruct.comp (relIncl Work.Pi6.SQ.F2 (TopCat.of L) ({h k₀} : Set L))
        (dualChainMap Work.Pi6.SQ.F2 (TopCat.of K) (TopCat.of L) (TopCat.ofHom h)) :=
  lmCompRelIncl Work.Pi6.SQ.F2 (X₁ := TopCat.of K) (X₂ := TopCat.of L)
    ({k₀} : Set K) ({h k₀} : Set L) (TopCat.ofHom h) _

theorem rhoNatural (K L : Type) [TopologicalSpace K] [TopologicalSpace L] (k₀ : K) (h : C(K, L)) (n : ℕ) : CategoryTheory.CategoryStruct.comp (Work.Pi6.cmap Work.Pi6.SQ.F2 h (n + 2)) (Work.Pi6.SQM.SIG.rhoLM K k₀ n) = CategoryTheory.CategoryStruct.comp (Work.Pi6.SQM.SIG.rhoLM L (h k₀) n) (HomologicalComplex.homologyMap (Work.Pi6.SQM.SIG.basePairMap K L k₀ h) (n + 2)) := by
  -- `homology` of the chain-level naturality square of `relIncl`
  have hnat :
      CategoryTheory.CategoryStruct.comp
          (HomologicalComplex.homologyMap (basePairMap K L k₀ h) (n + 2))
          (HomologicalComplex.homologyMap (relIncl Work.Pi6.SQ.F2 (TopCat.of K) ({k₀} : Set K))
            (n + 2)) =
        CategoryTheory.CategoryStruct.comp
          (HomologicalComplex.homologyMap (relIncl Work.Pi6.SQ.F2 (TopCat.of L) ({h k₀} : Set L))
            (n + 2))
          (Work.Pi6.cmap Work.Pi6.SQ.F2 h (n + 2)) := by
    have h1 := congrArg (fun φ => HomologicalComplex.homologyMap φ (n + 2))
      (basePairMap_relIncl K L k₀ h)
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at h1
    simpa only [Work.Pi6.cmap, Work.Cohomology.singularCohomologyMap] using h1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  -- `ρ_L` is a section of `relIncl_L`, so `c` may be replaced by `relIncl_L (ρ_L c)`;
  -- naturality of `relIncl` then converts this into `relIncl_K (basePairMap (ρ_L c))`,
  -- and `ρ_K` inverts `relIncl_K`.
  have hsec : (HomologicalComplex.homologyMap (relIncl Work.Pi6.SQ.F2 (TopCat.of L)
      ({h k₀} : Set L)) (n + 2)).hom ((rhoLM L (h k₀) n).hom c) = c :=
    relIncl_rhoLM L (h k₀) n c
  have hnat_lm := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom hnat)
    ((rhoLM L (h k₀) n).hom c)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hsec] at hnat_lm
  exact (congrArg (fun w => (rhoLM K k₀ n).hom w) hnat_lm.symm).trans
    (rhoLM_relIncl K k₀ n _)

end

end Work.Pi6.SQM.SIG
