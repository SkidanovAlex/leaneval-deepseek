import Submission.Work.Tubular.TubeClass.Core
import Submission.Work.Cohomology.onePoint_cokernel_pi_compl_point_bijective

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
-- The module structures on the homology groups are the ones induced from the ambient modules:
attribute [local instance 5000] Submodule.module
attribute [local instance 5000] Submodule.Quotient.module

/-!
# The reduction of `tubeCollapseClass_span_top` to two geometric inputs

Given

* `hA` : `H_{8+k}(ν⁺ ∖ {x₀}) = 0` (`punctComplTopHomologyVanishing`), and
* `hB` : the localisation at `x₀` of the Hurewicz class of the collapse generates the local group
  (`localisationCollapseClassSpanTop`),

the Hurewicz class `h` of the collapse generates `H_{8+k}(ν⁺)`: the localisation is injective
(long exact sequence of the pair, `hPair_exact₂`), and an injective map that sends `h` to a
generator has `h` generating.

If moreover the relative group `H_{8+k}(ν⁺, A)` is a quotient of `H_{8+k}(ν⁺)` — which it is for
`A = (ν∖0) ∪ {∞}` because `A` is contractible
(`Work.Tubular.bijective_homologyMap_onePoint_compl_zero`) — then the image of `h` in
`H_{8+k}(ν⁺,A)` generates, which is `Work.Tubular.tubeCollapseClass_span_top`.
-/

open CategoryTheory Limits
open scoped Topology

namespace Work.Tubular

noncomputable section

open Work.Cohomology

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- **Injectivity of the localisation at `x₀`** from the vanishing of the top homology of the
complement (long exact sequence of the pair `(ν⁺, ν⁺∖{x₀})`). -/
theorem injective_localisationPunct (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (v₀ : V.pt)
    (hA : IsZero ((singularChains ℤ (TopCat.of (PunctCompl E v₀))).homology (8 + k))) :
    Function.Injective (localisationPunct E v₀ (8 + k)) := by
  set X : TopCat := TopCat.of (OnePoint (NormalTotal E)) with hX
  set B : Set X := ({zeroSectionPunctPt E v₀}ᶜ : Set (OnePoint (NormalTotal E))) with hBdef
  have h1 : IsZero ((singularChains ℤ (TopCat.of B)).homology (8 + k)) := hA
  have hexact := (Work.Cohomology.hPair_exact₂ X B (8 + k)).moduleCat_range_eq_ker
  have hf : HomologicalComplex.homologyMap (inclChains X B) (8 + k) = 0 := h1.eq_of_src _ 0
  have hrange : (ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap (inclChains X B) (8 + k))).range = ⊥ := by
    rw [hf]; exact LinearMap.range_zero
  have hker : (ModuleCat.Hom.hom
      (HomologicalComplex.homologyMap (cokernel.π (inclChains X B)) (8 + k))).ker = ⊥ := by
    rw [← hexact, hrange]
  exact LinearMap.ker_eq_bot.mp hker

/-- **The Hurewicz class of the collapse generates `H_{8+k}(ν⁺)`**, given the two geometric
inputs. -/
theorem span_hurewiczChain_top_of_localisation {E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)}
    {ε : ℝ} (C : TubeChart E ε) (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
    (hbox : ∀ y ∈ C.U, ∀ i : Fin (8 + k), |y i| < R)
    (g : C(OnePoint (Euc (8 + k)), OnePoint (NormalTotal E)))
    (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
    (hg2 : ∀ y, y ∈ C.openTube → g (OnePoint.some y)
      = OnePoint.some (normalBlowUp E ε (C.inv y)))
    (v₀ : V.pt)
    (hA : IsZero ((singularChains ℤ (TopCat.of (PunctCompl E v₀))).homology (8 + k)))
    (hB : Submodule.span ℤ
      {(localisationPunct E v₀ (8 + k)
        (Work.Stems.hurewiczChain (8 + k) (by omega) OnePoint.infty
          (tubeGenLoopOnePoint C g hg hR hbox)))} = ⊤) :
    Submodule.span ℤ
      {(Work.Stems.hurewiczChain (8 + k) (by omega) OnePoint.infty
        (tubeGenLoopOnePoint C g hg hR hbox))} = ⊤ := by
  have hinj := injective_localisationPunct E v₀ hA
  set h := Work.Stems.hurewiczChain (8 + k) (by omega) OnePoint.infty
    (tubeGenLoopOnePoint C g hg hR hbox) with hhdef
  change Submodule.span ℤ ({h} : Set _) = ⊤
  refine Submodule.eq_top_iff'.mpr fun z => ?_
  have hmap : Submodule.map (localisationPunct E v₀ (8 + k)) (Submodule.span ℤ ({h} : Set _)) = ⊤ := by
    rw [Submodule.map_span, Set.image_singleton]
    exact hB
  have hmem : localisationPunct E v₀ (8 + k) z ∈
      Submodule.map (localisationPunct E v₀ (8 + k)) (Submodule.span ℤ ({h} : Set _)) := by
    rw [hmap]; exact Submodule.mem_top
  obtain ⟨y, hy, hzy⟩ := Submodule.mem_map.mp hmem
  rw [← hinj hzy]
  exact hy

end

end Work.Tubular
