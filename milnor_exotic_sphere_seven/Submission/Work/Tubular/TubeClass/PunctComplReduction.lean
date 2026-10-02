import Submission.Work.Tubular.TubeClass.ComplPointMan8All
import Submission.Work.Tubular.onePoint_compl_zero
import Submission.Work.Cohomology.excision
import Submission.Work.Cohomology.onePoint_cokernel_pi_compl_point_bijective
import Submission.Work.Cohomology.localCohomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

/-!
# Reduction of `punctComplTopHomologyVanishing` to the vanishing of the pair `(ν⁺, A)`

For `E : EmbeddingData V (8+k)`, `ν⁺ = OnePoint (NormalTotal E)` (the Thom space), `x₀` the point of
the zero section over `v₀`, `X = ν⁺ ∖ {x₀}` and `A = onePointNonzero E = ν⁺ ∖ (zero section)`, the
contractibility of `A` (`Work.Tubular.contractibleSpace_onePointNonzero`) makes the map
`H_{8+k}(X) ⟶ H_{8+k}(X,A)` an isomorphism, so

  `H_{8+k}(X) = 0  ⟺  H_{8+k}(X,A) = 0`.

This file records that step (`Work.Tubular.TubeClass.punctComplTopHomologyVanishing_of_isZero_pair`)
together with the homeomorphism `↥A ≃ₜ ↥(onePointNonzero E)` used to transport the contractibility
of `A` (which is a contractible *subspace of `ν⁺`*, not of `X`).
-/

open CategoryTheory Limits
open scoped Topology

namespace Work.Tubular.TubeClass

noncomputable section

open Work.Cohomology

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- The point of the normal bundle at which the collapse is a local homeomorphism. -/
abbrev zeroNormalPt (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt) :
    Work.Tubular.NormalTotal E :=
  ⟨(v₀, 0), Work.Tubular.zero_mem_normalSpace E v₀⟩

/-- `x₀` lies in the zero section of `ν⁺`. -/
theorem zeroSectionPunctPt_mem (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (v₀ : V.pt) : zeroSectionPunctPt E v₀ ∈ Work.Tubular.onePointZeroSection E := by
  rw [zeroSectionPunctPt, Work.Tubular.zeroSectionOnePoint, Work.Tubular.onePointZeroSection]
  exact ⟨⟨(v₀, 0), Work.Tubular.zero_mem_normalSpace E v₀⟩, by simp [Work.Tubular.normalNorm], rfl⟩

/-- `x₀` does not lie in `A = onePointNonzero E`. -/
theorem zeroSectionPunctPt_notMem_onePointNonzero
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt) :
    zeroSectionPunctPt E v₀ ∉ Work.Tubular.onePointNonzero E := by
  rw [← Work.Tubular.compl_onePointZeroSection]
  exact fun h => h (zeroSectionPunctPt_mem E v₀)

/-- **`A = onePointNonzero E`, viewed as a subspace of `X = ν⁺ ∖ {x₀}`, is `A` itself.** -/
def homeomorph_pairA (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (v₀ : V.pt) :
    ↥{q : PunctCompl E v₀ | (q : OnePoint (Work.Tubular.NormalTotal E))
        ∈ Work.Tubular.onePointNonzero E} ≃ₜ ↥(Work.Tubular.onePointNonzero E) where
  toFun q := ⟨q.1.1, q.2⟩
  invFun p := ⟨⟨p.1, fun h => zeroSectionPunctPt_notMem_onePointNonzero E v₀ (h ▸ p.2)⟩, p.2⟩
  left_inv q := Subtype.ext (Subtype.ext rfl)
  right_inv p := Subtype.ext rfl
  continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  continuous_invFun :=
    Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _

/-- **The vanishing of the top homology of `X = ν⁺ ∖ {x₀}` follows from the vanishing of the
relative group of the pair `(X, A)`.** -/
theorem punctComplTopHomologyVanishing_of_isZero_pair [ConnectedSpace V.pt]
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt)
    (h : CategoryTheory.Limits.IsZero ((relChains
      (TopCat.of (PunctCompl E v₀))
      {q | (q : OnePoint (Work.Tubular.NormalTotal E)) ∈ Work.Tubular.onePointNonzero E}).homology
        (8 + k))) :
    CategoryTheory.Limits.IsZero ((singularChains ℤ
      (TopCat.of (PunctCompl E v₀))).homology (8 + k)) := by
  set X : TopCat := TopCat.of (PunctCompl E v₀) with hX
  set A : Set X := {q | (q : OnePoint (Work.Tubular.NormalTotal E))
      ∈ Work.Tubular.onePointNonzero E} with hA
  have hhomeo : ↥A ≃ₜ ↥(Work.Tubular.onePointNonzero E) := homeomorph_pairA E v₀
  have hA0 : CategoryTheory.Limits.IsZero
      ((singularChains ℤ (TopCat.of A)).homology (8 + k)) :=
    isZero_homology_of_homeomorph (X := TopCat.of A)
      (Y := TopCat.of (Work.Tubular.onePointNonzero E)) hhomeo (8 + k)
      (Work.Tubular.isZero_homology_onePointNonzero E (8 + k) (by omega))
  have hA1 : CategoryTheory.Limits.IsZero
      ((singularChains ℤ (TopCat.of A)).homology (8 + k - 1)) :=
    isZero_homology_of_homeomorph (X := TopCat.of A)
      (Y := TopCat.of (Work.Tubular.onePointNonzero E)) hhomeo (8 + k - 1)
      (Work.Tubular.isZero_homology_onePointNonzero E (8 + k - 1) (by omega))
  have hbij := homologyMap_cokernel_pi_bijective_of_isZero X A (8 + k) (by omega) hA0 hA1
  haveI : IsIso (HomologicalComplex.homologyMap
      (CategoryTheory.Limits.cokernel.π (inclChains X A)) (8 + k)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  exact IsZero.of_iso h (asIso (HomologicalComplex.homologyMap
    (CategoryTheory.Limits.cokernel.π (inclChains X A)) (8 + k)))

end

end Work.Tubular.TubeClass

namespace Work.Tubular.TubeClass

noncomputable section

open Work.Cohomology

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- `x₀` is not the point at infinity. -/
theorem zeroSectionPunctPt_ne_infty (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (v₀ : V.pt) : zeroSectionPunctPt E v₀ ≠ OnePoint.infty := by
  rw [zeroSectionPunctPt, Work.Tubular.zeroSectionOnePoint]
  exact OnePoint.coe_ne_infty _

/-- The point at infinity, as a point of `X = ν⁺ ∖ {x₀}`. -/
def inftyPunct (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt) :
    PunctCompl E v₀ :=
  ⟨OnePoint.infty, fun h => zeroSectionPunctPt_ne_infty E v₀ h.symm⟩

/-- `(onePointRangeHomeo X₀) x` is the point `some x`, as an element of the complement of `∞`. -/
theorem onePointRangeHomeo_apply_some {X₀ : Type*} [TopologicalSpace X₀] (x : X₀) :
    Work.Tubular.onePointRangeHomeo X₀ x
      = ⟨OnePoint.some x, Set.mem_compl_singleton_iff.mpr (OnePoint.coe_ne_infty x)⟩ :=
  Subtype.ext (Work.Tubular.onePointRangeHomeo_apply x)

/-- Reordering the two subtype conditions `q ≠ x₀` and `q ≠ ∞`. -/
def reorderPunct (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (v₀ : V.pt) :
    {q : PunctCompl E v₀ // (q : OnePoint (Work.Tubular.NormalTotal E)) ∈
        ({OnePoint.infty}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))}
      ≃ₜ {y : ({p : OnePoint (Work.Tubular.NormalTotal E) //
          p ∈ ({OnePoint.infty}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))})
        // y ≠ ⟨zeroSectionPunctPt E v₀,
            Set.mem_compl_singleton_iff.mpr (zeroSectionPunctPt_ne_infty E v₀)⟩} where
  toFun q := ⟨⟨q.1.1, q.2⟩, fun h => q.1.2 (congrArg Subtype.val h)⟩
  invFun y := ⟨⟨y.1.1, fun h => y.2 (Subtype.ext h)⟩, y.1.2⟩
  left_inv q := Subtype.ext (Subtype.ext rfl)
  right_inv y := Subtype.ext (Subtype.ext rfl)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- **The homeomorphism of pairs `(X ∖ {∞}, A ∖ {∞}) ≅ (ν ∖ {x₀'}, ν ∖ 0)`,** where
`X = ν⁺ ∖ {x₀}` and `A = ν⁺ ∖ (zero section)`. -/
def homeomorph_punctPair (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (v₀ : V.pt) :
    {q : PunctCompl E v₀ // (q : OnePoint (Work.Tubular.NormalTotal E)) ∈
        ({OnePoint.infty}ᶜ : Set (OnePoint (Work.Tubular.NormalTotal E)))}
      ≃ₜ {p : Work.Tubular.NormalTotal E // p ≠ zeroNormalPt E v₀} :=
  (reorderPunct E v₀).trans
    ((homeomorphComplSingleton (Work.Tubular.onePointRangeHomeo (Work.Tubular.NormalTotal E))
      (zeroNormalPt E v₀)
      ⟨zeroSectionPunctPt E v₀,
        Set.mem_compl_singleton_iff.mpr (zeroSectionPunctPt_ne_infty E v₀)⟩
      (onePointRangeHomeo_apply_some (zeroNormalPt E v₀))).symm)

end

end Work.Tubular.TubeClass
