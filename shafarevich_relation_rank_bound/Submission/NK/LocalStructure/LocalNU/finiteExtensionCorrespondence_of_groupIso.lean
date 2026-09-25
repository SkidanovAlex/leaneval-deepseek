import Mathlib
import Submission.NK.LocalStructure.Defs
import Submission.NeukirchUchida.GaloisIso

set_option linter.style.haveILetI false

namespace NK.LocalStructure.LocalNU

open scoped Classical Pointwise
open IsDedekindDomain.HeightOneSpectrum

universe u

/-- A bijective closed map is an open map: the image of the complement is the complement of the
image. -/
private lemma isOpenMap_of_isClosedMap_bijective {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsClosedMap f) (hb : Function.Bijective f) :
    IsOpenMap f := by
  intro s hs
  have hc : IsClosed (sᶜ) := hs.isClosed_compl
  have h := hf _ hc
  rw [Set.image_compl_eq hb] at h
  simpa using h.isOpen_compl

/-- **An isomorphism of absolute Galois groups of `p`-adic fields induces a correspondence of the
lattices of finite extensions.**

Given `Φ : Gal(L'/N) ≃* Gal(K'/K_𝔭)` (a continuous isomorphism of absolute Galois groups), every
finite extension `M/N` inside the separable closure `L'` has a corresponding finite extension
`level M` of `K_𝔭` inside `K'`, of the same degree, whose fixing subgroup is the `Φ`-image of the
fixing subgroup of `M`.  This is the Galois correspondence together with the fact that a continuous
bijection of profinite groups is a homeomorphism (so that `Φ` carries the Krull-open fixing
subgroups onto Krull-open subgroups). -/
theorem finiteExtensionCorrespondence_of_groupIso
    (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (L' : Type u) [Field L'] [Algebra (𝔮.adicCompletion L) L'] [IsSepClosure (𝔮.adicCompletion L) L']
    (N : IntermediateField (𝔮.adicCompletion L) L') [FiniteDimensional (𝔮.adicCompletion L) ↥N]
    (K' : Type u) [Field K'] [Algebra (𝔭.adicCompletion K) K'] [IsSepClosure (𝔭.adicCompletion K) K']
    (Φ : Gal(L'/↥N) ≃* Gal(K'/𝔭.adicCompletion K)) (hΦ : Continuous ⇑Φ) :
    Nonempty (NK.LocalStructure.FiniteExtensionCorrespondence Φ) := by
  classical
  haveI : IsGalois (𝔮.adicCompletion L) L' := inferInstance
  haveI : IsGalois ↥N L' := inferInstance
  haveI : IsGalois (𝔭.adicCompletion K) K' := inferInstance
  have hbij : Function.Bijective (Φ : Gal(L'/↥N) → Gal(K'/𝔭.adicCompletion K)) := Φ.bijective
  have hclosed : IsClosedMap (Φ : Gal(L'/↥N) → Gal(K'/𝔭.adicCompletion K)) := hΦ.isClosedMap
  have hiso : IsHomeomorph (Φ : Gal(L'/↥N) → Gal(K'/𝔭.adicCompletion K)) :=
    ⟨hΦ, isOpenMap_of_isClosedMap_bijective hclosed hbij, hbij⟩
  have key : ∀ M : {M : IntermediateField ↥N L' // FiniteDimensional ↥N ↥M},
      ∃ L₂ : IntermediateField (𝔭.adicCompletion K) K',
        FiniteDimensional (𝔭.adicCompletion K) ↥L₂ ∧
        ((M.1).fixingSubgroup).map (Φ : Gal(L'/↥N) →* Gal(K'/𝔭.adicCompletion K)) =
          L₂.fixingSubgroup := by
    intro M
    haveI := M.2
    exact Submission.NeukirchUchida.exists_finite_fixingSubgroup_map (k₁ := ↥N) (K₁ := L')
      Φ hiso M.1
  choose level hlevel using key
  refine ⟨level, fun M => (hlevel M).1, ?_, fun M => (hlevel M).2.symm⟩
  intro M
  haveI := M.2
  have h1 : Module.finrank (𝔭.adicCompletion K) ↥(level M) =
      (level M).fixingSubgroup.index :=
    IntermediateField.finrank_eq_fixingSubgroup_index K' (level M)
  have h2 : (((M.1).fixingSubgroup).map (Φ : Gal(L'/↥N) →* Gal(K'/𝔭.adicCompletion K))).index =
      ((M.1).fixingSubgroup).index :=
    Subgroup.index_map_equiv (M.1).fixingSubgroup Φ
  rw [h1, ← (hlevel M).2, h2]
  exact (IntermediateField.finrank_eq_fixingSubgroup_index L' (M.1)).symm

end NK.LocalStructure.LocalNU
