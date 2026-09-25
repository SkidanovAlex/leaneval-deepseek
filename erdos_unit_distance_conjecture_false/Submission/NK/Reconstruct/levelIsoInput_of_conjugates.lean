import Mathlib
import Submission.NK.Reconstruct.Transport
import Submission.NK.Reconstruct.LevelMap
import Submission.NK.ReconstructField.LevelCandidate
import Submission.NK.ReconstructField.reconstructionInput_imp_levelPrimeIdentification

/-!
# The level-wise input of the reconstruction from a realizing field isomorphism

The chapter `NK.ReconstructField` reduces the Neukirch–Uchida theorem to the *σ-free* level-wise
input `NK.ReconstructField.LevelIsoInput ϕ hϕ`: for every finite level `L ⊆ K₁'` the fields `L`
and `levelMap ϕ L` are isomorphic — where `levelMap ϕ L` is the image of `L` under the
correspondence of levels induced by the isomorphism `ϕ` of absolute Galois groups.

Here we verify the consistency of that input with the *converse* direction of the theorem: whenever
`σ : K₂' ≃+* K₁'` maps the embedded copy of `K₂` onto the embedded copy of `K₁` and *realizes* `ϕ`
by conjugation, i.e. `ϕ g = σ⁻¹ ∘ g ∘ σ` (equivalently `(ϕ g) y = σ⁻¹ (g (σ y))`), the two level
correspondences are inverse to each other and the required level isomorphisms are simply the
restrictions of `σ⁻¹`.

The mathematical content is the purely Galois-theoretic computation

`σ(Fix(ϕ Gal(K₁'/L))) = Fix(Gal(K₁'/L)) = L`,

the second equality being the Galois correspondence `InfiniteGalois.fixedField_fixingSubgroup`.
No finiteness hypothesis on `L` is needed for the identification of the levels themselves.
-/

namespace NK.Reconstruct

set_option linter.unusedSectionVars false

open scoped Pointwise

variable {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- **The action of the conjugate `ϕ g` on a point**, in terms of `σ`:  if `ϕ` is realized by
conjugation by `σ⁻¹` (i.e. `(ϕ g) y = σ⁻¹ (g (σ y))`), then `(ϕ g) (σ⁻¹ x) = σ⁻¹ (g x)`. -/
theorem apply_symm_eq_symm_apply {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} {σ : K₂' ≃+* K₁'}
    (hconj : ∀ g : Gal(K₁'/K₁), (ϕ g).toRingEquiv = σ.trans (g.toRingEquiv.trans σ.symm))
    (g : Gal(K₁'/K₁)) (x : K₁') : (ϕ g) (σ.symm x) = σ.symm (g x) := by
  have h : (σ.trans (g.toRingEquiv.trans σ.symm)) (σ.symm x) = σ.symm (g x) := by
    simp [RingEquiv.trans_apply, σ.apply_symm_apply]
  rw [← h, ← hconj g]
  exact (congrFun (AlgEquiv.coe_ringEquiv (ϕ g)) (σ.symm x)).symm

/-- **The two level correspondences are inverse to each other.**  If `σ` maps the base fields onto
each other and realizes `ϕ` by conjugation, then the level of `K₁'` corresponding to `levelMap ϕ L`
under `σ` is `L` itself:

`sigmaLevel σ hσ (levelMap ϕ L) = {x | σ⁻¹ x ∈ Fix(ϕ Gal(K₁'/L))} = Fix(Gal(K₁'/L)) = L`.

The last equality is the Galois correspondence for the (infinite) Galois extension `K₁'/K₁`,
`InfiniteGalois.fixedField_fixingSubgroup`; no finiteness of `L` is required. -/
theorem sigmaLevel_levelMap_eq_of_conjugates {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} {σ : K₂' ≃+* K₁'}
    (hσ : Submission.NeukirchUchida.MapsBase (algebraMap K₁ K₁') (algebraMap K₂ K₂') σ)
    (hconj : ∀ g : Gal(K₁'/K₁), (ϕ g).toRingEquiv = σ.trans (g.toRingEquiv.trans σ.symm))
    (L : IntermediateField K₁ K₁') : sigmaLevel σ hσ (levelMap ϕ L) = L := by
  ext x
  rw [mem_sigmaLevel, mem_levelMap_iff]
  -- the fixed points of `Gal(K₁'/L)` are exactly the points of `L`
  have hmem : x ∈ L ↔ ∀ f, f ∈ L.fixingSubgroup → f x = x := by
    conv_lhs => rw [← InfiniteGalois.fixedField_fixingSubgroup L]
    exact IntermediateField.mem_fixedField_iff L.fixingSubgroup x
  rw [hmem]
  constructor
  · intro hx f hf
    have hf' : ∀ y ∈ L, f y = y := (IntermediateField.mem_fixingSubgroup_iff L f).mp hf
    have h1 : (ϕ f) (σ.symm x) = σ.symm x := hx f (fun y => hf' y y.2)
    rw [apply_symm_eq_symm_apply hconj f x] at h1
    exact σ.symm.injective h1
  · intro hx g hg
    have hg' : g ∈ L.fixingSubgroup :=
      (IntermediateField.mem_fixingSubgroup_iff L g).mpr (fun y hy => hg ⟨y, hy⟩)
    rw [apply_symm_eq_symm_apply hconj g x, hx g hg']

theorem levelIsoInput_of_conjugates {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂'] [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂'] [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂'] {ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)} (hϕ : IsHomeomorph ϕ) (σ : K₂' ≃+* K₁') (h : Submission.NeukirchUchida.Conjugates σ ϕ) : NK.ReconstructField.LevelIsoInput ϕ hϕ := by
  intro L _
  obtain ⟨hσ, hconj⟩ := h
  exact ⟨NK.ReconstructField.levelEquivOfSigma hσ L (levelMap ϕ L)
    (sigmaLevel_levelMap_eq_of_conjugates hσ hconj L)⟩

end NK.Reconstruct
