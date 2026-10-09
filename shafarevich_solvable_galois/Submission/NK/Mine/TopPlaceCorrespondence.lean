import Submission.NK.PTorsionTop.All
import Submission.NK.Mine.exists_isHomeomorph_mulEquiv_sepClosure_of_decompositionGroup_map
import Submission.NK.Mine.PlaceCorrespondenceArithmetic
import Submission.NK.LocalInputs.Global
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The arithmetic fields of the place correspondence, with the corrected local inputs

`Submission/Work/Mine/PlaceCorrespondenceArithmetic.lean` proves the two arithmetic fields of the
place correspondence (`residueChar`, `localDegree`) from the (defective) bundle
`NK.LocalInputs.LocalGaloisInputs`.  This file redoes it with the **corrected** bundle
`NK.PTorsionTop.LocalGaloisInputsTop` of `Submission/Work/PTorsionTop/`, using

* `NK.PTorsionTop.residueChar_eq_of_decompositionGroupTop` for the residue characteristic (no
  continuity needed), and
* `NK.PTorsionTop.localDegree_eq_of_decompositionGroupTop` for the local degree, which needs the
  local isomorphism to be a **homeomorphism** — supplied here through the hypothesis `hψ` (and, when
  `NK.Mine.exists_isHomeomorph_mulEquiv_sepClosure_of_decompositionGroup_map` is available,
  discharged by it).
-/

namespace NK.Mine

open scoped Pointwise
open IsDedekindDomain.HeightOneSpectrum

universe u

variable {K₁ K₂ K₁' K₂' : Type u} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
  [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
  [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']

/-- The per-prime local arithmetic data in the `LocalFieldInputs` form, from the residue
characteristic. -/
private theorem localFieldInputsAtTop {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ}
    (hp : p.Prime)
    (hres : CharP (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) p) :
    NK.LocalInputs.LocalFieldInputs K 𝔭 p :=
  NK.LocalInputs.PowerQuotient.localFieldInputs_of_prime 𝔭 hp hres

/-- **The residue characteristic is preserved by the place correspondence**, from the corrected
local inputs (this half needs no continuity). -/
theorem residueChar_preserved_of_topInputs
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (h : Submission.NeukirchUchida.PreservesDecompositionGroups ϕ)
    (k₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ, p.Prime ∧
        NK.LocalInputs.LocalFieldInputs K₁ 𝔭 p ∧
        NK.PTorsionTop.LocalGaloisInputsTop K₁ 𝔭
          (SeparableClosure (𝔭.adicCompletion K₁)) p)
    (k₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ q : ℕ, q.Prime ∧
        NK.LocalInputs.LocalFieldInputs K₂ 𝔮 q ∧
        NK.PTorsionTop.LocalGaloisInputsTop K₂ 𝔮
          (SeparableClosure (𝔮.adicCompletion K₂)) q) :
    ∀ (A : NK.Reconstruct.FinitePlaceOf K₁ K₁') (ℓ : ℕ),
      CharP (NumberField.RingOfIntegers K₁ ⧸
          (Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal) ℓ →
        CharP (NumberField.RingOfIntegers K₂ ⧸
          (Submission.NeukirchUchida.primeOf
            (Submission.NeukirchUchida.placeMap ϕ h A).1
            (Submission.NeukirchUchida.placeMap ϕ h A).2).asIdeal) ℓ := by
  intro A ℓ hℓ
  set 𝔭 := Submission.NeukirchUchida.primeOf A.1 A.2 with h𝔭
  set B := Submission.NeukirchUchida.placeMap ϕ h A with hB
  set 𝔮 := Submission.NeukirchUchida.primeOf B.1 B.2 with h𝔮
  obtain ⟨p, hp, hF𝔭, hG𝔭⟩ := k₁ 𝔭
  obtain ⟨q, hq, hF𝔮, hG𝔮⟩ := k₂ 𝔮
  have hchar₁ : CharP (NumberField.RingOfIntegers K₁ ⧸ 𝔭.asIdeal) p :=
    (charP_residueField_iff 𝔭 p).mp hF𝔭.residue_char
  have hℓp : ℓ = p := CharP.eq (NumberField.RingOfIntegers K₁ ⧸ 𝔭.asIdeal) hℓ hchar₁
  have hAB : (NK.Mine.decompositionGroupOf K₁ K₁' A.1).map
      (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) = NK.Mine.decompositionGroupOf K₂ K₂' B.1 :=
    Submission.NeukirchUchida.placeMap_spec ϕ h A
  obtain ⟨ψ⟩ := NK.LocalInputs.Global.nonempty_mulEquiv_sepClosure_of_decompositionGroup_map
    𝔭 𝔮 A.1 B.1 (Submission.NeukirchUchida.primeOf_spec A.1 A.2)
    (Submission.NeukirchUchida.primeOf_spec B.1 B.2) ϕ hAB
  have hpq : p = q := NK.PTorsionTop.residueChar_eq_of_decompositionGroupTop
    𝔭 𝔮 A.1 B.1 (Submission.NeukirchUchida.primeOf_spec A.1 A.2)
    (Submission.NeukirchUchida.primeOf_spec B.1 B.2) ϕ hAB ψ hF𝔭 hG𝔭 hF𝔮 hG𝔮
  rw [hℓp, hpq]
  exact (charP_residueField_iff 𝔮 q).mp hF𝔮.residue_char

/-- **The absolute local degree is preserved by the place correspondence**, from the corrected local
inputs and the homeomorphy of the induced local isomorphism.

The homeomorphy of the induced local isomorphism is supplied by
`NK.Mine.exists_isHomeomorph_mulEquiv_sepClosure_of_decompositionGroup_map`. -/
theorem localDegree_preserved_of_topInputs
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (hϕ : IsHomeomorph ϕ)
    (h : Submission.NeukirchUchida.PreservesDecompositionGroups ϕ)
    (k₁ : ∀ (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₁)),
      ∃ p : ℕ, p.Prime ∧
        NK.LocalInputs.LocalFieldInputs K₁ 𝔭 p ∧
        NK.PTorsionTop.LocalGaloisInputsTop K₁ 𝔭
          (SeparableClosure (𝔭.adicCompletion K₁)) p)
    (k₂ : ∀ (𝔮 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K₂)),
      ∃ q : ℕ, q.Prime ∧
        NK.LocalInputs.LocalFieldInputs K₂ 𝔮 q ∧
        NK.PTorsionTop.LocalGaloisInputsTop K₂ 𝔮
          (SeparableClosure (𝔮.adicCompletion K₂)) q) :
    ∀ A : NK.Reconstruct.FinitePlaceOf K₁ K₁',
      ((Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal.inertiaDeg ℤ) *
          ((Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal.ramificationIdx ℤ) =
        ((Submission.NeukirchUchida.primeOf (Submission.NeukirchUchida.placeMap ϕ h A).1
            (Submission.NeukirchUchida.placeMap ϕ h A).2).asIdeal.inertiaDeg ℤ) *
          ((Submission.NeukirchUchida.primeOf (Submission.NeukirchUchida.placeMap ϕ h A).1
            (Submission.NeukirchUchida.placeMap ϕ h A).2).asIdeal.ramificationIdx ℤ) := by
  intro A
  set 𝔭 := Submission.NeukirchUchida.primeOf A.1 A.2 with h𝔭
  set B := Submission.NeukirchUchida.placeMap ϕ h A with hB
  set 𝔮 := Submission.NeukirchUchida.primeOf B.1 B.2 with h𝔮
  obtain ⟨p, hp, hF𝔭, hG𝔭⟩ := k₁ 𝔭
  obtain ⟨q, hq, hF𝔮, hG𝔮⟩ := k₂ 𝔮
  have hAB : (NK.Mine.decompositionGroupOf K₁ K₁' A.1).map
      (ϕ : Gal(K₁'/K₁) →* Gal(K₂'/K₂)) = NK.Mine.decompositionGroupOf K₂ K₂' B.1 :=
    Submission.NeukirchUchida.placeMap_spec ϕ h A
  obtain ⟨ψ, hψh⟩ := exists_isHomeomorph_mulEquiv_sepClosure_of_decompositionGroup_map
    𝔭 𝔮 A.1 B.1 (Submission.NeukirchUchida.primeOf_spec A.1 A.2)
    (Submission.NeukirchUchida.primeOf_spec B.1 B.2) ϕ hϕ hAB
  have hd : NK.LocalInputs.localDegree K₁ 𝔭 = NK.LocalInputs.localDegree K₂ 𝔮 :=
    NK.PTorsionTop.localDegree_eq_of_decompositionGroupTop
      𝔭 𝔮 A.1 B.1 (Submission.NeukirchUchida.primeOf_spec A.1 A.2)
      (Submission.NeukirchUchida.primeOf_spec B.1 B.2) ϕ hAB ψ hψh hF𝔭 hG𝔭 hF𝔮 hG𝔮
  rw [mul_comm ((Submission.NeukirchUchida.primeOf A.1 A.2).asIdeal.inertiaDeg ℤ),
      mul_comm ((Submission.NeukirchUchida.primeOf (Submission.NeukirchUchida.placeMap ϕ h A).1
        (Submission.NeukirchUchida.placeMap ϕ h A).2).asIdeal.inertiaDeg ℤ)]
  rw [h𝔭, h𝔮]
  rw [← NK.LocalInputs.Degree.localDegree_eq_ramificationIdx_mul_inertiaDeg 𝔭]
  rw [← NK.LocalInputs.Degree.localDegree_eq_ramificationIdx_mul_inertiaDeg 𝔮]
  exact hd

end NK.Mine
