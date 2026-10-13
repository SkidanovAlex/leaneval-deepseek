import Submission.Work.DSAM3.Basic

/-! # DSAM3: the AM3 node — transport of `ModSplit` along an almost retraction

Delivery for subproject DSAM3 (MIX subtree, `direct_summand`): the frozen interface
`DSMap.Mix.modSplit_of_retraction` (AM3 of `sources/dsmap/direct_summand_mix_design.md`),
proved sorry-free and axiom-clean as `Work.DSAM3.modSplit_of_retraction_proved`
(also exported under the requested name `DSMap.Mix.modSplit_of_retraction_proved`).

Mathematics: a `D`-linear retraction `σ : D' → D` of `D'` with `σ 1 = c'` and `σ(I·D') ⊆ I`
turns a splitting of `ε` over `D'` with value `algebraMap c` into a splitting over `D` with value
`c * c'`: push the `A`-linear form `t'` (`ModSplitA`, see `Basic.lean`) of the splitting forward
along the quotient map `D' ⧸ I·D' → D ⧸ I` induced by `σ`, then extend scalars back to `D`. -/

open scoped TensorProduct
open CategoryTheory

namespace Work.DSAM3

universe a

theorem modSplit_of_retraction_proved {A : Type a} [CommRing A]
    (P : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0)
    {D D' : Type a} [CommRing D] [CommRing D'] (ψ : A →+* D) [Algebra D D'] (I : Ideal D)
    (σ : D' →ₗ[D] D) (c c' : D)
    (hσI : ∀ x ∈ I.map (algebraMap D D'), σ x ∈ I) (hσ1 : σ 1 = c')
    (h : DSMap.Mix.ModSplit P ε ((algebraMap D D').comp ψ) (I.map (algebraMap D D'))
          (algebraMap D D' c)) :
    DSMap.Mix.ModSplit P ε ψ I (c * c') := by
  letI : Algebra A D := ψ.toAlgebra
  letI : Algebra A D' := ((algebraMap D D').comp ψ).toAlgebra
  haveI : IsScalarTower A D D' := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  have hA := (modSplit_iff_ModSplitA P ε ((algebraMap D D').comp ψ) (I.map (algebraMap D D'))
    (algebraMap D D' c)).mp h
  obtain ⟨t', ht'1, ht'2⟩ := hA
  -- the quotient map `D' ⧸ I·D' → D ⧸ I` induced by `σ`
  have hle : (I.map (algebraMap D D')).restrictScalars D ≤
      Submodule.comap σ (I : Submodule D D) := fun x hx => hσI x (by simpa using hx)
  set q : (D' ⧸ I.map (algebraMap D D')) →ₗ[D] (D ⧸ I) :=
    Submodule.mapQ ((I.map (algebraMap D D')).restrictScalars D) (I : Submodule D D) σ hle with hq
  have hq_apply : ∀ x : D', q (Ideal.Quotient.mk (I.map (algebraMap D D')) x) =
      Ideal.Quotient.mk I (σ x) := by
    intro x
    rw [← Ideal.Quotient.mk_eq_mk, ← Ideal.Quotient.mk_eq_mk (I := I) (σ x)]
    exact Submodule.mapQ_apply _ _ _ x
  -- the pushed-forward `A`-linear form
  refine (modSplit_iff_ModSplitA P ε ψ I (c * c')).mpr
    ⟨(LinearMap.restrictScalars A q).comp t', ?_, ?_⟩
  · rw [LinearMap.comp_assoc, ht'1, LinearMap.comp_zero]
  · have hσc : σ (algebraMap D D' c) = c * c' := by
      rw [show algebraMap D D' c = c • (1 : D') by
            rw [Algebra.smul_def, mul_one], map_smul, hσ1, smul_eq_mul]
    rw [LinearMap.comp_apply, LinearMap.restrictScalars_apply, ht'2, hq_apply, hσc]

end Work.DSAM3

namespace DSMap.Mix

universe a

/-- `DSMap.Mix.modSplit_of_retraction` (AM3), proved — same statement, under the requested name. -/
theorem modSplit_of_retraction_proved {A : Type a} [CommRing A]
    (P : CochainComplex (ModuleCat.{a} A) ℤ) (ε : ModuleCat.of A A ⟶ P.X 0)
    {D D' : Type a} [CommRing D] [CommRing D'] (ψ : A →+* D) [Algebra D D'] (I : Ideal D)
    (σ : D' →ₗ[D] D) (c c' : D)
    (hσI : ∀ x ∈ I.map (algebraMap D D'), σ x ∈ I) (hσ1 : σ 1 = c')
    (h : ModSplit P ε ((algebraMap D D').comp ψ) (I.map (algebraMap D D'))
          (algebraMap D D' c)) :
    ModSplit P ε ψ I (c * c') :=
  Work.DSAM3.modSplit_of_retraction_proved P ε ψ I σ c c' hσI hσ1 h

/-- The proved theorem has exactly the type of the frozen (sorried) `modSplit_of_retraction`. -/
example : @DSMap.Mix.modSplit_of_retraction_proved = @modSplit_of_retraction := rfl

end DSMap.Mix

/-- The same, for the `Work.DSAM3` copy. -/
example : @Work.DSAM3.modSplit_of_retraction_proved = @DSMap.Mix.modSplit_of_retraction := rfl
