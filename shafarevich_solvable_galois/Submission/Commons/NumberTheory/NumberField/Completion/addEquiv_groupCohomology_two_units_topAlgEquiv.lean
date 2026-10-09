import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.NumberTheory.NumberField.Completion

open Additive

set_option linter.unusedSimpArgs false

section Helpers

variable {F : Type} [Field F] {E : Type} [Field E] {E' : Type} [Field E']
  [Algebra F E] [Algebra F E']

/-- The additive equivalence of unit groups induced by an `F`-algebra isomorphism `ψ : E ≃ₐ[F] E'`.

It is the additive version of the multiplicative equivalence `Units.mapEquiv ψ`. -/
noncomputable def unitsAddEquiv (ψ : E ≃ₐ[F] E') : Additive Eˣ ≃+ Additive E'ˣ :=
  (Units.mapEquiv ψ.toMulEquiv).toAdditive

lemma unitsMapEquiv_conj (ψ : E ≃ₐ[F] E') (g : E ≃ₐ[F] E) (u : Eˣ) :
    (Units.mapEquiv ψ.toMulEquiv) (g • u) =
      (AlgEquiv.autCongr ψ g) • (Units.mapEquiv ψ.toMulEquiv u) := by
  ext
  simp only [Units.coe_mapEquiv, Units.coe_smul, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
    AlgEquiv.smul_def]
  change ψ (g (u : E)) = ψ (g (ψ.symm (ψ (u : E))))
  rw [AlgEquiv.symm_apply_apply]

lemma unitsAddEquiv_conj (ψ : E ≃ₐ[F] E') (g : E ≃ₐ[F] E) (u : Additive Eˣ) :
    (unitsAddEquiv ψ) ((Rep.ofAlgebraAutOnUnits F E).ρ g u) =
      (Rep.ofAlgebraAutOnUnits F E').ρ (AlgEquiv.autCongr ψ g) ((unitsAddEquiv ψ) u) := by
  apply Additive.toMul.injective
  rw [show (Rep.ofAlgebraAutOnUnits F E).ρ g u = Additive.ofMul (g • u.toMul) from rfl,
    show (Rep.ofAlgebraAutOnUnits F E').ρ (AlgEquiv.autCongr ψ g) ((unitsAddEquiv ψ) u) =
      Additive.ofMul ((AlgEquiv.autCongr ψ g) • ((unitsAddEquiv ψ) u).toMul) from rfl]
  show (Units.mapEquiv ψ.toMulEquiv) (g • u.toMul) =
    (AlgEquiv.autCongr ψ g) • (Units.mapEquiv ψ.toMulEquiv u.toMul)
  exact unitsMapEquiv_conj ψ g u.toMul

end Helpers

/-- **Invariance of `H²` of the units representation under a base-field-mapping algebra
isomorphism.** An `F`-algebra isomorphism `ψ : E ≃ₐ[F] E'` conjugates the automorphism group
`E ≃ₐ[F] E` to `E' ≃ₐ[F] E'` and transports the units representation accordingly, hence induces
an additive equivalence of the second group cohomology groups. -/
theorem addEquiv_groupCohomology_two_units_topAlgEquiv {F : Type} [Field F] {E : Type} [Field E]
    {E' : Type} [Field E'] [Algebra F E] [Algebra F E'] (ψ : E ≃ₐ[F] E') :
    Nonempty (groupCohomology (Rep.ofAlgebraAutOnUnits F E) 2 ≃+
      groupCohomology (Rep.ofAlgebraAutOnUnits F E') 2) := by
  refine ⟨(groupCohomology.mapIso
    (A := Rep.ofAlgebraAutOnUnits F E') (B := Rep.ofAlgebraAutOnUnits F E)
    (AlgEquiv.autCongr ψ)
    ((unitsAddEquiv ψ).toLinearEquiv (fun c x => map_zsmul _ c x)) ?_ 2
    ).toLinearEquiv.toAddEquiv⟩
  intro g
  apply LinearMap.ext
  intro u
  exact unitsAddEquiv_conj ψ g u

end Commons.NumberTheory.NumberField.Completion