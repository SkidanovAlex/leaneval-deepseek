import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Submission.NK.LocalReciprocityLubinTate.Unramified.Instance
import Submission.NK.LocalReciprocityLubinTate.Unramified.padicAlgebra_finiteDimensional_of_localField
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The norm index theorem at every finite abelian level, for a general local field

`NK.LocalArtin.NormIndex F (SeparableClosure F)` for a characteristic-zero nonarchimedean local
field `F`: at every finite (normal, hence abelian) level `L ≤ F^{ab}` of the maximal abelian
subextension of a separable closure of `F`, the norm group `N_{L/F} Lˣ` has index `[L : F]` in
`Fˣ`.

The mathematics is the local norm index theorem, which the workspace has proved for the *model*
case `F = Q.adicCompletion K` (the completion of a number field at a finite place) in
`NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion` — the full cohomological chain
(fundamental class, Tate's theorem, the Sylow reduction, the norm-transitivity assembly) is
available there with the base field specialised to `Q.adicCompletion K`.  What remains here is to
run that same chain with *base field* the given `F`, which is possible as soon as one knows that
`F` is a *finite* extension of the `p`-adic field `ℚ_[p]` (`p` = the residue characteristic):
`padicAlgebra_finiteDimensional_of_localField` supplies the `ℚ_[p]`-algebra structure and
the finite-dimensionality.

## Route

* `padicAlgebra_finiteDimensional_of_localField F` gives `p`, `[Fact p.Prime]`, an algebra structure
  `Algebra ℚ_[p] F` and `FiniteDimensional ℚ_[p] F`.
* Mathlib's `Rat.HeightOneSpectrum.adicCompletion.padicEquiv` transfers this to the model base
  `Q.adicCompletion ℚ` for the place `Q = primesEquiv.symm ⟨p, ·⟩` of `𝓞 ℚ`
  (`finiteDimensional_transport`), which is the shape required by the commons chain.
* At a level `L` the abelian local norm index theorem
  `Commons.NumberTheory.NumberField.Completion.abelian_local_norm_index_at_base` gives
  `#(Fˣ ⧸ N_{L/F} Lˣ) = #Gal(L/F)`, and `IsGalois.card_aut_eq_finrank` turns this into
  `[L : F]`; `Subgroup.index_eq_card` converts the index into the cardinality of the quotient.
-/

open IsDedekindDomain (HeightOneSpectrum)

set_option linter.style.haveILetI false

namespace NK.LocalReciprocityLubinTate.Unramified

universe u

/-- **The norm index theorem for a characteristic-zero nonarchimedean local field.** -/
theorem normIndex_of_localField (F : Type u) [Field F] [CharZero F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    NK.LocalArtin.NormIndex F (SeparableClosure F) := by
  obtain ⟨p, hp, hA, hFD⟩ := padicAlgebra_finiteDimensional_of_localField F
  letI : Fact p.Prime := hp
  letI : Algebra ℚ_[p] F := hA
  haveI : FiniteDimensional ℚ_[p] F := hFD
  -- the model base field `Q.adicCompletion ℚ` of `ℚ_[p]`
  let Q : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) :=
    Rat.HeightOneSpectrum.primesEquiv.symm ⟨p, hp.out⟩
  have hQ : Rat.HeightOneSpectrum.primesEquiv Q = ⟨p, hp.out⟩ := Equiv.apply_symm_apply _ _
  letI : Algebra ℚ (Q.adicCompletion ℚ) :=
    HeightOneSpectrum.instAlgebraAdicCompletion (NumberField.RingOfIntegers ℚ) ℚ Q
  have e : Q.adicCompletion ℚ ≃A[ℚ] ℚ_[p] := by
    have h := Rat.HeightOneSpectrum.adicCompletion.padicEquiv Q
    rw [hQ] at h
    exact h
  let ρ : Q.adicCompletion ℚ ≃+* ℚ_[p] := e.toRingEquiv
  letI : Algebra (Q.adicCompletion ℚ) F := RingHom.toAlgebra ((algebraMap ℚ_[p] F).comp ρ.toRingHom)
  have he : (algebraMap (Q.adicCompletion ℚ) F).comp ρ.symm.toRingHom = algebraMap ℚ_[p] F := by
    ext x
    show (algebraMap ℚ_[p] F) (ρ (ρ.symm x)) = (algebraMap ℚ_[p] F) x
    rw [RingEquiv.apply_symm_apply]
  haveI : FiniteDimensional (Q.adicCompletion ℚ) F :=
    Commons.NumberTheory.NumberField.Completion.finiteDimensional_transport (E := F) ρ.symm he
  intro L hfd hnorm
  haveI : FiniteDimensional F ↥L := hfd
  haveI : Normal F ↥L := hnorm
  haveI hgal : IsGalois F ↥L := NK.LocalCFT.NormGroup.instIsGaloisLevelOfMaxAbelian L
  have hcomm : ∀ σ τ : ↥L ≃ₐ[F] ↥L, σ * τ = τ * σ :=
    NK.LocalCFT.NormGroup.normGroup_eq_iff_commutative_gal L
  letI : Algebra (Q.adicCompletion ℚ) ↥L :=
    RingHom.toAlgebra ((algebraMap F ↥L).comp (algebraMap (Q.adicCompletion ℚ) F))
  haveI : IsScalarTower (Q.adicCompletion ℚ) F ↥L :=
    IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI : FiniteDimensional (Q.adicCompletion ℚ) ↥L :=
    FiniteDimensional.trans (Q.adicCompletion ℚ) F ↥L
  rw [Subgroup.index_eq_card]
  change Nat.card (Fˣ ⧸ MonoidHom.range (Units.map (Algebra.norm F : ↥L →* F)))
    = Module.finrank F ↥L
  rw [Commons.NumberTheory.NumberField.Completion.abelian_local_norm_index_at_base (K := ℚ) Q hcomm,
    IsGalois.card_aut_eq_finrank F ↥L]

end NK.LocalReciprocityLubinTate.Unramified
