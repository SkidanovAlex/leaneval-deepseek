import Mathlib
import Submission.NK.CFTLib.ArtinReciprocityIdeal.exists_algEquiv_zeta_pow
import Submission.NK.CFTLib.ARL.disjoint_restrictScalars_adjoin_zeta
import Submission.NK.CFTLib.ArtinReciprocityIdeal.AuxFamily.autToPow_surjective_of_not_dvd_discr
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.CFTLib.ArtinReciprocityIdeal

/-- **The cyclotomic character of `K(ζ_M)/K` is surjective, in unit form.**

Let `K` be a number field, `M > 0` such that no prime divisor of `M` divides `disc K`, let `Ω` be a
field with `Algebra K Ω` and `ζ ∈ Ω` a primitive `M`-th root of unity.  Then the
`K`-automorphism group of `K⟮ζ⟯` acts on `ζ` through every unit `u` of `ℤ/M`: there is `σ` with
`σ ζ = ζ ^ u.val`.

This is `NK.CFTLib.ArtinReciprocityIdeal.AuxFamily.autToPow_surjective_of_not_dvd_discr`
(surjectivity of `IsPrimitiveRoot.autToPow` onto `(ℤ/M)ˣ`, obtained by the degree computation
`[K(ζ_M) : K] = φ(M)`), read through the canonical representative `u.val` of a unit, which is
coprime to `M` (`ZMod.val_coe_unit_coprime`). -/
theorem exists_algEquiv_zeta_pow_gen {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (M : ℕ) [NeZero M]
    (hM : ∀ p : ℕ, p.Prime → p ∣ M → ¬ p ∣ (NumberField.discr K).natAbs)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ M) (u : (ZMod M)ˣ) :
    ∃ σ : (IntermediateField.adjoin K ({ζ} : Set Ω)) ≃ₐ[K]
        (IntermediateField.adjoin K ({ζ} : Set Ω)),
      σ ⟨ζ, IntermediateField.mem_adjoin_simple_self K ζ⟩ =
        (⟨ζ, IntermediateField.mem_adjoin_simple_self K ζ⟩ :
          ↥(IntermediateField.adjoin K ({ζ} : Set Ω))) ^ (u : ZMod M).val :=
  NK.CFTLib.ArtinReciprocityIdeal.AuxFamily.autToPow_surjective_of_not_dvd_discr
    M (NeZero.ne M) ζ hζ hM (u : ZMod M).val (ZMod.val_coe_unit_coprime u)

end NK.CFTLib.ArtinReciprocityIdeal
