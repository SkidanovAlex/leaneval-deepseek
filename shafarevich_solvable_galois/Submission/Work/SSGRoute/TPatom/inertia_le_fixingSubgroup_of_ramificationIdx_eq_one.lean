import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped NumberField

namespace Work.SSGRoute.TPatom

/-- **The inertia subgroup is contained in the fixing subgroup of an intermediate field which is
unramified at the prime below.**  Let `k ⊆ M` be a finite Galois extension of number fields,
`F` an intermediate field (not assumed Galois over `k`), `P` a nonzero prime of `𝓞 M`.  If the
ramification index of `P ∩ 𝓞 F` over `k` is `1`, then every inertia element of `P` in `Gal(M/k)`
fixes `F` pointwise.

Suggested ingredients (all in Mathlib): `AddSubgroup.inertia_map_subtype` gives
`Ideal.inertia G P ⊓ F.fixingSubgroup = map F.fixingSubgroup.subtype (Ideal.inertia ↥F.fixingSubgroup P)`;
`Ideal.inertiaEquiv` transfers `Ideal.inertia ↥F.fixingSubgroup P` to
`Ideal.inertia (M ≃ₐ[F] M) P` (using `IntermediateField.fixingSubgroupEquiv`);
`Ideal.card_inertia_eq_ramificationIdxIn` identifies the cardinalities with the ramification
indices `(P.under 𝓞k).ramificationIdx` and `(P.under 𝓞F).ramificationIdx` (via
`Ideal.ramificationIdxIn_eq_ramificationIdx`), and `Ideal.ramificationIdx_tower` with the
hypothesis `- = 1` shows these two cardinalities agree; two subgroups of equal finite cardinality,
one contained in the other, are equal. -/
theorem inertia_le_fixingSubgroup_of_ramificationIdx_eq_one {k M : Type} [Field k] [NumberField k]
    [Field M] [NumberField M] [Algebra k M] [FiniteDimensional k M] [IsGalois k M]
    (F : IntermediateField k M) [FiniteDimensional k F]
    (P : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers M))
    (hram : (P.asIdeal.under (NumberField.RingOfIntegers F)).ramificationIdx
      (NumberField.RingOfIntegers k) = 1) :
    Ideal.inertia (M ≃ₐ[k] M) P.asIdeal ≤ F.fixingSubgroup := by
  -- ### Set-up: the relevant Galois group structures
  have : IsGaloisGroup (M ≃ₐ[k] M) k M := inferInstance
  have : IsGaloisGroup (M ≃ₐ[k] M) (𝓞 k) (𝓞 M) := inferInstance
  have : NumberField ↥F := inferInstance
  have : IsGalois ↥F M := inferInstance
  have : FiniteDimensional ↥F M := inferInstance
  have : IsGaloisGroup (M ≃ₐ[↥F] M) ↥F M := inferInstance
  have : IsGaloisGroup (M ≃ₐ[↥F] M) (𝓞 ↥F) (𝓞 M) := inferInstance
  have : Finite (M ≃ₐ[k] M) := inferInstance

  -- ### The cardinality of the inertia subgroup of `P` over `k` is the ramification index
  have htop : Nat.card ↥(Ideal.inertia (M ≃ₐ[k] M) P.asIdeal)
      = P.asIdeal.ramificationIdx (𝓞 k) := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (P.asIdeal.under (𝓞 k)) P.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx (P.asIdeal.under (𝓞 k)) P.asIdeal (M ≃ₐ[k] M)]

  -- ### The cardinality of the inertia subgroup of `P` over `F` is the ramification index
  have hbot : Nat.card ↥(Ideal.inertia (M ≃ₐ[↥F] M) P.asIdeal)
      = P.asIdeal.ramificationIdx (𝓞 ↥F) := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (P.asIdeal.under (𝓞 ↥F)) P.asIdeal,
      Ideal.ramificationIdxIn_eq_ramificationIdx (P.asIdeal.under (𝓞 ↥F)) P.asIdeal (M ≃ₐ[↥F] M)]

  -- ### The two ramification indices agree, by the tower formula and the hypothesis
  have hramEq : P.asIdeal.ramificationIdx (𝓞 k) = P.asIdeal.ramificationIdx (𝓞 ↥F) := by
    rw [Ideal.ramificationIdx_tower (P.asIdeal.under (𝓞 ↥F)) P.asIdeal, hram, one_mul]

  -- ### Transferring the inertia subgroup of `Gal(M/k)` to `Gal(M/F)`
  have hcardIF : Nat.card ↥(Ideal.inertia ↥F.fixingSubgroup P.asIdeal)
      = Nat.card ↥(Ideal.inertia (M ≃ₐ[↥F] M) P.asIdeal) :=
    Nat.card_congr
      (Ideal.inertiaEquiv P.asIdeal (IntermediateField.fixingSubgroupEquiv F) fun _ _ ↦
        Subtype.ext rfl).toEquiv

  -- ### The intersection with the fixing subgroup as the image of the subgroup-level inertia
  have hmap : (Ideal.inertia ↥F.fixingSubgroup P.asIdeal).map F.fixingSubgroup.subtype
      = Ideal.inertia (M ≃ₐ[k] M) P.asIdeal ⊓ F.fixingSubgroup :=
    AddSubgroup.inertia_map_subtype _ _

  have hcardmap :
      Nat.card ↥((Ideal.inertia ↥F.fixingSubgroup P.asIdeal).map F.fixingSubgroup.subtype)
        = Nat.card ↥(Ideal.inertia ↥F.fixingSubgroup P.asIdeal) :=
    Subgroup.card_map_of_injective Subtype.coe_injective

  -- ### Hence `I ⊓ fixingSubgroup F` has the same cardinality as `I`
  have hfin : Nat.card ↥(Ideal.inertia (M ≃ₐ[k] M) P.asIdeal ⊓ F.fixingSubgroup)
      = Nat.card ↥(Ideal.inertia (M ≃ₐ[k] M) P.asIdeal) := by
    rw [← hmap, hcardmap, hcardIF, hbot, ← hramEq, htop]

  -- ### Two subgroups of equal finite cardinality, one inside the other, are equal
  have hEq : Ideal.inertia (M ≃ₐ[k] M) P.asIdeal ⊓ F.fixingSubgroup
      = Ideal.inertia (M ≃ₐ[k] M) P.asIdeal :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq hfin.symm)

  rw [← hEq]
  exact inf_le_right

end Work.SSGRoute.TPatom
