import Mathlib
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.Defs
import Submission.NK.GlobalCFTdeep.SecondInequality.finrank_kummerAdjoin
import Submission.NK.GlobalCFTdeep.Herbrand.SIdeles
import Submission.NK.GlobalCFTdeep.Herbrand.TUnitsRank
import Submission.NK.GlobalCFTdeep.Herbrand.index_normGroup_completion_eq_finrank
import Submission.NK.GlobalCFTdeep.SecondInequality.KummerCase.no_isReal_of_isPrimitiveRoot_ne_two
import Submission.Commons.NumberTheory.NumberField.numberField_of_intermediateField
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Kummer `S`-field of the `S`-units

Let `K` be a number field containing a primitive `p`-th root of unity `ζ` (`p` prime), `S` a
finite set of places of `K`, and `Ω` a separable closure of `K`.  This file defines the field

`kummerSUnitField K Ω p S = K(U(S)^{1/p}) ⊆ Ω`,

the subfield generated over `K` by the `p`-th roots of the `S`-units `U(S) = TUnits S`.  It is the
maximal abelian extension of `K` of exponent dividing `p` which is unramified outside `S`; its
degree over `K` is `p ^ S.card` (`finrank_kummerSUnitField`).

## Main definitions

* `NK.NUV2.ArtinBridge.kummerSUnitField` — the field `K(U(S)^{1/p})`.

## Main results

* `kummerSUnitField_eq_kummerAdjoin` — it is `kummerAdjoin p (U(S) ⊔ Kˣ^p)`;
* `isMulCommutative_algEquiv` / `pow_algEquiv_eq_one` — the Galois group of `K(U(S)^{1/p})/K` is
  abelian of exponent dividing `p` (the Kummer pairing is injective);
* instances: `Field`, `NumberField`, `FiniteDimensional`, `IsGalois`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain
open IntermediateField Polynomial

noncomputable section

namespace NK.NUV2.ArtinBridge

open NK.GlobalCFT
open NK.GlobalCFTdeep.SecondInequality (kummerAdjoin kummerRootSet)

variable {K : Type} [Field K] [NumberField K] {Ω : Type*} [Field Ω] [Algebra K Ω]

/-- The subgroup `U(S) · Kˣ^p ≤ Kˣ` of the `S`-units together with the `p`-th powers. -/
def sUnitKummerGroup (p : ℕ) (S : Finset (Place K)) : Subgroup Kˣ :=
  NK.GlobalCFTdeep.TUnits (L := K) (S : Set (Place K)) ⊔ NK.LocalAnabelian.powSubgroup p K

/-- **The Kummer `S`-field** `K(U(S)^{1/p})`: the subfield of `Ω` generated over `K` by the
`p`-th roots of the `S`-units. -/
noncomputable abbrev kummerSUnitField (K : Type) [Field K] [NumberField K] (Ω : Type*)
    [Field Ω] [Algebra K Ω] (p : ℕ) (S : Finset (Place K)) : IntermediateField K Ω :=
  kummerAdjoin (K' := Ω) p (sUnitKummerGroup (K := K) p S)

/-- The Kummer `S`-field of `K` inside a separable closure of `K`. -/
noncomputable abbrev kummerSUnitFieldClosure (K : Type) [Field K] [NumberField K]
    (p : ℕ) (S : Finset (Place K)) : IntermediateField K (SeparableClosure K) :=
  kummerSUnitField K (SeparableClosure K) p S

variable (p : ℕ) (S : Finset (Place K))

theorem kummerSUnitField_eq_kummerAdjoin :
    kummerSUnitField K Ω p S = kummerAdjoin (K' := Ω) p (sUnitKummerGroup (K := K) p S) := rfl

/-- The roots of the `S`-units generate `K(U(S)^{1/p})`. -/
theorem kummerSUnitField_eq_adjoin_TUnits :
    kummerSUnitField K Ω p S
      = IntermediateField.adjoin K {x : Ω |
          ∃ a ∈ NK.GlobalCFTdeep.TUnits (L := K) (S : Set (Place K)), x ^ p = algebraMap K Ω (a : K)} := by
  have h1 : kummerSUnitField K Ω p S
      = kummerAdjoin (K' := Ω) p (NK.GlobalCFTdeep.TUnits (L := K) (S : Set (Place K))
          ⊔ NK.LocalAnabelian.powSubgroup p K) := rfl
  rw [h1, NK.GlobalCFTdeep.SecondInequality.kummerAdjoin_sup_powSubgroup]
  rfl

/-- A `p`-th root of an `S`-unit lies in the Kummer `S`-field. -/
theorem mem_kummerSUnitField_of_pow_eq {x : Ω} {a : Kˣ}
    (ha : a ∈ NK.GlobalCFTdeep.TUnits (L := K) (S : Set (Place K)))
    (hx : x ^ p = algebraMap K Ω (a : K)) : x ∈ kummerSUnitField K Ω p S := by
  rw [kummerSUnitField_eq_adjoin_TUnits]
  exact IntermediateField.subset_adjoin K _ (Set.mem_ofPred.mpr ⟨a, ha, hx⟩)


/-! ### The `S`-units modulo `p`-th powers -/

section Units

variable {p : ℕ}

/-- An `S`-unit which is a `p`-th power in `Kˣ` is a `p`-th power of an `S`-unit: the `p`-th root
of a local unit is a local unit (its valuation is `1/p` of the valuation of the root). -/
theorem tUnits_inf_powSubgroup {p : ℕ} (hp : p.Prime) (S : Finset (Place K)) :
    (NK.GlobalCFTdeep.TUnits (L := K) (S : Set (Place K))
        ⊓ NK.LocalAnabelian.powSubgroup p K)
      = Subgroup.map (powMonoidHom p)
          (NK.GlobalCFTdeep.TUnits (L := K) (S : Set (Place K))) := by
  refine le_antisymm ?_ ?_
  · intro u hu
    rw [Subgroup.mem_inf] at hu
    obtain ⟨huT, hv⟩ := hu
    obtain ⟨v, hv'⟩ := MonoidHom.mem_range.mp hv
    refine Subgroup.mem_map.mpr ⟨v, ?_, hv'⟩
    rw [NK.GlobalCFTdeep.mem_TUnits_iff_expUnit] at huT ⊢
    intro q hq
    have h := huT q hq
    rw [← hv', powMonoidHom_apply, show v ^ p = v ^ (p : ℤ) by rw [zpow_natCast],
      NK.GlobalCFTdeep.expUnit_zpow] at h
    exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hp.ne_zero)
  · rw [Subgroup.map_le_iff_le_comap]
    intro u hu
    rw [Subgroup.mem_comap, powMonoidHom_apply]
    exact ⟨pow_mem hu p, ⟨u, rfl⟩⟩

end Units

/-! ### The Galois group of the Kummer `S`-field -/

section Galois

variable [IsSepClosure K Ω]

theorem isGalois_kummerSUnitField {p : ℕ} (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    IsGalois K ↥(kummerSUnitField K Ω p S) :=
  NK.GlobalCFTdeep.SecondInequality.isGalois_kummerAdjoin (K' := Ω) hp hζ _

/-- The Galois group of `K(U(S)^{1/p})/K` is commutative: the Kummer pairing embeds it into
`U(S)·Kˣ^p/Kˣ^p → K(U(S)^{1/p})ˣ`, and the latter is a commutative group. -/
theorem isMulCommutative_kummerSUnitField {p : ℕ} (hp : p.Prime) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) :
    IsMulCommutative (↥(kummerSUnitField K Ω p S) ≃ₐ[K] ↥(kummerSUnitField K Ω p S)) := by
  have hT : NK.LocalAnabelian.powSubgroup p K ≤ sUnitKummerGroup (K := K) p S := le_sup_right
  have hinj : Function.Injective
      ⇑(NK.GlobalCFTdeep.SecondInequality.kummerPairingQuot (K' := Ω) hp hζ
        (sUnitKummerGroup (K := K) p S) hT) :=
    NK.GlobalCFTdeep.SecondInequality.kummerPairingQuot_injective (K' := Ω) hp hζ _ hT
  refine IsMulCommutative.of_comm (fun σ τ => hinj ?_)
  refine MonoidHom.ext fun v => ?_
  refine Quotient.inductionOn v fun c => ?_
  simp only [map_mul, MonoidHom.mul_apply,
    NK.GlobalCFTdeep.SecondInequality.kummerPairingQuot_apply_mk]
  exact mul_comm _ _

/-- The Galois group of `K(U(S)^{1/p})/K` has exponent dividing `p`. -/
theorem pow_algEquiv_eq_one_kummerSUnitField {p : ℕ} (hp : p.Prime) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p)
    (σ : ↥(kummerSUnitField K Ω p S) ≃ₐ[K] ↥(kummerSUnitField K Ω p S)) : σ ^ p = 1 := by
  have hT : NK.LocalAnabelian.powSubgroup p K ≤ sUnitKummerGroup (K := K) p S := le_sup_right
  have hinj : Function.Injective
      ⇑(NK.GlobalCFTdeep.SecondInequality.kummerPairingQuot (K' := Ω) hp hζ
        (sUnitKummerGroup (K := K) p S) hT) :=
    NK.GlobalCFTdeep.SecondInequality.kummerPairingQuot_injective (K' := Ω) hp hζ _ hT
  refine hinj ?_
  rw [map_pow, map_one]
  refine MonoidHom.ext fun v => ?_
  rw [MonoidHom.pow_apply, MonoidHom.one_apply]
  have hv : v ^ p = 1 := by
    refine Quotient.inductionOn v (fun c => ?_)
    change ((QuotientGroup.mk' ((NK.LocalAnabelian.powSubgroup p K).subgroupOf
      (sUnitKummerGroup (K := K) p S))) c) ^ p = 1
    rw [← map_pow]
    change (QuotientGroup.mk (c ^ p) : ↥(sUnitKummerGroup (K := K) p S) ⧸
      (NK.LocalAnabelian.powSubgroup p K).subgroupOf (sUnitKummerGroup (K := K) p S)) = 1
    rw [QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr
      (MonoidHom.mem_range.mpr ⟨(c : Kˣ), by rw [powMonoidHom_apply]; rfl⟩)
  calc (NK.GlobalCFTdeep.SecondInequality.kummerPairingQuot (K' := Ω) hp hζ
        (sUnitKummerGroup (K := K) p S) hT σ) v ^ p
      = (NK.GlobalCFTdeep.SecondInequality.kummerPairingQuot (K' := Ω) hp hζ
        (sUnitKummerGroup (K := K) p S) hT σ) (v ^ p) := by rw [map_pow]
    _ = 1 := by rw [hv, map_one]

end Galois


end NK.NUV2.ArtinBridge
