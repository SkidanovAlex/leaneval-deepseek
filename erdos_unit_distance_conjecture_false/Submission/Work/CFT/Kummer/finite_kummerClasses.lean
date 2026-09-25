import Mathlib
import Submission.Work.CFT.Kummer.Defs
import Submission.Work.CFT.Kummer.finrank_kummerClasses_empty

/-!
# Finiteness of `V_S/K^{×p}` as an `𝔽_p`-module

For a number field `K`, a prime `p` and a finite set `S` of finite places, the Kummer class group
`V_S/K^{×p}` (`Work.CFT.Kummer.kummerClasses K p S`) is a finite `𝔽_p`-module.

The proof is a comparison with the case `S = ∅`.  The inclusion `V_S ↪ V_∅` of Selmer groups
(the local conditions at places of `S` are simply dropped) induces a map
`V_S/K^{×p} → V_∅/K^{×p}` which is injective, since an element of `V_S` that becomes a `p`-th
power in `V_∅` was already one in `V_S`.  It therefore suffices to know that `V_∅/K^{×p}` is
finite; this is extracted from the exact sequence

`0 → 𝒪_Kˣ/(𝒪_Kˣ)^p → V_∅/K^{×p} → Cl_K[p] → 0`

of `Work.CFT.Kummer.finrank_kummerClasses_empty`: both `𝒪_Kˣ/(𝒪_Kˣ)^p` (Dirichlet's unit
theorem) and `Cl_K[p]` (finiteness of the class number) are finite.

## Main result

* `Work.CFT.Kummer.finite_kummerClasses`.
-/

open scoped nonZeroDivisors
open NumberField

noncomputable section

set_option linter.style.haveILetI false

attribute [local instance] Classical.propDecidable

namespace Work.CFT.Kummer

/-! ## The inclusion `V_S ↪ V_∅` and the induced map on Kummer classes -/

/-- `V_S ≤ V_∅`: the local conditions at the places of `S` are simply dropped. -/
theorem selmerGroupAt_le_empty (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :
    selmerGroupAt K p S ≤ selmerGroupAt K p ∅ := by
  intro x hx
  exact ⟨hx.1, fun v hv => (Finset.notMem_empty v hv).elim⟩

/-- The side condition for `QuotientGroup.map`: an element of `V_S` which is a `p`-th power in
`Kˣ` maps to an element of `V_∅` which is a `p`-th power in `Kˣ`. -/
theorem comap_le_comap_inclusion (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :
    (pthPowerSubgroup Kˣ p).comap (selmerGroupAt K p S).subtype ≤
      Subgroup.comap (Subgroup.inclusion (selmerGroupAt_le_empty K p S))
        ((pthPowerSubgroup Kˣ p).comap (selmerGroupAt K p ∅).subtype) := by
  intro x hx
  rw [Subgroup.mem_comap] at hx
  rw [Subgroup.mem_comap]
  rw [Subgroup.mem_comap]
  change (((Subgroup.inclusion (selmerGroupAt_le_empty K p S)) x :
    ↥(selmerGroupAt K p ∅)) : Kˣ) ∈ pthPowerSubgroup Kˣ p
  rw [Subgroup.coe_inclusion]
  exact hx

/-- The comparison map `V_S/K^{×p} → V_∅/K^{×p}` induced by the inclusion `V_S ↪ V_∅`. -/
noncomputable def kummerClassesMap (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :
    (selmerGroupAt K p S ⧸ (pthPowerSubgroup Kˣ p).comap (selmerGroupAt K p S).subtype) →*
      (selmerGroupAt K p ∅ ⧸ (pthPowerSubgroup Kˣ p).comap (selmerGroupAt K p ∅).subtype) :=
  QuotientGroup.map _ _ (Subgroup.inclusion (selmerGroupAt_le_empty K p S))
    (comap_le_comap_inclusion K p S)

/-- The comparison map `V_S/K^{×p} → V_∅/K^{×p}` is injective: an element of `V_S` which becomes
a `p`-th power in `V_∅` is already a `p`-th power in `Kˣ`. -/
theorem kummerClassesMap_injective (K : Type*) [Field K] [NumberField K] (p : ℕ)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :
    Function.Injective (kummerClassesMap K p S) := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro q hq
  rw [MonoidHom.mem_ker] at hq
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q
  rw [kummerClassesMap, QuotientGroup.mk'_apply, QuotientGroup.map_mk] at hq
  rw [QuotientGroup.eq_one_iff] at hq
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hq

/-! ## Finiteness of `V_∅/K^{×p}` -/

/-- `V_∅/K^{×p}` is finite: it sits in the exact sequence
`0 → 𝒪_Kˣ/(𝒪_Kˣ)^p → V_∅/K^{×p} → Cl_K[p] → 0`, whose outer terms are finite. -/
theorem finite_kummerClasses_empty (K : Type*) [Field K] [NumberField K] (p : ℕ) (hp : p.Prime) :
    Finite (selmerGroupAt K p ∅ ⧸ (pthPowerSubgroup Kˣ p).comap (selmerGroupAt K p ∅).subtype) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact p.Prime := ⟨hp⟩
  -- `𝒪_Kˣ/(𝒪_Kˣ)^p` has `p ^ (rank K + δ_{K,p})` elements
  have hcardB : Nat.card (KummerB K p) = p ^ (NumberField.Units.rank K + deltaK K p) :=
    card_units_quotient_pthPower K p hp
  -- counting the exact sequence: `V_∅/K^{×p}` and `Cl_K[p] × 𝒪_Kˣ/(𝒪_Kˣ)^p` have equal cardinality
  have hcardQ : Nat.card (KummerQ K p) = Nat.card ↥(classGroupP K p) * Nat.card (KummerB K p) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (kummerToClassGroup K p hp).ker
    have h2 : Nat.card (KummerQ K p ⧸ (kummerToClassGroup K p hp).ker) =
        Nat.card ↥(classGroupP K p) := by
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange (kummerToClassGroup K p hp)).toEquiv,
        MonoidHom.range_eq_top.mpr (kummerToClassGroup_surjective K p hp)]
      exact Nat.card_congr (Subgroup.topEquiv).toEquiv
    have h3 : Nat.card ↥((kummerToClassGroup K p hp).ker) = Nat.card (KummerB K p) :=
      (Nat.card_congr (unitsEquivKer K p hp)).symm
    rw [h1, h2, h3]
  -- both factors are nonzero, hence `V_∅/K^{×p}` is a finite type
  have hne : Nat.card (KummerQ K p) ≠ 0 := by
    rw [hcardQ, hcardB]
    exact mul_ne_zero (ne_of_gt Nat.card_pos) (pow_ne_zero _ hp.ne_zero)
  exact Nat.finite_of_card_ne_zero hne

/-! ## The main result -/

/-- `V_S/K^{×p}` is a finite type: it injects into `V_∅/K^{×p}`. -/
theorem finite_kummerClasses_quotient (K : Type*) [Field K] [NumberField K] (p : ℕ) (hp : p.Prime)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :
    Finite (kummerClasses K p S) := by
  haveI : Finite (selmerGroupAt K p ∅ ⧸
      (pthPowerSubgroup Kˣ p).comap (selmerGroupAt K p ∅).subtype) :=
    finite_kummerClasses_empty K p hp
  haveI : Finite (selmerGroupAt K p S ⧸
      (pthPowerSubgroup Kˣ p).comap (selmerGroupAt K p S).subtype) :=
    Finite.of_injective (kummerClassesMap K p S) (kummerClassesMap_injective K p S)
  exact Finite.of_equiv _ Additive.ofMul

theorem finite_kummerClasses (K : Type*) [Field K] [NumberField K] (p : ℕ) (hp : p.Prime)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))) :
    Module.Finite (ZMod p) (Work.CFT.Kummer.kummerClasses K p S) := by
  haveI := finite_kummerClasses_quotient K p hp S
  infer_instance

end Work.CFT.Kummer
