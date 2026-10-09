import Mathlib
import Submission.Work.SSGRoute.E7bDefs
import Submission.Work.SSGRoute.sylow_in_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Z8 setup: the Sylow subgroup of `D_w(K/k)` and its fixed field

For the assembly `Work.SSGRoute.local_duality_ext_detect_levels` the class is first restricted to a
Sylow `p`-subgroup `S ≤ D_w(K/k)` (so that every simple module over the local group is `𝔽_p`), and
the base field is changed to the fixed field `k' = K^S` of `S` (so that `Gal(K/k') = S` and the
local group at the new base field is a `p`-group).

This file supplies the two elementary inputs:

* `exists_isPGroup_sylow_decompK` — a Sylow `p`-subgroup `S ≤ D_w` of prime-to-`p` index;
* `isPGroup_decompK_fixedBase` — with `k' := K^S`, the decomposition group `D_w(K/k')` is a
  `p`-group (it is `Gal(K/k') = S`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

section Sylow

variable (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K]
  [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]

/-- **A Sylow `p`-subgroup of the decomposition group.** -/
theorem exists_isPGroup_sylow_decompK (w : NK.GlobalCFT.Place K) :
    ∃ S : Subgroup (decompK (k := k) w), IsPGroup p ↥S ∧ ¬ p ∣ S.index := by
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := ↥(decompK (k := k) w))
  refine ⟨(P : Subgroup ↥(decompK (k := k) w)), P.isPGroup', ?_⟩
  have hfi : (P : Subgroup ↥(decompK (k := k) w)).FiniteIndex := inferInstance
  exact P.not_dvd_index

end Sylow

section FixedField

variable (p : ℕ) [Fact p.Prime] {k K : Type} [Field k] [NumberField k] [Field K]
  [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]

/-- The image of a subgroup of the decomposition group inside `Gal(K/k)`. -/
noncomputable def galSub (w : NK.GlobalCFT.Place K) (S : Subgroup (decompK (k := k) w)) :
    Subgroup (K ≃ₐ[k] K) := S.map (decompK (k := k) w).subtype

/-- **The fixed field `k' = K^S` of a subgroup `S ≤ D_w`.** -/
abbrev fixedBase (w : NK.GlobalCFT.Place K) (S : Subgroup (decompK (k := k) w)) : Type :=
  ↥(IntermediateField.fixedField (galSub (k := k) w S))

/-- `galSub` is a subgroup of the decomposition group. -/
theorem galSub_le (w : NK.GlobalCFT.Place K) (S : Subgroup (decompK (k := k) w)) :
    galSub (k := k) w S ≤ decompK (k := k) w :=
  Subgroup.map_subtype_le S

/-- A `p`-subgroup of `D_w` has a `p`-group image in `Gal(K/k)`. -/
theorem isPGroup_galSub {p : ℕ} (w : NK.GlobalCFT.Place K)
    (S : Subgroup (decompK (k := k) w)) (hS : IsPGroup p ↥S) :
    IsPGroup p ↥(galSub (k := k) w S) := by
  haveI : IsPGroup p ↥S := hS
  exact IsPGroup.of_equiv hS
    (Subgroup.equivMapOfInjective S (decompK (k := k) w).subtype Subtype.coe_injective)

/-- **The local group at the base `k' = K^S` is a `p`-group.**  It is `Gal(K/k') = S`. -/
theorem isPGroup_decompK_fixedBase {p : ℕ} (w : NK.GlobalCFT.Place K)
    (S : Subgroup (decompK (k := k) w)) (hS : IsPGroup p ↥S) :
    IsPGroup p (decompK (k := fixedBase (k := k) w S) w) := by
  haveI : IsPGroup p ↥(galSub (k := k) w S) := isPGroup_galSub w S hS
  have h1 : IsPGroup p (K ≃ₐ[fixedBase (k := k) w S] K) :=
    SylowIn.isPGroup_fixedField (galSub (k := k) w S) ‹_›
  exact IsPGroup.of_injective h1 (decompK (k := fixedBase (k := k) w S) w).subtype
    (Subtype.coe_injective)

end FixedField

end Work.SSGRoute
