import Mathlib.Tactic.Have
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Submission.NK.CFTLib.ArtinReciprocityIdeal.relNormUnit_trans
import Submission.NK.NUV2.ArtinBridge.spanUnit_norm_mem_principalRay_of_congrOne
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Descent of the principal ray and the norm ray along a relative norm

The transfer (Lang, *Algebraic Number Theory*, X §2, Theorem 2) norms ideals down from an auxiliary
field `E` to `K`.  This module records the two resulting inclusions:

* `principalRay_map_relNormUnit_le`: the relative norm of a principal-ray element of `E` lies in the
  principal ray of `K` (the "congruence descent", `NK.NUV2.ArtinBridge.spanUnit_norm_mem_principalRay_of_congrOne`);
* `normRay_map_relNormUnit_le`: in a tower `K ⊆ L ⊆ LE`, `K ⊆ E ⊆ LE`, the relative norm of a norm
  ideal of `LE` over `E` is a norm ideal of `K` over `L` (transitivity of the norm,
  `NK.CFTLib.ARL.relNormUnit_trans`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open NumberField IsDedekindDomain
open scoped NumberField nonZeroDivisors

noncomputable section

namespace NK.CFTLib.ARLAlt

open NK.CFTLib.ArtinReciprocityIdeal

/-- **The relative norm of a principal ideal.**  For a finite extension `E/K` of number fields and
`β ∈ Eˣ`, the relative norm of the principal ideal `(β)` is the principal ideal of
`N_{E/K}(β)`. -/
theorem relNormUnit_unitsToIdealUnits {K E : Type} [Field K] [NumberField K] [Field E]
    [NumberField E] [Algebra K E] [FiniteDimensional K E] (β : Eˣ) :
    NK.CFTLib.ARL.relNormUnit (K := K) (L := E) (NK.CFTLib.ARL.unitsToIdealUnits E β) =
      NK.CFTLib.ARL.unitsToIdealUnits K (Units.map (Algebra.norm K) β) := by
  apply Units.ext
  rw [NK.CFTLib.ARL.relNormUnit_apply_e, NK.CFTLib.ARL.unitsToIdealUnits_coe,
    NK.CFTLib.ARL.unitsToIdealUnits_coe]
  rw [← NK.GlobalCFT.Idele.idealOf_principalIdele (K := E) β,
    ← NK.CFTLib.ARL.idealOf_normIdeleHom (K := K) (L := E)
      (NK.GlobalCFT.Idele.principalIdele E β),
    NK.GlobalCFT.Idele.normIdeleHom_principalIdele]
  exact NK.GlobalCFT.Idele.idealOf_principalIdele (K := K) (Units.map (Algebra.norm K) β)

/-- **The relative norm maps the principal ray into the principal ray.** -/
theorem principalRay_map_relNormUnit_le {K E : Type} [Field K] [NumberField K] [Field E]
    [NumberField E] [Algebra K E] [FiniteDimensional K E] (c m : ℕ) (hm : 0 < m) (hc : 0 < c)
    (hcm : m ∣ c) :
    (principalRay E c).map (NK.CFTLib.ARL.relNormUnit (K := K) (L := E)) ≤ principalRay K m := by
  rw [principalRay, Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
  rintro A ⟨β, hβ, rfl⟩
  change NK.CFTLib.ARL.relNormUnit (K := K) (L := E) (spanUnit β) ∈ principalRay K m
  have hspanE : spanUnit β = NK.CFTLib.ARL.unitsToIdealUnits E β := Units.ext rfl
  have hspanK : NK.CFTLib.ARL.unitsToIdealUnits K (Units.map (Algebra.norm K) β)
      = spanUnit (Units.map (Algebra.norm K) β) := Units.ext rfl
  have h : NK.CFTLib.ARL.relNormUnit (K := K) (L := E) (spanUnit β) =
      spanUnit (Units.map (Algebra.norm K) β) := by
    rw [hspanE, relNormUnit_unitsToIdealUnits, hspanK]
  rw [h]
  exact NK.NUV2.ArtinBridge.spanUnit_norm_mem_principalRay_of_congrOne
    (m := m) (m' := c) hc hcm β hβ

/-- **The relative norm maps norm ideals of a tower down to norm ideals.**  In the tower
`K ⊆ L ⊆ LE`, `K ⊆ E ⊆ LE`, the relative norm `N_{E/K}` sends the norm group of `LE/E` (at a
modulus `c`) into the norm group of `L/K` at any modulus `m ∣ c`. -/
theorem normRay_map_relNormUnit_le {K L E LE : Type}
    [Field K] [NumberField K] [Field L] [NumberField L] [Field E] [NumberField E]
    [Field LE] [NumberField LE]
    [Algebra K E] [Algebra E LE] [Algebra K LE] [IsScalarTower K E LE]
    [Algebra K L] [Algebra L LE] [IsScalarTower K L LE]
    [FiniteDimensional K E] [FiniteDimensional E LE] [FiniteDimensional K L]
    [FiniteDimensional L LE]
    (c m : ℕ) (hm : 0 < m) (hcm : m ∣ c) :
    (normRay E LE c).map (NK.CFTLib.ARL.relNormUnit (K := K) (L := E)) ≤ normRay K L m := by
  rw [normRay, Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
  rintro A ⟨I, hI, hcop, rfl⟩
  classical
  have hEne : Ideal.relNorm (𝓞 E) I ≠ ⊥ := fun h => hI ((Ideal.relNorm_eq_bot_iff).mp h)
  have hEne' : Ideal.relNorm (𝓞 E) I ≠ ⊥ := fun h => hI ((Ideal.relNorm_eq_bot_iff).mp h)
  set J : Ideal (𝓞 L) := Ideal.relNorm (𝓞 L) I with hJdef
  have hJne : J ≠ ⊥ := fun h => hI ((Ideal.relNorm_eq_bot_iff).mp (hJdef ▸ h))
  -- `J` is coprime to `(m)`
  have hcopJ : FracCoprime (K := L) m (idealUnit J hJne) := by
    intro 𝔮 h𝔮
    have hiter : ∀ 𝔓 ∈ NK.GlobalCFT.Place.primesOverFinite (K := L) (L := LE) 𝔮,
        FractionalIdeal.count LE 𝔓 (I : FractionalIdeal (𝓞 LE)⁰ LE) = 0 := by
      intro 𝔓 h𝔓
      have hlies : 𝔓.asIdeal.LiesOver 𝔮.asIdeal :=
        (NK.GlobalCFT.Place.mem_primesOverFinite (K := L) (L := LE)).mp h𝔓
      have hm𝔓 : (m : 𝓞 LE) ∈ 𝔓.asIdeal := by
        have h1 : (m : 𝓞 L) ∈ 𝔓.asIdeal.under (𝓞 L) := hlies.over.symm ▸ h𝔮
        have h2 := (Ideal.mem_under (𝓞 L) 𝔓.asIdeal).mp h1
        rwa [map_natCast] at h2
      have hc𝔓 : (c : 𝓞 LE) ∈ 𝔓.asIdeal := by
        obtain ⟨k, rfl⟩ := hcm
        rw [Nat.cast_mul]
        exact Ideal.mul_mem_right _ _ hm𝔓
      exact hcop 𝔓 hc𝔓
    show FractionalIdeal.count L 𝔮 (J : FractionalIdeal (𝓞 L)⁰ L) = 0
    rw [hJdef, ← NK.CFTLib.ARL.relNormFI_coeIdeal (K := L) (L := LE) I hI,
      NK.CFTLib.ARL.count_relNormFI, NK.CFTLib.ARL.relNormExp]
    exact Finset.sum_eq_zero fun 𝔓 h𝔓 => by rw [hiter 𝔓 h𝔓, mul_zero]
  -- the main computation
  show NK.CFTLib.ARL.relNormUnit (K := K) (L := E)
      (idealUnit (Ideal.relNorm (𝓞 E) I) hEne') ∈ normRay K L m
  have hmain : NK.CFTLib.ARL.relNormUnit (K := K) (L := E)
      (idealUnit (Ideal.relNorm (𝓞 E) I) hEne') =
      idealUnit (Ideal.relNorm (𝓞 K) J) (fun h => hJne ((Ideal.relNorm_eq_bot_iff).mp h)) := by
    apply Units.ext
    rw [NK.CFTLib.ARL.relNormUnit_apply_e]
    show NK.CFTLib.ARL.relNormFI (K := K) (L := E)
        ((Ideal.relNorm (𝓞 E) I : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) =
      ((Ideal.relNorm (𝓞 K) J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
    rw [NK.CFTLib.ARL.relNormFI_coeIdeal (K := K) (L := E) (Ideal.relNorm (𝓞 E) I) hEne,
      Ideal.relNorm_relNorm (𝓞 K) (𝓞 E) I,
      ← Ideal.relNorm_relNorm (𝓞 K) (𝓞 L) I]
  rw [hmain]
  exact Subgroup.subset_closure ⟨J, hJne, hcopJ, rfl⟩

end NK.CFTLib.ARLAlt
