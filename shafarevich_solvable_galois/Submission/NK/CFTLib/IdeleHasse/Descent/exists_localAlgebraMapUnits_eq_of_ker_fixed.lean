import Mathlib
import Submission.NK.NUV2.ARL.HR.locUnits_inflation_eq_zero_iff
import Submission.NK.HassePrinciple.LocalUnits
import Submission.NK.GlobalCFT.Galois.globalCFT_localFixed_finite
import Submission.NK.GlobalCFT.Galois.globalCFT_localFixed_infinite
import Submission.NK.NUV2.LC.RouteB.locUnits_tower_eq_zero
import Submission.NK.GlobalCFT.Inclusion.globalCFT_ideleClassGroup_inclusion_injective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Descent of local units along an intermediate field, from the kernel of `stabRestrict`

Let `K ⊆ M ⊆ E` be a tower of Galois number fields, `w` a place of `M` and `ŵ` a place of `E`
over `w`.  The restriction of decomposition groups `stabRestrict : D_ŵ →* D_w` has kernel
`Gal(E/M) ∩ D_ŵ = D_ŵ(E/M)`, the decomposition group of `ŵ` in the *relative* extension `E/M`.

The local fixed-point lemma for the single extension `E/M`
(`NK.GlobalCFT.Galois.globalCFT_localFixed_finite`,
`NK.GlobalCFT.Galois.globalCFT_localFixed_infinite`) says that a unit of `E_ŵ` fixed by all of
`D_ŵ(E/M)` lies in the image of `M_wˣ`.  This file transfers that hypothesis to the form used by
the descent argument: it is enough that the unit be fixed by the *kernel* of `stabRestrict`
(inside `Gal(E/K)`), acting through `NK.HassePrinciple.localUnitsRep K E ŵ`.

## Main result

* `NK.CFTLib.IdeleHasse.Descent.exists_localAlgebraMapUnits_eq_of_ker_fixed`.
-/

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open NK.GlobalCFT

namespace NK.CFTLib.IdeleHasse.Descent

/-! ## Elementary transports -/

/-- Cancelling a transport along an equality and its inverse: if `h ▸ z = w` then
`z = h.symm ▸ w`. -/
lemma eq_rec_symm_eq_rec_iff {α : Sort _} {X : α → Sort _} {a b : α} (h : a = b) (z : X a)
    (w : X b) : (h ▸ z = w) ↔ (z = h.symm ▸ w) := by
  cases h
  rfl

/-! ## The restriction of an automorphism of `E` fixing `M` -/

/-- An automorphism of `E` over `M`, viewed as an automorphism over `K`, restricts to the identity
on `M`. -/
lemma restrictScalars_restrictHom_eq_one {K M E : Type} [Field K] [Field M] [Field E]
    [Algebra K M] [Algebra K E] [Algebra M E] [IsScalarTower K M E] [IsGalois K M]
    (σ : E ≃ₐ[M] E) :
    NK.NUV2.ARL.HR.restrictHom (K := K) (L := M) (E := E) (AlgEquiv.restrictScalars K σ) = 1 := by
  ext m
  apply (algebraMap M E).injective
  rw [NK.NUV2.ARL.HR.restrictHom_apply_coe]
  exact σ.commutes m

/-- **The kernel of `stabRestrict` is the decomposition group of the relative extension
`E/M`**: an automorphism of `E` over `M` fixing `ŵ` belongs to `ker (stabRestrict)`. -/
lemma mem_ker_stabRestrict_of_restrictScalars {K M E : Type} [Field K] [NumberField K] [Field M]
    [NumberField M] [Field E] [NumberField E] [Algebra K M] [Algebra K E] [Algebra M E]
    [IsScalarTower K M E] [FiniteDimensional K M] [FiniteDimensional K E] [IsGalois K M]
    [IsGalois K E] [IsGalois M E]
    {w : Place M} {ŵ : Place E} (hw : ŵ.LiesOver w) (σ : E ≃ₐ[M] E) (hσ : σ • ŵ = ŵ) :
    (⟨AlgEquiv.restrictScalars K σ, hσ⟩ : MulAction.stabilizer Gal(E/K) ŵ) ∈
      (NK.NUV2.ARL.HR.stabRestrict (K := K) (M := M) (E := E) w ŵ hw).ker := by
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  simpa [NK.NUV2.ARL.HR.stabRestrict_coe] using
    restrictScalars_restrictHom_eq_one (K := K) (M := M) (E := E) σ

/-! ## The action of a relative automorphism in the form used by the fixed point lemma -/

/-- **The action of `ker (stabRestrict)` in the cast form of the local fixed point lemmas.**  If a
unit `b` of `E_ŵ` is fixed by the local action of the kernel element attached to `σ : E ≃ₐ[M] E`
fixing `ŵ` (acting on `Gal(E/K)` by `AlgEquiv.restrictScalars`), then `b` is fixed by the local
automorphism `Place.localRingEquiv σ ŵ`, up to the transport along `σ • ŵ = ŵ`. -/
lemma localUnitsRep_ker_apply {K M E : Type} [Field K] [NumberField K] [Field M] [NumberField M]
    [Field E] [NumberField E] [Algebra K M] [Algebra K E] [Algebra M E] [IsScalarTower K M E]
    [FiniteDimensional K M] [FiniteDimensional K E] [IsGalois K M] [IsGalois K E] [IsGalois M E]
    (ŵ : Place E) (σ : E ≃ₐ[M] E) (hσ : σ • ŵ = ŵ) (b : (Place.localField E ŵ)ˣ)
    (hb : (NK.HassePrinciple.localUnitsRep K E ŵ).ρ
        (⟨AlgEquiv.restrictScalars K σ, hσ⟩ : MulAction.stabilizer Gal(E/K) ŵ)
        (Additive.ofMul b) = Additive.ofMul b) :
    Units.map (Place.localRingEquiv σ ŵ).toMonoidHom b = hσ.symm ▸ b := by
  let s : MulAction.stabilizer Gal(E/K) ŵ := ⟨AlgEquiv.restrictScalars K σ, hσ⟩
  have hb' : (NK.HassePrinciple.localUnitsRep K E ŵ).ρ s (Additive.ofMul b)
      = Additive.ofMul b := hb
  have h1 : NK.HassePrinciple.localUnitsEquiv ŵ s b = b := congrArg Additive.toMul hb'
  have h2 : NK.HassePrinciple.localAut ŵ s b.val = b.val := by
    have h := congrArg Units.val h1
    rw [NK.HassePrinciple.coe_localUnitsEquiv] at h
    exact h
  rw [NK.HassePrinciple.localAut_apply] at h2
  rw [NK.HassePrinciple.ringEquiv_cast_apply_eq] at h2
  have h2' : (Place.localRingEquiv s.1 ŵ) b.val
      = (MulAction.mem_stabilizer_iff.mp s.2).symm ▸ b.val :=
    (eq_rec_symm_eq_rec_iff _ _ _).mp h2
  refine Units.ext ?_
  rw [Units.coe_map, NK.HassePrinciple.units_val_cast]
  exact h2'

/-! ## The descent -/

theorem exists_localAlgebraMapUnits_eq_of_ker_fixed {K M E : Type} [Field K] [NumberField K]
    [Field M] [NumberField M] [Field E] [NumberField E] [Algebra K M] [Algebra K E] [Algebra M E]
    [IsScalarTower K M E] [FiniteDimensional K M] [FiniteDimensional K E] [IsGalois K M]
    [IsGalois K E] [IsGalois M E]
    (w : NK.GlobalCFT.Place M) (ŵ : NK.GlobalCFT.Place E)
    (hw : NK.GlobalCFT.Place.LiesOver ŵ w)
    (b : (NK.GlobalCFT.Place.localField E ŵ)ˣ)
    (hb : ∀ s : (NK.NUV2.ARL.HR.stabRestrict (K := K) (M := M) (E := E) w ŵ hw).ker,
        (NK.HassePrinciple.localUnitsRep K E ŵ).ρ (s : MulAction.stabilizer Gal(E/K) ŵ)
          (Additive.ofMul b) = Additive.ofMul b) :
    ∃ a : (NK.GlobalCFT.Place.localField M w)ˣ,
      NK.GlobalCFT.Place.localAlgebraMapUnits ŵ w hw a = b := by
  rcases ŵ with w' | q
  · rcases w with v' | Q
    · -- both places archimedean
      have h : w'.LiesOver v' := by
        rcases hw with ⟨w'', v'', h1, h2, h⟩ | ⟨q, Q, h1, h2, h⟩
        · rw [Place.ofInfinite_inj] at h1
          rw [Place.ofInfinite_inj] at h2
          subst h1; subst h2
          exact h
        · exact absurd h1 (Place.ofInfinite_ne_ofFinite w' q)
      refine NK.GlobalCFT.Galois.globalCFT_localFixed_infinite (K := M) (L := E) h b ?_
      intro σ hσ
      exact localUnitsRep_ker_apply (K := K) (M := M) (E := E) (Place.ofInfinite w') σ hσ b
        (hb ⟨⟨AlgEquiv.restrictScalars K σ, hσ⟩,
          mem_ker_stabRestrict_of_restrictScalars (K := K) (M := M) (E := E) hw σ hσ⟩)
    · -- `ŵ` archimedean and `w` nonarchimedean is impossible
      exact absurd ((Place.isFinite_of_liesOver hw).mpr (Place.isFinite_ofFinite Q))
        (Place.not_isFinite_ofInfinite w')
  · rcases w with v' | Q
    · -- `ŵ` nonarchimedean and `w` archimedean is impossible
      exact absurd ((Place.isFinite_of_liesOver hw).mp (Place.isFinite_ofFinite q))
        (Place.not_isFinite_ofInfinite v')
    · -- both places nonarchimedean
      have h : q.asIdeal.LiesOver Q.asIdeal := by
        rcases hw with ⟨w'', v'', h1, h2, h⟩ | ⟨q', Q', h1, h2, h⟩
        · exact absurd h1.symm (Place.ofInfinite_ne_ofFinite w'' q)
        · rw [Place.ofFinite_inj] at h1
          rw [Place.ofFinite_inj] at h2
          subst h1; subst h2
          exact h
      refine NK.GlobalCFT.Galois.globalCFT_localFixed_finite (K := M) (L := E) h b ?_
      intro σ hσ
      exact localUnitsRep_ker_apply (K := K) (M := M) (E := E) (Place.ofFinite q) σ hσ b
        (hb ⟨⟨AlgEquiv.restrictScalars K σ, hσ⟩,
          mem_ker_stabRestrict_of_restrictScalars (K := K) (M := M) (E := E) hw σ hσ⟩)

end NK.CFTLib.IdeleHasse.Descent
