import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.Work.SSGRoute.ext_idele_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Fixed points of the decomposition-group action on the local units

`NK.HassePrinciple.localUnitsEquiv w σ` is the action of the decomposition group
`D_w = MulAction.stabilizer (L ≃ₐ[K] L) w` on the local units `L_wˣ`, obtained by transporting
units along the local automorphism `localAutHom w σ` — the canonical isomorphism
`L_w ≃+* L_{σ w}` transported along `σ • w = w`.

The present file records the elementary but indispensable description of this action in terms of
the *untwisted* local isomorphism `NK.GlobalCFT.Place.localRingEquiv σ w`: for an element `σ` of
the decomposition group with `hσ : σ • w = w`,

`localUnitsEquiv w σ a = cast hσ (localRingEquiv σ w a)`,

where `cast hσ` is the transport along `hσ`.  Consequently, an element `a` of the local units is
fixed by the whole decomposition group iff for every `σ : L ≃ₐ[K] L` with `σ • w = w` the
element `localRingEquiv σ w a` is `a` itself, `a` re-read along `σ • w = w` — which is the shape
in which the statement is consumed in the Shapiro/level-decomposition argument.
-/

set_option linter.unusedSectionVars false

namespace Work.SSGRoute

open NK.GlobalCFT
open NumberField IsDedekindDomain

section Helpers

variable (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

/-- **The decomposition-group action on the local units, unfolded.**  For an element `σ` of the
decomposition group of `w` and any proof `hσ` of `σ • w = w`, the action `localUnitsEquiv w σ` is
the composite of the canonical local isomorphism `localRingEquiv σ w : L_w ≃+* L_{σ w}` with the
transport along `hσ`. -/
theorem localUnitsEquiv_eq_cast_ringEquiv (w : NK.GlobalCFT.Place K)
    (σ : MulAction.stabilizer (K ≃ₐ[k] K) w) (a : (NK.GlobalCFT.Place.localField K w)ˣ)
    (hσ : σ.1 • w = w) :
    NK.HassePrinciple.localUnitsEquiv (K := k) w σ a
      = Units.map (RingEquiv.cast (R := fun v : NK.GlobalCFT.Place K =>
            NK.GlobalCFT.Place.localField K v) hσ).toMonoidHom
          (Units.map (NK.GlobalCFT.Place.localRingEquiv σ.1 w).toMonoidHom a) := by
  ext
  rw [NK.HassePrinciple.coe_localUnitsEquiv]
  simp only [NK.HassePrinciple.localAutHom, MonoidHom.coe_mk, OneHom.coe_mk, Units.coe_map]
  rw [NK.HassePrinciple.localAut_apply,
    show (MulAction.mem_stabilizer_iff.mp σ.2) = hσ from Subsingleton.elim _ _]
  rfl

/-- Cancelling a transport along an equality against the transport back, for units. -/
theorem units_map_cast_symm (w w' : NK.GlobalCFT.Place K) (h : w = w')
    (b : (NK.GlobalCFT.Place.localField K w')ˣ) :
    Units.map (RingEquiv.cast (R := fun v : NK.GlobalCFT.Place K =>
        NK.GlobalCFT.Place.localField K v) h).toMonoidHom (h.symm ▸ b) = b := by
  rw [NK.HassePrinciple.units_map_cast h (h.symm ▸ b)]
  cases h; rfl

/-- Cancelling a transport along an equality and back, for units. -/
theorem units_eqRec_symm_eqRec (w w' : NK.GlobalCFT.Place K) (h : w = w')
    (b : (NK.GlobalCFT.Place.localField K w)ˣ) :
    (h.symm ▸ (h ▸ b) : (NK.GlobalCFT.Place.localField K w)ˣ) = b := by
  cases h; rfl

/-- The transport of a unit along an equality of places depends only on the equality as a proof,
not on its construction. -/
theorem eqRec_eq_of_eq {w w' : NK.GlobalCFT.Place K} {e₁ e₂ : w = w'}
    (he : e₁ = e₂) (b : (NK.GlobalCFT.Place.localField K w)ˣ) :
    e₁ ▸ b = e₂ ▸ b := by rw [he]

/-- **The fixed points of the decomposition-group action on the local units, in terms of the
untwisted local isomorphism.**  For an arbitrary place `w` of `K` and `a ∈ K_wˣ`, `a` is fixed by
every element of the decomposition group `D_w` iff for every `σ : K ≃ₐ[k] K` with `σ • w = w` the
unit `localRingEquiv σ w a` is `a` re-read along `σ • w = w`. -/
theorem localUnitsEquiv_fixed_iff_ringEquiv_fixed_general (w : NK.GlobalCFT.Place K)
    (a : (NK.GlobalCFT.Place.localField K w)ˣ) :
    (∀ σ : MulAction.stabilizer (K ≃ₐ[k] K) w,
        NK.HassePrinciple.localUnitsEquiv (K := k) w σ a = a)
      ↔ ∀ (σ : K ≃ₐ[k] K) (hσ : σ • w = w),
          Units.map (NK.GlobalCFT.Place.localRingEquiv σ w).toMonoidHom a = hσ.symm ▸ a := by
  constructor
  · intro h σ hσ
    let σ' : MulAction.stabilizer (K ≃ₐ[k] K) w := ⟨σ, hσ⟩
    have h0 : σ'.1 • w = w := MulAction.mem_stabilizer_iff.mp σ'.2
    have hfix : NK.HassePrinciple.localUnitsEquiv (K := k) w σ' a = a := h σ'
    rw [localUnitsEquiv_eq_cast_ringEquiv k K w σ' a h0] at hfix
    have h1 : h0 ▸ (Units.map (NK.GlobalCFT.Place.localRingEquiv σ'.1 w).toMonoidHom a) = a := by
      rw [← NK.HassePrinciple.units_map_cast h0
        (Units.map (NK.GlobalCFT.Place.localRingEquiv σ'.1 w).toMonoidHom a)]
      exact hfix
    have h2 : Units.map (NK.GlobalCFT.Place.localRingEquiv σ'.1 w).toMonoidHom a
        = h0.symm ▸ a := by
      have h2' := congrArg (fun z => h0.symm ▸ z) h1
      rwa [units_eqRec_symm_eqRec (K := K) (σ'.1 • w) w h0
        (Units.map (NK.GlobalCFT.Place.localRingEquiv σ'.1 w).toMonoidHom a)] at h2'
    have h3 : h0.symm ▸ a = hσ.symm ▸ a :=
      eqRec_eq_of_eq (K := K) (congrArg Eq.symm (Subsingleton.elim h0 hσ)) a
    exact h2.trans h3
  · intro h σ
    have h0 : σ.1 • w = w := MulAction.mem_stabilizer_iff.mp σ.2
    rw [localUnitsEquiv_eq_cast_ringEquiv k K w σ a h0, h σ.1 h0]
    exact units_map_cast_symm (K := K) (σ.1 • w) w h0 a

end Helpers

theorem localUnitsEquiv_fixed_iff_ringEquiv_fixed (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (a : (q.adicCompletion K)ˣ) :
    (∀ σ : MulAction.stabilizer (K ≃ₐ[k] K) (NK.GlobalCFT.Place.ofFinite q),
        NK.HassePrinciple.localUnitsEquiv (K := k) (NK.GlobalCFT.Place.ofFinite q) σ a = a)
      ↔ ∀ (σ : K ≃ₐ[k] K) (hσ : σ • NK.GlobalCFT.Place.ofFinite q = NK.GlobalCFT.Place.ofFinite q),
          Units.map (NK.GlobalCFT.Place.localRingEquiv σ (NK.GlobalCFT.Place.ofFinite q)).toMonoidHom a
            = hσ.symm ▸ a :=
  localUnitsEquiv_fixed_iff_ringEquiv_fixed_general k K (NK.GlobalCFT.Place.ofFinite q) a

end Work.SSGRoute
