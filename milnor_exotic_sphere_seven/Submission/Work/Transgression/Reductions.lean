import Mathlib
import Submission.Work.Transgression.Statement
import Submission.Work.TangentClasses.DiscSplitting
import Submission.Work.CharacteristicClasses.Capped
import Submission.Work.Thom.Euler

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

/-!
# SUBPROJECT TRANSGRESSION: the reductions

This module contains the two auxiliary lemmas of the reduction of `Work.Agree.EulerClutch` to the
punctured-cohomology input `Work.Transgression.PuncturedCoh`:

* `Work.Transgression.PiStarGen` — the pullback `π^*` along the bundle projection
  `π = Work.TangentClasses.discProj` sends every generator of `H⁴(S⁴;ℤ)` to `± τ`;
* `Work.Transgression.QuotSpan` — the pure `ℤ`-module lemma that reads off the coefficient of the
  Euler class from the quotient `H⁴(S⁴;ℤ)/⟨e⟩ ≅ ℤ/(a+b)`.
-/

namespace Work.Transgression

open Work.TangentClasses

noncomputable section

/-! ## The pullback of a generator along the bundle projection -/

/-- **`π^*` sends generators to `± τ`.**  The pullback along the bundle projection
`π = Work.TangentClasses.discProj : D(ξ) → S⁴` is injective *and surjective* in degree `4`
(`Work.TangentClasses.surjective_HMap_discProj`), so it carries generators of `H⁴(S⁴;ℤ) ≅ ℤ` to
generators of `H⁴(D(ξ);ℤ) ≅ ℤ`, i.e. to `± tauD`. -/
theorem PiStarGen (G : Work.Thom.Coh ℤ 4 Work.Agree.S4)
    (hG : ∀ z : Work.Thom.Coh ℤ 4 Work.Agree.S4, ∃ c : ℤ, z = c • G) :
    (Work.TangentClasses.HMap Work.TangentClasses.discProj 4).hom G = Work.Milnor.tauD ∨
    (Work.TangentClasses.HMap Work.TangentClasses.discProj 4).hom G = -Work.Milnor.tauD := by
  have hgen : ∀ z : Work.Milnor.discH4, ∃ c : ℤ, z = c •
      (Work.TangentClasses.HMap Work.TangentClasses.discProj 4).hom G := by
    intro z
    obtain ⟨w, hw⟩ := Work.TangentClasses.surjective_HMap_discProj 4 z
    obtain ⟨c, hc⟩ := hG w
    exact ⟨c, by rw [← hw, hc, map_zsmul]⟩
  obtain ⟨m, hm⟩ := Work.Milnor.generates_tauD
      ((Work.TangentClasses.HMap Work.TangentClasses.discProj 4).hom G)
  obtain ⟨c, hc⟩ := hgen Work.Milnor.tauD
  have hm' : ModuleCat.Hom.hom Work.Milnor.discH4Iso.hom
      ((Work.TangentClasses.HMap Work.TangentClasses.discProj 4).hom G) = m := by
    rw [hm, map_zsmul, Work.Milnor.discH4Iso_tauD, smul_eq_mul, mul_one]
  have h1 : ModuleCat.Hom.hom Work.Milnor.discH4Iso.hom Work.Milnor.tauD
      = c * ModuleCat.Hom.hom Work.Milnor.discH4Iso.hom
          ((Work.TangentClasses.HMap Work.TangentClasses.discProj 4).hom G) := by
    rw [hc, map_zsmul, smul_eq_mul]
  rw [Work.Milnor.discH4Iso_tauD, hm'] at h1
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp h1.symm with ⟨-, hm1⟩ | ⟨-, hm1⟩
  · left; rw [hm, hm1, one_smul]
  · right; rw [hm, hm1]; simp

/-! ## Reading off the coefficient from the quotient -/

/-- **The cardinality of the quotient `M ⧸ ⟨e⟩` determines `φ e` up to sign.**  This is the
`Nat.card` form of `Work.Transgression.QuotSpan`, which avoids the `Module ℤ` instance of the
quotient in its statement. -/
theorem QuotSpanCard {M : Type} [AddCommGroup M] [Module ℤ M]
    (φ : M ≃ₗ[ℤ] ℤ) (e : M) (m : ℕ)
    (h : Nat.card (M ⧸ Submodule.span ℤ {e}) = m) :
    φ e = (m : ℤ) ∨ φ e = -(m : ℤ) := by
  have hmap : Submodule.map (φ : M →ₗ[ℤ] ℤ) (Submodule.span ℤ {e}) =
      Submodule.span ℤ {φ e} := by
    rw [Submodule.map_span, Set.image_singleton]
    simp
  have hcard2 : Nat.card (ℤ ⧸ Submodule.span ℤ {φ e}) = m := by
    rw [← h, Nat.card_congr
      (Submodule.Quotient.equiv (Submodule.span ℤ {e}) (Submodule.span ℤ {φ e}) φ hmap).toEquiv]
  have hcard3 : Nat.card (ℤ ⧸ Submodule.span ℤ {φ e}) = (φ e).natAbs := by
    rcases Int.natAbs_eq (φ e) with hk | hk
    · rw [hk, Int.natAbs_natCast]
      change Nat.card (ℤ ⧸ Ideal.span {((φ e).natAbs : ℤ)}) = (φ e).natAbs
      rw [Nat.card_congr (Int.quotientSpanNatEquivZMod (φ e).natAbs).toEquiv, Nat.card_zmod]
    · have hspan : Submodule.span ℤ {φ e} = Submodule.span ℤ {(↑(φ e).natAbs : ℤ)} := by
        conv_lhs => rw [hk]
        exact Ideal.span_singleton_neg ((↑(φ e).natAbs : ℤ))
      rw [hspan]
      change Nat.card (ℤ ⧸ Ideal.span {((φ e).natAbs : ℤ)}) = (φ e).natAbs
      rw [Nat.card_congr (Int.quotientSpanNatEquivZMod (φ e).natAbs).toEquiv, Nat.card_zmod]
  have hmn : (φ e).natAbs = m := by rw [← hcard3, hcard2]
  rcases Int.natAbs_eq (φ e) with hk | hk
  · left; rw [hk, hmn]
  · right; rw [hk, hmn]

/-- **The quotient `M ⧸ ⟨e⟩` determines `φ e` up to sign.**  If `M` is a `ℤ`-module with a linear
equivalence `φ : M ≃ₗ[ℤ] ℤ` and `M ⧸ Submodule.span ℤ {e} ≃ₗ[ℤ] ZMod m`, then `φ e = ±m`; the
reason is `Nat.card (ZMod m) = m` and `Nat.card (ℤ ⧸ ⟨φ e⟩) = |φ e|`. -/
theorem QuotSpan {M : Type} [AddCommGroup M] [Module ℤ M]
    (φ : M ≃ₗ[ℤ] ℤ) (e : M) (m : ℕ)
    (h : Nonempty ((M ⧸ Submodule.span ℤ {e}) ≃ₗ[ℤ] ZMod m)) :
    φ e = (m : ℤ) ∨ φ e = -(m : ℤ) := by
  obtain ⟨h⟩ := h
  have hcard : Nat.card (M ⧸ Submodule.span ℤ {e}) = m := by
    rw [Nat.card_congr h.toEquiv, Nat.card_zmod]
  have hmap : Submodule.map (φ : M →ₗ[ℤ] ℤ) (Submodule.span ℤ {e}) =
      Submodule.span ℤ {φ e} := by
    rw [Submodule.map_span, Set.image_singleton]
    simp
  have hcard2 : Nat.card (ℤ ⧸ Submodule.span ℤ {φ e}) = m := by
    rw [← hcard, Nat.card_congr
      (Submodule.Quotient.equiv (Submodule.span ℤ {e}) (Submodule.span ℤ {φ e}) φ hmap).toEquiv]
  have hcard3 : Nat.card (ℤ ⧸ Submodule.span ℤ {φ e}) = (φ e).natAbs := by
    rcases Int.natAbs_eq (φ e) with hk | hk
    · rw [hk, Int.natAbs_natCast]
      change Nat.card (ℤ ⧸ Ideal.span {((φ e).natAbs : ℤ)}) = (φ e).natAbs
      rw [Nat.card_congr (Int.quotientSpanNatEquivZMod (φ e).natAbs).toEquiv, Nat.card_zmod]
    · have hspan : Submodule.span ℤ {φ e} = Submodule.span ℤ {(↑(φ e).natAbs : ℤ)} := by
        conv_lhs => rw [hk]
        exact Ideal.span_singleton_neg ((↑(φ e).natAbs : ℤ))
      rw [hspan]
      change Nat.card (ℤ ⧸ Ideal.span {((φ e).natAbs : ℤ)}) = (φ e).natAbs
      rw [Nat.card_congr (Int.quotientSpanNatEquivZMod (φ e).natAbs).toEquiv, Nat.card_zmod]
  have hmn : (φ e).natAbs = m := by rw [← hcard3, hcard2]
  rcases Int.natAbs_eq (φ e) with hk | hk
  · left; rw [hk, hmn]
  · right; rw [hk, hmn]

end

end Work.Transgression
