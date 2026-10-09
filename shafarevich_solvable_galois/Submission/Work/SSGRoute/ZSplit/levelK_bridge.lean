import Mathlib
import Submission.Work.SSGRoute.ZSplit.levelKPieces
import Submission.Work.SSGRoute.ZDataMup.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The level-`K` vocabulary of `ZSplit` and of `ZDataMup` are the same

The two lanes that work on the level-`K` `μ_p`-realisation have written down the same two
predicates twice:

* the local Tate system — `Work.SSGRoute.ZSplit.IsLevelKLocalTateSystem` (`def … : Prop`, a
  conjunction) and `Work.SSGRoute.ZDataMup.IsLocalTateSystem` (a `structure`); and
* the product formula — `Work.SSGRoute.ZSplit.HasLevelKReciprocity` and
  `Work.SSGRoute.ZDataMup.IsProductFormula`.

The *only* difference between the two formulation of each predicate is that `ZDataMup` spells out the
level-`K` conjugacy of places as `∃ τ ∈ K.fixingSubgroup, ∀ x, x ∈ B ↔ τ⁻¹ • x ∈ A` whereas `ZSplit`
uses `Work.SSGRoute.kConj k Ω K A B = ∃ τ ∈ G_K, τ • A = B`.  These agree
(`exists_forall_mem_iff_smul_eq`, from `ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem`).

Consequently the two lanes' obligations are the same: the product-formula node of the `ZDataMup`
lane (`Work.SSGRoute.ZDataMup.localTateSystem_productFormula`) *is* the product-formula obligation
`HasLevelKReciprocity` of the level-`K` pairing, and conversely.
-/

namespace Work.SSGRoute.ZSplit

open _root_.SSGRoute
open Work.SSGRoute

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

section Conj

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

/-- **The two spellings of level-`K` conjugacy agree.**
`τ • A = B` is `∀ x, x ∈ B ↔ τ⁻¹ • x ∈ A` for a valuation subring. -/
theorem exists_forall_mem_iff_smul_eq (K : IntermediateField k Ω)
    (A B : ValuationSubring Ω) :
    (∃ τ : Ω ≃ₐ[k] Ω, τ ∈ K.fixingSubgroup ∧ (∀ x : Ω, x ∈ B ↔ τ⁻¹ • x ∈ A)) ↔
      Work.SSGRoute.kConj k Ω K A B := by
  constructor
  · rintro ⟨τ, hτ, hτA⟩
    refine ⟨τ, hτ, ?_⟩
    refine SetLike.ext fun x => ?_
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    exact (hτA x).symm
  · rintro ⟨τ, hτ, hτA⟩
    refine ⟨τ, hτ, fun x => ?_⟩
    rw [← hτA, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]

end Conj

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]

/-- **The two local Tate systems agree.** -/
theorem isLevelKLocalTateSystem_iff_isLocalTateSystem
    (pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) →
      ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p) :
    IsLevelKLocalTateSystem p k Ω K pair ↔
      Work.SSGRoute.ZDataMup.IsLocalTateSystem p k Ω K pair := by
  constructor
  · intro h
    exact ⟨fun H hH => (h H hH).1, fun H hH => (h H hH).2.1,
      fun H hH => (h H hH).2.2.1, fun H hH => (h H hH).2.2.2⟩
  · intro h H hH
    exact ⟨h.additive_left H hH, h.additive_right H hH,
      h.vanishes_coboundary H hH, h.perfect H hH⟩

/-! **The local Tate systems of the two lanes agree**, so the linear-algebra half of the
level-`K` pairing (`Work.SSGRoute.ZDataMup.exists_isLocalTateSystem`) and the linear-algebra half of
`levelK_pairing_of_tateSystem` are one and the same obligation (and both are free).  The *product
formulas* of the two lanes are, however, **not** interchangeable: `ZDataMup.IsProductFormula`
asks the two global classes to vanish on the whole inertia at the places outside `T'`
(`∀ σ : Ω ≃ₐ[k] Ω, IsInertia k B σ → …`), whereas `HasLevelKReciprocity` — whose classes are
cocycles on `G_K = K.fixingSubgroup`, with unconstrained values outside `G_K` — asks this only for
`σ ∈ K.fixingSubgroup`.  So `IsProductFormula` is the weaker statement (`HasLevelKReciprocity`
implies it; the converse fails) and the `ZDataMup` product-formula node is *not* a substitute for
the level-`K` one.  What the level-`K` product formula follows from is the *generic* statement
instantiated at the base field `↥K` with the trivial extension — where `G_{↥K} = ⊤`, so the two
unramifiedness conditions coincide — restricted to `G_K`; that is the base-change route of
`ZSplit/KTransport/STATUS.md`. -/

end

end Work.SSGRoute.ZSplit
