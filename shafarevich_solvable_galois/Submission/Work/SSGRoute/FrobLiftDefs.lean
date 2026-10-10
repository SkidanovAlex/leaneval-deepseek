import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.InertiaDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Frobenius-lift predicate for a finite place

For a number field `k`, an algebraic closure `Ω` and a finite place `A` of `Ω`, the decomposition
group `D_A = decomp k A` has the inertia subgroup `I_A = inertiaSub k Ω A` as a closed normal
subgroup, and the quotient `D_A/I_A` is procyclic (it is the Galois group of the residue field
extension, `Ẑ`).  The statement proved downstream is that the extension
`1 → I_A → D_A → D_A/I_A → 1` splits, i.e. that there is a *Frobenius lift* `σ ∈ D_A` whose
closed cyclic subgroup is a complement of `I_A` in `D_A`.

This file isolates the property of `σ` that is used to construct such a lift: `σ` generates
`D_A ⧸ (D_A ⊓ V)` for every open subgroup `V ≤ G_k` containing `I_A`.

## Definition

* `Work.SSGRoute.IsFrobLift k A σ` — `σ ∈ D_A` and `σ` generates `D_A ⧸ (D_A ⊓ V)` for every
  open `V ≤ G_k` with `I_A ≤ V`; the latter is expressed elementwise as
  `∀ δ ∈ D_A, ∃ m : ℤ, δ⁻¹ * σ ^ m ∈ V`.

Nothing here is `sorry`.
-/

open scoped Pointwise

namespace Work.SSGRoute

open _root_.SSGRoute

variable (k : Type) [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]

/-- **A Frobenius lift at the place `A`**, in the form used to build the complement of the inertia
subgroup: an element `σ ∈ D_A = decomp k A` whose class generates `D_A ⧸ (D_A ⊓ V)` for every open
subgroup `V ≤ G_k = Ω ≃ₐ[k] Ω` containing the inertia subgroup `I_A = inertiaSub k Ω A`.

Unfolded, this says: for every open `V` with `I_A ≤ V` and every `δ ∈ D_A` there is `m : ℤ` with
`δ⁻¹ * σ ^ m ∈ V`. -/
def IsFrobLift (A : ValuationSubring Ω) (σ : Ω ≃ₐ[k] Ω) : Prop :=
  σ ∈ SSGRoute.decomp k A ∧
    ∀ V : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (V : Set (Ω ≃ₐ[k] Ω)) →
      inertiaSub k Ω A ≤ V →
      ∀ δ ∈ SSGRoute.decomp k A, ∃ m : ℤ, δ⁻¹ * σ ^ m ∈ V

lemma IsFrobLift.mem_decomp {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]
    {A : ValuationSubring Ω} {σ : Ω ≃ₐ[k] Ω} (h : IsFrobLift k A σ) :
    σ ∈ SSGRoute.decomp k A := h.1

/-- The generation condition of `IsFrobLift`, applied with `δ⁻¹`: for an open `V` with
`I_A ≤ V` and any `δ ∈ D_A` there is `m` with `δ * σ ^ m ∈ V`. -/
lemma IsFrobLift.mul_zpow_mem {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]
    {A : ValuationSubring Ω} {σ : Ω ≃ₐ[k] Ω}
    (h : IsFrobLift k A σ) {V : Subgroup (Ω ≃ₐ[k] Ω)}
    (hV : IsOpen (V : Set (Ω ≃ₐ[k] Ω))) (hIV : inertiaSub k Ω A ≤ V)
    {δ : Ω ≃ₐ[k] Ω} (hδ : δ ∈ SSGRoute.decomp k A) :
    ∃ m : ℤ, δ * σ ^ m ∈ V := by
  obtain ⟨m, hm⟩ := h.2 V hV hIV δ⁻¹ ((SSGRoute.decomp k A).inv_mem hδ)
  refine ⟨m, ?_⟩
  rwa [inv_inv] at hm

end Work.SSGRoute
