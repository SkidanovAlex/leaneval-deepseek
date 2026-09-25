import Mathlib
import Submission.NK.LocalAnabelian.ResidueField.Defs

/-!
# The inertia subgroup is the fixing subgroup of `κ(μ_{p'})`

`unramifiedClosure p` is the compositum `κ(μ_{p'}) = ⨆ κ⟮ζ⟯` over all primitive roots of
unity of order prime to `p`, and `inertiaSubgroup p` collects the automorphisms acting
trivially on all of them.  This file records the tautological-but-useful identification
of the two subgroups of `Gal(K'/κ)`:

  `inertiaSubgroup p = (unramifiedClosure p).fixingSubgroup`.

The content is entirely bookkeeping about `IntermediateField.fixingSubgroup`: it turns
`iSup`s of intermediate fields into `iInf`s of subgroups and evaluates the fixing subgroup
of a simple extension `κ⟮ζ⟯` on the generator `ζ`.
-/

open scoped Classical
open IntermediateField

namespace NK.LocalAnabelian.ResidueField

variable {κ K' : Type*} [Field κ] [Field K'] [Algebra κ K']

/-! ## Two structural lemmas about `IntermediateField.fixingSubgroup` -/

/-- The fixing subgroup of a supremum of intermediate fields is the infimum of the fixing
subgroups.  (The pair `(fixingSubgroup, fixedField)` is a Galois connection, and `fixingSubgroup`
is the upper adjoint, hence preserves `iInf`s.) -/
theorem fixingSubgroup_iSup {ι : Sort*} (f : ι → IntermediateField κ K') :
    (⨆ i, f i).fixingSubgroup = ⨅ i, (f i).fixingSubgroup := by
  refine le_antisymm ?_ ?_
  · refine le_iInf fun i => IntermediateField.fixingSubgroup_le (le_iSup f i)
  · intro σ hσ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hle : ∀ i, f i ≤ IntermediateField.fixedField (Subgroup.zpowers σ) := by
      intro i
      rw [IntermediateField.le_iff_le]
      exact Subgroup.zpowers_le.mpr (Subgroup.mem_iInf.mp hσ i)
    have hx' : x ∈ IntermediateField.fixedField (Subgroup.zpowers σ) := (iSup_le hle) hx
    rw [IntermediateField.mem_fixedField_iff] at hx'
    exact hx' σ (Subgroup.mem_zpowers σ)

/-- A `κ`-automorphism of `K'` fixes the simple extension `κ⟮ζ⟯` if and only if it fixes the
generator `ζ`. -/
theorem mem_fixingSubgroup_adjoin_singleton_iff (ζ : K') (σ : Gal(K'/κ)) :
    σ ∈ (κ⟮ζ⟯).fixingSubgroup ↔ σ ζ = ζ := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h
    exact h ζ (IntermediateField.mem_adjoin_simple_self κ ζ)
  · intro h x hx
    have h1 : ∀ y ∈ κ⟮ζ⟯, σ • y = y := by
      rw [IntermediateField.forall_mem_adjoin_smul_eq_self_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      rw [AlgEquiv.smul_def]
      exact h
    rw [← AlgEquiv.smul_def]
    exact h1 x hx

/-! ## The main identification -/

theorem inertiaSubgroup_eq_fixingSubgroup_unramifiedClosure {κ K' : Type*} [Field κ] [Field K']
    [Algebra κ K'] (p : ℕ) :
    inertiaSubgroup (κ := κ) (K' := K') p =
      (unramifiedClosure (κ := κ) (K' := K') p).fixingSubgroup := by
  ext σ
  rw [mem_inertiaSubgroup_iff]
  simp only [unramifiedClosure, fixingSubgroup_iSup, Subgroup.mem_iInf,
    mem_fixingSubgroup_adjoin_singleton_iff]
  rw [Subtype.forall]

end NK.LocalAnabelian.ResidueField
