import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Frobenius groups: definitions

This is the base module of area A8 (Frobenius groups) of the Feit--Thompson
(odd order theorem) drive.

A subgroup `H ≤ G` is a **Frobenius complement** if it is nontrivial, proper and
`H ∩ H^g = 1` for every `g ∉ H` (`IsFrobeniusComplement`).  The associated
**Frobenius kernel** (a priori only a set) is `{1}` together with the elements which
are not conjugate into `H` (`frobeniusKernel`).  The main theorem of the area,
`Work.Frobenius.frobenius_theorem`, shows that this set is the carrier of a normal
subgroup which is a complement to `H`.

A group `G` with subgroups `K`, `H` is a **Frobenius group with kernel `K` and
complement `H`** if `K` is normal, `K ⊓ H = ⊥`, `K ⊔ H = ⊤` and `H` acts
fixed-point-freely on `K` by conjugation (`IsFrobeniusGroupWithKernel`); see
`Work.Frobenius.isFrobeniusComplement_iff_isFrobeniusGroupWithKernel` for the
equivalence with the complement condition.

The conventions are those of area A8 of `Submission/Work/NOTES_LEAD_ft_blueprint.md`:
everything is universe-polymorphic; conjugation of subgroups is Mathlib's pointwise
`MulAut.conj g • H`, so that `x ∈ MulAut.conj g • H ↔ g⁻¹ * x * g ∈ H`.
-/

@[expose] public section

noncomputable section

open Classical

open scoped Pointwise

namespace Work.Frobenius

variable {G : Type*} [Group G]

/-- `H` is a Frobenius complement in `G`: `H` is nontrivial and proper, and any two
distinct conjugates of `H` intersect trivially. -/
structure IsFrobeniusComplement (H : Subgroup G) : Prop where
  ne_bot : H ≠ ⊥
  ne_top : H ≠ ⊤
  ti : ∀ g : G, g ∉ H → H ⊓ MulAut.conj g • H = ⊥

/-- The Frobenius kernel associated with a subgroup `H`: the identity together with all
elements which are not conjugate into `H`. -/
def frobeniusKernel (H : Subgroup G) : Set G :=
  {1} ∪ (Set.univ \ ⋃ g : G, (MulAut.conj g • H : Set G))

/-- `H` acts fixed-point-freely on `K` (by conjugation in `G`). -/
def IsFixedPointFreeOn (K H : Subgroup G) : Prop :=
  ∀ ⦃h : G⦄, h ∈ H → h ≠ 1 → ∀ ⦃k : G⦄, k ∈ K → h * k * h⁻¹ = k → k = 1

/-- `G` is a Frobenius group with kernel `K` and complement `H`. -/
structure IsFrobeniusGroupWithKernel (K H : Subgroup G) : Prop where
  normal : K.Normal
  inf_eq_bot : K ⊓ H = ⊥
  sup_eq_top : K ⊔ H = ⊤
  fpf : IsFixedPointFreeOn K H

section Mem

variable {H : Subgroup G}

/-- Conjugation of subgroups: `x ∈ H^g ↔ g⁻¹ x g ∈ H`. -/
theorem mem_conj_smul_iff {g x : G} {H : Subgroup G} :
    x ∈ (MulAut.conj g • H) ↔ g⁻¹ * x * g ∈ H := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def, MulAut.conj_inv_apply]

/-- Conjugation of subgroups, set-valued form. -/
theorem mem_conj_smul_iff' {g x : G} {H : Subgroup G} :
    x ∈ (MulAut.conj g • H : Set G) ↔ g⁻¹ * x * g ∈ H := by
  rw [← Subgroup.coe_pointwise_smul]
  exact mem_conj_smul_iff

/-- Membership in the Frobenius kernel, in terms of non-conjugacy. -/
theorem mem_frobeniusKernel_iff {x : G} :
    x ∈ frobeniusKernel H ↔ x = 1 ∨ ∀ g : G, g⁻¹ * x * g ∉ H := by
  rw [frobeniusKernel]
  constructor
  · rintro (h | h)
    · exact Or.inl h
    · refine Or.inr fun g hg => ?_
      exact h.2 (Set.mem_iUnion.mpr ⟨g, mem_conj_smul_iff'.mpr hg⟩)
  · rintro (h | h)
    · exact Or.inl h
    · refine Or.inr ⟨Set.mem_univ _, ?_⟩
      rw [Set.mem_iUnion]
      rintro ⟨g, hg⟩
      exact h g (mem_conj_smul_iff'.mp hg)

theorem one_mem_frobeniusKernel : (1 : G) ∈ frobeniusKernel H :=
  mem_frobeniusKernel_iff.mpr (Or.inl rfl)

/-- Elements of `H` lie in the Frobenius kernel only if they are trivial. -/
theorem mem_frobeniusKernel_of_mem_complement {x : G} (hx : x ∈ H) :
    x ∈ frobeniusKernel H ↔ x = 1 := by
  refine ⟨fun h => ?_, fun h => h ▸ one_mem_frobeniusKernel⟩
  rw [mem_frobeniusKernel_iff] at h
  rcases h with h | h
  · exact h
  · exact absurd (by simpa using hx) (h 1)

/-- The Frobenius kernel is invariant under conjugation. -/
theorem conj_mem_frobeniusKernel {x y : G} (hx : x ∈ frobeniusKernel H) :
    y * x * y⁻¹ ∈ frobeniusKernel H := by
  rw [mem_frobeniusKernel_iff] at hx ⊢
  rcases hx with rfl | hx
  · simp
  · right
    intro g hconj
    refine hx (y⁻¹ * g) ?_
    have : (y⁻¹ * g)⁻¹ * x * (y⁻¹ * g) = g⁻¹ * (y * x * y⁻¹) * g := by group
    rw [this]; exact hconj

end Mem

/-- `K` and `H` are complements in `G` (Mathlib's `Subgroup.IsComplement'`): every element of
`G` is uniquely a product `k * h` with `k ∈ K`, `h ∈ H`. -/
abbrev IsComplement' (K H : Subgroup G) : Prop := Subgroup.IsComplement' K H

theorem isComplement'_iff (K H : Subgroup G) : IsComplement' K H ↔ Subgroup.IsComplement' K H :=
  Iff.rfl

end Work.Frobenius
