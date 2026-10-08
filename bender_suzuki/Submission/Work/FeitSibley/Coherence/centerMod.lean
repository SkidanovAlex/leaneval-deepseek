import Submission.Work.FeitSibley.Coherence.engine

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.Coherence.centerMod`

Peterfalvi II, Appendice XII, step (1) works with `Z/Q₃ = Z(Q₁/Q₃)`.  This module provides the
preimage in `G` of that centre:

`centerMod h Q₃ = (Z(Q₁/Q₃)).comap (Q₁ →* Q₁/Q₃)`, pushed into `G`, i.e. the subgroup of `Q₁`
consisting of the elements centralising `Q₁` modulo `Q₃`.

The characteristic property is the elementwise one,
`x ∈ centerMod h Q₃ ↔ x ∈ Q₁ ∧ ∀ y ∈ Q₁, x·y·x⁻¹·y⁻¹ ∈ Q₃` (`mem_centerMod_iff`), and the
subgroup is normalised by `H` (`centerMod_normal`); these are the two facts the chief-series
descent of step (1) needs.

The normality of `Q₃` in `Q₁` is an instance argument, so that the definition is the plain
preimage map and its API is usable by `rw`/`simp`.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Classical

open scoped commutatorElement

namespace Work.FeitSibley.Coherence

variable {G : Type} [Group G] [Fintype G]

/-- **The preimage in `G` of `Z(Q₁/Q₃)`.** -/
noncomputable def centerMod (h : Work.FeitSibley.FSData G) (Q3 : Subgroup G)
    [(Q3.subgroupOf h.Q1).Normal] : Subgroup G :=
  ((Subgroup.center (↥h.Q1 ⧸ Q3.subgroupOf h.Q1)).comap
    (QuotientGroup.mk' (Q3.subgroupOf h.Q1))).map h.Q1.subtype

theorem centerMod_le (h : Work.FeitSibley.FSData G) (Q3 : Subgroup G)
    [(Q3.subgroupOf h.Q1).Normal] : centerMod h Q3 ≤ h.Q1 := by
  rintro x ⟨x', -, rfl⟩
  exact x'.2

/-- **The elementwise description of `centerMod`**: the elements of `Q₁` centralising `Q₁`
modulo `Q₃`. -/
theorem mem_centerMod_iff (h : Work.FeitSibley.FSData G) (Q3 : Subgroup G)
    [(Q3.subgroupOf h.Q1).Normal] {x : G} :
    x ∈ centerMod h Q3 ↔
      x ∈ h.Q1 ∧ ∀ y : G, y ∈ h.Q1 → x * y * x⁻¹ * y⁻¹ ∈ Q3 := by
  constructor
  · rintro ⟨x', hx', rfl⟩
    have hx'2 : QuotientGroup.mk' (Q3.subgroupOf h.Q1) x'
        ∈ Subgroup.center (↥h.Q1 ⧸ Q3.subgroupOf h.Q1) := hx'
    refine ⟨x'.2, fun y hy => ?_⟩
    have hcomm : (QuotientGroup.mk' (Q3.subgroupOf h.Q1) x')
          * (QuotientGroup.mk' (Q3.subgroupOf h.Q1) (⟨y, hy⟩ : ↥h.Q1))
        = (QuotientGroup.mk' (Q3.subgroupOf h.Q1) (⟨y, hy⟩ : ↥h.Q1))
          * (QuotientGroup.mk' (Q3.subgroupOf h.Q1) x') := by
      first
        | exact Subgroup.mem_center_iff.mp hx'2 _
        | exact (Subgroup.mem_center_iff.mp hx'2 _).symm
    have hgoal : x' * ⟨y, hy⟩ * x'⁻¹ * ⟨y, hy⟩⁻¹ ∈ Q3.subgroupOf h.Q1 := by
      rw [Subgroup.mem_subgroupOf]
      have h1 : QuotientGroup.mk' (Q3.subgroupOf h.Q1)
          (x' * ⟨y, hy⟩ * x'⁻¹ * ⟨y, hy⟩⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
        group
      exact (QuotientGroup.eq_one_iff (N := Q3.subgroupOf h.Q1) _).mp h1
    exact Subgroup.mem_subgroupOf.mp hgoal
  · rintro ⟨hxQ1, hxc⟩
    refine ⟨(⟨x, hxQ1⟩ : ↥h.Q1), ?_, rfl⟩
    show QuotientGroup.mk' (Q3.subgroupOf h.Q1) (⟨x, hxQ1⟩ : ↥h.Q1)
      ∈ Subgroup.center (↥h.Q1 ⧸ Q3.subgroupOf h.Q1)
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (Q3.subgroupOf h.Q1) w
    suffices key : (QuotientGroup.mk' (Q3.subgroupOf h.Q1) (⟨x, hxQ1⟩ : ↥h.Q1))
          * (QuotientGroup.mk' (Q3.subgroupOf h.Q1) y)
        = (QuotientGroup.mk' (Q3.subgroupOf h.Q1) y)
          * (QuotientGroup.mk' (Q3.subgroupOf h.Q1) (⟨x, hxQ1⟩ : ↥h.Q1)) by
      first | exact key | exact key.symm
    have h1 : (QuotientGroup.mk' (Q3.subgroupOf h.Q1) (⟨x, hxQ1⟩ : ↥h.Q1))
          * (QuotientGroup.mk' (Q3.subgroupOf h.Q1) y)
          * (QuotientGroup.mk' (Q3.subgroupOf h.Q1) (⟨x, hxQ1⟩ : ↥h.Q1))⁻¹
          * (QuotientGroup.mk' (Q3.subgroupOf h.Q1) y)⁻¹ = 1 := by
      have h := (QuotientGroup.eq_one_iff (N := Q3.subgroupOf h.Q1)
        ((⟨x, hxQ1⟩ : ↥h.Q1) * y * ⟨x, hxQ1⟩⁻¹ * y⁻¹)).mpr (by
          rw [Subgroup.mem_subgroupOf]
          simpa using hxc (y : G) y.2)
      simpa using h
    have h5 : (QuotientGroup.mk' (Q3.subgroupOf h.Q1) (⟨x, hxQ1⟩ : ↥h.Q1))
          * (QuotientGroup.mk' (Q3.subgroupOf h.Q1) y)
          * (QuotientGroup.mk' (Q3.subgroupOf h.Q1) (⟨x, hxQ1⟩ : ↥h.Q1))⁻¹
        = (QuotientGroup.mk' (Q3.subgroupOf h.Q1) y) := by
      have := congrArg (· * (QuotientGroup.mk' (Q3.subgroupOf h.Q1) y)) h1
      simpa [mul_assoc] using this
    have := congrArg (· * (QuotientGroup.mk' (Q3.subgroupOf h.Q1) (⟨x, hxQ1⟩ : ↥h.Q1))) h5
    simpa [mul_assoc] using this

/-- **`centerMod h Q₃` is normalised by `H`.**  An element of `H` conjugates the defining
condition into itself, since `H` normalises both `Q₁` and `Q₃`. -/
theorem centerMod_normal (h : Work.FeitSibley.FSData G) (Q3 : Subgroup G)
    [(Q3.subgroupOf h.Q1).Normal] (hQ3n : h.H ≤ Subgroup.normalizer (Q3 : Set G)) :
    h.H ≤ Subgroup.normalizer (centerMod h Q3 : Set G) := by
  have hQ1n : ∀ a ∈ h.H, ∀ b ∈ h.Q1, a * b * a⁻¹ ∈ h.Q1 :=
    Subgroup.le_normalizer_iff.mp h.Q1_normal_in_H
  have hQ3nn : ∀ a ∈ h.H, ∀ b ∈ Q3, a * b * a⁻¹ ∈ Q3 :=
    Subgroup.le_normalizer_iff.mp hQ3n
  rw [Subgroup.le_normalizer_iff]
  intro t ht x hx
  rw [mem_centerMod_iff] at hx ⊢
  obtain ⟨hxQ1, hxc⟩ := hx
  refine ⟨hQ1n t ht x hxQ1, fun y hy => ?_⟩
  have hy' : t⁻¹ * y * t ∈ h.Q1 := by
    simpa using hQ1n t⁻¹ (h.H.inv_mem ht) y hy
  have h1 : (t * x * t⁻¹) * y * (t * x * t⁻¹)⁻¹ * y⁻¹
      = t * (x * (t⁻¹ * y * t) * x⁻¹ * (t⁻¹ * y * t)⁻¹) * t⁻¹ := by group
  rw [h1]
  exact hQ3nn t ht _ (hxc (t⁻¹ * y * t) hy')

/-- **`centerMod h Q₃` is a proper subgroup of `Q₁`** when `Q₃` is a proper subgroup of a
subgroup `Q₂ ≤ [Q₁,Q₁]` containing it: if every element of `Q₁` centralised `Q₁` modulo `Q₃`
then `Q₁/Q₃` would be abelian, i.e. `[Q₁,Q₁] ≤ Q₃`, forcing `Q₂ = Q₃`. -/
theorem centerMod_ne_Q1 (h : Work.FeitSibley.FSData G) (Q3 Q2 : Subgroup G)
    [(Q3.subgroupOf h.Q1).Normal] (hQ3Q2 : Q3 ≤ Q2) (hQ2' : Q2 ≤ ⁅h.Q1, h.Q1⁆)
    (hne : Q3 ≠ Q2) : centerMod h Q3 ≠ h.Q1 := by
  intro heq
  have hQ1'le : ⁅h.Q1, h.Q1⁆ ≤ Q3 := by
    rw [Subgroup.commutator_def]
    refine (Subgroup.closure_le Q3).mpr ?_
    rintro g ⟨a, ha, b, hb, rfl⟩
    have ha' : a ∈ centerMod h Q3 := heq.symm ▸ ha
    have h := (mem_centerMod_iff h Q3).mp ha'
    exact h.2 b hb
  exact hne (le_antisymm hQ3Q2 (hQ2'.trans hQ1'le))

end Work.FeitSibley.Coherence
