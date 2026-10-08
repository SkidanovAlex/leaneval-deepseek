import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.thompsonJ_characteristic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Z(J(P))` is characteristic in `P`

`Work.PGroup.ZJ P = Z(J(P))` is the center of the Thompson subgroup of `P`.  Since `J(P)` is
characteristic in `P` (`Work.PGroup.thompsonJ_characteristic`) and the center construction
commutes with conjugation (`Work.PGroup.centerIn_conj`), the center of `J(P)` is invariant under
conjugation by every element of the normalizer of `P`; i.e. `Z(J(P))` is *characteristic* in
`P`.  This is the formal content of the phrase "`Z(J(P))` is characteristic in `P`" used in the
Feit–Thompson development.
-/

open scoped Classical Pointwise
open Subgroup

noncomputable section

namespace Work.PGroup

/-- Membership in a conjugate of a subgroup: `x ∈ gHg⁻¹ ↔ g⁻¹ x g ∈ H`. -/
private lemma mem_conjBy_iff_aux {G : Type*} [Group G] {g x : G} {H : Subgroup G} :
    x ∈ Work.PGroup.conjBy g H ↔ g⁻¹ * x * g ∈ H := by
  rw [Work.PGroup.conjBy, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
    MulAut.conj_inv_apply]

/-- The center of a subgroup `H ≤ G`, viewed as a subgroup of `G`, consists of the elements of
`H` commuting elementwise with `H`. -/
theorem mem_centerIn_iff {G : Type*} [Group G] {H : Subgroup G} {x : G} :
    x ∈ Work.PGroup.centerIn H ↔ x ∈ H ∧ ∀ y ∈ H, y * x = x * y := by
  rw [Work.PGroup.centerIn]
  constructor
  · intro hx
    obtain ⟨c, hc, hcx⟩ := hx
    refine ⟨?_, ?_⟩
    · rw [← hcx]; exact c.2
    · intro y hy
      have h2 : y * (c : G) = (c : G) * y := by
        have := congrArg (Subtype.val) (Subgroup.mem_center_iff.mp hc ⟨y, hy⟩)
        simpa using this
      rw [← hcx]
      exact h2
  · rintro ⟨hxH, hcomm⟩
    exact ⟨⟨x, hxH⟩, Subgroup.mem_center_iff.mpr (fun w => Subtype.ext (hcomm w.val w.2)), rfl⟩

/-- Conjugation commutes with taking centers of subgroups: `g Z(H) g⁻¹ = Z(g H g⁻¹)`. -/
theorem centerIn_conj {G : Type*} [Group G] (g : G) (H : Subgroup G) :
    Work.PGroup.conjBy g (Work.PGroup.centerIn H) =
      Work.PGroup.centerIn (Work.PGroup.conjBy g H) := by
  ext x
  rw [mem_conjBy_iff_aux, mem_centerIn_iff, mem_centerIn_iff]
  constructor
  · rintro ⟨hxH, hcomm⟩
    refine ⟨mem_conjBy_iff_aux.mpr hxH, ?_⟩
    intro y hy
    have hyH : g⁻¹ * y * g ∈ H := mem_conjBy_iff_aux.mp hy
    have h := hcomm (g⁻¹ * y * g) hyH
    calc y * x = g * ((g⁻¹ * y * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * (g⁻¹ * y * g)) * g⁻¹ := by rw [h]
      _ = x * y := by group
  · rintro ⟨hxConj, hcomm⟩
    refine ⟨mem_conjBy_iff_aux.mp hxConj, ?_⟩
    intro y hy
    have hyC : g * y * g⁻¹ ∈ Work.PGroup.conjBy g H := by
      apply mem_conjBy_iff_aux.mpr
      have : g⁻¹ * (g * y * g⁻¹) * g = y := by group
      rw [this]; exact hy
    have h := hcomm (g * y * g⁻¹) hyC
    calc y * (g⁻¹ * x * g) = g⁻¹ * ((g * y * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * y * g⁻¹)) * g := by rw [h]
      _ = (g⁻¹ * x * g) * y := by group

/-- `Z(J(P))` is characteristic in `P`: it is invariant under conjugation by every element of
the normalizer of `P`. -/
theorem ZJ_characteristic {G : Type*} [Group G] (P : Subgroup G) (g : G)
    (hg : g ∈ Subgroup.normalizer (P : Set G)) :
    Work.PGroup.conjBy g (Work.PGroup.ZJ P) = Work.PGroup.ZJ P := by
  show Work.PGroup.conjBy g (Work.PGroup.centerIn (Work.PGroup.thompsonJ P)) =
    Work.PGroup.centerIn (Work.PGroup.thompsonJ P)
  rw [centerIn_conj, thompsonJ_characteristic P g hg]

end Work.PGroup
