import Mathlib
import Submission.Work.CORE3.Defs

/-!
# `Work.CORE3.NcardInvSetCentralizerConj`

If `g * a * g⁻¹ = b`, then `a` and `b` are `G`-conjugate, so their centralizers are conjugate
under the same element, and the number of involutions of `G` centralizing them is the same.

Concretely, conjugation by `g` is an automorphism of `G`; it carries `C_G(a)` onto
`C_G(g a g⁻¹) = C_G(b)` and preserves the order of every element, hence maps the set
`involutionSet ⊤ ∩ C_G(a)` bijectively (via the explicit bijection `y ↦ g * y * g⁻¹`) onto
`involutionSet ⊤ ∩ C_G(b)`.
-/

namespace Work.CORE3

open Subgroup

/-- Conjugation by `g` carries the centralizer of `a` onto the centralizer of `g * a * g⁻¹`:
`y` centralizes `a` iff `g * y * g⁻¹` centralizes `g * a * g⁻¹`. -/
private lemma conj_mem_centralizer_iff {G : Type} [Group G] (a g y : G) :
    (y ∈ Subgroup.centralizer ({a} : Set G)) ↔
      (g * y * g⁻¹ ∈ Subgroup.centralizer ({g * a * g⁻¹} : Set G)) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc (g * y * g⁻¹) * (g * a * g⁻¹) = g * (y * a) * g⁻¹ := by group
      _ = g * (a * y) * g⁻¹ := by rw [h]
      _ = (g * a * g⁻¹) * (g * y * g⁻¹) := by group
  · intro h
    have h2 := congrArg (fun z => g⁻¹ * z * g) h
    simpa [mul_assoc] using h2

/-- Conjugation preserves the order of an element. -/
private lemma orderOf_conj_eq {G : Type} [Group G] (g y : G) :
    orderOf (g * y * g⁻¹) = orderOf y := by
  have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y
  simpa [MulAut.conj_apply] using h

/-- Membership in `involutionSet ⊤` is just being of order two. -/
private lemma mem_involutionSet_top {G : Type} [Group G] {x : G} :
    x ∈ Work.GW2.involutionSet (⊤ : Subgroup G) ↔ orderOf x = 2 := by
  simp [Work.GW2.involutionSet]

/-- Conjugation by `g` maps `involutionSet ⊤ ∩ C_G(a)` onto `involutionSet ⊤ ∩ C_G(g a g⁻¹)`. -/
private lemma image_involutionSet_inter_centralizer {G : Type} [Group G] (a g : G) :
    (fun y : G => g * y * g⁻¹) ''
        (Work.GW2.involutionSet (⊤ : Subgroup G) ∩ Subgroup.centralizer ({a} : Set G))
      = Work.GW2.involutionSet (⊤ : Subgroup G) ∩
          Subgroup.centralizer ({g * a * g⁻¹} : Set G) := by
  ext x
  simp only [Set.mem_image, Set.mem_inter_iff, mem_involutionSet_top]
  constructor
  · rintro ⟨y, ⟨hord, hcen⟩, rfl⟩
    exact ⟨by rw [orderOf_conj_eq, hord], (conj_mem_centralizer_iff a g y).mp hcen⟩
  · rintro ⟨hord, hcen⟩
    refine ⟨g⁻¹ * x * g, ⟨?_, ?_⟩, by group⟩
    · have h1 : orderOf (g⁻¹ * x * g) = orderOf x := by
        simpa using orderOf_conj_eq g⁻¹ x
      rw [h1, hord]
    · have hyx : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
      exact (conj_mem_centralizer_iff a g (g⁻¹ * x * g)).mpr (by rw [hyx]; exact hcen)

theorem NcardInvSetCentralizerConj {G : Type} [Group G] (a b g : G) (h : g * a * g⁻¹ = b) :
    (Work.GW2.involutionSet (⊤ : Subgroup G) ∩ Subgroup.centralizer ({a} : Set G)).ncard =
      (Work.GW2.involutionSet (⊤ : Subgroup G) ∩ Subgroup.centralizer ({b} : Set G)).ncard := by
  subst h
  rw [← image_involutionSet_inter_centralizer a g]
  have hinj : Function.Injective (fun y : G => g * y * g⁻¹) :=
    fun p q hpq => mul_left_cancel (mul_right_cancel hpq)
  rw [Set.ncard_image_of_injective _ hinj]

end Work.CORE3
