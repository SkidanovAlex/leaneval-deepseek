import Mathlib
import Submission.Work.ZassenhausSuzuki.Odd.OddDefs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki.Odd

/-- "Being a product of two involutions" is invariant under conjugation. -/
theorem isStronglyReal_conj {G : Type} [Group G] {g x : G}
    (h : IsStronglyReal x) : IsStronglyReal (g * x * g⁻¹) := by
  obtain ⟨a, b, ha, hb, hab⟩ := h
  refine ⟨g * a * g⁻¹, g * b * g⁻¹, ?_, ?_, ?_⟩
  · calc (g * a * g⁻¹) * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by rw [ha]; simp
  · calc (g * b * g⁻¹) * (g * b * g⁻¹) = g * (b * b) * g⁻¹ := by group
      _ = 1 := by rw [hb]; simp
  · calc (g * a * g⁻¹) * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * x * g⁻¹ := by rw [hab]

/-- The converse of `isStronglyReal_conj`, i.e. conjugating back. -/
theorem isStronglyReal_of_conj {G : Type} [Group G] {g x : G}
    (h : IsStronglyReal (g * x * g⁻¹)) : IsStronglyReal x := by
  have h' := isStronglyReal_conj (g := g⁻¹) h
  rw [show (g⁻¹) * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x by group] at h'
  exact h'

/-- `IsStronglyReal` is a conjugacy invariant. -/
theorem isStronglyReal_conj_iff {G : Type} [Group G] (g x : G) :
    IsStronglyReal (g * x * g⁻¹) ↔ IsStronglyReal x :=
  ⟨isStronglyReal_of_conj, isStronglyReal_conj⟩

/-- `BadOdd` is a conjugacy invariant: the class of the set of odd-order elements that are
not strongly real. -/
theorem badOdd_conj {G : Type} [Group G] {g y : G}
    (hy : Work.ZassenhausSuzuki.Odd.BadOdd y) :
    Work.ZassenhausSuzuki.Odd.BadOdd (g * y * g⁻¹) := by
  unfold Work.ZassenhausSuzuki.Odd.BadOdd at hy ⊢
  obtain ⟨hodd, hy1, hnsr⟩ := hy
  have horder : orderOf (g * y * g⁻¹) = orderOf y := by
    rw [← MulAut.conj_apply g y]
    exact MulEquiv.orderOf_eq (MulAut.conj g) y
  refine ⟨?_, ?_, ?_⟩
  · rw [horder]; exact hodd
  · intro h
    apply hy1
    have hc : g⁻¹ * (g * y * g⁻¹) * g = 1 := by rw [h]; simp
    have h2 : g⁻¹ * (g * y * g⁻¹) * g = y := by group
    rwa [h2] at hc
  · intro h
    exact hnsr (isStronglyReal_of_conj (g := g) h)

end Work.ZassenhausSuzuki.Odd
