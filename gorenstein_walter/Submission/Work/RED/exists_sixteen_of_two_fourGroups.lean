import Mathlib
import Submission.Work.RED.Basic

/-!
# Two disjoint commuting four-groups generate an elementary abelian group of order 16

If `V₁` and `V₂` are Klein four-subgroups of `G` with `V₁ ⊓ V₂ = ⊥` and commuting
elementwise, then `W = V₁ ⊔ V₂` is an internal direct product `V₁ × V₂`, hence has
order `4 · 4 = 16`, and every element of `W` is an involution (`W` is elementary
abelian of type `(2,2,2,2)`).

The elementwise commutation makes `V₂` normalize `V₁`, so the carrier of `V₁ ⊔ V₂`
is the pointwise product `V₁ * V₂`; multiplication then gives a bijection
`V₁ × V₂ ≃ W`.
-/

open scoped Pointwise

namespace Work.RED

theorem exists_sixteen_of_two_fourGroups {G : Type*} [Group G]
    {V₁ V₂ : Subgroup G} (h₁ : Work.RED.GW2.IsFourGroup V₁) (h₂ : Work.RED.GW2.IsFourGroup V₂)
    (hdisj : V₁ ⊓ V₂ = ⊥) (hcomm : ∀ x ∈ V₁, ∀ y ∈ V₂, x * y = y * x) :
    ∃ W : Subgroup G, Nat.card W = 16 ∧ ∀ x ∈ W, x ^ 2 = 1 := by
  have hV2leN : V₂ ≤ Subgroup.normalizer (V₁ : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro y hy x hx
    rw [← hcomm x hx y hy]
    simpa using hx
  let W : Subgroup G := V₁ ⊔ V₂
  have hcoe : (↑W : Set G) = (V₁ : Set G) * (V₂ : Set G) := by
    simpa [W] using Subgroup.coe_mul_of_right_le_normalizer_left V₁ V₂ hV2leN
  let f' : V₁ × V₂ → W := fun p => ⟨(p.1 : G) * (p.2 : G),
    Subgroup.mul_mem W (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)⟩
  have hf' : Function.Bijective f' := by
    constructor
    · rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
      have hh : (a₁ : G) * b₁ = (a₂ : G) * b₂ := by
        simpa only [f'] using congrArg Subtype.val h
      have hab : (b₁ : G) * (b₂ : G)⁻¹ = (a₁ : G)⁻¹ * a₂ := by
        have := congrArg (fun t => (a₁ : G)⁻¹ * t * (b₂ : G)⁻¹) hh
        simpa [mul_assoc] using this
      have hmem : (a₁ : G)⁻¹ * a₂ ∈ V₁ ⊓ V₂ :=
        Subgroup.mem_inf.mpr
          ⟨Subgroup.mul_mem V₁ (Subgroup.inv_mem V₁ a₁.2) a₂.2,
           hab.symm ▸ Subgroup.mul_mem V₂ b₁.2 (Subgroup.inv_mem V₂ b₂.2)⟩
      rw [hdisj] at hmem
      simp at hmem
      have ha : (a₁ : G) = a₂ := inv_mul_eq_one.mp hmem
      have hb : (b₁ : G) = b₂ := by
        rw [ha] at hh
        exact mul_left_cancel hh
      exact Prod.ext (Subtype.ext ha) (Subtype.ext hb)
    · intro w
      have hw : (w : G) ∈ (V₁ : Set G) * (V₂ : Set G) := by
        rw [← hcoe]
        exact w.2
      rw [Set.mem_mul] at hw
      obtain ⟨a, ha, b, hb, hab⟩ := hw
      refine ⟨(⟨a, ha⟩, ⟨b, hb⟩), ?_⟩
      apply Subtype.ext
      change (a : G) * b = (w : G)
      exact hab
  have hcardW : Nat.card W = 16 := by
    have hc : Nat.card (V₁ × V₂) = Nat.card W := Nat.card_congr (Equiv.ofBijective f' hf')
    rw [Nat.card_prod, h₁.1, h₂.1] at hc
    norm_num at hc
    exact hc.symm
  refine ⟨W, hcardW, ?_⟩
  intro x hx
  have hx' : x ∈ (V₁ : Set G) * (V₂ : Set G) := by
    rw [← hcoe]
    exact hx
  rw [Set.mem_mul] at hx'
  obtain ⟨a, ha, b, hb, hab⟩ := hx'
  rw [← hab, Commute.mul_pow (hcomm a ha b hb) 2, h₁.2 a ha, h₂.2 b hb]
  simp

end Work.RED
