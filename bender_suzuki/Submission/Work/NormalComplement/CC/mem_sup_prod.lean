import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NormalComplement.CC

/-- If `B` normalises `A`, every element of `A ⊔ B` is a product `a * b` with `a ∈ A`, `b ∈ B`. -/
theorem mem_sup_prod {G : Type*} [Group G] {A B : Subgroup G}
    (h : B ≤ Subgroup.normalizer (A : Set G)) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  -- `B` conjugates `A` into itself.
  have hN' : ∀ b ∈ B, ∀ n ∈ A, b * n * b⁻¹ ∈ A := by
    intro b hb n hn
    have hb' := (Subgroup.mem_set_normalizer_iff.mp (h hb)) n
    exact hb'.mp hn
  -- The set of products `a * b` (`a ∈ A`, `b ∈ B`) is a subgroup.
  let T : Subgroup G :=
    { carrier := {x : G | ∃ a ∈ A, ∃ b ∈ B, a * b = x}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, one_mul 1⟩
      mul_mem' := by
        rintro x y ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        exact ⟨a * (b * a' * b⁻¹), A.mul_mem ha (hN' b hb a' ha'),
               b * b', B.mul_mem hb hb', by group⟩
      inv_mem' := by
        rintro x ⟨a, ha, b, hb, rfl⟩
        exact ⟨b⁻¹ * a⁻¹ * b,
               by simpa using hN' b⁻¹ (B.inv_mem hb) a⁻¹ (A.inv_mem ha),
               b⁻¹, B.inv_mem hb, by group⟩ }
  have hAT : A ≤ T := fun a ha => ⟨a, ha, 1, B.one_mem, mul_one a⟩
  have hBT : B ≤ T := fun b hb => ⟨1, A.one_mem, b, hb, one_mul b⟩
  exact sup_le hAT hBT hx

end Work.NormalComplement.CC
