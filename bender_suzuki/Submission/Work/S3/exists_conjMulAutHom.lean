import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.S3

theorem exists_conjMulAutHom {G : Type} [Group G] {K P : Subgroup G}
    (hKinv : ∀ p ∈ P, ∀ k ∈ K, p * k * p⁻¹ ∈ K) :
    ∃ γ : ↥P →* MulAut ↥K, ∀ (p : ↥P) (k : ↥K), ((γ p k : ↥K) : G) = (p : G) * (k : G) * (p : G)⁻¹ := by
  -- Conjugation by an element of `P` maps `K` onto itself, because `P` normalizes `K`:
  -- `hKinv` supplies both the forward map and (applied to `p⁻¹ ∈ P`) the inverse map.
  let γ : ↥P →* MulAut ↥K :=
    { toFun := fun p =>
        { toFun := fun k => ⟨(p : G) * (k : G) * (p : G)⁻¹, hKinv (p : G) p.2 (k : G) k.2⟩
          invFun := fun k => ⟨(p : G)⁻¹ * (k : G) * (p : G),
            by simpa using hKinv (p : G)⁻¹ (P.inv_mem p.2) (k : G) k.2⟩
          left_inv := by intro k; ext; simp [mul_assoc]
          right_inv := by intro k; ext; simp [mul_assoc]
          map_mul' := by intro k1 k2; ext; simp [mul_assoc] }
      map_one' := by
        ext k
        simp
      map_mul' := by
        intro p q
        ext k
        simp [mul_assoc] }
  refine ⟨γ, ?_⟩
  intro p k
  rfl

end Work.S3
