import Mathlib

set_option linter.unusedVariables false

namespace Work.CORE4

/-- Pure computation: if `x` conjugates `z` to the power `z ^ j`, then `x` conjugates the
`m`-th power of `z ^ d` to the `(j * m)`-th power of `z ^ d`. -/
lemma conj_pow_zpow_mem {G : Type*} [Group G] (x z : G) (d : ℕ) (j : ℤ)
    (hj : z ^ j = x * z * x⁻¹) (m : ℤ) :
    x * (z ^ d) ^ m * x⁻¹ = (z ^ d) ^ (j * m) := by
  have h1 : (z ^ j) ^ d = (z ^ d) ^ j := by
    rw [← zpow_natCast (z ^ j) d, ← zpow_mul z j (d : ℤ),
      ← zpow_natCast z d, ← zpow_mul z (d : ℤ) j, mul_comm]
  rw [show x * (z ^ d) ^ m * x⁻¹ = MulAut.conj x ((z ^ d) ^ m) by rw [MulAut.conj_apply]]
  rw [map_zpow, map_pow, MulAut.conj_apply, ← hj, h1, ← zpow_mul]

/-- If `g` normalizes the cyclic subgroup `⟨z⟩`, then `g` normalizes `⟨z ^ d⟩` for *every*
`d : ℕ`: conjugation by `g` is an automorphism of `⟨z⟩`, hence sends the generator `z` to another
generator `z ^ j` of `⟨z⟩`, and then it sends `(z ^ d) ^ m` to `(z ^ d) ^ (j * m)`. -/
theorem normalizer_zpowers_le_normalizer_zpowers_pow {G : Type*} [Group G] (z : G) (d : ℕ) :
    Subgroup.normalizer (Subgroup.zpowers z : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers (z ^ d) : Set G) := by
  have key : ∀ x ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G),
      ∀ y ∈ Subgroup.zpowers (z ^ d : G), x * y * x⁻¹ ∈ Subgroup.zpowers (z ^ d : G) := by
    intro x hx y hy
    rw [Subgroup.mem_set_normalizer_iff] at hx
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp ((hx z).mp (Subgroup.mem_zpowers z))
    rw [Subgroup.mem_zpowers_iff] at hy ⊢
    obtain ⟨m, rfl⟩ := hy
    exact ⟨j * m, (conj_pow_zpow_mem x z d j hj m).symm⟩
  intro g hg
  rw [Subgroup.mem_set_normalizer_iff]
  intro y
  exact ⟨fun hy => key g hg y hy,
    fun hy => by
      have hmem := key g⁻¹ (Subgroup.inv_mem _ hg) (g * y * g⁻¹) hy
      rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at hmem⟩

theorem NormalizerZpowersDiv {G : Type*} [Group G] [Finite G] (z : G) {r : ℕ}
    (hr : r.Prime) (hrdvd : r ∣ orderOf z) :
    Subgroup.normalizer (Subgroup.zpowers z : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers (z ^ (orderOf z / r)) : Set G) := by
  exact normalizer_zpowers_le_normalizer_zpowers_pow z (orderOf z / r)

end Work.CORE4
