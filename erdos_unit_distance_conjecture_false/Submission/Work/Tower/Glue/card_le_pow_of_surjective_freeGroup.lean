import Mathlib

namespace Work.Tower.Glue

/-- Every value of a hom out of a free group on `Fin d`, landing in a commutative group,
is a product of integer powers of the images of the `d` generators. -/
theorem exists_zpow_prod_eq {G : Type*} [CommGroup G] {d : ℕ} (φ : FreeGroup (Fin d) →* G)
    (w : FreeGroup (Fin d)) : ∃ a : Fin d → ℤ, φ w = ∏ i, φ (.of i) ^ a i := by
  induction w using FreeGroup.induction_on with
  | one => exact ⟨0, by simp⟩
  | of x =>
    refine ⟨Pi.single x 1, Eq.symm ?_⟩
    rw [Finset.prod_eq_single x (fun b _ hb ↦ by rw [Pi.single_eq_of_ne hb, zpow_zero])
      (fun h ↦ absurd (Finset.mem_univ x) h)]
    rw [Pi.single_eq_same, zpow_one]
  | inv_of x ih =>
    obtain ⟨a, ha⟩ := ih
    refine ⟨-a, ?_⟩
    rw [map_inv, ha, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [Pi.neg_apply, ← zpow_neg]
  | mul u v hu hv =>
    obtain ⟨a, ha⟩ := hu
    obtain ⟨b, hb⟩ := hv
    refine ⟨a + b, ?_⟩
    rw [map_mul, ha, hb, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [Pi.add_apply, ← zpow_add]

/-- In a group where `x ^ 3 = 1`, integer powers of `x` only depend on the exponent mod `3`. -/
theorem zpow_eq_pow_toNat_emod {G : Type*} [CommGroup G] {x : G} (hx : x ^ 3 = 1) (a : ℤ) :
    x ^ a = x ^ ((a % 3).toNat : ℕ) := by
  have hx3 : x ^ (3 : ℤ) = 1 := by
    rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]; exact hx
  conv_lhs => rw [← Int.emod_add_mul_ediv a 3]
  rw [zpow_add, zpow_mul, hx3, one_zpow, mul_one, ← zpow_natCast,
    Int.toNat_of_nonneg (Int.emod_nonneg a (by norm_num))]

theorem card_le_pow_of_surjective_freeGroup {G : Type*} [CommGroup G] [Fintype G]
    (h3 : ∀ g : G, g ^ 3 = 1) {d : ℕ} (φ : FreeGroup (Fin d) →* G)
    (hφ : Function.Surjective φ) : Fintype.card G ≤ 3 ^ d := by
  have hmod : ∀ a : ℤ, (a % 3).toNat < 3 := fun a ↦ by
    have h1 : 0 ≤ a % 3 := Int.emod_nonneg _ (by norm_num)
    have h2 : a % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
    omega
  -- Every element of `G` is a product of powers (with exponents in `Fin 3`) of the images
  -- of the `d` generators, so `G` is a quotient of `Fin d → Fin 3`.
  have hF : Function.Surjective (fun b : Fin d → Fin 3 ↦ ∏ i, φ (.of i) ^ (b i : ℕ)) := by
    intro g
    obtain ⟨w, rfl⟩ := hφ g
    obtain ⟨a, ha⟩ := exists_zpow_prod_eq φ w
    refine ⟨fun i ↦ ⟨(a i % 3).toNat, hmod (a i)⟩, ?_⟩
    rw [ha]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    exact (zpow_eq_pow_toNat_emod (h3 _) (a i)).symm
  calc Fintype.card G ≤ Fintype.card (Fin d → Fin 3) := Fintype.card_le_of_surjective _ hF
    _ = 3 ^ d := by simp [Fintype.card_pi]

end Work.Tower.Glue
