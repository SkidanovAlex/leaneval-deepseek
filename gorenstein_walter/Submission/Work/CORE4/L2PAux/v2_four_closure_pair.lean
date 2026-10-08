import Mathlib

namespace Work.CORE4.L2PAux

/-- Two distinct (nontrivial) commuting involutions generate a Klein four group:
the subgroup they generate has exactly four elements and every element is an involution. -/
theorem v2_four_closure_pair {G : Type*} [Group G] (u v : G) (hu : u ^ 2 = 1) (hv : v ^ 2 = 1)
    (hc : u * v = v * u) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v) :
    Nat.card (Subgroup.closure ({u, v} : Set G)) = 4 ∧
      ∀ w ∈ Subgroup.closure ({u, v} : Set G), w ^ 2 = 1 := by
  have hu' : u * u = 1 := by rw [← pow_two]; exact hu
  have hv' : v * v = 1 := by rw [← pow_two]; exact hv
  have huv2 : (u * v) ^ 2 = 1 := by
    rw [pow_two, mul_assoc u v (u * v), hc, ← mul_assoc v v u, hv', one_mul, hu']
  have huv' : (u * v) * (u * v) = 1 := by rw [← pow_two]; exact huv2
  have hne1 : u * v ≠ 1 := fun h => huv ((mul_left_cancel (h.trans hu'.symm)).symm)
  have hne2 : u * v ≠ u := fun h => hv1 (mul_left_cancel (h.trans (mul_one u).symm))
  have hne3 : u * v ≠ v := fun h => hu1 (mul_right_cancel (h.trans (one_mul v).symm))
  have hpvu : v * u = u * v := hc.symm
  have hpuuv : u * (u * v) = v := by rw [← mul_assoc u u v, hu', one_mul]
  have hpvuv : v * (u * v) = u := by rw [hc, ← mul_assoc v v u, hv', one_mul]
  have hpuvu : (u * v) * u = v := by rw [hc, mul_assoc v u u, hu', mul_one]
  have hpuvv : (u * v) * v = u := by rw [mul_assoc u v v, hv', mul_one]
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu'
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv'
  have huvinv : (u * v)⁻¹ = u * v := inv_eq_of_mul_eq_one_right huv'
  let H : Subgroup G := Subgroup.closure ({u, v} : Set G)
  let T : Set G := ({1, u, v, u * v} : Set G)
  have huH : u ∈ H := Subgroup.subset_closure (by simp)
  have hvH : v ∈ H := Subgroup.subset_closure (by simp)
  have he1H : (1 : G) ∈ H := one_mem H
  have huvH : u * v ∈ H := mul_mem huH hvH
  have memT : ∀ x : G, x ∈ T ↔ (x = 1 ∨ x = u ∨ x = v ∨ x = u * v) := by
    intro x
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff]
  have hHsubT : (H : Set G) ⊆ T := by
    intro x hx
    rw [memT x]
    refine Subgroup.closure_induction (k := ({u, v} : Set G))
      (p := fun x _ => x = 1 ∨ x = u ∨ x = v ∨ x = u * v) ?_ ?_ ?_ ?_ hx
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with h | h
      · subst h; exact Or.inr (Or.inl rfl)
      · subst h; exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inl rfl
    · intro y z hy hz ihy ihz
      rcases ihy with rfl | rfl | rfl | rfl <;> rcases ihz with rfl | rfl | rfl | rfl <;>
        simp [hu', hv', hpvu, hpuuv, hpvuv, hpuvu, hpuvv, huv']
    · intro y hy ihy
      rcases ihy with rfl | rfl | rfl | rfl
      · exact Or.inl (by simp)
      · exact Or.inr (Or.inl huinv)
      · exact Or.inr (Or.inr (Or.inl hvinv))
      · exact Or.inr (Or.inr (Or.inr huvinv))
  have hTsubH : T ⊆ (H : Set G) := by
    intro x hx
    rw [memT x] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact he1H
    · exact huH
    · exact hvH
    · exact huvH
  let e : Fin 4 → H
    | 0 => ⟨1, he1H⟩
    | 1 => ⟨u, huH⟩
    | 2 => ⟨v, hvH⟩
    | 3 => ⟨u * v, huvH⟩
  have hd01 : e 0 ≠ e 1 := fun h => hu1 (Subtype.ext_iff.mp h).symm
  have hd02 : e 0 ≠ e 2 := fun h => hv1 (Subtype.ext_iff.mp h).symm
  have hd03 : e 0 ≠ e 3 := fun h => hne1 (Subtype.ext_iff.mp h).symm
  have hd12 : e 1 ≠ e 2 := fun h => huv (Subtype.ext_iff.mp h)
  have hd13 : e 1 ≠ e 3 := fun h => hne2 (Subtype.ext_iff.mp h).symm
  have hd23 : e 2 ≠ e 3 := fun h => hne3 (Subtype.ext_iff.mp h).symm
  have hinj : Function.Injective e := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | rfl
        | exact absurd hij hd01
        | exact absurd hij hd02
        | exact absurd hij hd03
        | exact absurd hij hd12
        | exact absurd hij hd13
        | exact absurd hij hd23
        | exact absurd hij.symm hd01
        | exact absurd hij.symm hd02
        | exact absurd hij.symm hd03
        | exact absurd hij.symm hd12
        | exact absurd hij.symm hd13
        | exact absurd hij.symm hd23
  have hsurj : Function.Surjective e := by
    intro x
    have hxT : (x : G) ∈ T := hHsubT x.2
    rw [memT (x : G)] at hxT
    rcases hxT with h | h | h | h
    · exact ⟨0, by apply Subtype.ext; rw [h]⟩
    · exact ⟨1, by apply Subtype.ext; rw [h]⟩
    · exact ⟨2, by apply Subtype.ext; rw [h]⟩
    · exact ⟨3, by apply Subtype.ext; rw [h]⟩
  constructor
  · have hbij : Function.Bijective e := ⟨hinj, hsurj⟩
    have h1 := Nat.card_eq_of_bijective e hbij
    rw [Nat.card_fin 4] at h1
    exact h1.symm
  · intro w hw
    have hwT : w ∈ T := hHsubT hw
    rw [memT w] at hwT
    rcases hwT with rfl | rfl | rfl | rfl
    · simp
    · exact hu
    · exact hv
    · exact huv2

end Work.CORE4.L2PAux
