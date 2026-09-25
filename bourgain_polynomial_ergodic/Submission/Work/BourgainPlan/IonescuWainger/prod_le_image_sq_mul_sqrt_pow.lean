import Mathlib

namespace Work.BourgainPlan.IonescuWainger

/-- Fiberwise product formula: a product over the domain equals the product over the image of
the value raised to the cardinality of its fiber. -/
lemma prod_eq_prod_image_pow_card {κ ι M : Type*} [Fintype κ] [CommMonoid M] [DecidableEq ι]
    (g : κ → ι) (f : ι → M) :
    ∏ j, f (g j) = ∏ i ∈ Finset.univ.image g, f i ^ (Finset.univ.filter (fun j => g j = i)).card :=
  Finset.prod_comp (s := Finset.univ) f g

/-- Sum of fiber cardinalities over the image equals the cardinality of the domain. -/
lemma card_eq_sum_card_fiber {κ ι : Type*} [Fintype κ] [DecidableEq ι] (g : κ → ι) :
    Fintype.card κ = ∑ i ∈ Finset.univ.image g, (Finset.univ.filter (fun j => g j = i)).card := by
  rw [← Finset.card_univ]
  exact Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (t := Finset.univ.image g)
    (fun x _ => Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩)

/-- If every value of `g` is attained at least twice, every fiber over the image has at least
two elements. -/
lemma two_le_card_fiber {κ ι : Type*} [Fintype κ] [DecidableEq ι] (g : κ → ι)
    (hg : ∀ j, ∃ k, k ≠ j ∧ g k = g j) {i : ι} (hi : i ∈ Finset.univ.image g) :
    2 ≤ (Finset.univ.filter (fun j => g j = i)).card := by
  classical
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hi
  obtain ⟨k, hkj, hk⟩ := hg j
  have hmemj : j ∈ Finset.univ.filter (fun x => g x = i) := by simp [hj]
  have hmemk : k ∈ Finset.univ.filter (fun x => g x = i) := by simp [hk, hj]
  have hsub : ({j, k} : Finset κ) ⊆ Finset.univ.filter (fun x => g x = i) := by
    intro x hx
    rcases Finset.mem_insert.mp hx with h | h
    · rw [h]; exact hmemj
    · rw [Finset.mem_singleton.mp h]; exact hmemk
  have hle := Finset.card_le_card hsub
  rw [Finset.card_pair (Ne.symm hkj)] at hle
  exact hle

/-- Weighted power bound: each factor is at most `√(∑ aᵢ²)`. -/
lemma prod_pow_le_sqrt_sum_pow {ι : Type*} [Fintype ι] (S : Finset ι) (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (d : ι → ℕ) (t : ℕ) (hd : ∑ i ∈ S, d i = 2 * t) :
    ∏ i ∈ S, a i ^ d i ≤ (Real.sqrt (∑ i, a i ^ 2)) ^ (2 * t) := by
  have hM : ∀ i ∈ S, a i ≤ Real.sqrt (∑ k, a k ^ 2) := by
    intro i _
    have h1 : a i ^ 2 ≤ ∑ k, a k ^ 2 :=
      Finset.single_le_sum (f := fun k => a k ^ 2) (s := Finset.univ)
        (fun k _ => sq_nonneg (a k)) (Finset.mem_univ i)
    calc a i = Real.sqrt (a i ^ 2) := (Real.sqrt_sq (ha i)).symm
      _ ≤ Real.sqrt (∑ k, a k ^ 2) := Real.sqrt_le_sqrt h1
  calc ∏ i ∈ S, a i ^ d i
      ≤ ∏ i ∈ S, (Real.sqrt (∑ k, a k ^ 2)) ^ d i := by
        apply Finset.prod_le_prod₀
        · intro i _; exact pow_nonneg (ha i) _
        · intro i hi; exact pow_le_pow_left₀ (ha i) (hM i hi) (d i)
    _ = (Real.sqrt (∑ k, a k ^ 2)) ^ (∑ i ∈ S, d i) := Finset.prod_pow_eq_pow_sum S d _
    _ = (Real.sqrt (∑ k, a k ^ 2)) ^ (2 * t) := by rw [hd]

theorem prod_le_image_sq_mul_sqrt_pow {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (r : ℕ) (hκ : Fintype.card κ = 2 * r) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (s : κ → ι)
    (hs : ∀ j : κ, ∃ k : κ, k ≠ j ∧ s k = s j) :
    ∏ j, a (s j) ≤ (∏ i ∈ Finset.univ.image s, (a i) ^ 2)
      * (Real.sqrt (∑ i, a i ^ 2)) ^ (2 * (r - (Finset.univ.image s).card)) := by
  classical
  set S := Finset.univ.image s with hS
  set c : ι → ℕ := fun i => (Finset.univ.filter (fun j => s j = i)).card with hc
  have hfib : ∀ i ∈ S, 2 ≤ c i := by
    intro i hi
    rw [hc]
    exact two_le_card_fiber s hs (by rwa [hS] at hi)
  have hsum : ∑ i ∈ S, c i = 2 * r := by
    have h := card_eq_sum_card_fiber s
    simp only [hc, hS]
    rw [← h, hκ]
  have hconst : ∑ i ∈ S, (2 : ℕ) = 2 * S.card := by
    simp [Finset.sum_const, Nat.mul_comm]
  have hexp : ∑ i ∈ S, (c i - 2) = 2 * (r - S.card) := by
    have h1 : ∑ i ∈ S, c i = (∑ i ∈ S, (c i - 2)) + 2 * S.card := by
      rw [← hconst, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i hi => (Nat.sub_add_cancel (hfib i hi)).symm)
    have h2 := Nat.eq_sub_of_add_eq h1.symm
    rw [h2, hsum, Nat.mul_sub_left_distrib]
  have hprod : ∏ j, a (s j) = ∏ i ∈ S, (a i) ^ (c i) := by
    simp only [hS, hc]
    exact prod_eq_prod_image_pow_card s a
  have hsplit : ∏ i ∈ S, (a i) ^ (c i)
      = (∏ i ∈ S, (a i) ^ 2) * ∏ i ∈ S, (a i) ^ (c i - 2) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i hi => by
      rw [← pow_add]
      congr 1
      exact (Nat.add_sub_cancel' (hfib i hi)).symm)
  have hpow : ∏ i ∈ S, (a i) ^ (c i - 2)
      ≤ (Real.sqrt (∑ i, a i ^ 2)) ^ (2 * (r - S.card)) :=
    prod_pow_le_sqrt_sum_pow S a ha (fun i => c i - 2) (r - S.card) hexp
  rw [hprod, hsplit]
  exact mul_le_mul_of_nonneg_left hpow (Finset.prod_nonneg (fun i _ => sq_nonneg (a i)))

end Work.BourgainPlan.IonescuWainger
