import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.GroupTheory

/-- A nonabelian group of order `6` (necessarily `S₃`) has exactly three elements of order `2`. -/
theorem order_six_involutions {α : Type*} [Group α] [Finite α] (hcard : Nat.card α = 6)
    (hnc : ∃ x y : α, x * y ≠ y * x) :
    Nat.card {x : α // orderOf x = 2} = 3 := by
  classical
  -- Cauchy's theorem: an element of order 3, which generates the (unique) Sylow 3-subgroup.
  have h3dvd : 3 ∣ Nat.card α := by rw [hcard]; norm_num
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := α) 3 h3dvd
  set N : Subgroup α := Subgroup.zpowers x with hN
  have hNcard : Nat.card N = 3 := by
    rw [hN, Nat.card_zpowers, hx]
  have hNindex : N.index = 2 := by
    have h := Subgroup.card_mul_index N
    rw [hNcard, hcard] at h
    omega
  haveI : N.Normal := Subgroup.normal_of_index_eq_two hNindex
  -- The quotient by `N` has order 2, so every square lies in `N`.
  have hquot : Nat.card (α ⧸ N) = 2 := by
    rw [← Subgroup.index_eq_card]
    exact hNindex
  have sqmem : ∀ g : α, g * g ∈ N := by
    intro g
    have h1 : (QuotientGroup.mk' N) (g * g) = 1 := by
      rw [map_mul]
      have hd : orderOf ((QuotientGroup.mk' N) g) ∣ Nat.card (α ⧸ N) :=
        orderOf_dvd_natCard _
      rw [hquot] at hd
      have h2 : ((QuotientGroup.mk' N) g) ^ 2 = 1 :=
        orderOf_dvd_iff_pow_eq_one.mp hd
      rwa [pow_two] at h2
    have hmem : g * g ∈ (QuotientGroup.mk' N).ker := MonoidHom.mem_ker.mpr h1
    rwa [QuotientGroup.ker_mk' N] at hmem
  -- Exactly the elements outside `N` have order 2.
  have key : ∀ g : α, orderOf g = 2 ↔ g ∉ N := by
    intro g
    constructor
    · intro hg hgN
      have hdiv : orderOf g ∣ 3 := by
        rw [hN] at hgN
        have h := orderOf_dvd_of_mem_zpowers (x := x) (y := g) hgN
        rwa [hx] at h
      obtain ⟨k, hk⟩ := hdiv
      rw [hg] at hk
      omega
    · intro hgN
      have hdvd : orderOf g ∣ 6 := by
        rw [← hcard]; exact orderOf_dvd_natCard g
      have hle : orderOf g ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
      have hpos : 0 < orderOf g := orderOf_pos g
      interval_cases h : orderOf g
      · -- order 1
        exfalso
        have hg1 : g = 1 := orderOf_eq_one_iff.mp h
        exact hgN (by rw [hg1]; exact N.one_mem)
      · rfl
      · -- order 3: then `g = (g^2)^{-1} ∈ N`, contradiction
        exfalso
        have hg3 : g ^ 3 = 1 :=
          orderOf_dvd_iff_pow_eq_one.mp (by rw [h])
        have h2 : g ^ 2 * g = 1 := by
          rw [← pow_succ]
          exact hg3
        have hg2eq : g ^ 2 = g⁻¹ := eq_inv_of_mul_eq_one_left h2
        have hg2N : g ^ 2 ∈ N := by rw [pow_two]; exact sqmem g
        have hginv : g⁻¹ ∈ N := by rw [← hg2eq]; exact hg2N
        exact hgN (by simpa using N.inv_mem hginv)
      · -- order 4 impossible since 4 ∤ 6
        exact absurd hdvd (by norm_num)
      · -- order 5 impossible since 5 ∤ 6
        exact absurd hdvd (by norm_num)
      · -- order 6 would make `α` cyclic, hence abelian
        exfalso
        have htop : Subgroup.zpowers g = ⊤ := by
          apply (Subgroup.card_eq_iff_eq_top _).mp
          rw [Nat.card_zpowers, h, hcard]
        have hcomm : ∀ a b : α, a * b = b * a := by
          intro a b
          have ha : a ∈ Subgroup.zpowers g := by rw [htop]; exact Subgroup.mem_top a
          have hb : b ∈ Subgroup.zpowers g := by rw [htop]; exact Subgroup.mem_top b
          obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ha
          obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hb
          rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
        obtain ⟨u, v, huv⟩ := hnc
        exact huv (hcomm u v)
  -- Hence the elements of order 2 are exactly the non-elements of `N`.
  have hset : (Set.ofPred (fun y : α => orderOf y = 2)) = (N : Set α)ᶜ := by
    ext g
    simp only [Set.mem_compl_iff, SetLike.mem_coe]
    exact key g
  change Nat.card ↥(Set.ofPred (fun y : α => orderOf y = 2)) = 3
  rw [Nat.card_coe_set_eq, hset, Set.ncard_compl]
  have hNncard : (N : Set α).ncard = 3 := by
    rw [← Nat.card_coe_set_eq]
    exact hNcard
  rw [hNncard, hcard]

end Work.GroupTheory
