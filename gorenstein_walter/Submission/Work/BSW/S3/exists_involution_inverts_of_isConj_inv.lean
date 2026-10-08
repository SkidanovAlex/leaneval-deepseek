import Mathlib

/-!
# An element with odd-order centralizer that is conjugate to its inverse is
inverted by an involution

If `y ≠ 1` is conjugate to `y⁻¹` and the centralizer `C_G(y)` has odd order, then `y` is
inverted by an involution of `G`.

The argument: pick `g` with `g * y * g⁻¹ = y⁻¹`.  Then `g² ∈ C_G(y)`, so `m := orderOf (g²)`
is odd.  Put `t := g ^ m`.  Then `t * t = (g²)^m = 1`, and since `m = 2k+1` is odd,
`t * y * t⁻¹ = (g²)^k * (g * y * g⁻¹) * ((g²)^k)⁻¹ = y⁻¹`.  Finally `t ≠ 1`: otherwise
`y = y⁻¹`, so `orderOf y ∣ 2`, while `orderOf y` is odd (dividing `|C_G(y)|`), forcing
`y = 1`.  Taking `u := t⁻¹` (an involution inverting `y` in the required orientation) proves
the claim.
-/

namespace Work.BSW.S3

theorem exists_involution_inverts_of_isConj_inv {G : Type} [Group G] [Finite G] {y : G}
    (hy : y ≠ 1) (hodd : Odd (Nat.card (Subgroup.centralizer ({y} : Set G))))
    (hc : IsConj y y⁻¹) : ∃ u : G, orderOf u = 2 ∧ u⁻¹ * y * u = y⁻¹ := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hc
  -- every element of `C_G(y)` fixes `y` by conjugation
  have hC_conj : ∀ c ∈ Subgroup.centralizer ({y} : Set G), c * y * c⁻¹ = y := by
    intro c hc
    have h : c * y = y * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    simp [h]
  -- `g² ∈ C_G(y)`
  have hg2C : g ^ 2 ∈ Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : g * y⁻¹ * g⁻¹ = y := by
      have h := congrArg Inv.inv hg
      simpa [mul_assoc] using h
    have h2 : g * g * y * (g * g)⁻¹ = y := by
      calc g * g * y * (g * g)⁻¹ = g * (g * y * g⁻¹) * g⁻¹ := by group
        _ = g * y⁻¹ * g⁻¹ := by rw [hg]
        _ = y := h1
    have h2' : (g * g) * y = y * (g * g) := by
      have := congrArg (· * (g * g)) h2
      simpa [mul_assoc] using this
    simpa [pow_two] using h2'
  set m : ℕ := orderOf (g ^ 2) with hm
  -- `m` is odd, since it divides the odd number `|C_G(y)|`
  have hm_odd : Odd m := by
    rw [hm]
    exact Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hg2C)
  obtain ⟨k, hk⟩ := hm_odd
  have ht_eq : g ^ m = (g ^ 2) ^ k * g := by rw [hk, pow_succ, pow_mul]
  have hpowC : (g ^ 2) ^ k ∈ Subgroup.centralizer ({y} : Set G) := Subgroup.pow_mem _ hg2C k
  have hpow_fix : (g ^ 2) ^ k * y * ((g ^ 2) ^ k)⁻¹ = y := hC_conj _ hpowC
  have hpow_fix_inv : (g ^ 2) ^ k * y⁻¹ * ((g ^ 2) ^ k)⁻¹ = y⁻¹ := by
    have h := congrArg Inv.inv hpow_fix
    simpa [mul_assoc] using h
  -- `g ^ m` inverts `y`
  have ht' : g ^ m * y * (g ^ m)⁻¹ = y⁻¹ := by
    rw [ht_eq]
    calc ((g ^ 2) ^ k * g) * y * ((g ^ 2) ^ k * g)⁻¹
        = (g ^ 2) ^ k * (g * y * g⁻¹) * ((g ^ 2) ^ k)⁻¹ := by group
      _ = (g ^ 2) ^ k * y⁻¹ * ((g ^ 2) ^ k)⁻¹ := by rw [hg]
      _ = y⁻¹ := hpow_fix_inv
  -- `g ^ m` is an involution
  have hpowsq : g ^ m * g ^ m = 1 := by
    have h : g ^ m * g ^ m = (g ^ 2) ^ m := by
      rw [← pow_add, show m + m = 2 * m from by ring, pow_mul]
    rw [h, hm]
    exact pow_orderOf_eq_one (g ^ 2)
  have hm_ne : g ^ m ≠ 1 := by
    intro h1
    have hyy : y = y⁻¹ := by
      have h := ht'
      rw [h1] at h
      simpa using h
    have hy2 : y ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [hyy]
      rw [mul_inv_cancel]
    have hdvd : orderOf y ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hy2
    have hyd : y ∈ Subgroup.centralizer ({y} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
    have hodd_y : Odd (orderOf y) :=
      Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hyd)
    obtain ⟨j, hj⟩ := hodd_y
    have hle : orderOf y ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    have : orderOf y = 1 := by omega
    exact hy (orderOf_eq_one_iff.mp this)
  refine ⟨(g ^ m)⁻¹, ?_, ?_⟩
  · rw [orderOf_inv]
    exact orderOf_eq_prime (by rw [pow_two]; exact hpowsq) hm_ne
  · show ((g ^ m)⁻¹)⁻¹ * y * (g ^ m)⁻¹ = y⁻¹
    rw [inv_inv]
    exact ht'

end Work.BSW.S3
