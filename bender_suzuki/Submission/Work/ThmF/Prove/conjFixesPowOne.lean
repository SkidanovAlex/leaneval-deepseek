import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.ThmF.Prove

/-- If `T` is a finite cyclic subgroup, `y` normalizes `T` with `y ^ p = 1` for a prime `p`, and
`t ∈ T` with `t ^ p = 1`, then conjugation by `y` fixes `t`.

The proof picks a generator `g` of `T`, writes `t = g ^ k` and `y * g * y⁻¹ = g ^ a`. Since
`y ^ p = 1`, conjugation by `y ^ p` is the identity, giving `g ^ (a ^ p) = g`, whence
`t ^ (a ^ p) = t`. As `t` has order dividing the prime `p`, either `t = 1` or `t` has order `p`;
in the latter case `p ∣ a ^ p - 1`, so Fermat's little theorem gives `p ∣ a - 1`, and therefore
`t ^ a = t`. Finally `y * t * y⁻¹ = t ^ a = t`. -/
theorem conjFixesPowOne {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {T : Subgroup G} (hTc : IsCyclic ↥T) {y t : G}
    (hyT : ∀ x ∈ T, y * x * y⁻¹ ∈ T) (hy : y ^ p = 1) (ht : t ∈ T) (htp : t ^ p = 1) :
    y * t * y⁻¹ = t := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥T)
  -- `T` is generated (as a subgroup of `G`) by the image of `g`
  have hTg : T = Subgroup.zpowers (g : G) := by
    apply le_antisymm
    · intro x hx
      have h1 := hg ⟨x, hx⟩
      rw [Subgroup.mem_zpowers_iff] at h1 ⊢
      obtain ⟨k, hk⟩ := h1
      exact ⟨k, by rw [← Subgroup.coe_zpow]; exact congrArg Subtype.val hk⟩
    · rw [Subgroup.zpowers_le]
      exact g.2
  -- `t` and `y * g * y⁻¹` are powers of `g`
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (g : G) ^ k = t := by
    rw [hTg, Subgroup.mem_zpowers_iff] at ht
    exact ht
  obtain ⟨a, ha⟩ : ∃ a : ℤ, (g : G) ^ a = y * (g : G) * y⁻¹ := by
    have hmem : y * (g : G) * y⁻¹ ∈ Subgroup.zpowers (g : G) := by
      rw [← hTg]; exact hyT (g : G) g.2
    rwa [Subgroup.mem_zpowers_iff] at hmem
  -- conjugation by `y ^ n` is the power map `x ↦ x ^ (a ^ n)` on `⟨g⟩`
  have hconj : ∀ n : ℕ, y ^ n * (g : G) * (y ^ n)⁻¹ = (g : G) ^ (a ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show y ^ (n + 1) * (g : G) * (y ^ (n + 1))⁻¹
            = y ^ n * (y * (g : G) * y⁻¹) * (y ^ n)⁻¹ by rw [pow_succ]; group]
      rw [← ha, ← conj_zpow, ih, ← zpow_mul, ← pow_succ]
  -- hence `g ^ (a ^ p) = g`
  have hgen : (g : G) ^ (a ^ p) = (g : G) := by
    have h := hconj p
    rw [hy, one_mul, inv_one, mul_one] at h
    exact h.symm
  have ht_pow : t ^ (a ^ p) = t := by
    calc t ^ (a ^ p) = ((g : G) ^ k) ^ (a ^ p) := by rw [← hk]
      _ = (g : G) ^ (k * a ^ p) := by rw [← zpow_mul]
      _ = (g : G) ^ (a ^ p * k) := by rw [mul_comm]
      _ = ((g : G) ^ (a ^ p)) ^ k := by rw [zpow_mul]
      _ = (g : G) ^ k := by rw [hgen]
      _ = t := hk
  have ht_pow1 : t ^ (a ^ p - 1) = 1 := by
    rw [zpow_sub_one, ht_pow, mul_inv_cancel]
  have hdvd : (orderOf t : ℤ) ∣ a ^ p - 1 :=
    (orderOf_dvd_iff_zpow_eq_one).mpr ht_pow1
  -- `y * t * y⁻¹ = t ^ a`
  have hconjt : y * t * y⁻¹ = t ^ a := by
    calc y * t * y⁻¹ = y * (g : G) ^ k * y⁻¹ := by rw [← hk]
      _ = (y * (g : G) * y⁻¹) ^ k := by rw [conj_zpow]
      _ = ((g : G) ^ a) ^ k := by rw [← ha]
      _ = (g : G) ^ (a * k) := by rw [← zpow_mul]
      _ = (g : G) ^ (k * a) := by rw [mul_comm]
      _ = ((g : G) ^ k) ^ a := by rw [zpow_mul]
      _ = t ^ a := by rw [hk]
  have hdvd_p : orderOf t ∣ p := (orderOf_dvd_iff_pow_eq_one).mpr htp
  rcases hp.eq_one_or_self_of_dvd (orderOf t) hdvd_p with h1 | hp'
  · -- `t = 1`
    have ht1 : t = 1 := orderOf_eq_one_iff.mp h1
    rw [ht1, mul_one, mul_inv_cancel]
  · -- `t` has order `p`; Fermat's little theorem forces `a ≡ 1 (mod p)`
    rw [hp'] at hdvd
    haveI : Fact p.Prime := ⟨hp⟩
    have hmod : (a : ZMod p) = 1 := by
      have hcast : (a : ZMod p) ^ p = ((a ^ p : ℤ) : ZMod p) := (Int.cast_pow a p).symm
      have h2 : ((a ^ p : ℤ) : ZMod p) = 1 := by
        have h0 : ((a ^ p - 1 : ℤ) : ZMod p) = 0 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd (a ^ p - 1) p).mpr hdvd
        rw [Int.cast_sub, Int.cast_one] at h0
        exact sub_eq_zero.mp h0
      calc (a : ZMod p) = (a : ZMod p) ^ p := (ZMod.pow_card _).symm
        _ = ((a ^ p : ℤ) : ZMod p) := hcast
        _ = 1 := h2
    have hdvd_a : (p : ℤ) ∣ a - 1 := by
      have h : ((a - 1 : ℤ) : ZMod p) = 0 := by
        rw [Int.cast_sub, Int.cast_one, hmod, sub_self]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd (a - 1) p).mp h
    obtain ⟨c, hc⟩ := hdvd_a
    have ht_a1 : t ^ (a - 1) = 1 := by
      rw [hc, zpow_mul, zpow_natCast, htp, one_zpow]
    have ht_a : t ^ a = t := by
      rw [show a = (a - 1) + 1 by ring, zpow_add, ht_a1, one_mul, zpow_one]
    rw [hconjt, ht_a]

end Work.ThmF.Prove
