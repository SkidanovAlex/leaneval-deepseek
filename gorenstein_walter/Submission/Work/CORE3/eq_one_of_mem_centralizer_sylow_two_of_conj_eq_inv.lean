import Mathlib

namespace Work.CORE3

/-- If `a` has odd order and inverts `b`, then `a` commutes with `b`.

Indeed `a b a⁻¹ = b⁻¹` implies `a²` centralizes `b`; and an element `a` of odd order
`2m+1` satisfies `a = ((a²)^m)⁻¹`, hence is a power (inverse) of `a²` and therefore also
centralizes `b`. -/
private lemma commute_of_conj_eq_inv_of_odd {H : Type*} [Group H] {a b : H}
    (ha : Odd (orderOf a)) (h : a * b * a⁻¹ = b⁻¹) : Commute a b := by
  obtain ⟨m, hm⟩ := ha
  have h1 : a ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one a
  have h2 : (a ^ 2) ^ m * a = 1 := by rw [← pow_mul, ← pow_succ]; exact h1
  have key : a ^ 2 * b * (a ^ 2)⁻¹ = b :=
    calc a ^ 2 * b * (a ^ 2)⁻¹ = a * (a * b * a⁻¹) * a⁻¹ := by
          rw [pow_two, mul_inv_rev]; group
      _ = a * b⁻¹ * a⁻¹ := by rw [h]
      _ = (a * b * a⁻¹)⁻¹ := by group
      _ = (b⁻¹)⁻¹ := by rw [h]
      _ = b := by rw [inv_inv]
  have hcomm2 : Commute (a ^ 2) b := by
    show a ^ 2 * b = b * a ^ 2
    calc a ^ 2 * b = a ^ 2 * b * (a ^ 2)⁻¹ * a ^ 2 := by group
      _ = b * a ^ 2 := by rw [key]
  have h3 : a = ((a ^ 2) ^ m)⁻¹ := eq_inv_of_mul_eq_one_right h2
  rw [h3]
  exact (hcomm2.pow_left m).inv_left

/-- In a group, an element of odd order cannot invert a nontrivial element of odd order:
if `a * b * a⁻¹ = b⁻¹` with `a`, `b` of odd order, then `b = 1`. -/
private lemma eq_one_of_conj_eq_inv_of_odd {H : Type*} [Group H] {a b : H}
    (ha : Odd (orderOf a)) (hb : Odd (orderOf b)) (h : a * b * a⁻¹ = b⁻¹) : b = 1 := by
  have hcomm : Commute a b := commute_of_conj_eq_inv_of_odd ha h
  have hbb : b = b⁻¹ := by rw [← h, hcomm.eq]; group
  have hb2 : b ^ 2 = 1 := by rw [pow_two]; nth_rewrite 2 [hbb]; exact mul_inv_cancel b
  have hdvd : orderOf b ∣ 2 := orderOf_dvd_of_pow_eq_one hb2
  obtain hb1 | hb2' := (Nat.dvd_prime Nat.prime_two).mp hdvd
  · exact orderOf_eq_one_iff.mp hb1
  · rw [hb2'] at hb; obtain ⟨k, hk⟩ := hb; omega

/-- If `a ∣ b` and `b` is odd then `a` is odd. -/
private lemma odd_of_dvd_of_odd {a b : ℕ} (h : a ∣ b) (hb : Odd b) : Odd a := by
  rw [← Nat.not_even_iff_odd] at hb ⊢
  rw [even_iff_two_dvd] at hb ⊢
  exact fun ha => hb (ha.trans h)

/-- The only odd power of `2` is `2 ^ 0 = 1`. -/
private lemma pow_two_odd_eq_zero {k : ℕ} (h : Odd (2 ^ k)) : k = 0 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · exact hk
  · exfalso
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hk)
    rw [pow_succ] at h
    exact (Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr ⟨2 ^ j, mul_comm _ _⟩)) h

/-- If `T` is a Sylow 2-subgroup of a finite group `G`, `g ∈ N_G(T)`, and `x` is an element of
odd order centralizing `T` which is inverted by `g` (`g * x * g⁻¹ = x⁻¹`), then `x = 1`.

Proof sketch: `N = N_G(T)` has `T ⊴ N` with `[N : T]` odd (the index of a Sylow subgroup), so
`N/T` has odd order.  The image `ḡ` of `g` in `N/T` inverts the image `x̄` of `x`, and with
`k = orderOf ḡ` odd we get `x̄ = ḡ^k x̄ ḡ^{-k} = x̄^{(-1)^k} = x̄⁻¹`, so `x̄² = 1`; since `x̄`
has odd order (`orderOf x̄ ∣ orderOf x`) this gives `x̄ = 1`, i.e. `x ∈ T`; and an element of
odd order in the 2-group `T` is trivial. -/
theorem eq_one_of_mem_centralizer_sylow_two_of_conj_eq_inv {G : Type} [Group G] [Finite G]
    (T : Sylow 2 G) {g x : G}
    (hg : g ∈ Subgroup.normalizer ((T : Subgroup G) : Set G))
    (hxc : ∀ t ∈ (T : Subgroup G), t * x = x * t)
    (hodd : Odd (orderOf x))
    (hconj : g * x * g⁻¹ = x⁻¹) : x = 1 := by
  -- `N = N_G(T)`, so that `x ∈ N` (it even centralizes `T`) and `g ∈ N`.
  set N : Subgroup G := Subgroup.normalizer ((T : Subgroup G) : Set G) with hN
  have hgN : g ∈ N := by rw [hN]; exact hg
  have hxN : x ∈ N := by
    rw [hN]
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr hxc)
  -- The index of the Sylow 2-subgroup `T` is odd.
  have hTodd : Odd (T : Subgroup G).index := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact Sylow.not_dvd_index T
  -- `T` viewed inside `N`; it is normal there, and `[N : T]` (its index) is odd.
  let T' : Subgroup N := (T : Subgroup G).subgroupOf N
  have hdvd : T'.index ∣ (T : Subgroup G).index := by
    refine ⟨N.index, ?_⟩
    exact (Subgroup.relIndex_mul_index (Subgroup.le_normalizer (H := (T : Subgroup G)))).symm
  have hT'odd : Odd T'.index := odd_of_dvd_of_odd hdvd hTodd
  have hQodd : Odd (Nat.card (N ⧸ T')) := by
    rw [← Subgroup.index_eq_card]; exact hT'odd
  -- Pass to the odd-order quotient `Q = N / T`.
  let a : N ⧸ T' := QuotientGroup.mk' T' ⟨g, hgN⟩
  let b : N ⧸ T' := QuotientGroup.mk' T' ⟨x, hxN⟩
  have ha_odd : Odd (orderOf a) := odd_of_dvd_of_odd (orderOf_dvd_natCard a) hQodd
  have hb_odd : Odd (orderOf b) := odd_of_dvd_of_odd (orderOf_dvd_natCard b) hQodd
  have hab : a * b * a⁻¹ = b⁻¹ := by
    have hlift : (⟨g, hgN⟩ : N) * (⟨x, hxN⟩ : N) * (⟨g, hgN⟩ : N)⁻¹
        = (⟨x, hxN⟩ : N)⁻¹ := by
      apply Subtype.ext
      show g * x * g⁻¹ = x⁻¹
      exact hconj
    have h2 := congrArg (QuotientGroup.mk' T') hlift
    simpa only [map_mul, map_inv] using h2
  have hb_one : b = 1 := eq_one_of_conj_eq_inv_of_odd ha_odd hb_odd hab
  -- Hence `x ∈ T`, i.e. `x` lies in the 2-group `T`; with odd order this forces `x = 1`.
  have hxT : x ∈ (T : Subgroup G) := by
    have hmem : (⟨x, hxN⟩ : N) ∈ T' := by
      have hK : (⟨x, hxN⟩ : N) ∈ (QuotientGroup.mk' T').ker := by
        rw [MonoidHom.mem_ker]
        exact hb_one
      rwa [QuotientGroup.ker_mk'] at hK
    have h := Subgroup.mem_subgroupOf.mp hmem
    simpa using h
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp T.isPGroup') (⟨x, hxT⟩ : (T : Subgroup G))
  have hk' : orderOf x = 2 ^ k :=
    (Subgroup.orderOf_coe (⟨x, hxT⟩ : (T : Subgroup G))).trans hk
  have hk0 : k = 0 := pow_two_odd_eq_zero (hk' ▸ hodd)
  have hx1 : orderOf x = 1 := by rw [hk', hk0, pow_zero]
  exact orderOf_eq_one_iff.mp hx1

end Work.CORE3
