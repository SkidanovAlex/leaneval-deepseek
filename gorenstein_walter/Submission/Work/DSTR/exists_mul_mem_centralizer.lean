import Mathlib

namespace Work.DSTR

open scoped commutatorElement

/-- H¹(⟨t⟩, N) = 0 for `N` of odd order: if `⁅u,t⁆ ∈ N` with `t² = 1` and `N` a normal subgroup
of odd order, then `u` is congruent modulo `N` to an element centralizing `t`.

Proof sketch: `w := ⁅u⁻¹,t⁆ ∈ N`, `v := w * t = u⁻¹ * t * u` is an involution and `t * w * t = w⁻¹`.
Since `orderOf w` is odd, say `2*k+1`, take `m := w^(k+1) ∈ N`; then
`m * t * m⁻¹ = w^(2k+2) * t = w * t = v`, so `(u*m) * t * (u*m)⁻¹ = u * v * u⁻¹ = t`. -/
theorem exists_mul_mem_centralizer {G : Type*} [Group G] {N : Subgroup G} (hN : N.Normal)
    (hNodd : Odd (Nat.card N)) {t u : G} (ht : t * t = 1) (hu : ⁅u, t⁆ ∈ N) :
    ∃ m ∈ N, u * m ∈ Subgroup.centralizer ({t} : Set G) := by
  have ht_inv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  -- The commutator `w := u⁻¹ * t * u * t` lies in `N`.
  set w : G := u⁻¹ * t * u * t with hw_def
  have hw_mem : w ∈ N := by
    have h1 : ⁅u, t⁆⁻¹ ∈ N := N.inv_mem hu
    have h2 : u⁻¹ * ⁅u, t⁆⁻¹ * u ∈ N := hN.conj_mem' (⁅u, t⁆⁻¹) h1 u
    have heq : u⁻¹ * ⁅u, t⁆⁻¹ * u = w := by
      rw [hw_def]
      simp only [commutatorElement_def, mul_inv_rev, ht_inv, inv_inv]
      group
    rwa [heq] at h2
  -- Since `N` has odd order, so does `orderOf w`.
  have hodd_w : Odd (orderOf w) :=
    Odd.of_dvd_nat hNodd (Subgroup.orderOf_dvd_natCard N hw_mem)
  -- Conjugation by `t` inverts `w`.
  have hφw : MulAut.conj t w = w⁻¹ := by
    rw [hw_def, MulAut.conj_apply, ht_inv]
    simp only [mul_assoc, ht, mul_one, mul_inv_rev, ht_inv, inv_inv]
  obtain ⟨k, hk⟩ := hodd_w
  -- `m := w^(k+1)` is the square root of `w`.
  set m : G := w ^ (k + 1) with hm_def
  have hm_mem : m ∈ N := by rw [hm_def]; exact N.pow_mem hw_mem (k + 1)
  have hm_sq : m * m = w := by
    rw [hm_def, ← pow_add]
    have h2 : k + 1 + (k + 1) = orderOf w + 1 := by rw [hk]; ring
    rw [h2, pow_succ, pow_orderOf_eq_one, one_mul]
  have hφm : t * m * t = m⁻¹ := by
    have h : MulAut.conj t m = m⁻¹ := by rw [hm_def, map_pow, hφw, inv_pow]
    simpa only [MulAut.conj_apply, ht_inv] using h
  have htmt : t * m⁻¹ * t = m := by
    have h := congrArg Inv.inv hφm
    rw [mul_inv_rev, mul_inv_rev, ht_inv, inv_inv] at h
    simpa [mul_assoc] using h
  -- Hence `m * t * m⁻¹ = w * t = u⁻¹ * t * u`.
  have hconj : m * t * m⁻¹ = w * t := by
    calc m * t * m⁻¹ = m * (t * m⁻¹ * t) * t := by simp only [mul_assoc, ht, mul_one]
      _ = m * m * t := by rw [htmt]
      _ = w * t := by rw [hm_sq]
  refine ⟨m, hm_mem, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hmain : u * m * t * (u * m)⁻¹ = t := by
    calc u * m * t * (u * m)⁻¹
        = u * (m * t * m⁻¹) * u⁻¹ := by group
      _ = u * (w * t) * u⁻¹ := by rw [hconj]
      _ = t := by
          rw [hw_def]
          simp only [mul_assoc, ht, mul_one]
          group
  have h := congrArg (fun x => x * (u * m)) hmain
  simpa [mul_assoc] using h

end Work.DSTR
