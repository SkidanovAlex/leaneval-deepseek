import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.Frobenius.Complement

/-- A cyclic group is commutative.  Stated in terms of `IsMulCommutative`, which is what the
Frobenius/Feit--Thompson development uses. -/
private lemma isMulCommutative_of_isCyclic_of_group {G : Type*} [Group G] (h : IsCyclic G) :
    IsMulCommutative G := by
  haveI := h
  exact MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center (MonoidHom.id G) (by simp)

/-- **Structure of a non-abelian group of order `m * n`** (`m < n` primes).

If `K` is a finite non-abelian group of order `m * n`, with `m < n` primes, then `K` contains an
element `y` of order `n` and an element `x` of order `m` such that `x` conjugates `y` to a power
`y ^ s` with `s % n ≠ 1` (equivalently `x` does not centralize `y`, i.e. the action of `⟨x⟩` on
`⟨y⟩` is nontrivial).

The Sylow `n`-subgroup is normal (it is the unique one, because `m < n` and its number divides `m`
and is `≡ 1` mod `n`), so conjugation by any element lands in `⟨y⟩`; if `x` centralized `y` then
`x * y` would have order `m * n = |K|`, making `K` cyclic and hence commutative. -/
theorem exists_conj_action_of_nonabelian_card_eq_mul_primes {K : Type*} [Group K] [Finite K]
    {m n : ℕ} (hm : m.Prime) (hn : n.Prime) (hmn : m < n) (hcard : Nat.card K = m * n)
    (hNA : ¬ IsMulCommutative K) :
    ∃ (y x : K) (s : ℕ), orderOf y = n ∧ orderOf x = m ∧ s % n ≠ 1 ∧ x * y * x⁻¹ = y ^ s := by
  classical
  haveI : Fact n.Prime := ⟨hn⟩
  haveI : Fact m.Prime := ⟨hm⟩
  have hn_dvd : n ∣ Nat.card K := by rw [hcard]; exact dvd_mul_left n m
  have hm_dvd : m ∣ Nat.card K := by rw [hcard]; exact dvd_mul_right m n
  -- elements of order `n` and `m` (Cauchy's theorem)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' n hn_dvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' m hm_dvd
  -- The subgroup `H = ⟨y⟩` has order `n`, hence is the (unique) Sylow `n`-subgroup, hence normal.
  set H : Subgroup K := Subgroup.zpowers y with hHdef
  have hHcard : Nat.card H = n := by rw [hHdef, Nat.card_zpowers, hy]
  have hHindex : H.index = m := by
    have h := Subgroup.card_mul_index H
    rw [hHcard, hcard] at h
    exact Nat.mul_left_cancel hn.pos (h.trans (mul_comm m n))
  have hHind : ¬ n ∣ H.index := by
    rw [hHindex]
    intro hdiv
    exact absurd (Nat.le_of_dvd hm.pos hdiv) (not_le.mpr hmn)
  have hHisP : IsPGroup n H := IsPGroup.of_card (by rw [hHcard, pow_one])
  let P : Sylow n K := hHisP.toSylow hHind
  have hPcoe : (P : Subgroup K) = H := IsPGroup.toSylow_coe hHisP hHind
  have hPindex : (P : Subgroup K).index = m := by rw [hPcoe]; exact hHindex
  -- The number of Sylow `n`-subgroups divides `m` and is `≡ 1` mod `n`, hence equals `1`.
  have hSdvd : Nat.card (Sylow n K) ∣ m := by
    rw [Sylow.card_eq_index_normalizer P, ← hPindex]
    exact Subgroup.index_dvd_of_le (Subgroup.le_normalizer (H := (P : Subgroup K)))
  have hSmod : Nat.card (Sylow n K) ≡ 1 [MOD n] := card_sylow_modEq_one n K
  have hSle : Nat.card (Sylow n K) ≤ m := Nat.le_of_dvd hm.pos hSdvd
  have hSlt : Nat.card (Sylow n K) < n := lt_of_le_of_lt hSle hmn
  have hSone : Nat.card (Sylow n K) = 1 := by
    have hmod : Nat.card (Sylow n K) % n = 1 := by
      have h := hSmod
      rw [Nat.ModEq] at h
      rwa [Nat.mod_eq_of_lt hn.one_lt] at h
    rwa [Nat.mod_eq_of_lt hSlt] at hmod
  haveI : Subsingleton (Sylow n K) := (Nat.card_eq_one_iff_unique.mp hSone).1
  have hHnorm : H.Normal := by
    rw [← hPcoe]
    exact Sylow.normal_of_subsingleton P
  -- Conjugation by `x` preserves `H = ⟨y⟩`, so `x * y * x⁻¹ = y ^ s` for some `s : ℕ`.
  have hyH : y ∈ H := by rw [hHdef]; exact Subgroup.mem_zpowers y
  have hconj : x * y * x⁻¹ ∈ H := hHnorm.conj_mem y hyH x
  obtain ⟨s, _, hs⟩ :=
    Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp (hHdef ▸ hconj))
  refine ⟨y, x, s, hy, hx, ?_, hs.symm⟩
  -- If `s % n = 1` then `x` centralizes `y`, and then `x * y` has order `m * n = |K|`, so `K`
  -- is cyclic, hence commutative — contradicting non-abelianness.
  intro hsmod
  have hyn : y ^ n = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hys : y ^ s = y := by
    rw [pow_eq_pow_mod (a := y) (n := n) s hyn, hsmod, pow_one]
  have hxy : Commute x y := by
    show x * y = y * x
    have h := hs.symm.trans hys      -- `x * y * x⁻¹ = y`
    calc x * y = (x * y * x⁻¹) * x := by group
      _ = y * x := by rw [h]
  have hmn_dvd : ¬ m ∣ n := by
    intro hdiv
    rcases (Nat.dvd_prime hn).mp hdiv with h | h
    · exact hm.ne_one h
    · exact absurd h (ne_of_lt hmn)
  have hcop : (orderOf x).Coprime (orderOf y) := by
    rw [hx, hy]
    exact hm.coprime_iff_not_dvd.mpr hmn_dvd
  have hord : orderOf (x * y) = Nat.card K := by
    rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime hxy hcop, hx, hy, hcard]
  exact hNA (isMulCommutative_of_isCyclic_of_group (isCyclic_of_orderOf_eq_card (x * y) hord))

end Work.Frobenius.Complement
