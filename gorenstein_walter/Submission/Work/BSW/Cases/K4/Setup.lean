/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW, the `|K| = 4` case)

# The `|K| = 4` case of BSW: the involution centralizer is dihedral of order `8`

Under `Work.GW2.BSWHyps2 G t s K` with `Nat.card K = 4`, the subgroup `K` is cyclic of order `4`
(it is abelian with the unique involution `t`), so `C_G(t) = K ⊔ ⟨s⟩ = K ⋊ ⟨s⟩` has order `8` and
is dihedral: `s` inverts `K` and `s ∉ K`.  Every element of `C_G(t)` is either an element of `K`
(order dividing `4`) or of the form `k * s` with `k ∈ K` (an involution).

Since all involutions of `G` are conjugate to `t`, every involution centralizer is a conjugate of
`C_G(t)`: it has order `8` and is dihedral, so it contains no element of order `6` or `18`, and the
elements of any involution centralizer have order `1`, `2` or `4`.

These are the elementary facts on which the case analysis of `bswK4StructureProp` rests.
-/
import Mathlib
import Submission.Work.BSW.Concl
import Submission.Work.BSW.Api.card_sup_zpowers
import Submission.Work.BSW.Api.mem_centralizer_iff
import Submission.Work.BSW.Api.normalizer_K_eq

namespace Work.BSW.Cases.K4

open Subgroup Work.GW2

variable {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}

/-- `|C_G(t)| = 2|K| = 8` in the `|K| = 4` case. -/
theorem card_centralizer_t (h : BSWHyps2 G t s K) (hK : Nat.card ↥K = 4) :
    Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = 8 := by
  rw [Work.BSW.centralizer_t_eq h, Work.BSW.Api.card_sup_zpowers h, hK]

/-- An element of a subgroup has order dividing the order of that subgroup. -/
theorem orderOf_dvd_natCard_of_mem {H : Subgroup G} {x : G} (hx : x ∈ H) :
    orderOf x ∣ Nat.card ↥H := by
  have h1 := orderOf_dvd_natCard (⟨x, hx⟩ : ↥H)
  have h2 : orderOf (⟨x, hx⟩ : ↥H) = orderOf x := (Subgroup.orderOf_coe (⟨x, hx⟩ : ↥H)).symm
  rwa [h2] at h1

/-- In the `|K| = 4` case, `K` is cyclic of order `4`: there is `k ∈ K` with `orderOf k = 4`,
`K = ⟨k⟩` and `k * k = t`. -/
theorem exists_gen_K (h : BSWHyps2 G t s K) (hK : Nat.card ↥K = 4) :
    ∃ k : G, orderOf k = 4 ∧ K = Subgroup.zpowers k ∧ k * k = t := by
  -- every element of `K` has order dividing `4`
  have hdvd : ∀ x ∈ K, orderOf x ∣ 4 := fun x hx => by
    have h1 := orderOf_dvd_natCard_of_mem (H := K) hx
    rwa [hK] at h1
  -- some element of `K` does not square to `1`
  obtain ⟨k, hkK, hk2⟩ : ∃ k ∈ K, k * k ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hle : K ≤ Subgroup.zpowers t := by
      intro x hx
      rcases Work.BSW.involution_mem_K h hx (hcon x hx) with h1 | h1
      · rw [h1]; exact Subgroup.one_mem _
      · rw [h1]; exact Subgroup.mem_zpowers t
    have hcard : Nat.card ↥K ≤ Nat.card ↥(Subgroup.zpowers t) :=
      Nat.card_le_card_of_injective (fun x : ↥K => (⟨x.1, hle x.2⟩ : ↥(Subgroup.zpowers t)))
        (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))
    rw [Nat.card_zpowers, hK, Work.BSW.orderOf_t h] at hcard
    omega
  have hk4 : orderOf k = 4 := by
    have h1 : orderOf k ∣ 4 := hdvd k hkK
    have h' : orderOf k ∣ 2 ^ 2 := by simpa using h1
    have h2 : ¬ orderOf k ∣ 2 := by
      intro hd
      have h2p : k ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hd
      exact hk2 (by rwa [pow_two] at h2p)
    obtain ⟨i, hi, hord⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 2)).mp h'
    have hi2 : i = 2 := by
      by_contra hne
      have hle : i ≤ 1 := by omega
      have hdvd2 : 2 ^ i ∣ 2 := by interval_cases i <;> norm_num
      exact h2 (hord ▸ hdvd2)
    subst hi2
    simpa using hord
  refine ⟨k, hk4, ?_, ?_⟩
  · have hle : Subgroup.zpowers k ≤ K := Subgroup.zpowers_le.mpr hkK
    have hcard : Nat.card ↥(Subgroup.zpowers k) = Nat.card ↥K := by
      rw [Nat.card_zpowers, hk4, hK]
    exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)).symm
  · have hmem : k * k ∈ K := K.mul_mem hkK hkK
    have hord : orderOf (k * k) = 2 := by
      have h1 : k * k = k ^ 2 := (pow_two k).symm
      rw [h1, orderOf_pow, hk4]
      norm_num
    exact Work.BSW.orderOf_eq_two_of_mem_K h hmem hord

/-- An element of `K⟨s⟩` outside `K` is an involution: `(y * s)² = 1` for `y ∈ K`. -/
theorem mul_s_self (h : BSWHyps2 G t s K) {y : G} (hy : y ∈ K) : (y * s) * (y * s) = 1 := by
  have h1 : s * y * s⁻¹ = y⁻¹ := Work.BSW.inverts_s_K h y hy
  have h2 : s * y = y⁻¹ * s := by
    rw [← h1]; group
  calc (y * s) * (y * s) = y * (s * y) * s := by group
    _ = y * (y⁻¹ * s) * s := by rw [h2]
    _ = (y * y⁻¹) * (s * s) := by group
    _ = 1 := by rw [mul_inv_cancel, Work.BSW.s_mul_self h, mul_one]

/-- The elements of `⟨y⟩` for an involution `y` are `1` and `y`. -/
theorem mem_zpowers_eq_one_or {y z : G} (hy : orderOf y = 2)
    (hz : z ∈ Subgroup.zpowers y) : z = 1 ∨ z = y := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hy2 : y ^ 2 = 1 := by
    rw [← hy]
    exact pow_orderOf_eq_one y
  have h1 : y ^ i = y ^ (i % (2 : ℤ)) := zpow_eq_zpow_emod' i hy2
  rcases Int.emod_two_eq_zero_or_one i with hh | hh
  · left; rw [h1, hh]; exact zpow_zero y
  · right; rw [h1, hh]; exact zpow_one y

/-- Every element of `C_G(t)` has order `1`, `2` or `4`: it lies in `K` (cyclic of order `4`) or is
of the form `y * s` with `y ∈ K`, and all such elements are involutions. -/
theorem orderOf_dichotomy_of_mem_centralizer_t (h : BSWHyps2 G t s K) (hK : Nat.card ↥K = 4)
    (_k : G) (_hkK : K = Subgroup.zpowers _k) (_hkt : _k * _k = t) {x : G}
    (hx : x ∈ Subgroup.centralizer ({t} : Set G)) :
    orderOf x = 1 ∨ orderOf x = 2 ∨ orderOf x = 4 := by
  rcases (Work.BSW.Api.mem_centralizer_iff h x).mp hx with hxK | ⟨y, hyK, rfl⟩
  · -- `x ∈ K`
    have hd : orderOf x ∣ 4 := by
      have h1 := orderOf_dvd_natCard_of_mem (H := K) hxK
      rwa [hK] at h1
    have h' : orderOf x ∣ 2 ^ 2 := by simpa using hd
    obtain ⟨i, hi, hord⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 2)).mp h'
    interval_cases i
    · exact Or.inl (by simpa using hord)
    · exact Or.inr (Or.inl (by simpa using hord))
    · exact Or.inr (Or.inr (by simpa using hord))
  · -- `x = y * s` with `y ∈ K`
    have hsq : (y * s) * (y * s) = 1 := mul_s_self h hyK
    have hne : y * s ≠ 1 := by
      intro h1
      have h2 : y = s⁻¹ := mul_eq_one_iff_eq_inv.mp h1
      rw [Work.BSW.s_inv h] at h2
      exact Work.BSW.s_notMem_K h (h2 ▸ hyK)
    have hd : orderOf (y * s) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hsq)
    have h' : orderOf (y * s) ∣ 2 ^ 1 := by simpa using hd
    obtain ⟨i, hi, hord⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 1)).mp h'
    interval_cases i
    · exact absurd (show orderOf (y * s) = 1 from by simpa using hord)
        (by rw [orderOf_eq_one_iff]; exact hne)
    · exact Or.inr (Or.inl (by simpa using hord))

/-- If `y` is an involution then every element of `C_G(y)` has order `1`, `2` or `4`: `y` is
conjugate to `t`, so `C_G(y)` is a conjugate of `C_G(t)`, and conjugation preserves orders. -/
theorem orderOf_dichotomy_of_mem_centralizer_of_orderOf_eq_two (h : BSWHyps2 G t s K)
    (hK : Nat.card ↥K = 4) {y x : G} (hy : orderOf y = 2)
    (hx : x ∈ Subgroup.centralizer ({y} : Set G)) :
    orderOf x = 1 ∨ orderOf x = 2 ∨ orderOf x = 4 := by
  obtain ⟨k, hk4, hkgen, hkt⟩ := exists_gen_K h hK
  obtain ⟨c, hc⟩ := isConj_iff.mp (Work.BSW.involutions_conj h y hy)
  have hxy : x * y = y * x := Subgroup.mem_centralizer_singleton_iff.mp hx
  have hmem : c * x * c⁻¹ ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (c * x * c⁻¹) * t = (c * x * c⁻¹) * (c * y * c⁻¹) := by rw [hc]
      _ = c * (x * y) * c⁻¹ := by group
      _ = c * (y * x) * c⁻¹ := by rw [← hxy]
      _ = (c * y * c⁻¹) * (c * x * c⁻¹) := by group
      _ = t * (c * x * c⁻¹) := by rw [hc]
  have h2 := orderOf_dichotomy_of_mem_centralizer_t h hK k hkgen hkt hmem
  have h3 : orderOf (c * x * c⁻¹) = orderOf x := by
    rw [← MulAut.conj_apply]
    exact MulEquiv.orderOf_eq (MulAut.conj c) x
  rwa [h3] at h2

/-- Every involution centralizer has order `8` in the `|K| = 4` case. -/
theorem card_centralizer_of_orderOf_eq_two (h : BSWHyps2 G t s K) (hK : Nat.card ↥K = 4)
    {y : G} (hy : orderOf y = 2) :
    Nat.card ↥(Subgroup.centralizer ({y} : Set G)) = 8 := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (Work.BSW.involutions_conj h y hy) -- c * y * c⁻¹ = t
  have hmap : (Subgroup.centralizer ({y} : Set G)).map (MulAut.conj c).toMonoidHom =
      Subgroup.centralizer ({c * y * c⁻¹} : Set G) := by
    ext z
    constructor
    · rintro ⟨w, hw, hwz⟩
      have hw' : w * y = y * w := Subgroup.mem_centralizer_singleton_iff.mp hw
      have hzw : c * w * c⁻¹ = z := by rw [← hwz]; rfl
      rw [← hzw, Subgroup.mem_centralizer_singleton_iff]
      calc (c * w * c⁻¹) * (c * y * c⁻¹) = c * (w * y) * c⁻¹ := by group
        _ = c * (y * w) * c⁻¹ := by rw [hw']
        _ = (c * y * c⁻¹) * (c * w * c⁻¹) := by group
    · intro hz
      have hz' : z * (c * y * c⁻¹) = (c * y * c⁻¹) * z :=
        Subgroup.mem_centralizer_singleton_iff.mp hz
      refine ⟨c⁻¹ * z * c, ?_, ?_⟩
      · change c⁻¹ * z * c ∈ Subgroup.centralizer ({y} : Set G)
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc (c⁻¹ * z * c) * y = c⁻¹ * (z * (c * y * c⁻¹)) * c := by group
          _ = c⁻¹ * ((c * y * c⁻¹) * z) * c := by rw [hz']
          _ = y * (c⁻¹ * z * c) := by group
      · show (MulAut.conj c).toMonoidHom (c⁻¹ * z * c) = z
        change c * (c⁻¹ * z * c) * c⁻¹ = z
        group
  calc Nat.card ↥(Subgroup.centralizer ({y} : Set G))
      = Nat.card ↥((Subgroup.centralizer ({y} : Set G)).map (MulAut.conj c).toMonoidHom) :=
        (Subgroup.card_map_of_injective (f := (MulAut.conj c).toMonoidHom)
          (MulAut.conj c).injective).symm
    _ = Nat.card ↥(Subgroup.centralizer ({c * y * c⁻¹} : Set G)) := by rw [hmap]
    _ = Nat.card ↥(Subgroup.centralizer ({t} : Set G)) := by rw [hc]
    _ = 8 := card_centralizer_t h hK

/-- There is no element of order `6` in the `|K| = 4` case: `x³` would be an involution commuting
with `x`, so `x` would lie in an involution centralizer, and the elements of such a centralizer have
order `1`, `2` or `4`. -/
theorem orderOf_ne_six (h : BSWHyps2 G t s K) (hK : Nat.card ↥K = 4) (x : G) :
    orderOf x ≠ 6 := by
  intro hx6
  have hx3 : orderOf (x ^ 3) = 2 := by
    rw [orderOf_pow, hx6]
    norm_num
  have hmem : x ∈ Subgroup.centralizer ({x ^ 3} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    group
  have h2 := orderOf_dichotomy_of_mem_centralizer_of_orderOf_eq_two h hK hx3 hmem
  omega

/-- There is no element of order `18` in the `|K| = 4` case. -/
theorem orderOf_ne_eighteen (h : BSWHyps2 G t s K) (hK : Nat.card ↥K = 4) (x : G) :
    orderOf x ≠ 18 := by
  intro hx18
  have hx9 : orderOf (x ^ 9) = 2 := by
    rw [orderOf_pow, hx18]
    norm_num
  have hmem : x ∈ Subgroup.centralizer ({x ^ 9} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    group
  have h2 := orderOf_dichotomy_of_mem_centralizer_of_orderOf_eq_two h hK hx9 hmem
  omega

/-- The normalizer of `⟨y⟩` for an involution `y` is its centralizer (an element normalizing a
group of order `2` fixes its unique involution). -/
theorem normalizer_zpowers_eq_centralizer_of_orderOf_eq_two {y : G} (hy : orderOf y = 2) :
    Subgroup.normalizer (Subgroup.zpowers y : Set G) =
      Subgroup.centralizer ({y} : Set G) := by
  apply le_antisymm
  · intro g hg
    have hmem : g * y * g⁻¹ ∈ Subgroup.zpowers y :=
      (Subgroup.mem_normalizer_iff.mp hg y).mp (Subgroup.mem_zpowers y)
    have hord : orderOf (g * y * g⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hy
    rcases mem_zpowers_eq_one_or hy hmem with h1 | h1
    · rw [h1, orderOf_one] at hord
      exact absurd hord (by norm_num)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc g * y = (g * y * g⁻¹) * g := by group
        _ = y * g := by rw [h1]
  · rw [Subgroup.le_normalizer_iff]
    intro g hg z hz
    have hgy : g * y * g⁻¹ = y := by
      have h' : g * y = y * g := Subgroup.mem_centralizer_singleton_iff.mp hg
      calc g * y * g⁻¹ = y * g * g⁻¹ := by rw [h']
        _ = y := by group
    have hconj : ∀ n : ℤ, g * y ^ n * g⁻¹ = y ^ n := by
      intro n
      rw [← MulAut.conj_apply, map_zpow, show (MulAut.conj g) y = y from by
        rw [MulAut.conj_apply]; exact hgy]
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    change g * y ^ n * g⁻¹ ∈ Subgroup.zpowers y
    rw [hconj n]
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩

end Work.BSW.Cases.K4
