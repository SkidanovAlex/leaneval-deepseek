import Mathlib
import Submission.Work.BSW.Cases.Order.Setup
import Submission.Work.BSW.Cases.Order.centralizerSingletonEqK
import Submission.Work.BSW.Cases.Order.ncardModEqFixedConj
import Submission.Work.BSW.Cases.Order.invOdd
import Submission.Work.BSW.Api.ncard_involutions_eq_index
import Submission.Work.BSW.Api.normalizer_K_eq
import Submission.Work.BSW.Api.mem_centralizer_iff
import Submission.Work.BSW.Char.coset_sK_involutions

namespace Work.BSW.Cases.Order

open Subgroup

/-- **Odd primes.**  If `p ≠ 2` is a prime dividing `|K|` then `p` does not divide the index of
`C_G(t)`: pick `x ∈ K` of order `p`, so `C_G(x) = K` (`centralizerSingletonEqK`); counting the
involutions of `G` (a conjugation-stable set, `orderOf (g y g⁻¹) = orderOf y`) modulo `p` with
`ncardModEqFixedConj` shows that the involutions commuting with `x` are just `{t}`, hence the
number of involutions is `≡ 1 [MOD p]`; and the number of involutions is `[G : C_G(t)]`
(`Work.BSW.Api.ncard_involutions_eq_index`). -/
theorem oddPrime {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpdvd : p ∣ Nat.card ↥K) :
    ¬ p ∣ (Subgroup.centralizer ({t} : Set G)).index := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) p hpdvd
  set xg : G := (x : G) with hxg
  have hxK : xg ∈ K := x.2
  have hxord' : orderOf xg = p := by rw [hxg, Subgroup.orderOf_coe]; exact hxord
  have hxne1 : xg ≠ 1 := by
    intro hc
    rw [hc, orderOf_one] at hxord'
    exact hp.ne_one hxord'.symm
  have hxt : xg ≠ t := by
    intro hc
    rw [hc, Work.BSW.orderOf_t h] at hxord'
    exact hp2 hxord'.symm
  have hCeq : Subgroup.centralizer ({xg} : Set G) = K :=
    centralizerSingletonEqK h hxK hxne1 hxt
  have hfix : {y : G | orderOf y = 2 ∧ xg * y = y * xg}.ncard = 1 := by
    have hset : {y : G | orderOf y = 2 ∧ xg * y = y * xg} = {t} := by
      rw [Set.eq_singleton_iff_unique_mem]
      refine ⟨⟨Work.BSW.orderOf_t h, ?_⟩, ?_⟩
      · have hmem : t ∈ Subgroup.centralizer ({xg} : Set G) := by
          rw [hCeq]; exact Work.BSW.t_mem_K h
        exact (Subgroup.mem_centralizer_singleton_iff.mp hmem).symm
      · intro y hy
        obtain ⟨hy2, hycomm⟩ := hy
        have hymem : y ∈ Subgroup.centralizer ({xg} : Set G) :=
          Subgroup.mem_centralizer_singleton_iff.mpr hycomm.symm
        rw [hCeq] at hymem
        exact Work.BSW.orderOf_eq_two_of_mem_K h hymem hy2
    rw [hset, Set.ncard_singleton]
  have hS : ∀ g : G, ∀ y ∈ ({y : G | orderOf y = 2} : Set G),
      g * y * g⁻¹ ∈ ({y : G | orderOf y = 2} : Set G) := by
    intro g y hy
    simp only [Set.mem_ofPred_eq] at hy ⊢
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hy]
  have hmod := ncardModEqFixedConj ({y : G | orderOf y = 2} : Set G) hS hp hxord'
  have hset2 : {y ∈ ({y : G | orderOf y = 2} : Set G) | xg * y = y * xg}
      = {y : G | orderOf y = 2 ∧ xg * y = y * xg} := by
    ext y; simp only [Set.mem_ofPred_eq]
  rw [hset2, hfix] at hmod
  rw [Work.BSW.Api.ncard_involutions_eq_index h] at hmod
  intro hdvd
  have h0 : (Subgroup.centralizer ({t} : Set G)).index ≡ 0 [MOD p] :=
    Nat.modEq_zero_iff_dvd.mpr hdvd
  exact hp.not_dvd_one (Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans h0))

/-- **The prime 2.**  The number of involutions of `G` is odd (`invOdd`), and it equals the index
of `C_G(t)`. -/
theorem not_two_dvd_index {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) :
    ¬ 2 ∣ (Subgroup.centralizer ({t} : Set G)).index := by
  have hodd : Odd (Subgroup.centralizer ({t} : Set G)).index := by
    rw [← Work.BSW.Api.ncard_involutions_eq_index h]
    exact invOdd ⟨t, Work.BSW.orderOf_t h⟩
  exact fun h2 => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

/-- **Bender 1974, §2, p. 231**: `H = C_G(t)` is a Hall subgroup of `G`, in the form
`gcd(2k, [G : C_G(t)]) = 1` with `k = |K|` (`|C_G(t)| = 2k`). -/
theorem hallProp {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) :
    Nat.Coprime (2 * Nat.card ↥K) (Subgroup.centralizer ({t} : Set G)).index := by
  classical
  show Nat.gcd (2 * Nat.card ↥K) (Subgroup.centralizer ({t} : Set G)).index = 1
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have hp2k : p ∣ 2 * Nat.card ↥K := hpd.trans (Nat.gcd_dvd_left _ _)
  have hpR : p ∣ (Subgroup.centralizer ({t} : Set G)).index := hpd.trans (Nat.gcd_dvd_right _ _)
  rcases hp.dvd_mul.mp hp2k with h2 | hk
  · -- `p ∣ 2`, so `p = 2`
    have hpeq : p = 2 := ((Nat.dvd_prime Nat.prime_two).mp h2).resolve_left hp.ne_one
    subst hpeq
    exact not_two_dvd_index h hpR
  · rcases eq_or_ne p 2 with hpeq | hp2
    · subst hpeq
      exact not_two_dvd_index h hpR
    · exact oddPrime h hp hp2 hk hpR

end Work.BSW.Cases.Order
