import Mathlib
import Submission.Work.Coprime.Defs
import Submission.Work.Coprime.Internal
import Submission.Work.Coprime.fixedPoints_quotient
import Submission.Work.Coprime.cocycle_is_coboundary

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped Pointwise

namespace Work.ThreePoints.ThmC

/-- Lifting an element of order `p` through a normal `p'`-subgroup: if `gN` has order `p` in
`G ⧸ N` and `Nat.card N` is coprime to `p`, then some power `g ^ k` has order exactly `p` and the
same image `gN`.

Writing `orderOf g = p * d` (as `p ∣ orderOf g`), the element `g ^ p` lies in `N`, so
`d = orderOf (g ^ p) ∣ Nat.card N` is coprime to `p`.  Take `k = d * s` with `d * s ≡ 1 (mod p)`;
then `gcd (orderOf g) k = d`, so `orderOf (g ^ k) = p`, and `k ≡ 1 (mod p)` gives `g ^ k N = gN`. -/
theorem lift_orderOf_prime {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (N : Subgroup G) [N.Normal] (hcop : Nat.Coprime (Nat.card N) p) {g : G}
    (hg : orderOf (QuotientGroup.mk' N g) = p) :
    ∃ k : ℕ, orderOf (g ^ k) = p ∧ QuotientGroup.mk' N (g ^ k) = QuotientGroup.mk' N g := by
  classical
  -- `p` divides `orderOf g`, so `orderOf g = p * d`.
  have hdvd : p ∣ orderOf g := by
    rw [← hg]
    exact orderOf_map_dvd (QuotientGroup.mk' N) g
  obtain ⟨d, hd⟩ : ∃ d, orderOf g = p * d :=
    ⟨orderOf g / p, (Nat.mul_div_cancel' hdvd).symm⟩
  have hd_pos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h, mul_zero] at hd
      exact absurd hd (orderOf_pos g).ne'
    · exact h
  -- `g ^ p ∈ N`.
  have hgp_mem : g ^ p ∈ N := by
    have h1 : QuotientGroup.mk' N (g ^ p) = 1 := by
      rw [map_pow, ← hg, pow_orderOf_eq_one]
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  -- `orderOf (g ^ p) = d`, and `d` divides `Nat.card N`, hence `p ∤ d`.
  have hord_gp : orderOf (g ^ p) = d := by
    rw [orderOf_pow, hd, Nat.gcd_eq_right (show p ∣ p * d from ⟨d, rfl⟩)]
    exact Nat.mul_div_cancel_left d hp.pos
  have hd_dvd : d ∣ Nat.card N := by
    have h := orderOf_dvd_natCard (⟨g ^ p, hgp_mem⟩ : ↥N)
    rw [Subgroup.orderOf_mk, hord_gp] at h
    exact h
  have hpd : ¬ p ∣ d := by
    intro hdiv
    have hp_card : p ∣ Nat.card N := hdiv.trans hd_dvd
    have h1 : p ∣ (Nat.card N).gcd p := Nat.dvd_gcd hp_card dvd_rfl
    rw [hcop.gcd_eq_one] at h1
    exact hp.ne_one (Nat.dvd_one.mp h1)
  -- Solve `d * s ≡ 1 (mod p)`.
  have hdpcop : Nat.Coprime d p := hcop.coprime_dvd_left hd_dvd
  obtain ⟨s, hs_lt, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime (k := p) (n := d) hdpcop hp.one_lt
  have hs_cop : Nat.Coprime p s := by
    refine hp.coprime_iff_not_dvd.mpr ?_
    intro hps
    have h2 : d * s % p = 0 := ((Nat.dvd_iff_mod_eq_zero).mp (dvd_mul_of_dvd_right hps d))
    rw [h2] at hs
    exact Nat.zero_ne_one hs
  have hgcd : (p * d).gcd (d * s) = d := by
    rw [Nat.mul_comm p d, Nat.gcd_mul_left, hs_cop.gcd_eq_one, mul_one]
  refine ⟨d * s, ?_, ?_⟩
  · rw [orderOf_pow, hd, hgcd, Nat.mul_comm p d]
    exact Nat.mul_div_cancel_left p hd_pos
  · have hmod : d * s ≡ 1 [MOD p] := by
      rw [Nat.ModEq, hs, Nat.mod_eq_of_lt hp.one_lt]
    rw [map_pow]
    have h2 : (QuotientGroup.mk' N g) ^ (d * s) = QuotientGroup.mk' N g := by
      have h3 := (pow_eq_pow_iff_modEq (x := QuotientGroup.mk' N g) (n := d * s) (m := 1)).mpr
        (by rw [hg]; exact hmod)
      simpa using h3
    rw [h2]

/-- The coprime-action lifting step: if `y N ∈ M ⧸ N` is fixed by the conjugation action of the
`p`-subgroup `P` (assumed with `Nat.card N` coprime to `p`), then the coset `y N` contains a
representative `y'` centralising `P`.

The element `a ↦ y⁻¹ (a y a⁻¹)` (`a ∈ P`) is a `1`-cocycle with values in `N` for the conjugation
action of `P` on `N`; since `P` is a `p`-group (hence solvable) and `Nat.card N` is coprime to `p`,
`H¹` vanishes (`Work.Coprime.cocycle_is_coboundary`), so it is a coboundary `Φ a = n⁻¹ (a • n)`;
then `y' = y n⁻¹` centralises `P` and lies in the same coset. -/
theorem lift_to_centralizer {M : Type} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    (N : Subgroup M) [N.Normal] (hNp : Nat.Coprime (Nat.card N) p)
    {P : Subgroup M} (hPp : IsPGroup p P) {y : M}
    (hyP : ∀ g ∈ P, QuotientGroup.mk' N (g * y * g⁻¹) = QuotientGroup.mk' N y) :
    ∃ y' : M, y' ∈ Subgroup.centralizer (P : Set M) ∧
      QuotientGroup.mk' N y' = QuotientGroup.mk' N y := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hNorm : FT.Normalizes P N := ⟨by rw [Subgroup.normalizer_eq_top]; exact le_top⟩
  -- The `1`-cocycle `φ : P → N`, `a ↦ y⁻¹ (a y a⁻¹)`.
  let φ : ↥P → ↥N := fun a => ⟨y⁻¹ * ((a : M) * y * (a : M)⁻¹), by
    have hmem : (((a : M) * y * (a : M)⁻¹))⁻¹ * y ∈ N :=
      QuotientGroup.eq.mp (hyP (a : M) a.2)
    have hkey : y⁻¹ * ((a : M) * y * (a : M)⁻¹)
        = (((a : M) * y * (a : M)⁻¹)⁻¹ * y)⁻¹ := by group
    rw [hkey]
    exact N.inv_mem hmem⟩
  have hφ : ∀ a b : ↥P, φ (a * b) = φ a * (a • φ b) := by
    intro a b
    apply Subtype.ext
    simp only [φ, Subgroup.coe_mul, FT.conj_smul_coe]
    group
  have hcop : Nat.Coprime (Nat.card ↥P) (Nat.card ↥N) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPp
    rw [hk]
    exact hNp.symm.pow_left k
  have hsolv : Group.IsSolvable ↥P ∨ Group.IsSolvable ↥N := Or.inl (by
    haveI : Group.IsNilpotent ↥P := IsPGroup.isNilpotent hPp
    infer_instance)
  obtain ⟨n, hn⟩ := Work.Coprime.cocycle_is_coboundary ↥P hcop hsolv φ hφ
  refine ⟨y * (n : M)⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have hn' := congrArg (Subtype.val) (hn ⟨g, hg⟩)
    simp only [φ, Subgroup.coe_mul, Subgroup.coe_inv, FT.conj_smul_coe] at hn'
    -- `hn' : y⁻¹ * (g * y * g⁻¹) = (↑n)⁻¹ * (g * ↑n * g⁻¹)`
    have hkey : g * y * g⁻¹ = y * ((n : M))⁻¹ * (g * (n : M) * g⁻¹) := by
      calc g * y * g⁻¹ = y * (y⁻¹ * (g * y * g⁻¹)) := by group
        _ = y * (((n : M))⁻¹ * (g * (n : M) * g⁻¹)) := by rw [hn']
        _ = y * ((n : M))⁻¹ * (g * (n : M) * g⁻¹) := by group
    calc g * (y * ((n : M))⁻¹)
        = (g * y * g⁻¹) * (g * ((n : M))⁻¹ * g⁻¹) * g := by group
      _ = (y * ((n : M))⁻¹ * (g * (n : M) * g⁻¹)) * (g * ((n : M))⁻¹ * g⁻¹) * g := by
            rw [hkey]
      _ = (y * ((n : M))⁻¹) * g := by group
  · rw [map_mul]
    have hn1 : QuotientGroup.mk' N (n : M) = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact n.2
    rw [map_inv, hn1, inv_one, mul_one]

/-- Quotient/lifting step in the proof of Peterfalvi I App. IV (p. 210), used to transport the
hypothesis "every element of order `p` of `C_M(P)` lies in `P`" to a quotient `M/N` by a normal
`p'`-subgroup `N`.

If `ȳ ∈ M/N` has order `p` and is centralised by the image `PN/N` of the `p`-subgroup `P`, then some
representative `a` of `ȳ` lies in `C_M(P)` and has order exactly `p`.

Route: `C_{M/N}(PN/N) = C_M(P)·N/N` (coprime action, `P` is solvable as it is a `p`-group, and
`|N|` is coprime to `p`; use `Work.Coprime.fixedPoints_quotient` or the underlying coboundary
statement `Work.Coprime.cocycle_is_coboundary` with coefficients in `N`), so `y` may be replaced by
an element `y' ∈ C_M(P)` with the same image; writing `y' = y'_p · y'_{p'}` for the `p`-part and
`p'`-part of `y'` (coprime orders, both powers of `y'`), the `p'`-part maps to `1` (its order
divides both the `p`-power order of `ȳ` and the `p'`-number order of `y'_{p'}`), hence lies in `N`;
the `p`-part `y'_p` still maps to `ȳ`, and a suitable power of `y'_p` has order exactly `p` and the
same image. -/
theorem app4_lift {M : Type} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    (N : Subgroup M) [N.Normal] (hNp : Nat.Coprime (Nat.card N) p)
    {P : Subgroup M} (hPp : IsPGroup p P) {y : M}
    (hyP : ∀ g ∈ P, QuotientGroup.mk' N (g * y * g⁻¹) = QuotientGroup.mk' N y)
    (hyord : orderOf (QuotientGroup.mk' N y) = p) :
    ∃ a : M, a ∈ Subgroup.centralizer (P : Set M) ∧ orderOf a = p ∧
      QuotientGroup.mk' N a = QuotientGroup.mk' N y := by
  classical
  obtain ⟨y', hy'C, hy'im⟩ := lift_to_centralizer hp N hNp hPp hyP
  have hy'ord : orderOf (QuotientGroup.mk' N y') = p := by rw [hy'im]; exact hyord
  obtain ⟨k, hkord, hkim⟩ := lift_orderOf_prime hp N hNp hy'ord
  exact ⟨y' ^ k, Subgroup.pow_mem _ hy'C k, hkord, by rw [hkim, hy'im]⟩

end Work.ThreePoints.ThmC
