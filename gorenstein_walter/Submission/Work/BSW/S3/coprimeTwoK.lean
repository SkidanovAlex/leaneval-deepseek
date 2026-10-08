/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW)

# Bender §3.1 (f): `gcd(|C_G(x)|, 2|K|) = 1`

Setting: `G` finite with `BSWHyps2 G t s K` (Bender's (i)–(iv)), `H = C_G(t) = K⟨s⟩`,
`x ∉ H^G` inverted by `t`, and `F = C_G(x)`.

Bender 1974, §3.1 (f) claims that `F` is a Hall subgroup of `G` *coprime to `2k`*
(`REFS/bender1974_bsw.txt`, p. 232).  Here we prove the coprimality statement
`Nat.Coprime |F| (2 * |K|)` from the Hall-ness of `F` (taken as a hypothesis, `hhall`).

The mathematical content is the remark of design pass 8
(`Submission/Work/NOTES_LEAD_gw_design8.md`, §2.2, 3.1 (f)): an odd prime `r`
dividing `|F|` cannot divide `|K|`, since then an `r`-element of `F` would be conjugate
into `K ≤ H ⊆ H^G`, while `F ∩ H^G = 1`.

* `exists_sylow_le_of_not_dvd_index`: if `p ∤ [G : K]` then `K` contains a Sylow
  `p`-subgroup of `G` (because `|K|_p = |G|_p`).
* `centralizer_inf_HG_eq_bot`: `C_G(x) ∩ H^G = 1`: a nonidentity `y ∈ C_G(x)` conjugate
  into `C_G(t)` would centralize the involution `g⁻¹ t g`, hence `g⁻¹ t g ∈ C_G(y) = C_G(x)`,
  contradicting the fact that no involution lies in `C_G(x)`.
* the Sylow conjugacy step uses `Sylow.isPretransitive_of_finite`.

The Odd-prime input `¬ r ∣ [G : C_G(t)]` (Bender §2, `H` is a Hall subgroup, area
`Work.BSW.Cases.Order`, `hallProp`) is the only place the deep part of §2 is used.
-/
import Mathlib
import Submission.Work.BSW.S3.S31setup
import Submission.Work.BSW.Cases.Order.hallProp

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Pointwise

namespace Work.BSW.S3

open Subgroup Work.GW2

/-- If `p` does not divide `[G : K]`, then `K` contains a Sylow `p`-subgroup of `G`.

Indeed `|K|_p = |G|_p` in that case, so the image in `G` of a Sylow `p`-subgroup of `K` has
the order of a Sylow `p`-subgroup of `G`, and is contained in one; the two are therefore
equal and `K` contains a Sylow `p`-subgroup of `G`. -/
theorem exists_sylow_le_of_not_dvd_index {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {K : Subgroup G} (hidx : ¬ p ∣ K.index) : ∃ Q : Sylow p G, Q ≤ K := by
  classical
  obtain ⟨P⟩ : Nonempty (Sylow p ↥K) := Sylow.nonempty
  set Q₀ : Subgroup G := (P : Subgroup ↥K).map K.subtype with hQ₀
  have hQ₀_pg : IsPGroup p ↥Q₀ := (P.isPGroup').map K.subtype
  obtain ⟨Q, hQ₀Q⟩ := IsPGroup.exists_le_sylow (p := p) hQ₀_pg
  have hK0 : Nat.card ↥K ≠ 0 := by
    rw [Nat.card_ne_zero]; exact ⟨⟨⟨1, K.one_mem⟩⟩, inferInstance⟩
  have hidx0 : K.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hfac : (Nat.card G).factorization p = (Nat.card ↥K).factorization p := by
    conv_lhs => rw [← Subgroup.card_mul_index K]
    rw [Nat.factorization_mul hK0 hidx0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hidx, add_zero]
  have hcard_eq : Nat.card ↥(Q : Subgroup G) = Nat.card ↥Q₀ := by
    rw [Sylow.card_eq_multiplicity Q, hQ₀,
      Subgroup.card_map_of_injective K.subtype_injective, Sylow.card_eq_multiplicity P, hfac]
  have heq : Q₀ = (Q : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hQ₀Q (le_of_eq hcard_eq)
  exact ⟨Q, heq ▸ Subgroup.map_subtype_le (P : Subgroup ↥K)⟩

/-- `C_G(x) ∩ H^G = 1` for `x ∉ H^G` inverted by `t`, `H = C_G(t)`.

If `y ∈ C_G(x)` is conjugate into `C_G(t)` then `y` commutes with the involution
`g⁻¹ t g`; as `C_G(y) = C_G(x)` for `y ≠ 1` (Bender §3.1 (i)) this puts an involution
into `C_G(x)`, which is impossible. -/
theorem centralizer_inf_HG_eq_bot {G : Type} [Group G] [Finite G] {t s x : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) (hx : x ∉ Work.BSW.HG t) (hinv : t⁻¹ * x * t = x⁻¹) :
    ∀ y ∈ (Subgroup.centralizer ({x} : Set G) : Set G), y ∈ Work.BSW.HG t → y = 1 := by
  intro y hyF hyHG
  by_contra hy1
  obtain ⟨g, hg⟩ := hyHG
  have hcomm : (g⁻¹ * t * g) * y = y * (g⁻¹ * t * g) := by
    have h1 : (g * y * g⁻¹) * t = t * (g * y * g⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.mp hg
    calc (g⁻¹ * t * g) * y = g⁻¹ * (t * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * y * g⁻¹) * t) * g := by rw [← h1]
      _ = y * (g⁻¹ * t * g) := by group
  have hmem : g⁻¹ * t * g ∈ Subgroup.centralizer ({y} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  rw [centralizer_eq_of_mem_centralizer h hx hinv y hyF hy1] at hmem
  refine involution_notMem_centralizer h hx ?_ hmem
  have h2 : g⁻¹ * t * g = (MulAut.conj g⁻¹) t := by rw [MulAut.conj_apply, inv_inv]
  rw [h2, MulEquiv.orderOf_eq, Work.BSW.orderOf_t h]

/-- **Bender 1974, §3.1 (f).**  For `x ∉ H^G` inverted by `t`, `|C_G(x)|` is coprime to
`2|K|`: it is odd, and an odd prime dividing both `|C_G(x)|` and `|K|` would give an
element of order `r` in `C_G(x)` conjugate into `K ≤ H ⊆ H^G`. -/
theorem coprimeTwoK {G : Type} [Group G] [Finite G] {t s x : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) (hx : x ∉ Work.BSW.HG t) (hinv : t⁻¹ * x * t = x⁻¹)
    (hhall : Nat.Coprime (Nat.card ↥(Subgroup.centralizer ({x} : Set G)))
      (Subgroup.centralizer ({x} : Set G)).index) :
    Nat.Coprime (Nat.card ↥(Subgroup.centralizer ({x} : Set G))) (2 * Nat.card K) := by
  classical
  have hodd := odd_card_centralizer_of_notMem_HG h hx
  refine Nat.Coprime.mul_right (Nat.coprime_two_right.mpr hodd) ?_
  by_contra hnc
  obtain ⟨p, hp, hpf, hpk⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    intro h2
    rw [h2] at hpf
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpf)
  have hCidx : ¬ p ∣ (Subgroup.centralizer ({t} : Set G)).index :=
    Work.BSW.Cases.Order.oddPrime h hp hp2 hpk
  obtain ⟨a, ha_ord⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.centralizer ({x} : Set G))) p hpf
  set ag : G := (a : G) with hag
  have hag_ord : orderOf ag = p := by rw [hag, Subgroup.orderOf_coe]; exact ha_ord
  have hzp : IsPGroup p ↥(Subgroup.zpowers ag) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hag_ord, pow_one]
  obtain ⟨P, hPle⟩ := IsPGroup.exists_le_sylow (p := p) hzp
  obtain ⟨Q, hQle⟩ := exists_sylow_le_of_not_dvd_index (p := p)
    (K := Subgroup.centralizer ({t} : Set G)) hCidx
  haveI hfin : Finite (Sylow p G) := Sylow.finite_of_finiteIndex P
  have hpre : MulAction.IsPretransitive G (Sylow p G) :=
    Sylow.isPretransitive_of_finite (p := p) (G := G)
  obtain ⟨g, hg⟩ := hpre.exists_smul_eq P Q
  have hmemP : ag ∈ (P : Subgroup G) := hPle (Subgroup.mem_zpowers ag)
  have hQeq : (Q : Subgroup G) = MulAut.conj g • (P : Subgroup G) := by
    rw [← hg]; rfl
  have hmemQ : (MulAut.conj g) • ag ∈ (Q : Subgroup G) := by
    rw [hQeq, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← mul_smul, inv_mul_cancel,
      one_smul]
    exact hmemP
  have hmemC : g * ag * g⁻¹ ∈ (Subgroup.centralizer ({t} : Set G) : Subgroup G) := by
    have h2 := hQle hmemQ
    rwa [MulAut.smul_def, MulAut.conj_apply] at h2
  have hHG : ag ∈ Work.BSW.HG t := ⟨g, hmemC⟩
  have hFmem : ag ∈ (Subgroup.centralizer ({x} : Set G) : Set G) := a.2
  have h1 := centralizer_inf_HG_eq_bot h hx hinv ag hFmem hHG
  rw [h1, orderOf_one] at hag_ord
  exact hp.ne_one hag_ord.symm

end Work.BSW.S3
