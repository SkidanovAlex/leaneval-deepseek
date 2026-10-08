/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — `A₇` case of Bender 1981 §4: `|S ∩ E(M)| = 8`

`Work.CORE4.A7Vsylow`.  In the `A₇` configuration of Bender 1981, §4 (p. 226) — `E = E(M)` the
layer of the maximal subgroup `M` with `E/Z(E) ≅ A₇` and `S` a Sylow `2`-subgroup of `G` chosen so
that `S ∩ M ∈ Syl₂(M)` (`Case2PrePlus`) — the Sylow `2`-subgroup `S ∩ E` of `E` has order `8`.

The route is the one described in `CORE4/Defs10.lean` (`A7VProp`): `S ∩ E` is a Sylow
`2`-subgroup of `E` because `E ⊴ M` and `S ∩ M ∈ Syl₂(M)`; and `|E|₂ = 8` because

* `|E| = |Z(E)| · |E/Z(E)| = |Z(E)| · 2520` (`|A₇| = 7!/2`), and
* `Z(E)` has *odd* order: `Z(E)` is a normal abelian — so nilpotent (`le_fitting_of_normal_nilpotent`)
  — subgroup of `M`, hence lies in `F(M)`; and `π(F(M)) ⊆ π(F(U)) = {3}` is the fifth conjunct of
  `Case2SevenFacts` together with `A7Facts1`.

The two group-theoretic ingredients are proved below as separate lemmas:

* `not_two_dvd_relIndex_inf_of_normal` — `S ∩ M` Sylow in `M`, `E ⊴ M` ⟹ `S ∩ E` Sylow in `E`
  (in the index form `2 ∤ |E : S ∩ E|`), by pushing the quotient `P/(P ∩ E)` into `M/E` (the
  divisibility `|P : P ∩ E| ∣ |M : E|` is the only place normality is needed) and comparing the
  two factorisations of `|M : Q|`;
* `odd_card_center_of_normal` — the centre of a normal subgroup `E ⊴ M` whose order has only the
  prime `3` as prime divisor of `|F(M)|` has odd order.
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.API
import Submission.Work.CORE4.CountSetup

namespace Work.CORE4

open Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## Auxiliary group theory -/

/-- **A Sylow `2`-subgroup of a normal subgroup.**  Let `M E S ≤ G` with `E ⊴ M`
(`M ≤ N_G(E)`) and `S ∩ M` a Sylow `2`-subgroup of `M`, i.e. `2 ∤ |M : S ∩ M|`.  Then `S ∩ E` is
a Sylow `2`-subgroup of `E`, i.e. `2 ∤ |E : S ∩ E|`.

Write `P := S ∩ M`, `Q := S ∩ E = P ∩ E`.  The quotient map `P → M/E` has kernel `Q`, so
`|P : Q| = |PE : E|` divides `|M : E|`; and the two factorisations
`|M : Q| = |M : P| · |P : Q|` and `|M : Q| = |M : E| · |E : Q|` of the same number give
`|E : Q| = |P : Q| · |M : P| / |M : E|`, whose `2`-part vanishes because the `2`-part of `|P : Q|`
is at most that of `|M : E|` and that of `|M : P|` is zero. -/
theorem not_two_dvd_relIndex_inf_of_normal (M E S : Subgroup G)
    (hEM : E ≤ M) (hEsub : M ≤ Subgroup.normalizer (E : Set G))
    (hodd : ¬ 2 ∣ (S ⊓ M).relIndex M) : ¬ 2 ∣ (S ⊓ E).relIndex E := by
  set P : Subgroup G := S ⊓ M with hP
  set Q : Subgroup G := S ⊓ E with hQ
  have hPM : P ≤ M := by rw [hP]; exact inf_le_right
  have hQPE : Q = P ⊓ E := by rw [hQ, hP, inf_assoc, inf_eq_right.mpr hEM]
  have hQP : Q ≤ P := hQPE ▸ inf_le_left
  have hQE : Q ≤ E := hQPE ▸ inf_le_right
  have hodd' : ¬ 2 ∣ P.relIndex M := by rw [hP]; exact hodd
  have hEn : (E.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff hEM).mpr (fun h k hh hk =>
      Subgroup.le_normalizer_iff.mp hEsub k hk h hh)
  haveI := hEn
  -- the quotient map `P → M/E`, whose kernel is `Q`
  let ψ : ↥P →* ↥M ⧸ E.subgroupOf M :=
    (QuotientGroup.mk' (E.subgroupOf M)).comp (Subgroup.inclusion hPM)
  have hker : ψ.ker = Q.subgroupOf P := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hx' : (Subgroup.inclusion hPM x : ↥M) ∈ E.subgroupOf M := by
        have h2 : QuotientGroup.mk' (E.subgroupOf M) (Subgroup.inclusion hPM x) = 1 := hx
        rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      rw [Subgroup.mem_subgroupOf] at hx'
      rw [hQPE, Subgroup.mem_inf]
      exact ⟨x.2, by rw [← Subgroup.coe_inclusion hPM x]; exact hx'⟩
    · intro hx
      rw [hQPE, Subgroup.mem_inf] at hx
      obtain ⟨hxP, hxE⟩ := hx
      have h2 : QuotientGroup.mk' (E.subgroupOf M) (Subgroup.inclusion hPM x) = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        rwa [Subgroup.coe_inclusion hPM x]
      exact h2
  -- `|P : Q|` divides `|M : E|`
  have hdvd : Q.relIndex P ∣ E.relIndex M := by
    have h1 : Q.relIndex P = Nat.card ↥ψ.range := by
      rw [Subgroup.relIndex, Subgroup.index_eq_card, ← hker]
      exact Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv
    rw [h1, Subgroup.relIndex, Subgroup.index_eq_card]
    have h := Subgroup.card_dvd_of_le (le_top : ψ.range ≤ ⊤)
    rwa [Subgroup.card_top] at h
  -- the two factorisations of `|M : Q|`
  have heq : Q.relIndex E * E.relIndex M = Q.relIndex P * P.relIndex M := by
    have h1 := Subgroup.relIndex_mul_relIndex Q P M hQP hPM
    have h2 := Subgroup.relIndex_mul_relIndex Q E M hQE hEM
    rw [h2, h1]
  intro h2dvd
  obtain ⟨b, hb⟩ := hdvd
  have hCne : Q.relIndex P ≠ 0 := by
    intro h0
    have h := Subgroup.relIndex_mul_card Q P
    rw [h0, zero_mul] at h
    haveI : Nonempty ↥P := ⟨⟨1, P.one_mem⟩⟩
    exact Nat.card_pos.ne' h.symm
  have hAb : Q.relIndex E * b = P.relIndex M := by
    have h := heq
    rw [hb] at h
    have h2 : Q.relIndex P * (Q.relIndex E * b) = Q.relIndex P * P.relIndex M := by
      rw [← h]; ring
    exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hCne) h2
  have h2' : 2 ∣ Q.relIndex E * b := h2dvd.mul_right b
  rw [hAb] at h2'
  exact hodd' h2'

/-- A normal nilpotent subgroup lies in the Fitting subgroup. -/
theorem le_fitting_of_normal_nilpotent {X : Type*} [Group X] {N : Subgroup X} [N.Normal]
    (hN : Group.IsNilpotent ↥N) : N ≤ Work.GW2.fitting X := by
  have hsup : (sSup {N : Subgroup X | N.Normal ∧ Group.IsNilpotent N}).Normal :=
    Subgroup.sSup_normal _ (fun H hH => hH.1)
  have hfit : Work.GW2.fitting X =
      sSup {N : Subgroup X | N.Normal ∧ Group.IsNilpotent N} :=
    Subgroup.normalCore_eq_self _
  rw [hfit]
  exact le_sSup ⟨inferInstance, hN⟩

/-- **The centre of a normal subgroup of a `π = {3}`-Fitting group is odd.**  Let `E ⊴ M` in a
finite group `G`, and suppose that every prime divisor of `|F(M)|` is `3`.  Then `|Z(E)|` is odd.

`Z(E)` (as a subgroup of `M`) is abelian, hence nilpotent, and normal in `M` (the centre is
characteristic in `E ⊴ M`), so `Z(E) ≤ F(M)`; therefore all prime divisors of `|Z(E)|` divide
`|F(M)|`, hence are `3`, and `2 ∤ |Z(E)|`. -/
theorem odd_card_center_of_normal (M E : Subgroup G) (hEM : E ≤ M)
    (hEsub : M ≤ Subgroup.normalizer (E : Set G))
    (hpi : ∀ p ∈ (Nat.card ↥(Work.GW2.fittingIn M)).primeFactors, p = 3) :
    Odd (Nat.card ↥(Subgroup.center ↥E)) := by
  set N : Subgroup G := (Subgroup.center ↥E).map E.subtype with hN
  have hNleM : N ≤ M := (Subgroup.map_subtype_le (Subgroup.center ↥E)).trans hEM
  have hnormiff := Subgroup.le_normalizer_iff.mp hEsub
  -- `N = Z(E)` is normal in `M`: conjugate a central element of `E` by an element of `M`
  have hconj_mem : ∀ h ∈ N, ∀ k ∈ M, k * h * k⁻¹ ∈ N := by
    intro h hh k hk
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hh
    have hyc : ∀ e ∈ E, (y : G) * e = e * (y : G) := fun e he => by
      have h1 := Subtype.ext_iff.mp (Subgroup.mem_center_iff.mp hy ⟨e, he⟩)
      simpa using h1.symm
    have hconjE : k * (y : G) * k⁻¹ ∈ E := hnormiff k hk (y : G) y.2
    refine Subgroup.mem_map.mpr ⟨⟨k * (y : G) * k⁻¹, hconjE⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    have hk1 : k⁻¹ * (g : G) * k ∈ E := by
      have hh1 := hnormiff k⁻¹ (M.inv_mem hk) (g : G) g.2
      simpa using hh1
    have key : (k * (y : G) * k⁻¹) * (g : G) = (g : G) * (k * (y : G) * k⁻¹) := by
      calc (k * (y : G) * k⁻¹) * (g : G)
          = k * ((y : G) * (k⁻¹ * (g : G) * k)) * k⁻¹ := by group
        _ = k * ((k⁻¹ * (g : G) * k) * (y : G)) * k⁻¹ := by rw [hyc _ hk1]
        _ = (g : G) * (k * (y : G) * k⁻¹) := by group
    exact Subtype.ext key.symm
  have hNnorm : (N.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff hNleM).mpr (fun h k hh hk => hconj_mem h hh k hk)
  haveI hNnormI := hNnorm
  -- `N` is abelian, hence nilpotent
  have hiso : ↥(N.subgroupOf M) ≃* ↥(Subgroup.center ↥E) :=
    (Subgroup.subgroupOfEquivOfLe hNleM).trans
      (Subgroup.equivMapOfInjective (Subgroup.center ↥E) E.subtype
        (Subgroup.subtype_injective E)).symm
  haveI hcomm : IsMulCommutative ↥(N.subgroupOf M) :=
    ⟨⟨fun x y => hiso.injective (by
      show hiso (x * y) = hiso (y * x)
      rw [map_mul, map_mul]
      exact IsMulCommutative.is_comm.comm (hiso x) (hiso y))⟩⟩
  haveI hnil : Group.IsNilpotent ↥(N.subgroupOf M) := inferInstance
  -- hence `N ≤ F(M)`
  have hle : N.subgroupOf M ≤ Work.GW2.fitting ↥M := le_fitting_of_normal_nilpotent hnil
  have hle2 : N ≤ Work.GW2.fittingIn M := by
    have h1 := Subgroup.map_mono (f := M.subtype) hle
    rwa [Subgroup.map_subgroupOf_eq_of_le hNleM] at h1
  have hdvd : Nat.card ↥(Subgroup.center ↥E) ∣ Nat.card ↥(Work.GW2.fittingIn M) := by
    rw [show Nat.card ↥(Subgroup.center ↥E) = Nat.card ↥N from
      (Subgroup.card_map_of_injective (Subgroup.subtype_injective E)).symm]
    exact Subgroup.card_dvd_of_le hle2
  -- all prime divisors of `|Z(E)|` are `3`
  rw [← Nat.not_even_iff_odd]
  intro heven
  have h2dvd : 2 ∣ Nat.card ↥(Subgroup.center ↥E) := even_iff_two_dvd.mp heven
  have hmem : 2 ∈ (Nat.card ↥(Work.GW2.fittingIn M)).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, h2dvd.trans hdvd, by
      haveI : Nonempty ↥(Work.GW2.fittingIn M) := ⟨⟨1, (Work.GW2.fittingIn M).one_mem⟩⟩
      exact Nat.card_pos.ne'⟩
  exact absurd (hpi 2 hmem) (by norm_num)

/-- Elementary `2`-adic arithmetic for the final count: if `B = A · 2520 = c · 2^k` with `A` and
`c` odd (and nonzero), then `k = 3`. -/
theorem pow_two_eq_eight_of_factorization {B A c k : ℕ} (hA : A ≠ 0) (hc : c ≠ 0)
    (h1 : B = A * 2520) (hAodd : Odd A) (h2 : B = c * 2 ^ k) (hcodd : Odd c) : 2 ^ k = 8 := by
  have hA2 : A.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd
    (fun h => (Nat.not_even_iff_odd.mpr hAodd) (even_iff_two_dvd.mpr h))
  have hc2 : c.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd
    (fun h => (Nat.not_even_iff_odd.mpr hcodd) (even_iff_two_dvd.mpr h))
  have hpow : ∀ j : ℕ, ((2 : ℕ) ^ j).factorization 2 = j := by
    intro j
    rw [Nat.factorization_pow]
    simp [Nat.Prime.factorization_self Nat.prime_two]
  have h2520 : (2520 : ℕ).factorization 2 = 3 := by
    have hd : (2520 : ℕ) = 2 ^ 3 * 315 := by norm_num
    rw [hd, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      hpow 3, Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]
  have h3 : B.factorization 2 = 3 := by
    rw [h1, Nat.factorization_mul hA (by norm_num), Finsupp.add_apply, hA2, h2520, zero_add]
  have hk3 : B.factorization 2 = k := by
    rw [h2, Nat.factorization_mul hc (by positivity), Finsupp.add_apply, hc2, hpow k, zero_add]
  rw [← hk3, h3]
  norm_num

/-! ## The lemma -/

theorem A7Vsylow (G : Type) [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    (C : Work.GW2.Case2Ctx6 B) (h : Work.GW2.Hyp9 G B C)
    (hA : Work.GW2.IsA7Case C.D) (hf : Work.GW2.A7Facts1 C.D) :
    Nat.card ↥((B.S : Subgroup G) ⊓ Work.GW2.layerIn C.D.M : Subgroup G) = 8 := by
  obtain ⟨hbc, hcase2, hplus, hseven, height⟩ := h
  obtain ⟨hKeq, hFeq, hK0K, hpi⟩ := hf
  set M : Subgroup G := C.D.M with hM
  set E : Subgroup G := Work.GW2.layerIn M with hE
  have hEM : E ≤ M := by rw [hE, hM]; exact Work.CORE4.layerIn_le C.D.M
  have hEsub : M ≤ Subgroup.normalizer (E : Set G) := by
    rw [hE, hM]; exact Work.CORE4.layerIn_le_normalizer C.D.M
  set P : Subgroup G := (B.S : Subgroup G) ⊓ M with hP
  set Q : Subgroup G := (B.S : Subgroup G) ⊓ E with hQ
  have hQE : Q ≤ E := by rw [hQ]; exact inf_le_right
  -- §4 (1)–(2): `S ∩ M ∈ Syl₂(M)`
  have hoddPM : ¬ 2 ∣ P.relIndex M := by rw [hP, hM]; exact hplus.1
  -- hence `Q = S ∩ E` is a Sylow `2`-subgroup of `E`
  have hoddQE : ¬ 2 ∣ Q.relIndex E :=
    not_two_dvd_relIndex_inf_of_normal M E (B.S : Subgroup G) hEM hEsub hoddPM
  -- `π(F(M)) = {3}`
  have hpiF : ∀ p ∈ (Nat.card ↥(Work.GW2.fittingIn M)).primeFactors, p = 3 := by
    have hsub : ∀ q ∈ (Nat.card ↥(Work.GW2.fittingIn M)).primeFactors, q ∈ B.piFU := by
      rw [hM]; exact hseven.2.2.2.2.1
    intro p hp
    have h2 : p ∈ B.piFU := hsub p hp
    have h3 : p ∈ ({3} : Set ℕ) := hpi ▸ h2
    simpa using h3
  -- `Z(E)` has odd order
  have hZodd : Odd (Nat.card ↥(Subgroup.center ↥E)) :=
    odd_card_center_of_normal M E hEM hEsub hpiF
  -- `E/Z(E) ≅ A₇`, so `|E/Z(E)| = 2520`
  have h2520 : Nat.card (↥E ⧸ Subgroup.center ↥E) = 2520 := by
    have hA' : Nonempty ((↥E ⧸ Subgroup.center ↥E) ≃* alternatingGroup (Fin 7)) := by
      rw [hE, hM]; exact hA
    obtain ⟨eiso⟩ := hA'
    rw [Nat.card_congr eiso.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.card_eq_fintype_card]
  -- `|E| = |Z(E)| · 2520`
  have hEcard : Nat.card ↥E =
      Nat.card ↥(Subgroup.center ↥E) * 2520 := by
    have h1 : Nat.card ↥E = Nat.card ↥(Subgroup.center ↥E) * (Subgroup.center ↥E).index :=
      (Subgroup.card_mul_index _).symm
    rw [h1, Subgroup.index_eq_card, h2520]
  -- `|E| = |E : Q| · |Q|`, with `|E : Q|` odd
  have hQp : IsPGroup 2 ↥Q :=
    IsPGroup.to_le (B.S).isPGroup' (by rw [hQ]; exact inf_le_left)
  obtain ⟨k, hk⟩ := hQp.exists_card_eq
  have hEcard2 : Nat.card ↥E = Q.relIndex E * Nat.card ↥Q := by
    have h1 := Subgroup.relIndex_mul_card Q E
    rw [inf_eq_left.mpr hQE] at h1
    exact h1.symm
  have hQne : Nat.card ↥Q ≠ 0 := by
    haveI : Nonempty ↥Q := ⟨⟨1, Q.one_mem⟩⟩
    exact Nat.card_pos.ne'
  have hZne : Nat.card ↥(Subgroup.center ↥E) ≠ 0 := by
    haveI : Nonempty ↥(Subgroup.center ↥E) := ⟨⟨1, Subgroup.one_mem _⟩⟩
    exact Nat.card_pos.ne'
  have hEne : Nat.card ↥E ≠ 0 := by
    haveI : Nonempty ↥E := ⟨⟨1, E.one_mem⟩⟩
    exact Nat.card_pos.ne'
  have hrelne : Q.relIndex E ≠ 0 := by
    intro h0
    have h1 := Subgroup.relIndex_mul_card Q E
    rw [inf_eq_left.mpr hQE, h0, zero_mul] at h1
    exact hEne h1.symm
  have hEcard2' : Nat.card ↥E = Q.relIndex E * 2 ^ k := by rw [hEcard2, hk]
  have hpow : 2 ^ k = 8 :=
    pow_two_eq_eight_of_factorization hZne hrelne hEcard hZodd hEcard2'
      (Nat.not_even_iff_odd.mp (fun h => hoddQE (even_iff_two_dvd.mp h)))
  rw [hk, hpow]

end Work.CORE4
