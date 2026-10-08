import Mathlib
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.sec3_lemma2
import Submission.Work.ThreePoints.app2_6_uniform
import Submission.Work.ThreePoints.Sec2
import Submission.Work.ThreePoints.exists_involution_conj_of_odd_orderOf_mul
import Submission.Work.ThreePoints.involutions_conj_of_stronglyEmbedded
import Submission.Work.DoubleTransitivity.App2.app2_2
import Submission.Work.BrauerSuzuki.Group.isConj_of_orderOf_eq_two
import Submission.Work.BrauerSuzuki.Group.uniqueInvolution_of_pgroup
import Submission.Work.BrauerSuzuki.OddCore.oddCard_oddCore
import Submission.Work.Coprime.lt_inf_normalizer_of_lt

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open LeanEval.GroupTheory.Defs

open scoped Pointwise

namespace Work.ThreePoints

open Submission.Blueprint

/-! ### The involution exchanging two distinct points of `Ω` -/

/-- Two distinct points of `Ω = G ⧸ K` (with `K` strongly embedded) are exchanged by an
involution of `G`: take involutions fixing each of them, whose (unique) fixed points differ,
whence they are conjugate by an involution of the dihedral group they generate (Ch. I §2
Prop. 1 (a)). -/
theorem exists_involution_smul_eq_of_ne {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hK : IsStronglyEmbedded K) {ω₁ ω₂ : G ⧸ K} (hne : ω₁ ≠ ω₂) :
    ∃ u : G, orderOf u = 2 ∧ u • ω₁ = ω₂ := by
  classical
  obtain ⟨t, ht2, htfix⟩ := exists_involution_smul_eq_self hK ω₁
  obtain ⟨s, hs2, hsfix⟩ := exists_involution_smul_eq_self hK ω₂
  obtain ⟨a, _hafix, hauniq⟩ := existsUnique_fixedPts_of_orderOf_eq_two hK ht2
  obtain ⟨b, _hbfix, hbuniq⟩ := existsUnique_fixedPts_of_orderOf_eq_two hK hs2
  have hω₁a : ω₁ = a := hauniq ω₁ htfix
  have hω₂b : ω₂ = b := hbuniq ω₂ hsfix
  have hsep : ∀ ω : G ⧸ K, t • ω = ω → s • ω ≠ ω := by
    intro ω hω hω'
    exact hne (hω₁a.trans ((hauniq ω hω).symm.trans ((hbuniq ω hω').trans hω₂b.symm)))
  obtain ⟨u, hu2, hconj, -⟩ :=
    exists_involution_conj_of_odd_orderOf_mul ht2 hs2 (odd_orderOf_mul hK ht2 hs2 hsep)
  refine ⟨u, hu2, ?_⟩
  have hsm : s • (u • ω₁) = u • ω₁ := by
    rw [← hconj]
    simp only [mul_smul, inv_smul_smul, htfix]
  rw [hbuniq (u • ω₁) hsm]
  exact hω₂b.symm

/-! ### Sylow conjugacy in a subgroup -/

/-- **Sylow conjugacy.** Two `p`-Sylow subgroups `Q`, `R` of a subgroup `D ≤ G` are conjugate
by an element of `D`. -/
theorem exists_conj_of_isSylowSubgroupOf {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {D Q R : Subgroup G} (hQD : Q ≤ D) (hQg : IsPGroup p Q) (hQi : ¬ p ∣ (Q.subgroupOf D).index)
    (hRD : R ≤ D) (hRg : IsPGroup p R) (hRi : ¬ p ∣ (R.subgroupOf D).index) :
    ∃ d ∈ D, conj d Q = R := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hQg' : IsPGroup p ↥(Q.subgroupOf D) :=
    hQg.comap_of_injective D.subtype Subtype.coe_injective
  have hRg' : IsPGroup p ↥(R.subgroupOf D) :=
    hRg.comap_of_injective D.subtype Subtype.coe_injective
  haveI : MulAction.IsPretransitive (↥D) (Sylow p ↥D) :=
    Sylow.isPretransitive_of_finite (p := p) (G := ↥D)
  obtain ⟨c, hc⟩ := (Sylow.isPretransitive_of_finite (p := p) (G := ↥D)).exists_smul_eq
    (hQg'.toSylow hQi) (hRg'.toSylow hRi)
  have hsub : Subgroup.map (MulAut.conj c).toMonoidHom (Q.subgroupOf D) = R.subgroupOf D := by
    have h1 : ((c • (hQg'.toSylow hQi) : Sylow p ↥D) : Subgroup ↥D) = R.subgroupOf D := by
      rw [hc]
      rfl
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def,
      MulDistribMulAction.toMonoidEnd_apply] at h1
    exact h1
  refine ⟨(c : G), c.2, ?_⟩
  have hmap := congrArg (Subgroup.map D.subtype) hsub
  rw [Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hRD] at hmap
  rw [show D.subtype.comp (MulAut.conj c).toMonoidHom
      = (MulAut.conj (c : G)).toMonoidHom.comp D.subtype from by
    ext y
    simp [MulAut.conj_apply]] at hmap
  rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hQD] at hmap
  exact hmap

/-- Conjugating a `p`-Sylow subgroup of `D` by an element normalising `D` does not change its
index in `D`. -/
theorem index_subgroupOf_conj {G : Type} [Group G] [Finite G] {D P : Subgroup G} {u : G}
    (hD : conj u D = D) (hP : P ≤ D) :
    ((conj u P).subgroupOf D).index = (P.subgroupOf D).index := by
  have hRle : conj u P ≤ D := by
    rw [← hD]; exact Subgroup.map_mono hP
  have hc1 : Nat.card ↥((conj u P).subgroupOf D) = Nat.card ↥(conj u P) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRle).toEquiv
  have hc2 : Nat.card ↥(conj u P) = Nat.card ↥P :=
    Subgroup.card_map_of_injective (MulAut.conj u).injective
  have hc3 : Nat.card ↥(P.subgroupOf D) = Nat.card ↥P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP).toEquiv
  have h1 := Subgroup.card_mul_index ((conj u P).subgroupOf D)
  have h2 := Subgroup.card_mul_index (P.subgroupOf D)
  rw [hc1, hc2] at h1
  rw [hc3] at h2
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)

/-- Being a `p`-Sylow subgroup of `D` only depends on the order of `D` (for a fixed `p`-subgroup
`P ≤ D`). -/
theorem isSylowSubgroupOf_of_card_eq {G : Type} [Group G] [Finite G] {p : ℕ}
    {P D D' : Subgroup G} (h : Work.DoubleTransitivity.IsSylowSubgroupOf p P D') (hP : P ≤ D)
    (hcard : Nat.card ↥D = Nat.card ↥D') : Work.DoubleTransitivity.IsSylowSubgroupOf p P D := by
  refine ⟨hP, h.2.1, ?_⟩
  have e1 : Nat.card ↥(P.subgroupOf D) = Nat.card ↥P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP).toEquiv
  have e2 : Nat.card ↥(P.subgroupOf D') = Nat.card ↥P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.1).toEquiv
  have h1 := Subgroup.card_mul_index (P.subgroupOf D)
  have h2 := Subgroup.card_mul_index (P.subgroupOf D')
  rw [e1] at h1
  rw [e2, ← hcard] at h2
  have hin : (P.subgroupOf D).index = (P.subgroupOf D').index :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)
  rw [hin]; exact h.2.2

/-- If a `p`-subgroup `P` of `D` is not a `p`-Sylow subgroup of `D`, then some `p`-subgroup of
`D` strictly contains it. -/
theorem exists_pSubgroup_lt_of_dvd_index {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {P D : Subgroup G} (hPp : IsPGroup p P) (hPD : P ≤ D) (h : p ∣ (P.subgroupOf D).index) :
    ∃ Q : Subgroup G, Q ≤ D ∧ IsPGroup p Q ∧ P < Q := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨Qd, hQd⟩ := IsPGroup.exists_le_sylow
    (hPp.comap_of_injective D.subtype Subtype.coe_injective :
      IsPGroup p ↥(P.subgroupOf D))
  have hQdne : (Qd : Subgroup ↥D) ≠ P.subgroupOf D := by
    intro heq
    have h2 := Sylow.not_dvd_index Qd
    rw [heq] at h2
    exact h2 h
  refine ⟨(Qd : Subgroup ↥D).map D.subtype, Subgroup.map_subtype_le _,
    Qd.isPGroup'.map D.subtype, ?_⟩
  have hle : P ≤ (Qd : Subgroup ↥D).map D.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hPD]
    exact Subgroup.map_mono hQd
  refine lt_of_le_of_ne hle fun heq => hQdne ?_
  have h2 : (P.subgroupOf D).map D.subtype = (Qd : Subgroup ↥D).map D.subtype :=
    (Subgroup.map_subgroupOf_eq_of_le hPD).trans heq
  have h3 := congrArg (Subgroup.comap D.subtype) h2
  rw [Subgroup.comap_map_eq_self_of_injective Subtype.coe_injective,
      Subgroup.comap_map_eq_self_of_injective Subtype.coe_injective] at h3
  exact h3.symm

/-- **Peterfalvi I Ch. I §3 Lemma 1.** Every `p`-Sylow subgroup of a two-point stabiliser
`Stab ω₁ ⊓ Stab ω₂` (`ω₁ ≠ ω₂`) is normalised by an involution exchanging `ω₁` and `ω₂`. -/
theorem sec3_lemma1 {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hK : IsStronglyEmbedded K) {p : ℕ} (hp : p.Prime)
    {ω₁ ω₂ : G ⧸ K} (hne : ω₁ ≠ ω₂) {P : Subgroup G}
    (hP : Work.DoubleTransitivity.IsSylowSubgroupOf p P
      (MulAction.stabilizer G ω₁ ⊓ MulAction.stabilizer G ω₂)) :
    ∃ u : G, orderOf u = 2 ∧ conj u P = P ∧ u • ω₁ = ω₂ := by
  classical
  obtain ⟨g₁, rfl⟩ := QuotientGroup.mk_surjective ω₁
  obtain ⟨g₂, rfl⟩ := QuotientGroup.mk_surjective ω₂
  set D : Subgroup G := MulAction.stabilizer G (g₁ : G ⧸ K) ⊓
    MulAction.stabilizer G (g₂ : G ⧸ K) with hDdef
  have hD1 : D ≤ MulAction.stabilizer G (g₁ : G ⧸ K) := by rw [hDdef]; exact inf_le_left
  have hD2 : D ≤ MulAction.stabilizer G (g₂ : G ⧸ K) := by rw [hDdef]; exact inf_le_right
  have hPle : P ≤ D := hP.1
  have hDodd : Odd (Nat.card D) := by
    have hne' : conj g₁ K ≠ conj g₂ K := fun h => hne (mk_eq_of_conj_eq hK h)
    have heq : D = conj g₁ K ⊓ conj g₂ K := by rw [hDdef, stabilizer_mk, stabilizer_mk]
    rw [heq]; exact card_inf_conj_odd hK hne'
  obtain ⟨u₀, hu₀2, hu₀⟩ := exists_involution_smul_eq_of_ne hK hne
  have hc1 : conj u₀ (MulAction.stabilizer G (g₁ : G ⧸ K)) =
      MulAction.stabilizer G (g₂ : G ⧸ K) := by
    rw [← Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj u₀ (g₁ : G ⧸ K), hu₀]
  have hc2 : conj u₀ (MulAction.stabilizer G (g₂ : G ⧸ K)) =
      MulAction.stabilizer G (g₁ : G ⧸ K) := by
    rw [← hc1, ← conj_mul, mul_self_eq_one_of_orderOf_eq_two hu₀2, conj_one]
  have hDinv : conj u₀ D = D := by
    rw [hDdef, conj_inf, hc1, hc2, inf_comm]
  have hconjD : ∀ x : G, x ∈ D → u₀ * x * u₀⁻¹ ∈ D := by
    intro x hx
    have h3 : (MulAut.conj u₀).toMonoidHom x ∈ conj u₀ D := Subgroup.mem_map_of_mem _ hx
    rw [hDinv] at h3
    simpa [mulAut_conj_apply] using h3
  have hu₀D : u₀ ∉ D := by
    intro h
    exact hne ((MulAction.mem_stabilizer_iff.mp (hD1 h)).symm.trans hu₀)
  have hRle : conj u₀ P ≤ D := by
    intro x hx
    have hx' : u₀⁻¹ * x * u₀ ∈ D := hPle (mem_conj_iff.mp hx)
    have h2 : u₀ * (u₀⁻¹ * x * u₀) * u₀⁻¹ ∈ D := hconjD _ hx'
    rwa [show u₀ * (u₀⁻¹ * x * u₀) * u₀⁻¹ = x from by group] at h2
  have hRg : IsPGroup p (conj u₀ P) := hP.2.1.map _
  have hRi : ¬ p ∣ ((conj u₀ P).subgroupOf D).index := by
    rw [index_subgroupOf_conj hDinv hPle]; exact hP.2.2
  obtain ⟨d, hdD, hd⟩ :=
    exists_conj_of_isSylowSubgroupOf hp hPle hP.2.1 hP.2.2 hRle hRg hRi
  -- `v = d⁻¹ u₀` normalises `P`, and `v * v ∈ D`
  set v : G := d⁻¹ * u₀ with hvdef
  have hvP : conj v P = P := by
    rw [hvdef, conj_mul, ← hd, ← conj_mul, inv_mul_cancel, conj_one]
  have hu₀inv : u₀⁻¹ = u₀ := inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_orderOf_eq_two hu₀2)
  have h1' : u₀ * (d : G)⁻¹ * u₀ ∈ D := by
    have h2 : u₀ * (d : G)⁻¹ * u₀⁻¹ ∈ D := hconjD _ (D.inv_mem hdD)
    simpa [hu₀inv] using h2
  have hv2D : v * v ∈ D := by
    have h : v * v = d⁻¹ * (u₀ * (d : G)⁻¹ * u₀) := by rw [hvdef]; group
    rw [h]; exact D.mul_mem (D.inv_mem hdD) h1'
  have hvD : v ∉ D := by
    intro hv
    have h : u₀ = d * v := by rw [hvdef]; group
    exact hu₀D (h ▸ D.mul_mem hdD hv)
  -- `v ∉ D` and `v * v ∈ D` (odd order): `v` has even order, `v ^ (orderOf (v*v))` is an
  -- involution, and it is an odd power of `v`
  have hv2odd : Odd (orderOf (v * v)) := by
    have hdvd : orderOf (v * v) ∣ Nat.card D := by
      have h := orderOf_dvd_natCard (⟨v * v, hv2D⟩ : ↥D)
      rwa [Subgroup.orderOf_mk] at h
    exact Odd.of_dvd hdvd hDodd
  have hneven : Even (orderOf v) := by
    by_contra h
    have hodd : Odd (orderOf v) := Nat.not_even_iff_odd.mp h
    obtain ⟨k, hk⟩ := hodd
    have hpow : (v * v) ^ (k + 1) = v := by
      rw [← pow_two, ← pow_mul]
      have : 2 * (k + 1) = orderOf v + 1 := by rw [hk]; ring
      rw [this, pow_succ, pow_orderOf_eq_one, one_mul]
    have hmem : (v * v) ^ (k + 1) ∈ D := pow_mem hv2D (k + 1)
    exact hvD (hpow ▸ hmem)
  have h2m : 2 * orderOf (v * v) = orderOf v := by
    have h1 : orderOf (v * v) = orderOf (v ^ 2) := by rw [pow_two]
    rw [h1, orderOf_pow]
    have hg : Nat.gcd (orderOf v) 2 = 2 := Nat.gcd_eq_right (even_iff_two_dvd.mp hneven)
    rw [hg]
    exact Nat.two_mul_div_two_of_even hneven
  obtain ⟨j, hj⟩ := hv2odd
  have hvsm1 : v • (g₁ : G ⧸ K) = (g₂ : G ⧸ K) := by
    rw [hvdef, mul_smul, hu₀]
    exact MulAction.mem_stabilizer_iff.mp (hD2 (D.inv_mem hdD))
  refine ⟨v ^ (orderOf (v * v)), ?_, ?_, ?_⟩
  · have hmpos : 0 < orderOf (v * v) := by
      rcases Nat.eq_zero_or_pos (orderOf (v * v)) with h | h
      · exfalso
        have hv0 : orderOf v = 0 := by omega
        have hpos : 0 < orderOf v :=
          Nat.pos_of_dvd_of_pos (orderOf_dvd_natCard v) Nat.card_pos
        omega
      · exact h
    have hsq : (v ^ orderOf (v * v)) * (v ^ orderOf (v * v)) = 1 := by
      rw [← pow_two, ← pow_mul, show orderOf (v * v) * 2 = orderOf v by omega,
        pow_orderOf_eq_one]
    exact orderOf_eq_two_of (by
      intro h
      have hdvd : orderOf v ∣ orderOf (v * v) := orderOf_dvd_iff_pow_eq_one.mpr h
      have hle : orderOf v ≤ orderOf (v * v) := Nat.le_of_dvd hmpos hdvd
      omega) hsq
  · have hvN : v ∈ Subgroup.normalizer (P : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hvP
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (pow_mem hvN _)
  · rw [hj]
    have hdecomp : v ^ (2 * j + 1) = (v * v) ^ j * v := by
      have h2j : v ^ (2 * j) = (v * v) ^ j := by rw [pow_mul, pow_two]
      rw [pow_succ, h2j]
    calc v ^ (2 * j + 1) • (g₁ : G ⧸ K)
        = ((v * v) ^ j * v) • (g₁ : G ⧸ K) := by rw [hdecomp]
      _ = (v * v) ^ j • (v • (g₁ : G ⧸ K)) := by rw [mul_smul]
      _ = (v * v) ^ j • (g₂ : G ⧸ K) := by rw [hvsm1]
      _ = (g₂ : G ⧸ K) :=
          MulAction.mem_stabilizer_iff.mp (hD2 (pow_mem hv2D j))

/-- If `y ^ 2` lies in a subgroup `H` of odd order and `y ∉ H`, then some odd power of `y` is an
involution. -/
theorem exists_odd_pow_involution_of_sq_mem {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : Odd (Nat.card H)) {y : G} (hy : y * y ∈ H) (hyH : y ∉ H) :
    ∃ k : ℕ, Odd k ∧ orderOf (y ^ k) = 2 := by
  have hy2odd : Odd (orderOf (y * y)) := by
    have hdvd : orderOf (y * y) ∣ Nat.card H := by
      have h := orderOf_dvd_natCard (⟨y * y, hy⟩ : ↥H)
      rwa [Subgroup.orderOf_mk] at h
    exact Odd.of_dvd hdvd hH
  have hneven : Even (orderOf y) := by
    by_contra h
    have hodd : Odd (orderOf y) := Nat.not_even_iff_odd.mp h
    obtain ⟨j, hj⟩ := hodd
    have hpow : (y * y) ^ (j + 1) = y := by
      rw [← pow_two, ← pow_mul]
      have : 2 * (j + 1) = orderOf y + 1 := by rw [hj]; ring
      rw [this, pow_succ, pow_orderOf_eq_one, one_mul]
    exact hyH (hpow ▸ pow_mem hy (j + 1))
  have h2m : 2 * orderOf (y * y) = orderOf y := by
    have h1 : orderOf (y * y) = orderOf (y ^ 2) := by rw [pow_two]
    rw [h1, orderOf_pow]
    have hg : Nat.gcd (orderOf y) 2 = 2 := Nat.gcd_eq_right (even_iff_two_dvd.mp hneven)
    rw [hg]
    exact Nat.two_mul_div_two_of_even hneven
  obtain ⟨j, hj⟩ := hy2odd
  have hpos : 0 < orderOf (y * y) := by
    rcases Nat.eq_zero_or_pos (orderOf (y * y)) with h | h
    · exfalso
      have hy0 : orderOf y = 0 := by omega
      have hp : 0 < orderOf y := Nat.pos_of_dvd_of_pos (orderOf_dvd_natCard y) Nat.card_pos
      omega
    · exact h
  refine ⟨orderOf (y * y), ⟨j, hj⟩, orderOf_eq_two_of (fun h => ?_) ?_⟩
  · have hdvd : orderOf y ∣ orderOf (y * y) := orderOf_dvd_iff_pow_eq_one.mpr h
    have hle : orderOf y ≤ orderOf (y * y) := Nat.le_of_dvd hpos hdvd
    omega
  · rw [← pow_two, ← pow_mul, show orderOf (y * y) * 2 = orderOf y by omega,
      pow_orderOf_eq_one]

/-- **Peterfalvi I Ch. I §3 Lemma 3.** Let `P` be maximal among the `p`-subgroups of `G` with at
least three fixed points of `Ω = G ⧸ K`, `M = N_G(P)`, and `ω₀ ≠ ω₂` two points of `Ω_P` lying in
the same `M`-orbit. Then some involution of `M` exchanges `ω₀` and `ω₂`. -/
theorem sec3_lemma3 {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hK : IsStronglyEmbedded K) {p : ℕ} (hp : p.Prime) {P : Subgroup G} (hPp : IsPGroup p P)
    (hPmax : ∀ R : Subgroup G, P ≤ R → IsPGroup p R →
      3 ≤ (Submission.Blueprint.fixedPts K R).ncard → R = P)
    {ω₀ ω₂ : G ⧸ K} (h₀ : ω₀ ∈ Submission.Blueprint.fixedPts K P)
    (h₂ : ω₂ ∈ Submission.Blueprint.fixedPts K P) (hne : ω₀ ≠ ω₂)
    (horbit : ∃ x ∈ Subgroup.normalizer (P : Set G), x • ω₀ = ω₂) :
    ∃ u ∈ Subgroup.normalizer (P : Set G), orderOf u = 2 ∧ u • ω₀ = ω₂ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g₁, rfl⟩ := QuotientGroup.mk_surjective ω₀
  obtain ⟨g₂, rfl⟩ := QuotientGroup.mk_surjective ω₂
  set M : Subgroup G := Subgroup.normalizer (P : Set G) with hMdef
  set D : Subgroup G := MulAction.stabilizer G (g₁ : G ⧸ K) ⊓
    MulAction.stabilizer G (g₂ : G ⧸ K) with hDdef
  have hD1 : D ≤ MulAction.stabilizer G (g₁ : G ⧸ K) := by rw [hDdef]; exact inf_le_left
  have hD2 : D ≤ MulAction.stabilizer G (g₂ : G ⧸ K) := by rw [hDdef]; exact inf_le_right
  have hDodd : Odd (Nat.card D) := by
    have hne' : conj g₁ K ≠ conj g₂ K := fun h => hne (mk_eq_of_conj_eq hK h)
    have heq : D = conj g₁ K ⊓ conj g₂ K := by rw [hDdef, stabilizer_mk, stabilizer_mk]
    rw [heq]; exact card_inf_conj_odd hK hne'
  have hP0 : P ≤ MulAction.stabilizer G (g₁ : G ⧸ K) := mem_fixedPts_iff_le_stabilizer.mp h₀
  have hP2 : P ≤ MulAction.stabilizer G (g₂ : G ⧸ K) := mem_fixedPts_iff_le_stabilizer.mp h₂
  have hPleD : P ≤ D := le_inf hP0 hP2
  by_cases hA : ¬ p ∣ (P.subgroupOf D).index
  · -- `P` is a `p`-Sylow of `D`: Ch. I §3 Lemma 1
    obtain ⟨u, hu2, huP, huω⟩ := sec3_lemma1 hK hp hne ⟨hPleD, hPp, hA⟩
    exact ⟨u, Subgroup.mem_normalizer_iff_map_conj_eq.mpr huP, hu2, huω⟩
  · -- `P` is not a `p`-Sylow of `D`
    obtain ⟨Qd, hQd⟩ := IsPGroup.exists_le_sylow
      (hPp.comap_of_injective D.subtype Subtype.coe_injective)
    have hQdne : (Qd : Subgroup ↥D) ≠ P.subgroupOf D := by
      intro heq
      have h := Sylow.not_dvd_index Qd
      rw [heq] at h
      exact hA h
    have hPltQ : P < (Qd : Subgroup ↥D).map D.subtype := by
      have hle : P ≤ (Qd : Subgroup ↥D).map D.subtype := by
        rw [← Subgroup.map_subgroupOf_eq_of_le hPleD]
        exact Subgroup.map_mono hQd
      refine lt_of_le_of_ne hle fun heq => hQdne ?_
      have h2 : (P.subgroupOf D).map D.subtype = (Qd : Subgroup ↥D).map D.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hPleD).trans heq
      have h3 := congrArg (Subgroup.comap D.subtype) h2
      rw [Subgroup.comap_map_eq_self_of_injective Subtype.coe_injective,
          Subgroup.comap_map_eq_self_of_injective Subtype.coe_injective] at h3
      exact h3.symm
    have hQg : IsPGroup p ((Qd : Subgroup ↥D).map D.subtype) := Qd.isPGroup'.map D.subtype
    set R0 : Subgroup G :=
      (Qd : Subgroup ↥D).map D.subtype ⊓ Subgroup.normalizer (P : Set G) with hR0def
    have hR0lt : P < R0 := Work.Coprime.lt_inf_normalizer_of_lt hQg hPltQ
    have hR0leD : R0 ≤ D := le_trans inf_le_left (Subgroup.map_subtype_le _)
    have hR0leM : R0 ≤ M := by rw [hR0def, hMdef]; exact inf_le_right
    have hR0g : IsPGroup p R0 := hQg.to_inf_left
    -- the fixed points of `R0` are exactly the two given ones
    have hfixR : Submission.Blueprint.fixedPts K R0 = ({(g₁ : G ⧸ K), (g₂ : G ⧸ K)} : Set (G ⧸ K)) := by
      have hsub : ({(g₁ : G ⧸ K), (g₂ : G ⧸ K)} : Set (G ⧸ K)) ⊆ Submission.Blueprint.fixedPts K R0 := by
        intro c hc
        rcases hc with h | h
        · rw [h, mem_fixedPts]
          exact fun r hr => MulAction.mem_stabilizer_iff.mp (hD1 (hR0leD hr))
        · rw [h, mem_fixedPts]
          exact fun r hr => MulAction.mem_stabilizer_iff.mp (hD2 (hR0leD hr))
      have hnot3 : ¬ 3 ≤ (Submission.Blueprint.fixedPts K R0).ncard := by
        intro h3
        exact hR0lt.ne (hPmax R0 hR0lt.le hR0g h3).symm
      have hle2 : (Submission.Blueprint.fixedPts K R0).ncard ≤ 2 := by omega
      refine (Set.eq_of_subset_of_ncard_le hsub ?_).symm
      rw [Set.ncard_pair hne]
      exact hle2
    -- apply App. II (2) to `M` acting on `Ω`
    letI : MulAction ↥M (G ⧸ K) := MulAction.compHom (G ⧸ K) M.subtype
    have hR0sub : IsPGroup p (R0.subgroupOf M) :=
      hR0g.comap_of_injective M.subtype Subtype.coe_injective
    have hfixM : Work.DoubleTransitivity.fixedBySub (X := ↥M) (E := G ⧸ K) (R0.subgroupOf M)
        = ({(g₁ : G ⧸ K), (g₂ : G ⧸ K)} : Set (G ⧸ K)) := by
      have hEq : Work.DoubleTransitivity.fixedBySub (X := ↥M) (E := G ⧸ K) (R0.subgroupOf M)
          = Submission.Blueprint.fixedPts K R0 := by
        ext c
        rw [Work.DoubleTransitivity.mem_fixedBySub, mem_fixedPts]
        constructor
        · intro hc r hr
          exact hc ⟨r, hR0leM hr⟩ (Subgroup.mem_subgroupOf.mpr hr)
        · intro hc m hm
          exact hc (m : G) hm
      rw [hEq, hfixR]
    have horbit' : ∃ x : ↥M, x • (g₁ : G ⧸ K) = (g₂ : G ⧸ K) := by
      obtain ⟨x, hxM, hxω⟩ := horbit
      exact ⟨⟨x, hMdef ▸ hxM⟩, hxω⟩
    obtain ⟨y, hy1, hy2⟩ := Work.DoubleTransitivity.App2.app2_2 (X := ↥M) (E := G ⧸ K)
      (p := p) hne ⟨R0.subgroupOf M, hR0sub, hfixM⟩ horbit'
    have hyG1 : (y : G) • (g₁ : G ⧸ K) = (g₂ : G ⧸ K) := hy1
    have hyG2 : (y : G) • (g₂ : G ⧸ K) = (g₁ : G ⧸ K) := hy2
    have hy2D : (y : G) * (y : G) ∈ D := by
      rw [hDdef]
      refine ⟨?_, ?_⟩
      · exact MulAction.mem_stabilizer_iff.mpr (by rw [mul_smul, hyG1, hyG2])
      · exact MulAction.mem_stabilizer_iff.mpr (by rw [mul_smul, hyG2, hyG1])
    have hyD : (y : G) ∉ D := by
      intro h
      exact hne ((MulAction.mem_stabilizer_iff.mp (hD1 h)).symm.trans hyG1)
    obtain ⟨k, hkodd, hk2⟩ := exists_odd_pow_involution_of_sq_mem hDodd hy2D hyD
    refine ⟨(y : G) ^ k, ?_, hk2, ?_⟩
    · simpa using ((y : ↥M) ^ k).2
    · obtain ⟨j, hj⟩ := hkodd
      have hdecomp : (y : G) ^ (2 * j + 1) = ((y : G) * (y : G)) ^ j * (y : G) := by
        have h2j : (y : G) ^ (2 * j) = ((y : G) * (y : G)) ^ j := by rw [pow_mul, pow_two]
        rw [pow_succ, h2j]
      calc (y : G) ^ k • (g₁ : G ⧸ K) = (y : G) ^ (2 * j + 1) • (g₁ : G ⧸ K) := by rw [hj]
        _ = (((y : G) * (y : G)) ^ j * (y : G)) • (g₁ : G ⧸ K) := by rw [hdecomp]
        _ = ((y : G) * (y : G)) ^ j • ((y : G) • (g₁ : G ⧸ K)) := by rw [mul_smul]
        _ = ((y : G) * (y : G)) ^ j • (g₂ : G ⧸ K) := by rw [hyG1]
        _ = (g₂ : G ⧸ K) := MulAction.mem_stabilizer_iff.mp (hD2 (pow_mem hy2D j))

/-- **Peterfalvi I, Appendix II (6)** (transitivity form): let `X` be a finite group acting
`2`-transitively on a finite set `E`, `a ∈ E`, and `P ≤ X_a` a `p`-subgroup which is maximal
among the `p`-subgroups of `X_a` fixing at least three points of `E`. Then (i) `P` is maximal
among the `p`-subgroups of `X` fixing at least three points, and (ii) the normaliser `N_X(P)`
acts transitively on the fixed-point set `E_P`.

Source proof (p. 204): if `P` is a `p`-Sylow of the two-point stabiliser `X_a ⊓ X_b`
(`b ∈ E_P`, `b ≠ a`), App. II (5) (`app2_5`) gives `2`-transitivity of `N_X(P)` on `E_P`.
Otherwise, for `c ∈ E_P \ {a}` a `p`-Sylow of `N_X(P) ⊓ X_a ⊓ X_c` strictly contains `P`
(equivalently: `P` is not a `p`-Sylow of `X_a ⊓ X_c`), hence by maximality of `P` in `X_a` it
has exactly the two fixed points `a, c`; and for distinct `c, d ∈ E_P \ {a}`, a `p`-Sylow of
`N_X(P) ⊓ X_c ⊓ X_d` strictly contains `P` yet is not contained in `X_a`, so `N_X(P)` does not
fix `a`. App. II (3) (`app2_3`), applied to the action of `N_X(P)` on `E_P`, then gives
`2`-transitivity (hence transitivity). Part (i) follows: if `Q ≥ P` is a `p`-subgroup of `X`
fixing at least three points and `c ∈ E_Q`, transitivity gives `x ∈ N_X(P)` with `x • a = c`, so
`x⁻¹ Q x ≤ X_a` is a `p`-subgroup strictly above `P`, contradicting the maximality of `P` in
`X_a`. -/
theorem app2_6_general {X E : Type} [Group X] [MulAction X E] [Finite X] [Fintype E]
    {p : ℕ} (hp : p.Prime) {a : E}
    (h2 : MulAction.IsMultiplyPretransitive X E 2)
    {P : Subgroup X} (hP : IsPGroup p P) (hPa : P ≤ MulAction.stabilizer X a)
    (hbig : 3 ≤ (Work.DoubleTransitivity.fixedBySub P : Set E).ncard)
    (hmax : ∀ Q : Subgroup X, IsPGroup p Q → Q ≤ MulAction.stabilizer X a →
      3 ≤ (Work.DoubleTransitivity.fixedBySub Q : Set E).ncard → P ≤ Q → Q ≤ P) :
    (∀ R : Subgroup X, P ≤ R → IsPGroup p R →
      3 ≤ (Work.DoubleTransitivity.fixedBySub R : Set E).ncard → R = P) ∧
      Work.DoubleTransitivity.IsTransitiveOnSub (Subgroup.normalizer (P : Set X))
        (Work.DoubleTransitivity.fixedBySub P : Set E) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set EP : Set E := Work.DoubleTransitivity.fixedBySub P with hEPdef
  set N : Subgroup X := Subgroup.normalizer (P : Set X) with hNdef
  have haEP : a ∈ EP := hPa
  have hEPbig : 3 ≤ EP.ncard := hbig
  have h2p : ∀ {u v u' v' : E}, u ≠ v → u' ≠ v' → ∃ g : X, g • u = u' ∧ g • v = v' :=
    fun huv huv' => (MulAction.is_two_pretransitive_iff.mp h2) huv huv'
  obtain ⟨b₀, hb₀EP, hb₀ne⟩ := Set.exists_ne_of_one_lt_ncard (by omega : 1 < EP.ncard) a
  -- two distinct points of `EP \ {a}`
  have h2diff : 2 ≤ (EP \ {a}).ncard := by
    have hsub : EP ⊆ insert a (EP \ {a}) := by
      intro x hx
      by_cases h : x = a
      · exact Set.mem_insert_iff.mpr (Or.inl h)
      · exact Set.mem_insert_iff.mpr (Or.inr ⟨hx, h⟩)
    have h1 := Set.ncard_le_ncard hsub
    have h2' := Set.ncard_insert_le a (EP \ {a})
    omega
  obtain ⟨c₀, hc₀, hc₀ne⟩ := Set.exists_ne_of_one_lt_ncard (by omega : 1 < (EP \ {a}).ncard) a
  have hc₀EP : c₀ ∈ EP := hc₀.1
  have hc₀ne_a : c₀ ≠ a := hc₀.2
  have hne2 : ((EP \ {a}) \ {c₀}).Nonempty := by
    rw [← Set.ncard_pos]
    have h1 := Set.ncard_sdiff_singleton_add_one hc₀
    omega
  obtain ⟨d₀, hd₀⟩ := hne2
  have hd₀EP : d₀ ∈ EP := hd₀.1.1
  have hd₀ne_a : d₀ ≠ a := hd₀.1.2
  have hd₀ne_c : d₀ ≠ c₀ := hd₀.2
  -- two-point stabilisers of `EP` all have the same order
  have hcard_stab : ∀ {u v : E}, u ≠ v →
      Nat.card ↥(MulAction.stabilizer X u ⊓ MulAction.stabilizer X v)
        = Nat.card ↥(MulAction.stabilizer X a ⊓ MulAction.stabilizer X b₀) := by
    intro u v huv
    obtain ⟨g, hgu, hgv⟩ := h2p hb₀ne.symm huv
    have hconj : conj g (MulAction.stabilizer X a ⊓ MulAction.stabilizer X b₀)
        = MulAction.stabilizer X u ⊓ MulAction.stabilizer X v := by
      rw [conj_inf, ← Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj g a,
        ← Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj g b₀, hgu, hgv]
    rw [← hconj]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hle_of_mem : ∀ c : E, c ∈ EP → P ≤ MulAction.stabilizer X c :=
    fun c hc x hx => MulAction.mem_stabilizer_iff.mpr
      ((Work.DoubleTransitivity.mem_fixedBySub.mp hc) x hx)
  have hPab : P ≤ MulAction.stabilizer X a ⊓ MulAction.stabilizer X b₀ :=
    fun x hx => ⟨hPa hx, hle_of_mem b₀ hb₀EP hx⟩
  have key : Work.DoubleTransitivity.IsTransitiveOnSub N EP := by
    by_cases hcase1 : Work.DoubleTransitivity.IsSylowSubgroupOf p P
        (MulAction.stabilizer X a ⊓ MulAction.stabilizer X b₀)
    · have ht : Work.DoubleTransitivity.IsTwoTransitiveOnSub N EP :=
        Work.DoubleTransitivity.App2.app2_5 (p := p) hb₀ne.symm h2 hcase1
      exact Work.DoubleTransitivity.IsTwoTransitiveOnSub.isTransitiveOnSub ht
    · -- `P` is not a `p`-Sylow of the two-point stabiliser
      have hcase2 : p ∣ (P.subgroupOf (MulAction.stabilizer X a
          ⊓ MulAction.stabilizer X b₀)).index := by
        by_contra hcon
        exact hcase1 ⟨hPab, hP, hcon⟩
      have hdvd : ∀ {u v : E}, u ∈ EP → v ∈ EP → u ≠ v →
          p ∣ (P.subgroupOf (MulAction.stabilizer X u ⊓ MulAction.stabilizer X v)).index := by
        intro u v hu hv huv
        by_contra hcon
        have hsyl : Work.DoubleTransitivity.IsSylowSubgroupOf p P
            (MulAction.stabilizer X u ⊓ MulAction.stabilizer X v) :=
          ⟨fun x hx => ⟨hle_of_mem u hu hx, hle_of_mem v hv hx⟩, hP, hcon⟩
        exact hcase1 (isSylowSubgroupOf_of_card_eq hsyl hPab (hcard_stab huv).symm)
      have hfix_lt : ∀ R : Subgroup X, R ≤ MulAction.stabilizer X a → IsPGroup p R → P < R →
          (Work.DoubleTransitivity.fixedBySub R : Set E).ncard < 3 := by
        intro R hRa hRg hlt
        by_contra hcon
        exact hlt.ne (le_antisymm hlt.le (hmax R hRg hRa (by omega) hlt.le))
      -- for `c ∈ EP \ {a}`: a `p`-subgroup of `N` with fixed point set `{a, c}`
      have hRc : ∀ c ∈ EP, c ≠ a → ∃ R : Subgroup X, R ≤ N ∧ IsPGroup p R ∧ P < R ∧
          (Work.DoubleTransitivity.fixedBySub R : Set E) = {a, c} := by
        intro c hcEP hca
        have hdac : P ≤ MulAction.stabilizer X a ⊓ MulAction.stabilizer X c :=
          fun x hx => ⟨hPa hx, hle_of_mem c hcEP hx⟩
        obtain ⟨Q₀, hQ₀le, hQ₀g, hQ₀lt⟩ := exists_pSubgroup_lt_of_dvd_index hp hP hdac
          (hdvd haEP hcEP (fun h => hca h.symm))
        have hQ₀a : Q₀ ≤ MulAction.stabilizer X a := le_trans hQ₀le inf_le_left
        have hlt : P < Q₀ ⊓ N := Work.Coprime.lt_inf_normalizer_of_lt hQ₀g hQ₀lt
        refine ⟨Q₀ ⊓ N, by rw [hNdef]; exact inf_le_right, hQ₀g.to_inf_left, hlt, ?_⟩
        have hle_a : Q₀ ⊓ N ≤ MulAction.stabilizer X a := le_trans inf_le_left hQ₀a
        have hlt3 := hfix_lt (Q₀ ⊓ N) hle_a hQ₀g.to_inf_left hlt
        have hsub : ({a, c} : Set E) ⊆ (Work.DoubleTransitivity.fixedBySub (Q₀ ⊓ N) : Set E) := by
          intro x hx
          rcases hx with h | h
          · rw [h, Work.DoubleTransitivity.mem_fixedBySub]
            exact fun m hm => MulAction.mem_stabilizer_iff.mp (hle_a hm)
          · rw [h, Work.DoubleTransitivity.mem_fixedBySub]
            exact fun m hm =>
              MulAction.mem_stabilizer_iff.mp (le_trans inf_le_left (le_trans hQ₀le inf_le_right) hm)
        have h2' : (Work.DoubleTransitivity.fixedBySub (Q₀ ⊓ N) : Set E).ncard ≤
            ({a, c} : Set E).ncard := by
          rw [Set.ncard_pair hca.symm]
          omega
        exact (Set.eq_of_subset_of_ncard_le hsub h2').symm
      -- `N` does not fix `a`
      have hNfix : ∃ n ∈ N, n • a ≠ a := by
        have hdcd : P ≤ MulAction.stabilizer X c₀ ⊓ MulAction.stabilizer X d₀ :=
          fun x hx => ⟨hle_of_mem c₀ hc₀EP hx, hle_of_mem d₀ hd₀EP hx⟩
        obtain ⟨Q₀, hQ₀le, hQ₀g, hQ₀lt⟩ := exists_pSubgroup_lt_of_dvd_index hp hP hdcd
          (hdvd hc₀EP hd₀EP (fun h => hd₀ne_c h.symm))
        have hRlt : P < Q₀ ⊓ N := Work.Coprime.lt_inf_normalizer_of_lt hQ₀g hQ₀lt
        have hRle_cd : Q₀ ⊓ N ≤ MulAction.stabilizer X c₀ ⊓ MulAction.stabilizer X d₀ :=
          le_trans inf_le_left hQ₀le
        by_contra hcon
        push_neg at hcon
        have hRa : Q₀ ⊓ N ≤ MulAction.stabilizer X a := by
          intro r hr
          exact MulAction.mem_stabilizer_iff.mpr (hcon r hr.2)
        have hR3 : 3 ≤ (Work.DoubleTransitivity.fixedBySub (Q₀ ⊓ N) : Set E).ncard := by
          have hsub : ({a, c₀, d₀} : Set E) ⊆
              (Work.DoubleTransitivity.fixedBySub (Q₀ ⊓ N) : Set E) := by
            intro x hx
            rcases hx with h | h | h
            · rw [h, Work.DoubleTransitivity.mem_fixedBySub]
              exact fun m hm => MulAction.mem_stabilizer_iff.mp (hRa hm)
            · rw [h, Work.DoubleTransitivity.mem_fixedBySub]
              exact fun m hm => MulAction.mem_stabilizer_iff.mp ((le_trans hRle_cd inf_le_left) hm)
            · rw [h, Work.DoubleTransitivity.mem_fixedBySub]
              exact fun m hm => MulAction.mem_stabilizer_iff.mp ((le_trans hRle_cd inf_le_right) hm)
          have hpair : ({a, c₀, d₀} : Set E).ncard = 3 := by
            rw [Set.ncard_eq_three]
            exact ⟨a, c₀, d₀, hc₀ne_a.symm, hd₀ne_a.symm, hd₀ne_c.symm, rfl⟩
          rw [← hpair]
          exact Set.ncard_le_ncard hsub
        exact hRlt.ne (le_antisymm hRlt.le (hmax (Q₀ ⊓ N) hQ₀g.to_inf_left hRa hR3 hRlt.le))
      -- App. II (3) for `N` acting on `EP`
      have hNsmul : ∀ (n : X), n ∈ N → ∀ x ∈ EP, n • x ∈ EP :=
        fun n hn x hx => Work.DoubleTransitivity.App2.smul_mem_fixedBySub_of_mem_normalizer hn hx
      let actN : MulAction ↥N ↥EP :=
        { smul := fun m x => ⟨(m : X) • (x : E), hNsmul (m : X) m.2 (x : E) x.2⟩
          one_smul := fun x => Subtype.ext (one_smul X (x : E))
          mul_smul := fun m₁ m₂ x => Subtype.ext (mul_smul (m₁ : X) (m₂ : X) (x : E)) }
      letI := actN
      have h30 : ∀ c ∈ ({⟨a, haEP⟩}ᶜ : Set ↥EP), ∃ P' : Subgroup ↥N, IsPGroup p P' ∧
          (Work.DoubleTransitivity.fixedBySub P' : Set ↥EP) = {⟨a, haEP⟩, c} := by
        intro c hc
        rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hc
        obtain ⟨R, hRleN, hRg, _hRlt, hRfix⟩ := hRc (c : E) c.2 (fun h => hc (Subtype.ext h))
        refine ⟨R.subgroupOf N, hRg.comap_of_injective N.subtype Subtype.coe_injective, ?_⟩
        ext z
        rw [Work.DoubleTransitivity.mem_fixedBySub]
        constructor
        · intro hz
          have hz' : (z : E) ∈ (Work.DoubleTransitivity.fixedBySub R : Set E) := by
            intro r hr
            exact congrArg (fun y : ↥EP => (y : E))
              (hz ⟨r, hRleN hr⟩ (Subgroup.mem_subgroupOf.mpr hr))
          rw [hRfix] at hz'
          rcases hz' with h | h
          · exact Or.inl (Subtype.ext h)
          · exact Or.inr (Subtype.ext h)
        · intro hz
          rcases hz with h | h
          · rw [h]
            intro m hm
            apply Subtype.ext
            exact (Work.DoubleTransitivity.mem_fixedBySub.mp
              (by rw [hRfix]; exact Or.inl rfl)) (m : X) (Subgroup.mem_subgroupOf.mp hm)
          · rw [h]
            intro m hm
            apply Subtype.ext
            exact (Work.DoubleTransitivity.mem_fixedBySub.mp
              (by rw [hRfix]; exact Or.inr rfl)) (m : X) (Subgroup.mem_subgroupOf.mp hm)
      have h30fix : ¬ ∀ x : ↥N, x • (⟨a, haEP⟩ : ↥EP) = ⟨a, haEP⟩ := by
        intro hcon
        obtain ⟨n, hnN, hna⟩ := hNfix
        exact hna (congrArg (fun y : ↥EP => (y : E)) (hcon ⟨n, hnN⟩))
      have h3t := Work.DoubleTransitivity.App2.app2_3 (X := ↥N) (E := ↥EP) (p := p) h30 h30fix
      intro c hc d hd
      by_cases hcd : c = d
      · exact ⟨1, N.one_mem, by rw [hcd, one_smul]⟩
      · have hne1 : (⟨c, hc⟩ : ↥EP) ≠ ⟨d, hd⟩ := fun h => hcd (Subtype.ext_iff.mp h)
        have hne2 : (⟨d, hd⟩ : ↥EP) ≠ ⟨c, hc⟩ := fun h => hcd (Subtype.ext_iff.mp h).symm
        obtain ⟨m, hm1, -⟩ := (MulAction.is_two_pretransitive_iff.mp h3t) hne1 hne2
        exact ⟨(m : X), m.2, congrArg (fun y : ↥EP => (y : E)) hm1⟩
  refine ⟨?_, key⟩
  -- Part (i)
  intro R hPR hRg hR3
  have hRsub : (Work.DoubleTransitivity.fixedBySub R : Set E) ⊆ EP := by
    rw [hEPdef]
    exact Work.DoubleTransitivity.fixedBySub_antitone hPR
  have hneR : (Work.DoubleTransitivity.fixedBySub R : Set E).Nonempty := by
    rw [← Set.ncard_pos]
    omega
  obtain ⟨c, hcR⟩ := hneR
  have hcEP : c ∈ EP := hRsub hcR
  obtain ⟨n, hnN, hna⟩ := key a haEP c hcEP
  have hRfixc : R ≤ MulAction.stabilizer X c :=
    fun r hr => MulAction.mem_stabilizer_iff.mpr
      ((Work.DoubleTransitivity.mem_fixedBySub.mp hcR) r hr)
  have hnR : conj n⁻¹ R ≤ MulAction.stabilizer X a := by
    have hconj : conj n⁻¹ (MulAction.stabilizer X c) = MulAction.stabilizer X a := by
      rw [(Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj n⁻¹ c).symm]
      congr 1
      rw [← hna, inv_smul_smul]
    exact le_trans (Subgroup.map_mono hRfixc) (le_of_eq hconj)
  have hnP : conj n P = P := Subgroup.mem_normalizer_iff_map_conj_eq.mp hnN
  have hnP' : conj n⁻¹ P = P := by
    conv_lhs => rw [← hnP]
    rw [← conj_mul, inv_mul_cancel, conj_one]
  have hPn : P ≤ conj n⁻¹ R := by
    rw [← hnP']
    exact Subgroup.map_mono hPR
  have hcard : 3 ≤ (Work.DoubleTransitivity.fixedBySub (conj n⁻¹ R) : Set E).ncard := by
    rw [Work.DoubleTransitivity.App2.app2_3_fixedBySub_map_conj R n⁻¹, Set.ncard_smul_set]
    exact hR3
  have hle := hmax (conj n⁻¹ R) (hRg.map _) hnR hcard hPn
  refine le_antisymm ?_ hPR
  have h1 : conj n (conj n⁻¹ R) ≤ conj n P := Subgroup.map_mono hle
  rwa [← conj_mul, mul_inv_cancel, conj_one, hnP] at h1

/-- **Brauer–Suzuki, consequence for involutions**: in a finite group of `2`-rank `≤ 1` satisfying
`G = O(G)·C_G(t)` for every involution `t`, any two involutions have the same image in `G / O(G)`,
i.e. their product lies in `O(G)`. -/
theorem involution_mul_involution_mem_oddCore (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    {G : Type} [Group G] [Finite G] (h4 : ¬ Submission.Blueprint.HasFourGroup G)
    {u v : G} (hu : orderOf u = 2) (hv : orderOf v = 2) :
    u * v ∈ Submission.Blueprint.oddCore G := by
  classical
  have huniq : ∀ S : Sylow 2 G, Work.BrauerSuzuki.HasUniqueInvolution ↥S := by
    intro S
    obtain ⟨S₀, huS₀⟩ := Work.BrauerSuzuki.Group.exists_sylow_mem_of_orderOf_eq_two hu
    haveI : MulAction.IsPretransitive G (Sylow 2 G) :=
      Sylow.isPretransitive_of_finite (p := 2) (G := G)
    obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := G) S₀ S
    have hm : g * u * g⁻¹ ∈ (S : Subgroup G) := by
      have h0 : (MulAut.conj g) • u ∈ (MulAut.conj g) • (S₀ : Subgroup G) :=
        Subgroup.smul_mem_pointwise_smul u (MulAut.conj g) (S₀ : Subgroup G) huS₀
      rw [← Sylow.coe_subgroup_smul] at h0
      rw [hg] at h0
      simpa [MulAut.smul_def, MulAut.conj_apply] using h0
    have hgu2 : orderOf (g * u * g⁻¹) = 2 :=
      (Work.BrauerSuzuki.Group.orderOf_conj_eq g u).trans hu
    refine ⟨⟨g * u * g⁻¹, hm⟩, ?_, ?_⟩
    · rw [Subgroup.orderOf_mk]; exact hgu2
    · intro w hw
      refine Subtype.ext (@Work.BrauerSuzuki.Group.uniqueInvolution_of_pgroup G _ _
        (S : Subgroup G) S.isPGroup' h4 (g * u * g⁻¹) ((w : ↥S) : G) hm w.2 hgu2
        (by rw [Subgroup.orderOf_coe]; exact hw)).symm
  obtain ⟨c, hc⟩ := isConj_iff.mp (Work.BrauerSuzuki.Group.isConj_of_orderOf_eq_two huniq hu hv)
  have hO : (Submission.Blueprint.oddCore G).Normal := Work.BrauerSuzuki.oddCore_normal G
  have hmem : c⁻¹ ∈ (Submission.Blueprint.oddCore G ⊔ Subgroup.centralizer ({u} : Set G) :
      Subgroup G) := by
    rw [hBrSz G h4 u hu]; exact Subgroup.mem_top _
  have hmem2 : c⁻¹ ∈ ((Submission.Blueprint.oddCore G : Set G) *
      (Subgroup.centralizer ({u} : Set G) : Set G) : Set G) := by
    rw [← Subgroup.normal_mul]
    exact hmem
  obtain ⟨a, haO, k, hkC, hak⟩ := Set.mem_mul.mp hmem2
  have hkcomm : k * u = u * k :=
    ((Subgroup.mem_centralizer_iff.mp hkC) u (by simp)).symm
  have hku : k⁻¹ * u * k = u := by
    calc k⁻¹ * u * k = k⁻¹ * (u * k) := by rw [mul_assoc]
      _ = k⁻¹ * (k * u) := by rw [← hkcomm]
      _ = u := by rw [← mul_assoc, inv_mul_cancel, one_mul]
  have hb : k⁻¹ * (u⁻¹ * a⁻¹ * u * a) * k ∈ Submission.Blueprint.oddCore G := by
    have h1 : u⁻¹ * a⁻¹ * u * a ∈ Submission.Blueprint.oddCore G :=
      (Submission.Blueprint.oddCore G).mul_mem
        (by simpa using hO.conj_mem a⁻¹ ((Submission.Blueprint.oddCore G).inv_mem haO) u⁻¹) haO
    simpa using hO.conj_mem (u⁻¹ * a⁻¹ * u * a) h1 k⁻¹
  have hu2 : u * u = 1 := by rw [← pow_two, ← hu]; exact pow_orderOf_eq_one u
  have hv' : v = u * (k⁻¹ * (u⁻¹ * a⁻¹ * u * a) * k) := by
    have hc'' : c = k⁻¹ * a⁻¹ := by
      rw [show c = (a * k)⁻¹ from by rw [hak, inv_inv], mul_inv_rev]
    calc v = c * u * c⁻¹ := hc.symm
      _ = (k⁻¹ * a⁻¹) * u * (k⁻¹ * a⁻¹)⁻¹ := by rw [hc'']
      _ = u * (k⁻¹ * (u⁻¹ * a⁻¹ * u * a) * k) := by
          rw [mul_inv_rev, inv_inv, inv_inv]
          calc k⁻¹ * a⁻¹ * u * (a * k) = k⁻¹ * (a⁻¹ * u * a) * k := by group
            _ = k⁻¹ * (u * (u⁻¹ * a⁻¹ * u * a)) * k := by
                rw [show a⁻¹ * u * a = u * (u⁻¹ * a⁻¹ * u * a) from by group]
            _ = (k⁻¹ * u * k) * (k⁻¹ * (u⁻¹ * a⁻¹ * u * a) * k) := by group
            _ = u * (k⁻¹ * (u⁻¹ * a⁻¹ * u * a) * k) := by rw [hku]
  rw [hv', ← mul_assoc, hu2, one_mul]
  exact hb

/-- **Peterfalvi I Ch. I §3 Prop. 1** (transitivity form): if `Q` is maximal among the
`p`-subgroups of `G` with at least three fixed points of `Ω = G ⧸ K` and `N_G(Q)` is transitive
on `Ω_Q`, then some point stabiliser `N_H(Q)` (`H ∈ Ω_Q`) has even order. -/
theorem sec3_prop1_transitive {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hK : IsStronglyEmbedded K) (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : Subgroup G} (hQp : IsPGroup p Q)
    (hQ3 : 3 ≤ (Submission.Blueprint.fixedPts K Q).ncard)
    (hQmax : ∀ R : Subgroup G, Q ≤ R → IsPGroup p R →
      3 ≤ (Submission.Blueprint.fixedPts K R).ncard → R = Q)
    (htrans : Work.DoubleTransitivity.IsTransitiveOnSub (Subgroup.normalizer (Q : Set G))
      (Submission.Blueprint.fixedPts K Q)) :
    ∃ ω ∈ Submission.Blueprint.fixedPts K Q,
      Even (Nat.card (MulAction.stabilizer G ω ⊓ Subgroup.normalizer (Q : Set G) : Subgroup G)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set M : Subgroup G := Subgroup.normalizer (Q : Set G) with hMdef
  have hMdef' : M = Subgroup.normalizer (Q : Set G) := hMdef
  have hQodd : Odd (Nat.card Q) := by
    rw [← Nat.not_even_iff_odd]
    intro hev
    haveI : Fintype ↥Q := Fintype.ofFinite ↥Q
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := ↥Q) 2
      (by rw [← Nat.card_eq_fintype_card]; exact even_iff_two_dvd.mp hev)
    obtain ⟨n, hn⟩ := hQp x
    have hxG : orderOf ((x : Q) : G) = 2 := (Subgroup.orderOf_coe x).trans hx
    have h2dvd : 2 ∣ p ^ n := by
      rw [← hxG]
      exact orderOf_dvd_of_pow_eq_one (by simpa using congrArg (fun y : Q => (y : G)) hn)
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2dvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp this).symm
  by_cases hA4 : Submission.Blueprint.HasFourGroup M
  · -- Case A: `N_G(Q)` has `2`-rank `≥ 2`
    obtain ⟨t, ht2⟩ : ∃ t : M, orderOf t = 2 := by
      obtain ⟨t, -, ht2, -, -, -⟩ := hA4
      exact ⟨t, ht2⟩
    have htG : orderOf ((t : G)) = 2 := (Subgroup.orderOf_coe t).trans ht2
    obtain ⟨ω, hωfix, -⟩ := existsUnique_fixedPts_of_orderOf_eq_two hK htG
    have hle : Q ≤ MulAction.stabilizer G ω :=
      le_stabilizer_of_involution_mem_normalizer hK hQodd hA4 ⟨t.2, htG⟩ hωfix
    refine ⟨ω, mem_fixedPts_iff_le_stabilizer.mpr hle, ?_⟩
    have hmem : (t : G) ∈ (MulAction.stabilizer G ω ⊓ M : Subgroup G) :=
      ⟨MulAction.mem_stabilizer_iff.mpr hωfix, t.2⟩
    refine even_iff_two_dvd.mpr ?_
    have hord : orderOf (⟨(t : G), hmem⟩ :
        ↥(MulAction.stabilizer G ω ⊓ M : Subgroup G)) = 2 := by
      rw [Subgroup.orderOf_mk]; exact htG
    have h2dvd : 2 ∣ orderOf (⟨(t : G), hmem⟩ :
        ↥(MulAction.stabilizer G ω ⊓ M : Subgroup G)) := by
      rw [hord]
    exact dvd_trans h2dvd (orderOf_dvd_natCard
      (⟨(t : G), hmem⟩ : ↥(MulAction.stabilizer G ω ⊓ M : Subgroup G)))
  · -- Case B: `N_G(Q)` has `2`-rank `1`
    have hB : ¬ Submission.Blueprint.HasFourGroup M := hA4
    have hne : (Submission.Blueprint.fixedPts K Q).Nonempty := by
      rw [← Set.ncard_pos]; omega
    obtain ⟨ω₀, hω₀⟩ := hne
    obtain ⟨ω₁, hω₁, hω₁ne⟩ :=
      Set.exists_ne_of_one_lt_ncard (by omega : 1 < (Submission.Blueprint.fixedPts K Q).ncard) ω₀
    have h2s : 2 ≤ ((Submission.Blueprint.fixedPts K Q) \ {ω₀}).ncard := by
      have h1 := Set.ncard_sdiff_singleton_add_one hω₀
      omega
    obtain ⟨ω₂, hω₂, hω₂ne⟩ := Set.exists_ne_of_one_lt_ncard
      (by omega : 1 < ((Submission.Blueprint.fixedPts K Q) \ {ω₀}).ncard) ω₁
    have hω₂mem : ω₂ ∈ Submission.Blueprint.fixedPts K Q := hω₂.1
    have hω₂ne₀ : ω₂ ≠ ω₀ := hω₂.2
    -- the three involutions
    obtain ⟨t₁, ht₁M, ht₁2, ht₁⟩ :=
      sec3_lemma3 hK hp hQp hQmax hω₀ hω₁ hω₁ne.symm (htrans ω₀ hω₀ ω₁ hω₁)
    obtain ⟨t₂, ht₂M, ht₂2, ht₂⟩ :=
      sec3_lemma3 hK hp hQp hQmax hω₀ hω₂mem hω₂ne₀.symm (htrans ω₀ hω₀ ω₂ hω₂mem)
    have ht₁M' : t₁ ∈ M := by rw [hMdef']; exact ht₁M
    have ht₂M' : t₂ ∈ M := by rw [hMdef']; exact ht₂M
    have hprodM : t₁ * t₂ ∈ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normalizer (Q : Set G)).mul_mem ht₁M ht₂M
    have hω' : (t₁ * t₂) • ω₀ ∈ Submission.Blueprint.fixedPts K Q :=
      Work.DoubleTransitivity.App2.smul_mem_fixedBySub_of_mem_normalizer hprodM hω₀
    have ht₁sq : t₁ * t₁ = 1 := mul_self_eq_one_of_orderOf_eq_two ht₁2
    have ht₂sq : t₂ * t₂ = 1 := mul_self_eq_one_of_orderOf_eq_two ht₂2
    have hne' : ω₀ ≠ (t₁ * t₂) • ω₀ := by
      intro hcon
      have h1 : t₁ • ((t₁ * t₂) • ω₀) = ω₂ := by
        rw [mul_smul, ← mul_smul, ht₁sq, one_smul, ht₂]
      have h2 : t₁ • ω₀ = t₁ • ((t₁ * t₂) • ω₀) := congrArg (fun y => t₁ • y) hcon
      exact hω₂ne (ht₁.symm.trans (h2.trans h1)).symm
    obtain ⟨t, htM, ht2, ht⟩ := sec3_lemma3 hK hp hQp hQmax hω₀ hω'
      hne' ⟨t₁ * t₂, hprodM, rfl⟩
    have htM' : t ∈ M := by rw [hMdef']; exact htM
    have hxmem : t₂ * t₁ * t ∈ M := M.mul_mem (M.mul_mem ht₂M' ht₁M') htM'
    have htsq : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two ht2
    have hxfix : (t₂ * t₁ * t) • ω₀ = ω₀ := by
      rw [mul_smul, mul_smul, ht, mul_smul]
      have h1 : t₁ • (t₁ • (t₂ • ω₀)) = t₂ • ω₀ := by
        rw [← mul_smul, ht₁sq, one_smul]
      rw [h1, ← mul_smul, ht₂sq, one_smul]
    refine ⟨ω₀, hω₀, ?_⟩
    refine even_iff_two_dvd.mpr ?_
    have hmem : (t₂ * t₁ * t) ∈ (MulAction.stabilizer G ω₀ ⊓ M : Subgroup G) :=
      ⟨MulAction.mem_stabilizer_iff.mpr hxfix, hxmem⟩
    -- work inside `M`
    set t₁' : M := ⟨t₁, ht₁M'⟩
    set t₂' : M := ⟨t₂, ht₂M'⟩
    set t' : M := ⟨t, htM'⟩
    have ht₁2' : orderOf t₁' = 2 := by rw [← Subgroup.orderOf_coe t₁']; exact ht₁2
    have ht₂2' : orderOf t₂' = 2 := by rw [← Subgroup.orderOf_coe t₂']; exact ht₂2
    have ht2' : orderOf t' = 2 := by rw [← Subgroup.orderOf_coe t']; exact ht2
    have htsq' : t' * t' = 1 := mul_self_eq_one_of_orderOf_eq_two ht2'
    have hO : (Submission.Blueprint.oddCore M).Normal := Work.BrauerSuzuki.oddCore_normal M
    have hprodO : t₂' * t₁' ∈ Submission.Blueprint.oddCore M :=
      involution_mul_involution_mem_oddCore hBrSz hB ht₂2' ht₁2'
    have htO : t' ∉ Submission.Blueprint.oddCore M := by
      intro hcon
      have hdvd : 2 ∣ Nat.card ↥(Submission.Blueprint.oddCore M) := by
        have h := orderOf_dvd_natCard (⟨t', hcon⟩ : ↥(Submission.Blueprint.oddCore M))
        rwa [Subgroup.orderOf_mk, ht2'] at h
      exact (Nat.not_even_iff_odd.mpr
        (Work.BrauerSuzuki.OddCore.oddCard_oddCore (G := M))) (even_iff_two_dvd.mpr hdvd)
    have hx2O : (t₂' * t₁' * t') * (t₂' * t₁' * t') ∈ Submission.Blueprint.oddCore M := by
      have h : t' * (t₂' * t₁') * t' ∈ Submission.Blueprint.oddCore M := by
        have h' := hO.conj_mem (t₂' * t₁') hprodO t'
        rwa [inv_eq_of_mul_eq_one_right htsq'] at h'
      have h1 : (t₂' * t₁' * t') * (t₂' * t₁' * t') =
          (t₂' * t₁') * (t' * (t₂' * t₁') * t') := by group
      rw [h1]
      exact (Submission.Blueprint.oddCore M).mul_mem hprodO h
    have hxtO : (t₂' * t₁' * t') * t' ∈ Submission.Blueprint.oddCore M := by
      have h1 : (t₂' * t₁' * t') * t' = t₂' * t₁' := by rw [mul_assoc, htsq', mul_one]
      rw [h1]; exact hprodO
    have hxO : (t₂' * t₁' * t') ∉ Submission.Blueprint.oddCore M := by
      intro hcon
      refine htO ?_
      have h1 : (t₂' * t₁' * t')⁻¹ * ((t₂' * t₁' * t') * t') = t' := by group
      rw [← h1]
      exact (Submission.Blueprint.oddCore M).mul_mem
        ((Submission.Blueprint.oddCore M).inv_mem hcon) hxtO
    have hxeven : Even (orderOf (t₂' * t₁' * t')) := by
      by_contra hcon
      have hodd : Odd (orderOf (t₂' * t₁' * t')) := Nat.not_even_iff_odd.mp hcon
      obtain ⟨j, hj⟩ := hodd
      have hpow : (t₂' * t₁' * t') = ((t₂' * t₁' * t') * (t₂' * t₁' * t')) ^ (j + 1) := by
        rw [← pow_two, ← pow_mul]
        have h2 : 2 * (j + 1) = orderOf (t₂' * t₁' * t') + 1 := by rw [hj]; ring
        rw [h2, pow_succ, pow_orderOf_eq_one, one_mul]
      exact hxO (hpow ▸ pow_mem hx2O (j + 1))
    have hxevenG : Even (orderOf (t₂ * t₁ * t)) := by
      have hcoee : (((t₂' * t₁' * t') : M) : G) = t₂ * t₁ * t := rfl
      rw [← hcoee, Subgroup.orderOf_coe]
      exact hxeven
    refine dvd_trans (even_iff_two_dvd.mp hxevenG) ?_
    have hord : orderOf (⟨t₂ * t₁ * t, hmem⟩ :
        ↥(MulAction.stabilizer G ω₀ ⊓ M : Subgroup G)) = orderOf (t₂ * t₁ * t) :=
      Subgroup.orderOf_mk _ _
    rw [← hord]
    exact orderOf_dvd_natCard _

/-- **Peterfalvi I Ch. I §4 Prop. 2** (p. 156), the unconditional form: let `F` be a finite group of 2-rank ≥ 2 (`HasFourGroup F`), `K ≤ F` a strongly embedded subgroup (so `F` acts on `Ω = F ⧸ K`), `p ≠ 2` a prime, and `Q ≤ K` a `p`-subgroup *maximal among the `p`-subgroups of `K` with at least three fixed points of `Ω`*.  Then `Q` is maximal among the `p`-subgroups of `F` with at least three fixed points and `|N_K(Q)|` is even.

This is the input consumed by Ch. II §4 Prop. 1(a) (p. 168) inside `F₁ = C_G(O^p(X))·P`, where `K = F₁ ⊓ M`, `F = F₁` and `Ξ = Ω`, and there it is "an involution `u ∈ N(Q) ∩ F₁ ∩ M`".  The hypothesis `hBrSz : BrauerSuzukiProp` is the black box the source's proof consumes: Ch. I §3 Prop. 1, Case 2 (p. 154) needs "`M/O_{2'}(M)` has a unique involution" for `M = N_F(Q)` of 2-rank 1 (cf. the workspace's `Work.ThreePoints.twoTransitive_stabilizer_even`, the 2-transitive 2-rank-1 case).

Route (`REFS/peterfalvi_I_ch1_2.md` pp. 152–157).  §3 Prop. 1: if `N_F(Q)` has 2-rank ≥ 2 then Ch. I §3 Lemma 2 (`Work.ThreePoints.le_stabilizer_of_involution_mem_normalizer`, proved in `sec3_lemma2`) gives, for every involution `t ∈ N_F(Q)`, that `Q ≤ Stab ω_t` for the fixed point `ω_t` of `t`, so `t ∈ N_{Stab ω_t}(Q)` and some point stabiliser is even; if instead Case 1 holds (all `N_F(Q)`-orbits on `Ω_Q` have size ≤ 2), §3 Lemma 1 + maximality of `Q` give a contradiction, so an orbit of size ≥ 3 yields an involution of `N_F(Q)` by §3 Lemma 3, and again some `H ∈ Ω_Q` has `|N_H(Q)|` even.  §4 Lemma 1/2 and §4 Prop. 1 (with `hBrSz` for the 2-rank-1 case, `M/O_{2'}(M)` having a unique involution, and the `R_p` analysis for the 2-transitive step) show that `Q` is maximal among the `p`-subgroups of `F` with ≥ 3 fixed points and that all point stabilisers `N_H(Q)` (`H ∈ Ω_Q`) have equal order; Theorem A (`hA`, whose hypothesis `HasFourGroup F` is assumed) makes `F` 2-transitive on `Ω`, so App. II (6) (`app2_6_uniform`) gives transitivity of `N_F(Q)` on `Ω_Q`, whence `|N_K(Q)|` is even. -/
theorem even_card_normalizer_of_maximal_p_subgroup {F : Type} [Group F] [Finite F]
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hA : Submission.Blueprint.ThmAProp)
    (hfour : Submission.Blueprint.HasFourGroup F) {K : Subgroup F}
    (hK : LeanEval.GroupTheory.Defs.IsStronglyEmbedded K)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : Subgroup F} (hQK : Q ≤ K)
    (hQp : IsPGroup p Q) (hQ3 : 3 ≤ (Submission.Blueprint.fixedPts K Q).ncard)
    (hQmax : ∀ R : Subgroup F, Q ≤ R → R ≤ K → IsPGroup p R →
      3 ≤ (Submission.Blueprint.fixedPts K R).ncard → R = Q) :
    Even (Nat.card (Subgroup.normalizer (Q.subgroupOf K : Set K) : Subgroup K)) := by
  classical
  haveI : Fintype (F ⧸ K) := Fintype.ofFinite _
  set M : Subgroup F := Subgroup.normalizer (Q : Set F) with hMdef
  have hstab : MulAction.stabilizer F (((1 : F)) : F ⧸ K) = K := by
    rw [Work.ThreePoints.stabilizer_mk K 1, conj_one]
  have h2tr : MulAction.IsMultiplyPretransitive F (F ⧸ K) 2 := hA F hfour K hK
  -- App. II (6): maximality in `F` and transitivity of `N_F(Q)` on `Ω_Q`
  obtain ⟨hQmaxF, htransF⟩ := app2_6_general (X := F) (E := F ⧸ K) (p := p) hp h2tr
    (P := Q) hQp (by rw [hstab]; exact hQK) hQ3
    (fun R hRg hRa hR3 hQR => by
      have hRK : R ≤ K := by rw [← hstab]; exact hRa
      rw [hQmax R hQR hRK hRg hR3])
  -- Ch. I §3 Prop. 1
  obtain ⟨ω, hω, heven⟩ := sec3_prop1_transitive hK hBrSz hp hp2 hQp hQ3
    (fun R hQR hRg hR3 => hQmaxF R hQR hRg hR3) htransF
  have hωK : (((1 : F)) : F ⧸ K) ∈ Submission.Blueprint.fixedPts K Q := by
    rw [Work.ThreePoints.mem_fixedPts_iff_le_stabilizer, hstab]
    exact hQK
  obtain ⟨n, hnM, hn⟩ := htransF (((1 : F)) : F ⧸ K) hωK ω hω
  -- all point stabilisers of `N_F(Q)` on `Ω_Q` have the same order
  have hcard_eq : Nat.card (MulAction.stabilizer F ω ⊓ M : Subgroup F) =
      Nat.card (MulAction.stabilizer F (((1 : F)) : F ⧸ K) ⊓ M : Subgroup F) := by
    have hnM' : n ∈ M := hnM
    have hMconj : conj n M = M := by
      have hstep : ∀ u ∈ M, conj u M ≤ M := by
        intro u hu m hm
        rw [mem_conj_iff] at hm
        have h := M.mul_mem (M.mul_mem hu hm) (M.inv_mem hu)
        rwa [show u * (u⁻¹ * m * u) * u⁻¹ = m from by group] at h
      refine le_antisymm (hstep n hnM') ?_
      calc M = conj n (conj n⁻¹ M) := by rw [← conj_mul, mul_inv_cancel, conj_one]
        _ ≤ conj n M := Subgroup.map_mono (hstep n⁻¹ (M.inv_mem hnM'))
    have h1 : MulAction.stabilizer F ω =
        conj n (MulAction.stabilizer F (((1 : F)) : F ⧸ K)) := by
      rw [← Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj n (((1 : F)) : F ⧸ K), hn]
    have key2 : MulAction.stabilizer F ω ⊓ M =
        conj n (MulAction.stabilizer F (((1 : F)) : F ⧸ K) ⊓ M) := by
      rw [conj_inf, ← h1, hMconj]
    rw [key2]
    exact Subgroup.card_map_of_injective (MulAut.conj n).injective
  have hevenK : Even (Nat.card (K ⊓ M : Subgroup F)) := by
    rw [← hstab, ← hcard_eq]
    exact heven
  -- `N_K(Q)` is isomorphic to its image in `F`, which is `K ⊓ N_F(Q)`
  have hmap : (Subgroup.normalizer (Q.subgroupOf K : Set K)).map K.subtype = K ⊓ M := by
    ext x
    rw [Subgroup.mem_map, Subgroup.mem_inf]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      rw [hMdef, Subgroup.mem_normalizer_iff_map_conj_eq]
      have hy' : (Q.subgroupOf K).map (MulAut.conj y).toMonoidHom = Q.subgroupOf K :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hy
      calc Q.map (MulAut.conj (y : F)).toMonoidHom
          = ((Q.subgroupOf K).map K.subtype).map (MulAut.conj (y : F)).toMonoidHom := by
            conv_lhs => rw [← Subgroup.map_subgroupOf_eq_of_le hQK]
        _ = (Q.subgroupOf K).map ((MulAut.conj (y : F)).toMonoidHom.comp K.subtype) := by
            rw [Subgroup.map_map]
        _ = (Q.subgroupOf K).map (K.subtype.comp (MulAut.conj y).toMonoidHom) := by
            rw [show (MulAut.conj (y : F)).toMonoidHom.comp K.subtype =
              K.subtype.comp (MulAut.conj y).toMonoidHom from by
                ext z
                simp [MulAut.conj_apply]]
        _ = ((Q.subgroupOf K).map (MulAut.conj y).toMonoidHom).map K.subtype := by
            rw [Subgroup.map_map]
        _ = (Q.subgroupOf K).map K.subtype := by rw [hy']
        _ = Q := Subgroup.map_subgroupOf_eq_of_le hQK
    · rintro ⟨hxK, hxN⟩
      refine Subgroup.mem_map.mpr ⟨⟨x, hxK⟩, ?_, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        have hyQ : (y : F) ∈ Q := Subgroup.mem_subgroupOf.mp hy
        have h1 : x * (y : F) * x⁻¹ ∈ Q :=
          (Subgroup.mem_normalizer_iff.mp hxN) (y : F) |>.mp hyQ
        rw [Subgroup.mem_subgroupOf]
        simpa using h1
      · intro hy
        have hyQ : x * (y : F) * x⁻¹ ∈ Q := by
          have h := Subgroup.mem_subgroupOf.mp hy
          simpa using h
        have hxi : x⁻¹ ∈ Subgroup.normalizer (Q : Set F) :=
          (Subgroup.normalizer (Q : Set F)).inv_mem hxN
        have h1 : x⁻¹ * (x * (y : F) * x⁻¹) * x⁻¹⁻¹ ∈ Q :=
          (Subgroup.mem_normalizer_iff.mp hxi) (x * (y : F) * x⁻¹) |>.mp hyQ
        have h2 : x⁻¹ * (x * (y : F) * x⁻¹) * x⁻¹⁻¹ = (y : F) := by group
        rw [h2] at h1
        exact Subgroup.mem_subgroupOf.mpr h1
  have hcardfin : Nat.card ↥(Subgroup.normalizer (Q.subgroupOf K : Set K)) =
      Nat.card ↥(K ⊓ M : Subgroup F) := by
    rw [← hmap]
    exact (Subgroup.card_map_of_injective (f := K.subtype) Subtype.coe_injective).symm
  rw [hcardfin]
  exact hevenK

end Work.ThreePoints
