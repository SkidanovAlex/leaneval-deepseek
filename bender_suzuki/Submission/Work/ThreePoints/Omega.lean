/-
# `Work.ThreePoints.Omega` — the geometry of `Ω = G ⧸ H` (Peterfalvi I Ch. I §1–§2)

`H` is a strongly embedded subgroup of a finite group `G`, and `Ω = G ⧸ H` is the set of its
conjugates, on which `G` acts by left translation (`x • gH = xgH`).  For a point `ω`,
`MulAction.stabilizer G ω` is the corresponding conjugate of `H`
(`Work.ThreePoints.stabilizer_mk`).

This file contains the part of Peterfalvi I Ch. I used by Chapter II:

* §1 (3): `H` contains a Sylow 2-subgroup of `G`, hence every involution lies in a conjugate
  of `H`;
* §2: the fixed point of an involution is unique, and the intersection of two distinct
  conjugates of `H` has odd order.
-/
import Submission.Work.ThreePoints.Basic
import Submission.Work.DoubleTransitivity.Basic
import Submission.Work.Coprime.lt_inf_normalizer_of_lt

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints

open Submission.Blueprint

variable {G : Type} [Group G]

/-! ## 0. Conjugates of a strongly embedded subgroup -/

/-- Conjugation by an element of `H` fixes `H`. -/
theorem conj_eq_self_of_mem {H : Subgroup G} {x : G} (hx : x ∈ H) : conj x H = H := by
  ext y
  rw [mem_conj_iff]
  constructor
  · intro hy
    have : x * (x⁻¹ * y * x) * x⁻¹ ∈ H := H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)
    rwa [show x * (x⁻¹ * y * x) * x⁻¹ = y from by group] at this
  · intro hy
    exact H.mul_mem (H.mul_mem (H.inv_mem hx) hy) hx

/-- Conjugation distributes over intersections. -/
theorem conj_inf (g : G) (A B : Subgroup G) : conj g (A ⊓ B) = conj g A ⊓ conj g B :=
  Subgroup.map_inf A B _ (MulAut.conj g).injective

/-- Conjugates of a strongly embedded subgroup are strongly embedded. -/
theorem conj_stronglyEmbedded {H : Subgroup G} (h : IsStronglyEmbedded H) (g : G) :
    IsStronglyEmbedded (conj g H) := by
  refine ⟨?_, ?_, ?_⟩
  · intro htop
    have h1 : conj g⁻¹ (⊤ : Subgroup G) = ⊤ := by
      rw [conj, Subgroup.map_top_of_surjective _ (MulAut.conj g⁻¹).surjective]
    have h2 : H = ⊤ := by
      have h3 := congrArg (conj g⁻¹) htop
      rw [DoubleTransitivity.conj_inv_conj, h1] at h3
      exact h3
    exact IsStronglyEmbedded.ne_top h h2
  · rw [Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective]
    exact IsStronglyEmbedded.even_card h
  · intro x hx
    have hxH : g⁻¹ * x * g ∉ H := fun hmem => hx (mem_conj_iff.mpr hmem)
    have hodd := IsStronglyEmbedded.odd_card_inf_conj h hxH
    have h1 : conj x (conj g H) = conj g (conj (g⁻¹ * x * g) H) := by
      rw [← DoubleTransitivity.conj_mul x g,
        show x * g = g * (g⁻¹ * x * g) from by group, DoubleTransitivity.conj_mul]
    have heq : conj g H ⊓ conj x (conj g H) = conj g (H ⊓ conj (g⁻¹ * x * g) H) := by
      rw [h1, conj_inf]
    have hcard : Nat.card (conj g (H ⊓ conj (g⁻¹ * x * g) H) : Subgroup G) =
        Nat.card (H ⊓ conj (g⁻¹ * x * g) H : Subgroup G) :=
      Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective
    rwa [heq, hcard]

/-! ## 1. Peterfalvi I Ch. I §1 (3): `H` contains a Sylow 2-subgroup of `G` -/

/-- **Peterfalvi I Ch. I §1 (3).**  A strongly embedded subgroup contains a Sylow 2-subgroup
of `G`. -/
theorem exists_sylow_le [Finite G] {H : Subgroup G} (h : IsStronglyEmbedded H) :
    ∃ S : Sylow 2 G, (S : Subgroup G) ≤ H := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, -⟩ := IsPGroup.exists_le_sylow (IsPGroup.of_bot : IsPGroup 2 (⊥ : Subgroup H))
  set Pg : Subgroup G := (P : Subgroup H).map H.subtype with hPge
  have hPg_le : Pg ≤ H := Subgroup.map_subtype_le _
  have hPg_isP : IsPGroup 2 Pg := P.isPGroup'.map H.subtype
  have hPg_card : Nat.card Pg = Nat.card (P : Subgroup H) :=
    Subgroup.card_map_of_injective (f := H.subtype) Subtype.coe_injective
  have hfac : 1 ≤ (Nat.card H).factorization 2 :=
    (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two Nat.card_pos.ne').mp
      (even_iff_two_dvd.mp (IsStronglyEmbedded.even_card h))
  have hPg_even : Even (Nat.card Pg) := by
    rw [hPg_card, Sylow.card_eq_multiplicity P]
    refine ⟨2 ^ ((Nat.card H).factorization 2 - 1), ?_⟩
    have hpow : 2 ^ (Nat.card H).factorization 2 =
        2 ^ ((Nat.card H).factorization 2 - 1) + 2 ^ ((Nat.card H).factorization 2 - 1) := by
      conv_lhs => rw [show (Nat.card H).factorization 2 = (Nat.card H).factorization 2 - 1 + 1
        from (Nat.succ_pred_eq_of_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one hfac)).symm]
      rw [pow_succ']
      ring
    exact hpow
  have hN_le : Subgroup.normalizer (Pg : Set G) ≤ H :=
    IsBenderGroup.normalizer_le_of_dvd (IsStronglyEmbedded.isBenderGroup_two h) hPg_le
      (even_iff_two_dvd.mp hPg_even)
  obtain ⟨Q, hPQ⟩ := IsPGroup.exists_le_sylow hPg_isP
  have hQle : (Q : Subgroup G) ≤ Pg := by
    by_contra hnotle
    have hneq : Pg ≠ (Q : Subgroup G) := fun heq => hnotle heq.ge
    have hlt : Pg < (Q : Subgroup G) := lt_of_le_of_ne hPQ hneq
    have hltN := Work.Coprime.lt_inf_normalizer_of_lt (p := 2)
      (hT := Q.isPGroup') (hRT := hlt)
    set N : Subgroup G :=
      (Q : Subgroup G) ⊓ Subgroup.normalizer (Pg : Set G) with hNdef
    have hNH : N ≤ H := le_trans inf_le_right hN_le
    have hNP : IsPGroup 2 N := IsPGroup.to_inf_left Q.isPGroup'
    have hA : IsPGroup 2 (N.subgroupOf H) :=
      hNP.comap_of_injective H.subtype Subtype.coe_injective
    have hPA : (P : Subgroup H) ≤ N.subgroupOf H := by
      intro p hp
      rw [Subgroup.mem_subgroupOf]
      exact ⟨hPQ (Subgroup.mem_map_of_mem H.subtype hp),
        Subgroup.le_normalizer (Subgroup.mem_map_of_mem H.subtype hp)⟩
    have heq : N.subgroupOf H = P := P.is_maximal' hA hPA
    have hmap : N = Pg := by
      have h1 := congrArg (Subgroup.map H.subtype) heq
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hNH] at h1
      exact h1.trans hPge.symm
    exact absurd hmap.symm hltN.ne
  exact ⟨Q, le_trans hQle hPg_le⟩

/-- **Peterfalvi I Ch. I §2.**  Every involution of `G` lies in a conjugate of `H`
(so that `H(t)` is defined for every involution `t`). -/
theorem exists_conj_mem [Finite G] {H : Subgroup G} (h : IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) : ∃ g : G, t ∈ conj g H := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hSH⟩ := exists_sylow_le h
  have htP : IsPGroup 2 (Subgroup.zpowers t) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, ht]
    norm_num
  obtain ⟨T, hT⟩ := IsPGroup.exists_le_sylow htP
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S T
  have hsylow : ((g • S : Sylow 2 G) : Subgroup G) = conj g (S : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  refine ⟨g, ?_⟩
  have : t ∈ ((g • S : Sylow 2 G) : Subgroup G) := by rw [hg]; exact hT (Subgroup.mem_zpowers t)
  rw [hsylow] at this
  exact Subgroup.map_mono hSH this

/-! ## 2. Distinct conjugates meet in odd order; fixed points of involutions are unique -/

/-- **Peterfalvi I Ch. I §1 (1).**  Two distinct conjugates of `H` meet in a subgroup of odd
order. -/
theorem card_inf_conj_odd {H : Subgroup G} (h : IsStronglyEmbedded H) {g g' : G}
    (hne : conj g H ≠ conj g' H) :
    Odd (Nat.card (conj g H ⊓ conj g' H : Subgroup G)) := by
  have hxH : g⁻¹ * g' ∉ H := by
    intro hx
    refine hne ?_
    have h2 : conj g' H = conj g H := by
      rw [show g' = g * (g⁻¹ * g') from by group, DoubleTransitivity.conj_mul,
        conj_eq_self_of_mem hx]
    exact h2.symm
  have hodd := IsStronglyEmbedded.odd_card_inf_conj h hxH
  have heq : conj g H ⊓ conj g' H = conj g (H ⊓ conj (g⁻¹ * g') H) := by
    rw [show conj g' H = conj g (conj (g⁻¹ * g') H) from by
      rw [← DoubleTransitivity.conj_mul, show g * (g⁻¹ * g') = g' from by group], conj_inf]
  have hcard : Nat.card (conj g (H ⊓ conj (g⁻¹ * g') H) : Subgroup G) =
      Nat.card (H ⊓ conj (g⁻¹ * g') H : Subgroup G) :=
    Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  rwa [heq, hcard]

/-- If the intersection of two conjugates of `H` has even order, the conjugates are equal. -/
theorem conj_eq_of_even_card_inf {H : Subgroup G} (h : IsStronglyEmbedded H) {g g' : G}
    (hev : Even (Nat.card (conj g H ⊓ conj g' H : Subgroup G))) : conj g H = conj g' H := by
  by_contra hne
  exact Nat.not_even_iff_odd.mpr (card_inf_conj_odd h hne) hev

/-- `gH = g'H` whenever `gHg⁻¹ = g'Hg'⁻¹`: a point of `Ω` is determined by its stabiliser. -/
theorem mk_eq_of_conj_eq {H : Subgroup G} (h : IsStronglyEmbedded H) {g g' : G}
    (hg : conj g H = conj g' H) : (g : G ⧸ H) = (g' : G ⧸ H) := by
  rw [QuotientGroup.eq]
  have hconj : conj (g⁻¹ * g') H = H := by
    rw [DoubleTransitivity.conj_mul, ← hg, DoubleTransitivity.conj_inv_conj]
  have hmem : g⁻¹ * g' ∈ Subgroup.normalizer (H : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hconj
  rwa [IsStronglyEmbedded.normalizer_eq h] at hmem

/-- **Peterfalvi I Ch. I §2.**  The set of fixed points in `Ω = G ⧸ H` of an involution has
exactly one element. -/
theorem ncard_fixedPts_zpowers [Finite G] {H : Subgroup G} (h : IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) : (fixedPts H (Subgroup.zpowers t)).ncard = 1 := by
  classical
  obtain ⟨g, hg⟩ := exists_conj_mem h ht
  have hmem : (g : G ⧸ H) ∈ fixedPts H (Subgroup.zpowers t) := by
    rw [mem_fixedPts]
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [DoubleTransitivity.smul_mk_eq_mk_iff]
    exact Subgroup.zpow_mem (K := conj g H) hg n
  rw [Set.ncard_eq_one]
  refine ⟨(g : G ⧸ H), ?_⟩
  ext ω
  constructor
  · intro hω
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective ω
    have hg' : t ∈ conj g' H :=
      DoubleTransitivity.smul_mk_eq_mk_iff.mp (mem_fixedPts.mp hω t (Subgroup.mem_zpowers t))
    have h2 : 2 ∣ Nat.card (conj g H ⊓ conj g' H : Subgroup G) := by
      have hdvd := Subgroup.card_dvd_of_le
        (le_inf (Subgroup.zpowers_le.mpr hg) (Subgroup.zpowers_le.mpr hg'))
      rwa [Nat.card_zpowers, ht] at hdvd
    have heven : Even (Nat.card (conj g H ⊓ conj g' H : Subgroup G)) := by
      obtain ⟨c, hc⟩ := h2
      exact ⟨c, by omega⟩
    rw [Set.mem_singleton_iff]
    exact (mk_eq_of_conj_eq h (conj_eq_of_even_card_inf h heven)).symm
  · intro hω
    rw [Set.mem_singleton_iff] at hω
    rw [hω]
    exact hmem

/-- **Peterfalvi I Ch. I §1 (2)** in fixed-point form: if the involution `s` fixes `ω`, then
`C_G(s) ≤ Stab_G(ω)` (the conjugate of `H` containing `s`). -/
theorem centralizer_le_stabilizer {H : Subgroup G} (h : IsStronglyEmbedded H) {s : G}
    (hs : orderOf s = 2) {ω : G ⧸ H} (hω : s • ω = ω) :
    Subgroup.centralizer ({s} : Set G) ≤ MulAction.stabilizer G ω := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective ω
  rw [stabilizer_mk]
  exact IsStronglyEmbedded.centralizer_le (conj_stronglyEmbedded h g)
    (DoubleTransitivity.smul_mk_eq_mk_iff.mp hω) (by rw [hs])


/-! ## 3. Peterfalvi I Ch. I §1 (6): `X ⊓ H` is strongly embedded in `X` -/

/-- `Odd` is inherited by divisors. -/
theorem Odd.of_dvd {m n : ℕ} (hmn : m ∣ n) (hn : Odd n) : Odd m :=
  (odd_iff_not_two_dvd m).mpr fun h2 => (odd_iff_not_two_dvd n).mp hn (dvd_trans h2 hmn)

/-- **Peterfalvi I Ch. I §1 (6).**  If `H` is strongly embedded in `G` and `X ⊓ H` has even order
(and is a proper subgroup of `X`), then `X ⊓ H` is strongly embedded in `X`. -/
theorem IsStronglyEmbedded.subgroupOf_inf {H X : Subgroup G} (h : IsStronglyEmbedded H)
    (hproper : (X ⊓ H).subgroupOf X ≠ ⊤) (hev : Even (Nat.card (X ⊓ H : Subgroup G))) :
    IsStronglyEmbedded ((X ⊓ H).subgroupOf X) := by
  have hcard : Nat.card ((X ⊓ H).subgroupOf X : Subgroup X) = Nat.card (X ⊓ H : Subgroup G) := by
    have h1 := Subgroup.card_map_of_injective (K := (X ⊓ H).subgroupOf X)
      (f := X.subtype) Subtype.coe_injective
    rw [Subgroup.subgroupOf_map_subtype] at h1
    simpa using h1.symm
  refine ⟨hproper, by rw [hcard]; exact hev, ?_⟩
  intro y hy
  have hyH : (y : G) ∉ H := by
    intro hmem
    exact hy (Subgroup.mem_subgroupOf.mpr ⟨y.2, hmem⟩)
  have hle : (((X ⊓ H).subgroupOf X) ⊓ conj y ((X ⊓ H).subgroupOf X)).map X.subtype ≤
      H ⊓ conj (y : G) H := by
    refine le_inf ?_ ?_
    · rintro z ⟨w, hw, rfl⟩
      exact (Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hw).1).2
    · rintro z ⟨w, hw, rfl⟩
      have hw' : y⁻¹ * w * y ∈ (X ⊓ H).subgroupOf X :=
        mem_conj_iff.mp (Subgroup.mem_inf.mp hw).2
      have hmem : ((y⁻¹ * w * y : X) : G) ∈ H := (Subgroup.mem_subgroupOf.mp hw').2
      rw [mem_conj_iff]
      simpa using hmem
  have hdvd : Nat.card ((((X ⊓ H).subgroupOf X) ⊓ conj y ((X ⊓ H).subgroupOf X)).map X.subtype) ∣
      Nat.card (H ⊓ conj (y : G) H : Subgroup G) :=
    Subgroup.card_dvd_of_le hle
  have hodd := IsStronglyEmbedded.odd_card_inf_conj h hyH
  have hcard2 : Nat.card ((((X ⊓ H).subgroupOf X) ⊓ conj y ((X ⊓ H).subgroupOf X)).map X.subtype) =
      Nat.card (((X ⊓ H).subgroupOf X) ⊓ conj y ((X ⊓ H).subgroupOf X) : Subgroup X) :=
    Subgroup.card_map_of_injective (f := X.subtype) Subtype.coe_injective
  rw [hcard2] at hdvd
  exact Odd.of_dvd hdvd hodd

end Work.ThreePoints
