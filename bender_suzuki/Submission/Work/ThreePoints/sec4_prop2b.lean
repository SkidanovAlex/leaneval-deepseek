/-
# `Work.ThreePoints.sec4_prop2b` — Peterfalvi I Ch. II §4 Prop. 2 (b)

With `H` a strongly embedded subgroup of the finite group `G`, `t ∉ H` an involution,
`D = H ⊓ H^t = twoPoint H t`, `V = C_D(t) = centD H t` and `K = J(D,t)`, the source's
Proposition 2 (b) (p. 169) says:

> If `X ≤ D` and `|Ω_X| ≥ 3`, then `X` is conjugate in `D` to a subgroup of `V`.

Source proof.  By Prop. 1 there is `v ∈ Inv(H)` with `X ⊆ C_D(v)`; by Prop. 2 (a) there is
`u ∈ Inv(H)` with `V = C_D(u)`; by Ch. I §2 Prop. 2 the two-point stabiliser `D` acts
transitively by conjugation on `Inv(H)`, so there is `d ∈ D` with `u = v^d`, and then
`X^d ⊆ C_D(u) = V`.

This file contains

* the final bookkeeping (`sec4_prop2b_of_inputs`): from the two inputs — an involution
  `v ∈ Inv(H)` centralising `X`, and an involution `u ∈ Inv(H)` with `V = C_D(u)` — the
  statement follows, using `Work.ThreePoints.twoPoint_transitive_on_involutions`
  (Ch. I §2 Prop. 2 (b), proved in `Submission/Work/ThreePoints/TwoPointTransitive.lean`);
* Prop. 2 (a) from Prop. 1 (a) (`exists_involution_centD_eq_of_prop1a`), which is the first
  conjunct of `Work.ThreePoints.centD_eq_centralizer_of_involution` with Prop. 1 (a) supplied
  as a hypothesis (that file's own Prop. 1 (a) is a `hole`);
* Prop. 1 (a) `⟹` the centralising involution (`exists_involution_centralizing_of_prop1a`);
* the remaining input: Ch. II §4 Prop. 1 (a) in the `BrauerSuzukiProp`-conditional form
  (`prop1a_brsz`), for which `X` with `≥ 3` fixed points and `M ∈ Ω_X` have `|C_M(X)|` even.
-/
import Mathlib
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.Sec2b
import Submission.Work.ThreePoints.TwoPointTransitive
import Submission.Work.ThreePoints.Prop1aBrSz.even_card_centralizer_of_fixes_three_brsz
import Submission.Work.DoubleTransitivity.Sec4.prop2
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup_nofour

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G]

/-! ## 0. Self-contained elementary ingredients

(Copies of `Work.ThreePoints.exists_orderOf_two_of_even_card`,
`Work.ThreePoints.three_le_ncard_fixedPts_centD` and `Work.ThreePoints.ncard_invertedBy_le_index`
from `Submission/Work/ThreePoints/centD_eq_centralizer_of_involution.lean`, repeated here so that
this file's import closure is free of `hole`; the last one is proved by orbit–stabiliser instead
of via the injectivity of `y ↦ y⁻¹ u y`.) -/

/-- An even-order subgroup contains an element of order `2` (Cauchy for `p = 2`). -/
theorem exists_orderOf_two_of_even_card {C : Subgroup G} (h : Even (Nat.card C)) :
    ∃ u ∈ C, orderOf u = 2 := by
  haveI : Fintype ↥C := Fintype.ofFinite ↥C
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Fintype.card ↥C := by
    rw [Fintype.card_eq_nat_card]; exact even_iff_two_dvd.mp h
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card (G := ↥C) 2 h2
  exact ⟨(u : G), u.2, (orderOf_injective C.subtype C.subtype_injective u).trans hu⟩

/-- `V = C_D(t)` fixes at least the three points `H`, `tH` and the (unique) fixed point of the
involution `t` in `Ω = G ⧸ H`. -/
theorem three_le_ncard_fixedPts_centD {H : Subgroup G} (hH : IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) :
    3 ≤ (fixedPts H (centD H t)).ncard := by
  have ht2 : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two ht
  set V : Subgroup G := centD H t with hV
  have hVH : V ≤ H := by
    rw [hV, centD_eq]
    exact le_trans inf_le_left inf_le_left
  have hVt : V ≤ conj t H := by
    rw [hV, centD_eq]
    exact le_trans inf_le_left inf_le_right
  have hmem1 : ((1 : G) : G ⧸ H) ∈ fixedPts H V := by
    rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk, conj_one]
    exact hVH
  have hmemt : (t : G ⧸ H) ∈ fixedPts H V := by
    rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk]
    exact hVt
  obtain ⟨ω, hω⟩ := Set.ncard_eq_one.mp (ncard_fixedPts_zpowers hH ht)
  have hmemω : ω ∈ fixedPts H V := by
    rw [mem_fixedPts_iff_le_stabilizer]
    intro v hv
    rw [MulAction.mem_stabilizer_iff]
    have hvC : v ∈ Subgroup.centralizer ({t} : Set G) := by
      rw [hV, centD_eq] at hv
      exact (Subgroup.mem_inf.mp hv).2
    have hvt : v * t = t * v := Subgroup.mem_centralizer_singleton_iff.mp hvC
    have htω : t • ω = ω := by
      have hmem : ω ∈ fixedPts H (Subgroup.zpowers t) := by rw [hω]; exact Set.mem_singleton ω
      exact mem_fixedPts.mp hmem t (Subgroup.mem_zpowers t)
    have htvω : t • (v • ω) = v • ω := by rw [← mul_smul, ← hvt, mul_smul, htω]
    have hmem : v • ω ∈ fixedPts H (Subgroup.zpowers t) := by
      rw [mem_fixedPts_iff_le_stabilizer, Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
      exact htvω
    rw [hω] at hmem
    simpa using hmem
  have h1t : ((1 : G) : G ⧸ H) ≠ (t : G ⧸ H) := by
    intro hcon
    rw [QuotientGroup.eq] at hcon
    exact htH (by simpa using hcon)
  have h1notmem : ((1 : G) : G ⧸ H) ∉ fixedPts H (Subgroup.zpowers t) := by
    intro hmem
    have h := mem_fixedPts.mp hmem t (Subgroup.mem_zpowers t)
    have h' : ((1 : G) : G ⧸ H) = (t : G) := by simpa [smul_mk] using h.symm
    exact h1t h'
  have h1ω : ((1 : G) : G ⧸ H) ≠ ω := by
    intro hcon
    have hmem : ω ∈ fixedPts H (Subgroup.zpowers t) := by rw [hω]; exact Set.mem_singleton ω
    rw [← hcon] at hmem
    exact h1notmem hmem
  have htnotmem : (t : G ⧸ H) ∉ fixedPts H (Subgroup.zpowers t) := by
    intro hmem
    have h := mem_fixedPts.mp hmem t (Subgroup.mem_zpowers t)
    have h' : ((1 : G) : G ⧸ H) = (t : G ⧸ H) := by simpa [smul_mk, ht2] using h
    exact h1t h'
  have htω : (t : G ⧸ H) ≠ ω := by
    intro hcon
    have hmem : ω ∈ fixedPts H (Subgroup.zpowers t) := by rw [hω]; exact Set.mem_singleton ω
    rw [← hcon] at hmem
    exact htnotmem hmem
  have hsub : ({((1 : G) : G ⧸ H), (t : G ⧸ H), ω} : Set (G ⧸ H)) ⊆ fixedPts H V := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hmem1
    · exact hmemt
    · exact hmemω
  have hcard : ({((1 : G) : G ⧸ H), (t : G ⧸ H), ω} : Set (G ⧸ H)).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [h1t, h1ω]),
      Set.ncard_insert_of_notMem (by simp [htω]), Set.ncard_singleton]
  calc 3 = _ := hcard.symm
    _ ≤ (fixedPts H V).ncard := Set.ncard_le_ncard hsub

/-- **Peterfalvi I Ch. I §2 Lemma 1, quantitative form**, via orbit–stabiliser: for an involution
`u ∈ H`, `|K| ≤ |D : C_D(u)|` where `K = J(D,t)` and `D = H ∩ H^t`.  Indeed `D` acts
transitively by conjugation on `Inv(H)` (Ch. I §2 Prop. 2 (b)), the orbit of `u` is `Inv(H)`,
and its stabiliser is `C_D(u)`; orbit–stabiliser and `|K| = |Inv H|` (Ch. I §2 Prop. 2) give the
claim. -/
theorem ncard_invertedBy_le_index {H : Subgroup G} (hH : IsStronglyEmbedded H) {t u : G}
    (ht : orderOf t = 2) (htH : t ∉ H) (hu : u ∈ H) (hu2 : orderOf u = 2) :
    (invertedBy (twoPoint H t) t).ncard ≤
      ((twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf (twoPoint H t)).index := by
  classical
  set D : Subgroup G := twoPoint H t with hD
  letI : MulAction ↥D G := MulAction.compHom G (MulAut.conj.comp D.subtype)
  have hsmul : ∀ (x : ↥D) (g : G), x • g = (x : G) * g * (x : G)⁻¹ := by
    intro x g
    rw [show x • g = (MulAut.conj (x : G)) • g from rfl, MulAut.smul_def, MulAut.conj_apply]
  have hstab : MulAction.stabilizer ↥D u
      = (D ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf D := by
    ext x
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      rw [hsmul] at h
      exact ⟨x.2, mul_inv_eq_iff_eq_mul.mp h⟩
    · rintro ⟨-, hx⟩
      rw [hsmul]
      exact mul_inv_eq_iff_eq_mul.mpr hx
  have hxD : ∀ (x : ↥D), (x : G) ∈ H := fun x => (mem_twoPoint.mp x.2).1
  have hsmul' : ∀ (x : ↥D), x • u = (x : G) * u * (x : G)⁻¹ := fun x => hsmul x u
  have horbit : MulAction.orbit ↥D u = involutions (H : Set G) := by
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      change x • u ∈ involutions (H : Set G)
      rw [hsmul' x]
      exact ⟨H.mul_mem (H.mul_mem (hxD x) hu) (H.inv_mem (hxD x)),
        by rw [Work.ThmF.Bender.orderOf_conj_eq, hu2]⟩
    · rintro ⟨hwH, hw2⟩
      obtain ⟨d, hdD, hd⟩ :=
        twoPoint_transitive_on_involutions hH ht htH ⟨hu, hu2⟩ ⟨hwH, hw2⟩
      refine ⟨⟨d, hdD⟩, ?_⟩
      change d * u * d⁻¹ = w
      exact hd
  have hcard : (invertedBy D t).ncard
      = ((D ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf D).index := by
    calc (invertedBy D t).ncard
        = (Work.ThmF.Kset H t).ncard := rfl
      _ = (involutions (H : Set G)).ncard := Work.ThmF.Bender.cardKsetEqInv hH ht htH
      _ = (MulAction.orbit ↥D u).ncard := by rw [horbit]
      _ = (MulAction.stabilizer ↥D u).index := by rw [MulAction.index_stabilizer]
      _ = ((D ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf D).index := by rw [hstab]
  exact hcard.le

/-! ## 1. The bookkeeping

Source: `X^d ⊆ C_D(u) = V` for `d ∈ D` conjugating `u` to the involution `v` centralising `X`. -/

/-- If `v ∈ Inv(H)` centralises `X ≤ D` and `V = C_D(t)` is the centraliser in `D` of the
involution `u ∈ Inv(H)`, then `X` is `D`-conjugate into `V`: the element `d ∈ D` of
Ch. I §2 Prop. 2 (b) with `v^d = u` does the job. -/
theorem sec4_prop2b_of_inputs {H : Subgroup G} (hH : IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) {X : Subgroup G} (hX : X ≤ twoPoint H t)
    (hHeart : ∃ v : G, v ∈ H ∧ orderOf v = 2 ∧ ∀ x ∈ X, v * x = x * v)
    (hU : ∃ u : G, u ∈ involutions (H : Set G) ∧
        centD H t = twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G)) :
    ∃ d ∈ twoPoint H t,
      X.map (MulAut.conj d).toMonoidHom ≤ centD H t := by
  classical
  obtain ⟨v, hvH, hv2, hvcent⟩ := hHeart
  obtain ⟨u, huInv, hVeq⟩ := hU
  obtain ⟨huH, hu2⟩ := huInv
  -- Ch. I §2 Prop. 2 (b): `D` is transitive on `Inv(H)`.
  obtain ⟨d, hdD, hd⟩ := twoPoint_transitive_on_involutions hH ht htH ⟨hvH, hv2⟩ ⟨huH, hu2⟩
  refine ⟨d, hdD, ?_⟩
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  rw [mulAut_conj_toMonoidHom_apply, hVeq]
  refine ⟨?_, ?_⟩
  · -- `d * x * d⁻¹ ∈ D`
    exact (twoPoint H t).mul_mem ((twoPoint H t).mul_mem hdD (hX hx))
      ((twoPoint H t).inv_mem hdD)
  · -- `d * x * d⁻¹` centralises `u = d * v * d⁻¹`, which commutes with `x`
    change d * x * d⁻¹ ∈ Subgroup.centralizer ({u} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [← hd]
    have hcomm : x * v = v * x := (hvcent x hx).symm
    calc (d * x * d⁻¹) * (d * v * d⁻¹) = d * (x * v) * d⁻¹ := by group
      _ = d * (v * x) * d⁻¹ := by rw [hcomm]
      _ = (d * v * d⁻¹) * (d * x * d⁻¹) := by group

/-! ## 2. Ch. II §4 Prop. 1 (a) `⟹` the centralising involution

`C_H(X)` has even order, so it contains an involution, which centralises `X`. -/

/-- Ch. II §4 Prop. 1 (a) gives `Even |C_H(X)|` for `X ≤ H` with `≥ 3` fixed points; an
involution of `C_H(X)` (Cauchy) centralises `X`. -/
theorem exists_involution_centralizing_of_prop1a {H : Subgroup G} (hH : IsStronglyEmbedded H)
    {X : Subgroup G} (hX3 : 3 ≤ (fixedPts H X).ncard) (hXH : X ≤ H)
    (hProp1a : ∀ {X' M' : Subgroup G}, 3 ≤ (fixedPts H X').ncard →
      (∃ g : G, M' = conj g H) → X' ≤ M' →
      Even (Nat.card (M' ⊓ Subgroup.centralizer (X' : Set G) : Subgroup G))) :
    ∃ v : G, v ∈ H ∧ orderOf v = 2 ∧ ∀ x ∈ X, v * x = x * v := by
  have hev : Even (Nat.card (H ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) :=
    hProp1a hX3 ⟨1, (conj_one H).symm⟩ hXH
  obtain ⟨v, hv_mem, hv2⟩ := exists_orderOf_two_of_even_card hev
  refine ⟨v, (Subgroup.mem_inf.mp hv_mem).1, hv2, ?_⟩
  intro x hx
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hv_mem).2 x hx).symm

/-! ## 3. Ch. II §4 Prop. 1 (a) `⟹` Prop. 2 (a)

`V = C_D(t)` fixes the three points `H`, `H^t`, `H(t)`, so `C_H(V)` is even and contains an
involution `u` centralising `V`; then `V ≤ C_D(u)` and `|C_D(u)| ≤ |V|` by Ch. I §2 Lemma 1
(`|K| ≤ |u^D|`), so `V = C_D(u)`.  This is the first conjunct of
`Work.ThreePoints.centD_eq_centralizer_of_involution` with Prop. 1 (a) supplied as a hypothesis
instead of that file's `hole`. -/
theorem exists_involution_centD_eq_of_prop1a {H : Subgroup G} (hH : IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H)
    (hProp1a : ∀ {X' M' : Subgroup G}, 3 ≤ (fixedPts H X').ncard →
      (∃ g : G, M' = conj g H) → X' ≤ M' →
      Even (Nat.card (M' ⊓ Subgroup.centralizer (X' : Set G) : Subgroup G))) :
    ∃ u : G, u ∈ involutions (H : Set G) ∧
      centD H t = twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G) := by
  classical
  have hV3 : 3 ≤ (fixedPts H (centD H t)).ncard := three_le_ncard_fixedPts_centD hH ht htH
  have hVH : (centD H t : Subgroup G) ≤ H := by
    rw [centD_eq, twoPoint_eq]
    exact le_trans inf_le_left inf_le_left
  have hev : Even (Nat.card
      (H ⊓ Subgroup.centralizer (centD H t : Set G) : Subgroup G)) :=
    hProp1a hV3 ⟨1, (conj_one H).symm⟩ hVH
  obtain ⟨u, hu_mem, hu2⟩ := exists_orderOf_two_of_even_card hev
  have huH : u ∈ H := (Subgroup.mem_inf.mp hu_mem).1
  have huC : u ∈ Subgroup.centralizer (centD H t : Set G) := (Subgroup.mem_inf.mp hu_mem).2
  refine ⟨u, ⟨huH, hu2⟩, ?_⟩
  have hVle : (centD H t : Subgroup G) ≤
      twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G) := by
    refine le_inf inf_le_left ?_
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp huC x hx
  have hcard_le : Nat.card (twoPoint H t ⊓
        Subgroup.centralizer ({u} : Set G) : Subgroup G)
      ≤ Nat.card (centD H t : Subgroup G) := by
    have hindex := ncard_invertedBy_le_index hH ht htH huH hu2
    have hCeq : Nat.card ((twoPoint H t ⊓
          Subgroup.centralizer ({u} : Set G)).subgroupOf
          (twoPoint H t))
        = Nat.card (twoPoint H t ⊓
          Subgroup.centralizer ({u} : Set G) : Subgroup G) :=
      Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe
          (inf_le_left : _ ≤ twoPoint H t)).toEquiv
    have hDcard' : Nat.card (twoPoint H t : Subgroup G)
        = ((twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf
              (twoPoint H t)).index
          * Nat.card (twoPoint H t ⊓
              Subgroup.centralizer ({u} : Set G) : Subgroup G) := by
      have h := Subgroup.card_mul_index
        ((twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf
          (twoPoint H t))
      rw [hCeq] at h
      exact h.symm.trans (Nat.mul_comm _ _)
    have hKpos : 0 < (invertedBy (twoPoint H t) t).ncard := by
      haveI : Fintype G := Fintype.ofFinite G
      exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨1, one_mem_invertedBy _ _⟩
    have hDcard : Nat.card (twoPoint H t : Subgroup G)
        = Nat.card (centD H t : Subgroup G) *
            (invertedBy (twoPoint H t) t).ncard :=
      card_twoPoint_eq_card_centD_mul_ncard_invertedBy hH ht htH
    refine Nat.le_of_mul_le_mul_left ?_ hKpos
    calc (invertedBy (twoPoint H t) t).ncard
            * Nat.card (twoPoint H t ⊓
                Subgroup.centralizer ({u} : Set G) : Subgroup G)
        ≤ ((twoPoint H t ⊓
              Subgroup.centralizer ({u} : Set G)).subgroupOf
              (twoPoint H t)).index
            * Nat.card (twoPoint H t ⊓
                Subgroup.centralizer ({u} : Set G) : Subgroup G) :=
          Nat.mul_le_mul_right _ hindex
      _ = Nat.card (twoPoint H t : Subgroup G) := hDcard'.symm
      _ = Nat.card (centD H t : Subgroup G) *
            (invertedBy (twoPoint H t) t).ncard := hDcard
      _ = (invertedBy (twoPoint H t) t).ncard
            * Nat.card (centD H t : Subgroup G) := Nat.mul_comm _ _
  exact Subgroup.eq_of_le_of_card_ge hVle hcard_le

/-! ## 3. Involution of `M` normalising `X` `⟹` Ch. II §4 Prop. 1 (a)

Source: `M` is strongly embedded, `X ≤ M ⊓ M₂` for a second fixed point `M₂ ≠ M` of `X`, and the
involution `u ∈ Inv(M)` normalises `X`; Theorem C says `u` centralises `X`, so `u` is an
involution of `M ⊓ C_G(X)`. -/
theorem even_card_of_involution_normalizing {H : Subgroup G} (hC : Submission.Blueprint.ThmCProp)
    (hS : Submission.Blueprint.Situation G) (hH : IsStronglyEmbedded H) {X M : Subgroup G}
    (hX3 : 3 ≤ (fixedPts H X).ncard)
    (hM : ∃ g : G, M = conj g H) (hXM : X ≤ M)
    (hu : ∃ u : G, u ∈ M ∧ u ∈ Subgroup.normalizer (X : Set G) ∧ orderOf u = 2) :
    Even (Nat.card (M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) := by
  classical
  obtain ⟨g₀, hg₀⟩ := hM
  obtain ⟨u, huM, huN, hu2⟩ := hu
  have hStab0 : MulAction.stabilizer G (g₀ : G ⧸ H) = M := by
    rw [hg₀, Work.ThreePoints.stabilizer_mk]
  have h2 : 1 < (fixedPts H X).ncard := by omega
  obtain ⟨ω₂, hω₂, hne⟩ := Set.exists_ne_of_one_lt_ncard h2 (g₀ : G ⧸ H)
  obtain ⟨g₂, hg₂⟩ := QuotientGroup.mk_surjective ω₂
  have hStab2 : MulAction.stabilizer G ω₂ = conj g₂ H := by
    rw [← hg₂, Work.ThreePoints.stabilizer_mk]
  have hX2 : X ≤ MulAction.stabilizer G ω₂ :=
    Work.ThreePoints.mem_fixedPts_iff_le_stabilizer.mp hω₂
  have hM2ne : MulAction.stabilizer G ω₂ ≠ M := by
    intro heq
    have hpt : (g₀ : G ⧸ H) = ω₂ := by
      rw [← hg₂]
      refine Work.ThreePoints.mk_eq_of_conj_eq hH ?_
      exact hg₀.symm.trans (hStab2.symm.trans heq).symm
    exact hne hpt.symm
  have hMstrong : IsStronglyEmbedded M := by
    rw [hg₀]; exact Work.ThreePoints.conj_stronglyEmbedded hH g₀
  obtain ⟨g, hgdef⟩ : ∃ g : G, g = g₂ * g₀⁻¹ := ⟨_, rfl⟩
  have hconjg : conj g M = MulAction.stabilizer G ω₂ := by
    rw [hgdef, hg₀, Work.DoubleTransitivity.conj_mul,
      Work.DoubleTransitivity.conj_inv_conj, hStab2]
  have hgnotMem : g ∉ M := by
    intro hgmem
    have h1 : conj g M = M := Work.ThreePoints.conj_eq_self_of_mem hgmem
    exact hM2ne (hconjg.symm.trans h1)
  -- Theorem C: `u` centralises `X`
  have hcent : ∀ x ∈ X, u * x = x * u :=
    hC G hS M hMstrong g hgnotMem u ⟨huM, hu2⟩ X (le_inf hXM (hconjg ▸ hX2)) huN
  refine even_iff_two_dvd.mpr ?_
  have hmem : u ∈ (M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) :=
    ⟨huM, Subgroup.mem_centralizer_iff.mpr (fun x hx => (hcent x hx).symm)⟩
  have hord : orderOf (⟨u, hmem⟩ :
      ↥(M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) = 2 := by
    rw [Subgroup.orderOf_mk]; exact hu2
  have hdvd := orderOf_dvd_natCard
    (⟨u, hmem⟩ : ↥(M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G))
  rwa [hord] at hdvd

/-! ## 3c. The remaining input: Ch. II §4 Prop. 1 (a) with the Brauer–Suzuki black box

Source (p. 168): "Let `X ≤ G` with `|Ω_X| ≥ 3`.  (a) If `M ∈ Ω_X`, `|C_M(X)|` is even."
The source proves it by induction on `|X|`: `X` has odd order hence is solvable, `Y = O^p(X) ⊊ X`
for a prime `p`, `P` a `p`-Sylow of `X` (`X = Y·P`), `F₁ = C_G(Y)·P`; by the induction hypothesis
for `Y` and Ch. I §2 Lemma 2 the map `M' ↦ F₁ ⊓ M'` is a bijection of `Ω_Y` onto a class `Ξ` of
proper Bender groups of `F₁`; a maximal `p`-subgroup `Q ⊇ P` of `F₁ ⊓ M` with `≥ 3` fixed points
in `Ξ` has an involution `u ∈ N(Q) ∩ F₁ ⊓ M` by Ch. I §4 Prop. 2; Theorem C makes `u` centralise
`Q ⊇ P`, and `u ∈ F₁` with `|F₁ : C_G(Y)|` a `p`-power (odd) forces `u ∈ C_G(Y)`, so
`u ∈ C_M(X)`.

This statement is proved by `Submission/Work/ThreePoints/P3NeBot/prop1a_brsz.lean` (with the
Brauer–Suzuki black box) and `Submission/Work/ThreePoints/Prop1aBrSz/
even_card_centralizer_of_fixes_three_brsz.lean` (with Ch. I §4 Prop. 2 as a hypothesis).
It is recorded here so that the rest of the reduction is available. -/
/-- **Peterfalvi I Ch. I §4 Prop. 2** (p. 156) in the form consumed by
`Work.ThreePoints.Prop1aBrSz.even_card_centralizer_of_fixes_three_brsz`: for a strongly embedded
`K ≤ F`, a prime `p ≠ 2` and a `p`-subgroup `Q ≤ K` maximal among the `p`-subgroups of `K` with at
least three fixed points of `F ⧸ K`, the normaliser `N_K(Q)` has even order.

`Work.DoubleTransitivity.Sec4.prop2` supplies `Even |N_F(Q) ⊓ K|` and
`card_normalizer_subgroupOf_eq_card_inf` identifies that cardinality with `|N_K(Q)|`. -/
theorem s4prop2_brsz (hBrSz : Submission.Blueprint.BrauerSuzukiProp) {F : Type} [Group F]
    [Finite F] {K : Subgroup F} (hK : LeanEval.GroupTheory.Defs.IsStronglyEmbedded K)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : Subgroup F} (hQK : Q ≤ K)
    (hQp : IsPGroup p Q) (hQ3 : 3 ≤ (Submission.Blueprint.fixedPts K Q).ncard)
    (hQmax : ∀ R : Subgroup F, Q ≤ R → R ≤ K → IsPGroup p R →
      3 ≤ (Submission.Blueprint.fixedPts K R).ncard → R = Q) :
    Even (Nat.card (Subgroup.normalizer (Q.subgroupOf K : Set K) : Subgroup K)) := by
  have hP : Work.DoubleTransitivity.MaxFixesThreeIn p K Q :=
    ⟨hQp, hQK, hQ3, fun R hRp hRK hR3 hQR => by
      rw [hQmax R hQR hRK hRp hR3]⟩
  have h := (Work.DoubleTransitivity.Sec4.prop2 hBrSz hK hp hp2 hP).2
  rw [inf_comm, ← card_normalizer_subgroupOf_eq_card_inf hQK] at h
  exact h

theorem prop1a_brsz {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hA : Submission.Blueprint.ThmAProp) (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    (hS : Submission.Blueprint.Situation G) {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {X M : Subgroup G}
    (hX3 : 3 ≤ (Submission.Blueprint.fixedPts H X).ncard)
    (hM : ∃ g : G, M = Submission.Blueprint.conj g H) (hXM : X ≤ M) :
    Even (Nat.card (M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) :=
  Prop1aBrSz.even_card_centralizer_of_fixes_three_brsz hFT hC
    (fun F _ _ K hK p hp hp2 Q hQK hQp hQ3 hQmax =>
      s4prop2_brsz (F := F) hBrSz hK hp hp2 hQK hQp hQ3 hQmax)
    hS hH hX3 hM hXM

/-! ## 4. The target -/

/-- Peterfalvi I Ch. II §4 Prop. 2 (b): if the subgroup `X ≤ D = H ⊓ H^t` fixes at least three
points of `Ω = G ⧸ H`, then `X` is conjugate in `D` to a subgroup of `V = C_D(t)`. -/
theorem sec4_prop2b {G : Type} [Group G] [Finite G] (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC : Submission.Blueprint.ThmCProp) (hA : Submission.Blueprint.ThmAProp)
    (hZJ : Submission.Blueprint.GlaubermanZJProp) (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    (hMod : Submission.Blueprint.ModelFactsProp) (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) {X : Subgroup G} (hX : X ≤ Submission.Blueprint.twoPoint H t)
    (hX3 : 3 ≤ (Submission.Blueprint.fixedPts H X).ncard) :
    ∃ d ∈ Submission.Blueprint.twoPoint H t,
      X.map (MulAut.conj d).toMonoidHom ≤ Submission.Blueprint.centD H t := by
  classical
  -- Ch. II §4 Prop. 1 (a), with the Brauer–Suzuki black box (Ch. I §4 Prop. 2 inside
  -- `F₁ = C_G(O^p(X))·P`): a subgroup with at least three fixed points has an even-order
  -- centraliser in every fixed point.
  have hProp1a : ∀ {X' M' : Subgroup G}, 3 ≤ (Submission.Blueprint.fixedPts H X').ncard →
      (∃ g : G, M' = Submission.Blueprint.conj g H) → X' ≤ M' →
      Even (Nat.card (M' ⊓ Subgroup.centralizer (X' : Set G) : Subgroup G)) := by
    intro X' M' hX3' hM' hXM'
    exact prop1a_brsz (G := G) hFT hC hA hBrSz hS hH hX3' hM' hXM'
  exact sec4_prop2b_of_inputs hH ht htH hX
    (exists_involution_centralizing_of_prop1a hH hX3 (le_trans hX inf_le_left) hProp1a)
    (exists_involution_centD_eq_of_prop1a hH ht htH hProp1a)

end Work.ThreePoints
