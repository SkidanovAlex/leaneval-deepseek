import Mathlib
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.Sec2
import Submission.Work.ThreePoints.card_eq_mul_ncard_invertedBy
import Submission.Work.NormalComplement.BenderPrelimAux
import Submission.Work.DoubleTransitivity.Sec4.prop2
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup_nofour
import Submission.Work.ThreePoints.three_involutions_even
import Submission.Work.ThreePoints.Prop1aBrSz.even_card_centralizer_of_fixes_three_brsz

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThreePoints.centD_eq_centralizer_of_involution`

Peterfalvi I, Ch. II §4, **Proposition 2 (a) and (c)** (p. 169).  In the situation (B0)–(B2)
(`Submission.Blueprint.Situation G`) with a strongly embedded subgroup `H`, an involution
`t ∉ H`, `D = H ∩ H^t = twoPoint H t`, `V = C_D(t) = centD H t` and `K = J(D,t) =
invertedBy (twoPoint H t) t`:

* (a) there is an involution `u ∈ H` with `V = C_D(u)`, i.e. `centD H t = D ⊓ C_G(u)`;
* (c) every non-trivial `x ∈ K` fixes exactly two points of `Ω = G ⧸ H`.

The two clauses rest on

* Ch. II §4 Prop. 1(a) (`Work.ThreePoints.prop1a_clean` below, the source's induction on `|X|`
  of `Work.ThreePoints.Prop1aBrSz.even_card_centralizer_of_fixes_three_brsz` fed with Ch. I §4
  Prop. 2 in the form `even_card_normalizer_of_maximal_p_subgroup_brsz`): a subgroup `X` fixing
  at least three points has `|C_M(X)|` even for every fixed point `M`;
* Ch. I §2 Lemma 1 (`inv_conj_injective_on_invertedBy` below): for an involution `v ∈ H` the map
  `y ↦ y⁻¹ v y` is injective on `K`, so that `|K| ≤ |v^D|`; combined with App. I (1)(b)
  (`card_eq_mul_ncard_invertedBy`, `|D| = |V| · |K|`) this gives `|C_D(u)| ≤ |V|` for the `u` of
  (a), hence `V = C_D(u)`; the same injection with `v^x = v` forces `x = 1` in (c).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G]

/-! ## Peterfalvi I Ch. I §2 Lemma 1: injectivity of `y ↦ y⁻¹ v y` on `J(D,t)` -/

/-- **Peterfalvi I Ch. I §2 Lemma 1 (the injectivity ingredient).**  For an involution `v ∈ H` and
an involution `t ∉ H`, the map `y ↦ y⁻¹ * v * y` is injective on `K = J(D,t)`, `D = H ∩ H^t`.

Indeed if `y₁⁻¹ v y₁ = y₂⁻¹ v y₂` with `y₁,y₂ ∈ K`, then conjugating by `t` (which inverts each
`yᵢ`) gives `(y₁t)⁻¹ v (y₁t) = (y₂t)⁻¹ v (y₂t)`; since `y₁t`, `y₂t` are involutions outside `H`
conjugating `v` to the same involution outside `H`, Ch. I §2 Prop. 1(a) (uniqueness of the
conjugating involution, `Work.NormalComplement.existsUnique_involution_conj`) forces
`y₁t = y₂t`, whence `y₁ = y₂`. -/
theorem inv_conj_injective_on_invertedBy {H : Subgroup G} (hH : IsStronglyEmbedded H) {t v : G}
    (ht : orderOf t = 2) (htH : t ∉ H) (hv : v ∈ H) (hv2 : orderOf v = 2) :
    ∀ y₁ ∈ invertedBy (twoPoint H t) t, ∀ y₂ ∈ invertedBy (twoPoint H t) t,
      y₁⁻¹ * v * y₁ = y₂⁻¹ * v * y₂ → y₁ = y₂ := by
  have ht2 : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two ht
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  intro y₁ hy₁ y₂ hy₂ heq
  have hy1H : y₁ ∈ H := (mem_twoPoint.mp hy₁.1).1
  have hy2H : y₂ ∈ H := (mem_twoPoint.mp hy₂.1).1
  have hyt1 : t * y₁ * t = y₁⁻¹ := by simpa [htinv] using hy₁.2
  have hyt2 : t * y₂ * t = y₂⁻¹ := by simpa [htinv] using hy₂.2
  have hinv1 : (y₁ * t) * (y₁ * t) = 1 := by
    rw [show (y₁ * t) * (y₁ * t) = y₁ * (t * y₁ * t) by group, hyt1, mul_inv_cancel]
  have hinv2 : (y₂ * t) * (y₂ * t) = 1 := by
    rw [show (y₂ * t) * (y₂ * t) = y₂ * (t * y₂ * t) by group, hyt2, mul_inv_cancel]
  have hzinv1 : (y₁ * t)⁻¹ = y₁ * t := (eq_inv_of_mul_eq_one_left hinv1).symm
  have hzinv2 : (y₂ * t)⁻¹ = y₂ * t := (eq_inv_of_mul_eq_one_left hinv2).symm
  have hne1 : y₁ * t ≠ 1 := by
    intro h
    have : t = y₁⁻¹ := eq_inv_of_mul_eq_one_right h
    exact htH (this ▸ H.inv_mem hy1H)
  have hne2 : y₂ * t ≠ 1 := by
    intro h
    have : t = y₂⁻¹ := eq_inv_of_mul_eq_one_right h
    exact htH (this ▸ H.inv_mem hy2H)
  have ho1 : orderOf (y₁ * t) = 2 := orderOf_eq_two_of hne1 hinv1
  have ho2 : orderOf (y₂ * t) = 2 := orderOf_eq_two_of hne2 hinv2
  have hzt1H : y₁ * t ∉ H := by
    intro h
    have h' : t = y₁⁻¹ * (y₁ * t) := by group
    exact htH (by rw [h']; exact H.mul_mem (H.inv_mem hy1H) h)
  have hzt2H : y₂ * t ∉ H := by
    intro h
    have h' : t = y₂⁻¹ * (y₂ * t) := by group
    exact htH (by rw [h']; exact H.mul_mem (H.inv_mem hy2H) h)
  set w : G := (y₁ * t)⁻¹ * v * (y₁ * t) with hw
  have hkey : (y₁ * t)⁻¹ * v * (y₁ * t) = (y₂ * t)⁻¹ * v * (y₂ * t) := by
    rw [show (y₁ * t)⁻¹ * v * (y₁ * t) = t⁻¹ * (y₁⁻¹ * v * y₁) * t by group,
        show (y₂ * t)⁻¹ * v * (y₂ * t) = t⁻¹ * (y₂⁻¹ * v * y₂) * t by group, heq]
  have hw2 : orderOf w = 2 := by
    have h := orderOf_injective (MulAut.conj (y₁ * t)).toMonoidHom
      (MulAut.conj (y₁ * t)).injective v
    have h2 : w = (MulAut.conj (y₁ * t)).toMonoidHom v := by
      simp only [MulEquiv.coe_toMonoidHom]
      rw [hw, MulAut.conj_apply, hzinv1]
    rw [h2, h, hv2]
  have hwH : w ∉ H := by
    intro hwmem
    have hwconj : w ∈ conj (y₁ * t) H := by
      have h := Subgroup.mem_map_of_mem (MulAut.conj (y₁ * t)).toMonoidHom hv
      have h2 : (MulAut.conj (y₁ * t)).toMonoidHom v = w := by
        simp only [MulEquiv.coe_toMonoidHom]
        rw [MulAut.conj_apply, hw, hzinv1]
      rwa [h2] at h
    have hwinf : w ∈ (H ⊓ conj (y₁ * t) H : Subgroup G) := ⟨hwmem, hwconj⟩
    have hodd := IsStronglyEmbedded.odd_card_inf_conj hH hzt1H
    have hdvd : 2 ∣ Nat.card (H ⊓ conj (y₁ * t) H : Subgroup G) := by
      have hle : Subgroup.zpowers w ≤ (H ⊓ conj (y₁ * t) H : Subgroup G) :=
        Subgroup.zpowers_le.mpr hwinf
      have h1 : Nat.card (Subgroup.zpowers w) ∣
          Nat.card (H ⊓ conj (y₁ * t) H : Subgroup G) := Subgroup.card_dvd_of_le hle
      rwa [Nat.card_zpowers, hw2] at h1
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  obtain ⟨z, -, hzuniq⟩ := Work.NormalComplement.existsUnique_involution_conj hH hv2 hv hw2 hwH
  have h1 : y₁ * t = z := hzuniq (y₁ * t) ⟨ho1, hzt1H, by rw [hw, hzinv1]⟩
  have h2 : y₂ * t = z := hzuniq (y₂ * t) ⟨ho2, hzt2H, by rw [hw, hkey, hzinv2]⟩
  exact (mul_right_cancel (h2.trans h1.symm)).symm

/-! ## The counting bound `|K| ≤ |D : C_D(u)|` -/

/-- **Peterfalvi I Ch. I §2 Lemma 1, quantitative form**: for an involution `u ∈ H`,
`|K| ≤ |D : C_D(u)|` where `K = J(D,t)` and `D = H ∩ H^t`.  The map `y ↦ y⁻¹ u y` is injective
on `K` (previous lemma) and lands in the orbit of `u` under conjugation by `D`, whose size is
`|D : C_D(u)|`. -/
theorem ncard_invertedBy_le_index {H : Subgroup G} (hH : IsStronglyEmbedded H) {t u : G}
    (ht : orderOf t = 2) (htH : t ∉ H) (hu : u ∈ H) (hu2 : orderOf u = 2) :
    (invertedBy (twoPoint H t) t).ncard ≤
      ((twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf (twoPoint H t)).index := by
  classical
  set D : Subgroup G := twoPoint H t with hD
  have hinj : Set.InjOn (fun y : G => y⁻¹ * u * y) (invertedBy D t : Set G) := by
    intro y₁ hy₁ y₂ hy₂ heq
    exact inv_conj_injective_on_invertedBy hH ht htH hu hu2 y₁ hy₁ y₂ hy₂ heq
  have hKcard : ((fun y : G => y⁻¹ * u * y) '' (invertedBy D t : Set G)).ncard
      = (invertedBy D t : Set G).ncard := hinj.ncard_image
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
      exact ⟨x.2, (mul_inv_eq_iff_eq_mul.mp h)⟩
    · rintro ⟨-, hx⟩
      rw [hsmul]
      exact mul_inv_eq_iff_eq_mul.mpr hx
  have hsub : ((fun y : G => y⁻¹ * u * y) '' (invertedBy D t : Set G))
      ⊆ MulAction.orbit ↥D u := by
    rintro w ⟨y, hy, rfl⟩
    rw [MulAction.mem_orbit_iff]
    refine ⟨⟨y⁻¹, D.inv_mem hy.1⟩, ?_⟩
    rw [hsmul]
    group
  calc (invertedBy D t).ncard
      = ((fun y : G => y⁻¹ * u * y) '' (invertedBy D t : Set G)).ncard := hKcard.symm
    _ ≤ (MulAction.orbit ↥D u).ncard := Set.ncard_le_ncard hsub
    _ = ((D ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf D).index := by
          rw [← hstab, MulAction.index_stabilizer]

/-! ## Two elementary ingredients -/

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
    have h' : ((1 : G) : G ⧸ H) = (t : G ⧸ H) := by simpa [smul_mk] using h.symm
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

/-! ## Ch. I §4 Prop. 2, and Ch. II §4 Prop. 1(a) derived from it -/

/-- **Peterfalvi I Ch. I §4 Prop. 2**, in the exact form in which this file consumes it: for a
finite group `F` with a strongly embedded subgroup `K`, an odd prime `p` and a `p`-subgroup
`Q ≤ K` maximal among the `p`-subgroups of `K` fixing at least three points of `F ⧸ K`, the
normaliser `N_K(Q)` has even order.

The mathematical content is the source's `Work.DoubleTransitivity.Sec4.prop2` (`𝓡_p`-dichotomy:
if `𝓡_p = ∅` then `F` is `2`-transitive on `F ⧸ K` and App. II (6) + Ch. I §3 Prop. 1 apply; if
`𝓡_p ≠ ∅` then Ch. I §4 Prop. 1(b) excludes `p`-subgroups with exactly two fixed points), with
the Brauer–Suzuki hypothesis discharged by `Work.ThreePoints.brauerSuzukiProp_from_cases`.  The
only point of the statement below is the bookkeeping `N_K(Q) ≅ K ⊓ N_F(Q)`. -/
theorem even_card_normalizer_of_maximal_p_subgroup_brsz
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) :
    ∀ (F : Type) [Group F] [Finite F] {K : Subgroup F},
      LeanEval.GroupTheory.Defs.IsStronglyEmbedded K →
      ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ Q : Subgroup F, Q ≤ K → IsPGroup p Q →
        3 ≤ (Submission.Blueprint.fixedPts K Q).ncard →
        (∀ R : Subgroup F, Q ≤ R → R ≤ K → IsPGroup p R →
          3 ≤ (Submission.Blueprint.fixedPts K R).ncard → R = Q) →
        Even (Nat.card (Subgroup.normalizer (Q.subgroupOf K : Set K) : Subgroup K)) := by
  intro F _ _ K hK p hp hp2 Q hQK hQp hQ3 hQmax
  have hP : Work.DoubleTransitivity.MaxFixesThreeIn p K Q :=
    ⟨hQp, hQK, hQ3, fun Q' hQ'p hQ'K hQ'3 hQQ' =>
      le_of_eq (hQmax Q' hQQ' hQ'K hQ'p hQ'3)⟩
  have hmain := (Work.DoubleTransitivity.Sec4.prop2 hBrSz hK hp hp2 hP).2
  have hcard : Nat.card ↥(Subgroup.normalizer (Q.subgroupOf K : Set K)) =
      Nat.card ↥(Subgroup.normalizer (Q : Set F) ⊓ K) := by
    rw [card_normalizer_subgroupOf_eq_card_inf hQK, inf_comm]
  rwa [hcard]

/-- **Peterfalvi I Ch. II §4 Prop. 1(a)** (p. 168) in the form needed here: under (B0)–(B2), if
`X ≤ M = H^g` fixes at least three points of `Ω = G ⧸ H`, then `|C_M(X)|` is even.

This is `Work.ThreePoints.Prop1aBrSz.even_card_centralizer_of_fixes_three_brsz` (the source's
induction on `|X|`) fed with Ch. I §4 Prop. 2 in the form
`even_card_normalizer_of_maximal_p_subgroup_brsz`, whose Brauer–Suzuki hypothesis is discharged
by the (already proved) `Work.ThreePoints.brauerSuzukiProp_from_cases`. -/
theorem prop1a_clean {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hA : Submission.Blueprint.ThmAProp) (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {X M : Subgroup G}
    (hX3 : 3 ≤ (Submission.Blueprint.fixedPts H X).ncard)
    (hM : ∃ g : G, M = Submission.Blueprint.conj g H) (hXM : X ≤ M) :
    Even (Nat.card (M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) :=
  Work.ThreePoints.Prop1aBrSz.even_card_centralizer_of_fixes_three_brsz hFT hC
    (even_card_normalizer_of_maximal_p_subgroup_brsz
      Work.ThreePoints.brauerSuzukiProp_from_cases)
    hS hH hX3 hM hXM

/-! ## The target -/

/-- Peterfalvi I Ch. II §4 Prop. 2 (a) and (c): under (B0)–(B2), for an involution `t ∉ H`,
`V = C_D(t)` is the centraliser in `D` of some involution of `H`, and every non-trivial element of
`K = J(D,t)` fixes exactly two points of `Ω = G ⧸ H` (namely `H` and `H^t`). -/
theorem centD_eq_centralizer_of_involution {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hA : Submission.Blueprint.ThmAProp) (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) :
    (∃ u ∈ Submission.Blueprint.involutions (H : Set G),
        Submission.Blueprint.centD H t = Submission.Blueprint.twoPoint H t ⊓
          Subgroup.centralizer ({u} : Set G)) ∧
    (∀ x ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t, x ≠ 1 →
        (Submission.Blueprint.fixedPts H (Subgroup.zpowers x)).ncard = 2) := by
  classical
  have ht2 : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two ht
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  -- `t` normalises `D = H ∩ H^t`
  have htD : t ∈ Subgroup.normalizer (twoPoint H t : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    show conj t (twoPoint H t) = twoPoint H t
    rw [twoPoint_eq, conj_inf, ← conj_mul, ht2, conj_one, inf_comm]
  have hoddD : Odd (Nat.card (twoPoint H t : Subgroup G)) :=
    IsStronglyEmbedded.odd_card_inf_conj hH htH
  have hDcard : Nat.card (twoPoint H t : Subgroup G)
      = Nat.card (centD H t : Subgroup G) * (invertedBy (twoPoint H t) t).ncard :=
    card_eq_mul_ncard_invertedBy (X := twoPoint H t) (t := t) ht hoddD htD
  constructor
  · -- ### Prop. 2 (a)
    have hEven : Even (Nat.card (H ⊓ Subgroup.centralizer (centD H t : Set G) : Subgroup G)) :=
      prop1a_clean hFT hC hA hS hH
        (three_le_ncard_fixedPts_centD hH ht htH) ⟨1, by rw [conj_one]⟩
        (le_trans inf_le_left inf_le_left)
    obtain ⟨u, hu_mem, hu2⟩ := exists_orderOf_two_of_even_card hEven
    have huH : u ∈ H := (Subgroup.mem_inf.mp hu_mem).1
    have huC : u ∈ Subgroup.centralizer (centD H t : Set G) := (Subgroup.mem_inf.mp hu_mem).2
    have hVle : (centD H t : Subgroup G) ≤ twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G) := by
      refine le_inf inf_le_left ?_
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp huC x hx
    have hcard_le : Nat.card (twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G)
        ≤ Nat.card (centD H t : Subgroup G) := by
      have hindex := ncard_invertedBy_le_index hH ht htH huH hu2
      have hCeq : Nat.card ((twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf
            (twoPoint H t))
          = Nat.card (twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (inf_le_left : _ ≤ twoPoint H t)).toEquiv
      have hDcard' : Nat.card (twoPoint H t : Subgroup G)
          = ((twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf
                (twoPoint H t)).index
            * Nat.card (twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) := by
        have h := Subgroup.card_mul_index
          ((twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf (twoPoint H t))
        rw [hCeq] at h
        exact h.symm.trans (Nat.mul_comm _ _)
      have hKpos : 0 < (invertedBy (twoPoint H t) t).ncard := by
        haveI : Fintype G := Fintype.ofFinite G
        exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨1, one_mem_invertedBy _ _⟩
      refine Nat.le_of_mul_le_mul_left ?_ hKpos
      calc (invertedBy (twoPoint H t) t).ncard
              * Nat.card (twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G)
          ≤ ((twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf
                (twoPoint H t)).index
              * Nat.card (twoPoint H t ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) :=
            Nat.mul_le_mul_right _ hindex
        _ = Nat.card (twoPoint H t : Subgroup G) := hDcard'.symm
        _ = Nat.card (centD H t : Subgroup G) * (invertedBy (twoPoint H t) t).ncard := hDcard
        _ = (invertedBy (twoPoint H t) t).ncard * Nat.card (centD H t : Subgroup G) :=
            Nat.mul_comm _ _
    refine ⟨u, ⟨huH, hu2⟩, Subgroup.eq_of_le_of_card_ge hVle hcard_le⟩
  · -- ### Prop. 2 (c)
    intro x hx hx1
    have hxD : x ∈ twoPoint H t := hx.1
    have hxH : x ∈ H := (mem_twoPoint.mp hxD).1
    have hxt : x ∈ conj t H := mem_conj_iff.mpr (mem_twoPoint.mp hxD).2
    have hmem1 : ((1 : G) : G ⧸ H) ∈ fixedPts H (Subgroup.zpowers x) := by
      rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk, conj_one]
      exact Subgroup.zpowers_le.mpr hxH
    have hmemt : (t : G ⧸ H) ∈ fixedPts H (Subgroup.zpowers x) := by
      rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk]
      exact Subgroup.zpowers_le.mpr hxt
    have h1t : ((1 : G) : G ⧸ H) ≠ (t : G ⧸ H) := by
      intro hcon
      rw [QuotientGroup.eq] at hcon
      exact htH (by simpa using hcon)
    refine le_antisymm ?_ ?_
    · -- `≤ 2`: otherwise Ch. II §4 Prop. 1(a) produces an involution of `H` centralising `x`
      by_contra hle
      have hge3 : 3 ≤ (fixedPts H (Subgroup.zpowers x)).ncard := by omega
      have hEven : Even (Nat.card
          (H ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) : Subgroup G)) :=
        prop1a_clean hFT hC hA hS hH hge3 ⟨1, by rw [conj_one]⟩
          (Subgroup.zpowers_le.mpr hxH)
      obtain ⟨v, hv_mem, hv2⟩ := exists_orderOf_two_of_even_card hEven
      have hvH : v ∈ H := (Subgroup.mem_inf.mp hv_mem).1
      have hvC : v ∈ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G) :=
        (Subgroup.mem_inf.mp hv_mem).2
      have hvx : x * v = v * x :=
        Subgroup.mem_centralizer_iff.mp hvC x (Subgroup.mem_zpowers x)
      have heq : x⁻¹ * v * x = (1 : G)⁻¹ * v * 1 := by
        rw [inv_one, one_mul, mul_one, mul_assoc, ← hvx, ← mul_assoc,
          inv_mul_cancel, one_mul]
      have hx1' : x = 1 :=
        inv_conj_injective_on_invertedBy hH ht htH hvH hv2 x hx 1 (one_mem_invertedBy _ _) heq
      exact hx1 hx1'
    · have h2 : ({((1 : G) : G ⧸ H), (t : G ⧸ H)} : Set (G ⧸ H)).ncard = 2 :=
        Set.ncard_pair h1t
      calc 2 = _ := h2.symm
        _ ≤ (fixedPts H (Subgroup.zpowers x)).ncard :=
            Set.ncard_le_ncard (by
              intro y hy
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
              rcases hy with rfl | rfl
              · exact hmem1
              · exact hmemt)

end Work.ThreePoints
