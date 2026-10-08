import Mathlib
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.ch1_lem2
import Submission.Work.ThreePoints.prop1a_even_card_centralizer
import Submission.Work.ThreePoints.stronglyEmbedded_subgroupOf_inf_conj
import Submission.Work.ThreePoints.odd_card_of_fixes_three

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints.Prop1aBrSz

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G]

/-! ## Auxiliary lemmas -/

/-- A nontrivial finite solvable group has a proper normal subgroup whose quotient is cyclic of
prime order: take a maximal proper normal subgroup `N`; then `H ⧸ N` is simple and solvable. -/
theorem exists_normal_prime_index {H : Type} [Group H] [Finite H]
    (hsolv : Group.IsSolvable H) (hcard : 1 < Nat.card H) :
    ∃ N : Subgroup H, N.Normal ∧ (Nat.card (H ⧸ N)).Prime := by
  classical
  haveI : Fintype H := Fintype.ofFinite H
  have hcard' : 1 < Fintype.card H := by rwa [← Nat.card_eq_fintype_card]
  haveI : Nontrivial H := Fintype.one_lt_card_iff_nontrivial.mp hcard'
  have hbot : (⊥ : Subgroup H) ≠ ⊤ := by
    intro h
    obtain ⟨a, ha⟩ := exists_ne (1 : H)
    exact ha (Subgroup.mem_bot.mp (h ▸ Subgroup.mem_top a))
  set S : Set (Subgroup H) := {N : Subgroup H | N.Normal ∧ N ≠ ⊤} with hS
  have hne : ((fun N : Subgroup H => Nat.card N) '' S).Nonempty :=
    ⟨Nat.card (⊥ : Subgroup H), ⊥, ⟨Subgroup.normal_bot, hbot⟩, rfl⟩
  have hbdd : BddAbove ((fun N : Subgroup H => Nat.card N) '' S) :=
    ⟨Nat.card H, by
      rintro x ⟨N, -, rfl⟩
      exact Nat.card_le_card_of_injective (fun y : ↥N => (y : H)) Subtype.coe_injective⟩
  obtain ⟨N, hNS, hNsSup⟩ := Nat.sSup_mem hne hbdd
  have hNmax : ∀ M ∈ S, Nat.card M ≤ Nat.card N := by
    intro M hM
    change (fun A : Subgroup H => Nat.card A) M ≤ (fun A : Subgroup H => Nat.card A) N
    rw [hNsSup]
    exact le_csSup hbdd ⟨M, hM, rfl⟩
  have hmax : ∀ M : Subgroup H, M.Normal → N < M → M = ⊤ := by
    intro M hMn hlt
    by_contra hMt
    have h1 := hNmax M ⟨hMn, hMt⟩
    have h2 : Nat.card N < Nat.card M := Subgroup.card_lt_of_lt hlt
    omega
  have hNn : N.Normal := hNS.1
  have hNt : N ≠ ⊤ := hNS.2
  haveI : N.Normal := hNn
  have hnt : Nontrivial (H ⧸ N) := by
    obtain ⟨a, ha⟩ : ∃ a : H, a ∉ N := by
      by_contra h
      push_neg at h
      exact hNt (le_antisymm le_top fun x _ => h x)
    exact ⟨(a : H ⧸ N), 1, fun hc => ha ((QuotientGroup.eq_one_iff a).mp hc)⟩
  have hprop : ∀ K : Subgroup (H ⧸ N), K.Normal → K = ⊥ ∨ K = ⊤ := by
    intro K hKn
    haveI : K.Normal := hKn
    set M : Subgroup H := K.comap (QuotientGroup.mk' N) with hMdef
    have hMn : M.Normal := hKn.comap (QuotientGroup.mk' N)
    have hNleM : N ≤ M := by
      intro x hx
      rw [hMdef, Subgroup.mem_comap]
      have hx1 : (QuotientGroup.mk' N) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      rw [hx1]
      exact K.one_mem
    have hKM : K = M.map (QuotientGroup.mk' N) :=
      (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) K).symm
    rcases eq_or_lt_of_le hNleM with hEq | hLt
    · left
      rw [hKM, ← hEq]
      ext y
      rw [Subgroup.mem_map, Subgroup.mem_bot]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (QuotientGroup.eq_one_iff x).mpr hx
      · intro hy
        exact ⟨1, N.one_mem, by rw [map_one, hy]⟩
    · right
      rw [hKM, hmax M hMn hLt,
        Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
  have hsimple : IsSimpleGroup (H ⧸ N) :=
    { toNontrivial := hnt, eq_bot_or_eq_top_of_normal := fun K _ => hprop K ‹_› }
  have hsolv' : Group.IsSolvable (H ⧸ N) := inferInstance
  refine ⟨N, hNn, ?_⟩
  haveI : IsMulCommutative (H ⧸ N) :=
    IsMulCommutative.of_comm (IsSimpleGroup.comm_iff_isSolvable.mpr hsolv')
  exact Group.is_simple_iff_prime_card.mp hsimple

/-- The data of the first step of the induction of Peterfalvi I Ch. II §4 Prop. 1 (a): for an
odd-order solvable subgroup `X ≠ 1` of `G`, a normal-in-`X` subgroup `Y < X` with `|X : Y|` a
prime `p ≠ 2`, together with a `p`-subgroup `P ≤ X` with `X ≤ Y ⊔ P` (indeed `X = Y · P`). -/
theorem exists_normal_sylow_data {G : Type} [Group G] [Finite G] {X : Subgroup G}
    (hodd : Odd (Nat.card X)) (hsolv : Group.IsSolvable ↥X) (hcard : 1 < Nat.card X) :
    ∃ (p : ℕ) (Y P : Subgroup G), Nat.Prime p ∧ p ≠ 2 ∧ Y ≤ X ∧
      X ≤ Subgroup.normalizer (Y : Set G) ∧ (Y.subgroupOf X).index = p ∧
      P ≤ X ∧ IsPGroup p P ∧ X ≤ Y ⊔ P := by
  classical
  obtain ⟨N, hNnorm, hNprime⟩ := exists_normal_prime_index hsolv hcard
  set p : ℕ := Nat.card (↥X ⧸ N) with hpdef
  haveI hNnorm' : N.Normal := hNnorm
  have hp : Nat.Prime p := hNprime
  haveI : Fact p.Prime := ⟨hp⟩
  have hNindex : N.index = p := Subgroup.index_eq_card N
  have hNtop : N ≠ ⊤ := by
    intro h
    have h1 : N.index = 1 := by rw [h, Subgroup.index_top]
    rw [hNindex] at h1
    exact hp.ne_one h1
  have hpdvd : p ∣ Nat.card ↥X := by
    rw [← hNindex]; exact Subgroup.index_dvd_card N
  have hpodd : Odd p := Work.ThreePoints.Odd.of_dvd hpdvd hodd
  have hp2 : p ≠ 2 := by
    intro h
    rw [h] at hpodd
    obtain ⟨k, hk⟩ := hpodd
    omega
  obtain ⟨P₀⟩ := (inferInstance : Nonempty (Sylow p ↥X))
  have hYidx : ((N.map X.subtype).subgroupOf X).index = p := by
    have h1 : (N.map X.subtype).subgroupOf X = N := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, hyx⟩
        have : y = x := Subtype.ext hyx
        rwa [← this]
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [h1, hNindex]
  refine ⟨p, N.map X.subtype, (P₀ : Subgroup ↥X).map X.subtype, hp, hp2,
    Subgroup.map_subtype_le N, ?_, hYidx, Subgroup.map_subtype_le (P₀ : Subgroup ↥X),
    P₀.isPGroup'.map _, ?_⟩
  · -- `X ≤ N_G(Y)`
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [Subgroup.mem_map] at hy ⊢
      obtain ⟨n, hn, hny⟩ := hy
      refine ⟨⟨x, hx⟩ * n * ⟨x, hx⟩⁻¹, hNnorm.conj_mem n hn ⟨x, hx⟩, ?_⟩
      have hny' : (n : G) = y := hny
      change x * (n : G) * x⁻¹ = x * y * x⁻¹
      rw [hny']
    · intro hy
      rw [Subgroup.mem_map] at hy ⊢
      obtain ⟨n, hn, hnxy⟩ := hy
      refine ⟨⟨x, hx⟩⁻¹ * n * ⟨x, hx⟩, ?_, ?_⟩
      · simpa using hNnorm.conj_mem n hn ⟨x, hx⟩⁻¹
      · change x⁻¹ * (n : G) * x = y
        have hnxy' : (n : G) = x * y * x⁻¹ := hnxy
        rw [hnxy']
        group
  · -- `X ≤ Y ⊔ P`
    have htop : N ⊔ (P₀ : Subgroup ↥X) = ⊤ := by
      set Q : Subgroup ↥X := N ⊔ (P₀ : Subgroup ↥X) with hQdef
      have hNQ : N ≤ Q := le_sup_left
      by_contra hne
      have hdiv : Q.index ∣ N.index := by rw [hQdef]; exact Subgroup.index_dvd_of_le le_sup_left
      have hidx : Q.index = p := by
        rcases hp.eq_one_or_self_of_dvd _ hdiv with h | h
        · exact absurd (Subgroup.index_eq_one.mp h) hne
        · exact h
      have hcard : Nat.card Q = Nat.card N := by
        have h1 := Subgroup.card_mul_index N
        have h2 := Subgroup.card_mul_index Q
        rw [hNindex] at h1
        rw [hidx] at h2
        have h3 : Nat.card Q * p = Nat.card N * p := by rw [h2, h1]
        exact Nat.eq_of_mul_eq_mul_right hp.pos h3
      have heq : N = Q := Subgroup.eq_of_le_of_card_ge hNQ (le_of_eq hcard)
      have hP₀N : (P₀ : Subgroup ↥X) ≤ N := by rw [heq, hQdef]; exact le_sup_right
      have hpdv : p ∣ (P₀ : Subgroup ↥X).index := by
        have h' : N.index ∣ (P₀ : Subgroup ↥X).index := by
          rw [← Subgroup.relIndex_mul_index hP₀N]; exact dvd_mul_left _ _
        rwa [hNindex] at h'
      exact P₀.not_dvd_index hpdv
    have hthis : N.map X.subtype ⊔ (P₀ : Subgroup ↥X).map X.subtype = X := by
      rw [← Subgroup.map_sup, htop]
      ext x
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨y, -, rfl⟩; exact y.2
      · intro hx; exact ⟨⟨x, hx⟩, trivial, rfl⟩
    exact le_of_eq hthis.symm

/-- If `u² = 1`, `u ∈ C ⊔ P` with `C` normal and `P` a `p`-group for a prime `p ≠ 2`, then
`u ∈ C`: the quotient `F ⧸ C` is a `p`-group and the image of `u` has order dividing `2`. -/
theorem mem_centralizer_of_sq_one_of_mem_sup {F : Type} [Group F] [Finite F]
    {C : Subgroup F} (hC : C.Normal) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup F} (hP : IsPGroup p P) (htop : C ⊔ P = ⊤)
    {u : F} (hu : u * u = 1) : u ∈ C := by
  haveI hCn : C.Normal := hC
  haveI : Fact p.Prime := ⟨hp⟩
  have hCbot : C.map (QuotientGroup.mk' C) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    exact le_of_eq (QuotientGroup.ker_mk' C).symm
  have hmem : QuotientGroup.mk' C u ∈ P.map (QuotientGroup.mk' C) := by
    have h1 : QuotientGroup.mk' C u ∈ (C ⊔ P).map (QuotientGroup.mk' C) :=
      Subgroup.mem_map_of_mem _ (htop ▸ Subgroup.mem_top u)
    rwa [Subgroup.map_sup, hCbot, bot_sup_eq] at h1
  obtain ⟨n, hn⟩ := (hP.map (QuotientGroup.mk' C)) ⟨QuotientGroup.mk' C u, hmem⟩
  have h2 : orderOf (QuotientGroup.mk' C u) ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_two, ← map_mul, hu, map_one]
  have h3 : orderOf (QuotientGroup.mk' C u) ∣ p ^ n := by
    rw [← Subgroup.orderOf_mk (QuotientGroup.mk' C u) hmem]
    exact orderOf_dvd_iff_pow_eq_one.mpr hn
  have hcop : Nat.Coprime 2 (p ^ n) :=
    Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have h4 := Nat.dvd_gcd h2 h3
  rw [hcop] at h4
  exact (QuotientGroup.eq_one_iff u).mp (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h4))

/-- **Prop. 1 (b), strong-embeddedness part.** Under the evenness hypothesis of Prop. 1 (a) for
the subgroup `X` alone (at all its fixed points), `F ⊓ M` is strongly embedded in `F` for every
fixed point `M = H^g ⊇ X` of `X`. -/
theorem stronglyEmbedded_subgroupOf_inf_conj_of_even_card_at {H X F M : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) (hX3 : 3 ≤ (fixedPts H X).ncard)
    (hFX : involutions (Subgroup.centralizer (X : Set G) : Set G) ⊆ F)
    (hXM : X ≤ M) (hM : ∃ g : G, M = conj g H)
    (hEVX : ∀ M' : Subgroup G, (∃ g' : G, M' = conj g' H) → X ≤ M' →
      Even (Nat.card (M' ⊓ Subgroup.centralizer (X : Set G) : Subgroup G))) :
    IsStronglyEmbedded ((F ⊓ M).subgroupOf F) := by
  obtain ⟨g, rfl⟩ := hM
  have hMstrong : IsStronglyEmbedded (conj g H) := conj_stronglyEmbedded hH g
  have hev : Even (Nat.card (F ⊓ conj g H : Subgroup G)) :=
    even_card_inf_of_even_card_inf_centralizer (hEVX (conj g H) ⟨g, rfl⟩ hXM) hFX
  have hproper : (F ⊓ conj g H).subgroupOf F ≠ ⊤ := by
    obtain ⟨g', hfix, hne_pt⟩ := exists_mk_fixedPts_ne (H := H) (X := X) (g := g) hX3
    have hXg' : X ≤ conj g' H := by
      rw [← stabilizer_mk H g']
      exact mem_fixedPts_iff_le_stabilizer.mp hfix
    have hconjne : conj g H ≠ conj g' H := by
      intro heq
      exact hne_pt (mk_eq_of_conj_eq hH heq.symm)
    obtain ⟨u, hu, hu2⟩ :=
      exists_mem_orderOf_eq_two_of_even_card (hEVX (conj g' H) ⟨g', rfl⟩ hXg')
    have huF : u ∈ F := hFX ⟨hu.2, hu2⟩
    have huNotM : u ∉ conj g H := by
      intro huM
      have huinf : u ∈ conj g H ⊓ conj g' H := ⟨huM, hu.1⟩
      have hdvd : Nat.card (Subgroup.zpowers u : Subgroup G) ∣
          Nat.card (conj g H ⊓ conj g' H : Subgroup G) :=
        Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr huinf)
      rw [Nat.card_zpowers, hu2] at hdvd
      exact Nat.not_even_iff_odd.mpr (card_inf_conj_odd hH hconjne)
        (even_iff_two_dvd.mpr hdvd)
    intro htop
    have hmem : u ∈ F ⊓ conj g H := by
      refine ⟨huF, ?_⟩
      have h' : (⟨u, huF⟩ : F) ∈ (F ⊓ conj g H).subgroupOf F := by rw [htop]; trivial
      exact (Subgroup.mem_subgroupOf.mp h').2
    exact huNotM hmem.2
  exact IsStronglyEmbedded.subgroupOf_inf hMstrong hproper hev

/-- **Prop. 1 (b), class part.** For two fixed points `M₁, M₂` of `X` (with the evenness
hypothesis for `X`), the subgroups `F ⊓ M₁`, `F ⊓ M₂` are conjugate in `F`: they lie in a single
class of proper Bender subgroups of `F`. -/
theorem inf_conj_class_of_even {H X F : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H)
    (hFXinv : involutions (Subgroup.centralizer (X : Set G) : Set G) ⊆ F)
    (hEVX : ∀ M' : Subgroup G, (∃ g' : G, M' = conj g' H) → X ≤ M' →
      Even (Nat.card (M' ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)))
    {M₁ M₂ : Subgroup G} (hM₁ : ∃ g : G, M₁ = conj g H) (hXM₁ : X ≤ M₁)
    (hM₂ : ∃ g : G, M₂ = conj g H) (hXM₂ : X ≤ M₂) :
    ∃ f ∈ F, conj f (F ⊓ M₁) = F ⊓ M₂ := by
  rcases eq_or_ne M₁ M₂ with rfl | hne
  · exact ⟨1, F.one_mem, by rw [conj_one]⟩
  · obtain ⟨g₁, rfl⟩ := hM₁
    obtain ⟨g₂, rfl⟩ := hM₂
    have h1 : Even (Nat.card (F ⊓ conj g₁ H : Subgroup G)) :=
      even_card_inf_of_even_card_inf_centralizer (hEVX (conj g₁ H) ⟨g₁, rfl⟩ hXM₁) hFXinv
    have h2 : Even (Nat.card (F ⊓ conj g₂ H : Subgroup G)) :=
      even_card_inf_of_even_card_inf_centralizer (hEVX (conj g₂ H) ⟨g₂, rfl⟩ hXM₂) hFXinv
    obtain ⟨t, htinv, htconj⟩ := exists_involution_conj_of_even_card_inf hH hne h1 h2
    exact ⟨t, htinv.1, by rw [conj_inf, htconj, conj_eq_self_of_mem htinv.1]⟩

/-- **Prop. 1 (b), injectivity.** The map `M ↦ F ⊓ M` (from the fixed points of `X` to the
subgroups of `F`) is injective: if `F ⊓ M₁ = F ⊓ M₂` then `M₁ = M₂` (the common subgroup would
be contained in `M₁ ⊓ M₂`, of odd order). -/
theorem inf_inj_of_even {H X F M₁ M₂ : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H)
    (hFXinv : involutions (Subgroup.centralizer (X : Set G) : Set G) ⊆ F)
    (hEVX : ∀ M' : Subgroup G, (∃ g' : G, M' = conj g' H) → X ≤ M' →
      Even (Nat.card (M' ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)))
    (hM₁ : ∃ g : G, M₁ = conj g H) (hXM₁ : X ≤ M₁)
    (hM₂ : ∃ g : G, M₂ = conj g H) (hXM₂ : X ≤ M₂) :
    F ⊓ M₁ = F ⊓ M₂ → M₁ = M₂ := by
  obtain ⟨g₁, rfl⟩ := hM₁
  obtain ⟨g₂, rfl⟩ := hM₂
  intro hEq
  by_contra hne
  have hle : F ⊓ conj g₁ H ≤ conj g₁ H ⊓ conj g₂ H := by
    rintro x ⟨hxF, hxM₁⟩
    refine ⟨hxM₁, ?_⟩
    have hx₂ : x ∈ F ⊓ conj g₁ H := ⟨hxF, hxM₁⟩
    rw [hEq] at hx₂
    exact hx₂.2
  have hev1 : Even (Nat.card (F ⊓ conj g₁ H : Subgroup G)) :=
    even_card_inf_of_even_card_inf_centralizer (hEVX (conj g₁ H) ⟨g₁, rfl⟩ hXM₁) hFXinv
  have hdvd : Nat.card (F ⊓ conj g₁ H : Subgroup G) ∣
      Nat.card (conj g₁ H ⊓ conj g₂ H : Subgroup G) := Subgroup.card_dvd_of_le hle
  have hodd : Odd (Nat.card (conj g₁ H ⊓ conj g₂ H : Subgroup G)) :=
    card_inf_conj_odd hH hne
  exact (Nat.not_even_iff_odd.mpr (Work.ThreePoints.Odd.of_dvd hdvd hodd)) hev1

/-- Membership in the normalizer is compatible between an ambient group and a subgroup: for
`Q ≤ P ≤ G` and `x : ↥P`, `x` normalises `Q` in `↥P` iff `x` normalises `Q` in `G`. -/
theorem mem_normalizer_subgroupOf {P Q : Subgroup G} (hQ : Q ≤ P) {x : ↥P} :
    x ∈ Subgroup.normalizer (Q.subgroupOf P : Set ↥P) ↔
      (x : G) ∈ Subgroup.normalizer (Q : Set G) := by
  constructor
  · intro hx
    rw [Subgroup.mem_normalizer_iff]
    intro q
    constructor
    · intro hq
      have hy : (⟨q, hQ hq⟩ : ↥P) ∈ Q.subgroupOf P := Subgroup.mem_subgroupOf.mpr hq
      have h2 := (Subgroup.mem_normalizer_iff.mp hx (⟨q, hQ hq⟩ : ↥P)).mp hy
      simpa using Subgroup.mem_subgroupOf.mp h2
    · intro hq
      have hinv : x⁻¹ ∈ Subgroup.normalizer (Q.subgroupOf P : Set ↥P) :=
        (Subgroup.normalizer (Q.subgroupOf P : Set ↥P)).inv_mem hx
      have hy : (⟨(x : G) * q * (x : G)⁻¹, hQ hq⟩ : ↥P) ∈ Q.subgroupOf P :=
        Subgroup.mem_subgroupOf.mpr hq
      have h2 := (Subgroup.mem_normalizer_iff.mp hinv _).mp hy
      simp only [inv_inv] at h2
      have h3 : (↑(x⁻¹ * (⟨(x : G) * q * (x : G)⁻¹, hQ hq⟩ : ↥P) * x) : G) = q := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      have h4 : (↑(x⁻¹ * (⟨(x : G) * q * (x : G)⁻¹, hQ hq⟩ : ↥P) * x) : G) ∈ Q :=
        Subgroup.mem_subgroupOf.mp h2
      rwa [h3] at h4
  · intro hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      exact (Subgroup.mem_normalizer_iff.mp hx (y : G)).mp hy
    · intro hy
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      have hinv : (x : G)⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
        (Subgroup.normalizer (Q : Set G)).inv_mem hx
      have h2 := (Subgroup.mem_normalizer_iff.mp hinv ((x : G) * (y : G) * (x : G)⁻¹)).mp hy
      convert h2 using 1
      group

/-- `N_G(Y) ≤ N_G(C_G(Y))`: the normalizer of a subgroup normalises its centralizer. -/
theorem normalizer_le_normalizer_centralizer (Y : Subgroup G) :
    Subgroup.normalizer (Y : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (Y : Set G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro x
  constructor
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    have hgy : g⁻¹ * y * g ∈ Y := by
      refine (hg (g⁻¹ * y * g)).mpr ?_
      have h2 : g * (g⁻¹ * y * g) * g⁻¹ = y := by group
      rw [h2]
      exact hy
    have h1 := hx (g⁻¹ * y * g) hgy
    calc y * (g * x * g⁻¹)
        = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = (g * x * g⁻¹) * y := by group
  · intro hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    have hgy : g * y * g⁻¹ ∈ Y := (hg y).mp hy
    have h1 := hx (g * y * g⁻¹) hgy
    calc y * x
        = g⁻¹ * ((g * y * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹)) * g := by rw [h1]
      _ = x * y := by group

/-- The centralizer of a supremum is the intersection of the centralizers. -/
theorem centralizer_sup (A B : Subgroup G) :
    Subgroup.centralizer (((A ⊔ B : Subgroup G)) : Set G) =
      Subgroup.centralizer (A : Set G) ⊓ Subgroup.centralizer (B : Set G) := by
  rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
  ext x
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨fun y hy => h y (Or.inl hy), fun y hy => h y (Or.inr hy)⟩
  · rintro ⟨h1, h2⟩ y (hy | hy)
    · exact h1 y hy
    · exact h2 y hy

/-- The centralizer of the trivial subgroup is everything. -/
theorem centralizer_bot_eq_top :
    Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
  refine le_antisymm le_top fun x _ => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Subgroup.mem_bot.mp hy]
  group

/-- From the even-order conclusion of Ch. I §4 Prop. 2 (`hS4`) for a maximal `p`-subgroup `Q ≤ K`
with `≥ 3` fixed points, extract an involution of `K` normalising `Q`. -/
theorem exists_involution_normalizer_of_maximal_p_subgroup_brsz
    (hS4 : ∀ (F : Type) [Group F] [Finite F] {K : Subgroup F},
        LeanEval.GroupTheory.Defs.IsStronglyEmbedded K →
        ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ Q : Subgroup F, Q ≤ K → IsPGroup p Q →
          3 ≤ (Submission.Blueprint.fixedPts K Q).ncard →
          (∀ R : Subgroup F, Q ≤ R → R ≤ K → IsPGroup p R →
            3 ≤ (Submission.Blueprint.fixedPts K R).ncard → R = Q) →
          Even (Nat.card (Subgroup.normalizer (Q.subgroupOf K : Set K) : Subgroup K)))
    {F : Type} [Group F] [Finite F] {K : Subgroup F}
    (hK : LeanEval.GroupTheory.Defs.IsStronglyEmbedded K)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (Q : Subgroup F) (hQK : Q ≤ K)
    (hQp : IsPGroup p Q) (hQ3 : 3 ≤ (Submission.Blueprint.fixedPts K Q).ncard)
    (hQmax : ∀ R : Subgroup F, Q ≤ R → R ≤ K → IsPGroup p R →
      3 ≤ (Submission.Blueprint.fixedPts K R).ncard → R = Q) :
    ∃ u : F, u ∈ K ∧ u ∈ Subgroup.normalizer (Q : Set F) ∧ orderOf u = 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx, hx2⟩ :=
    exists_mem_orderOf_eq_two_of_even_card (hS4 F hK p hp hp2 Q hQK hQp hQ3 hQmax)
  refine ⟨(x : F), x.2, ?_, (Subgroup.orderOf_coe x).trans hx2⟩
  rw [Subgroup.mem_normalizer_iff]
  intro q
  constructor
  · intro hq
    have hmem : (⟨q, hQK hq⟩ : K) ∈ Q.subgroupOf K := Subgroup.mem_subgroupOf.mpr hq
    have h2 := (Subgroup.mem_normalizer_iff.mp hx (⟨q, hQK hq⟩ : K)).mp hmem
    exact Subgroup.mem_subgroupOf.mp h2
  · intro hq
    have hinv : x⁻¹ ∈ Subgroup.normalizer (Q.subgroupOf K : Set K) :=
      (Subgroup.normalizer (Q.subgroupOf K : Set K)).inv_mem hx
    have hy : (⟨(x : F) * q * (x : F)⁻¹, hQK hq⟩ : K) ∈ Q.subgroupOf K :=
      Subgroup.mem_subgroupOf.mpr hq
    have h2 := (Subgroup.mem_normalizer_iff.mp hinv _).mp hy
    simp only [inv_inv] at h2
    have h3 : (↑(x⁻¹ * (⟨(x : F) * q * (x : F)⁻¹, hQK hq⟩ : K) * x) : F) = q := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have h4 : (↑(x⁻¹ * (⟨(x : F) * q * (x : F)⁻¹, hQK hq⟩ : K) * x) : F) ∈ Q :=
      Subgroup.mem_subgroupOf.mp h2
    rwa [h3] at h4

theorem even_card_centralizer_of_fixes_three_brsz {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hS4 : ∀ (F : Type) [Group F] [Finite F] {K : Subgroup F},
        LeanEval.GroupTheory.Defs.IsStronglyEmbedded K →
        ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ Q : Subgroup F, Q ≤ K → IsPGroup p Q →
          3 ≤ (Submission.Blueprint.fixedPts K Q).ncard →
          (∀ R : Subgroup F, Q ≤ R → R ≤ K → IsPGroup p R →
            3 ≤ (Submission.Blueprint.fixedPts K R).ncard → R = Q) →
          Even (Nat.card (Subgroup.normalizer (Q.subgroupOf K : Set K) : Subgroup K)))
    (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {X M : Subgroup G}
    (hX3 : 3 ≤ (Submission.Blueprint.fixedPts H X).ncard)
    (hM : ∃ g : G, M = Submission.Blueprint.conj g H) (hXM : X ≤ M) :
    Even (Nat.card (M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) := by
  classical
  suffices hmain : ∀ n : ℕ, ∀ X M : Subgroup G, Nat.card X ≤ n →
      3 ≤ (fixedPts H X).ncard → (∃ g : G, M = conj g H) → X ≤ M →
      Even (Nat.card (M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) by
    exact hmain (Nat.card X) X M le_rfl hX3 hM hXM
  intro n
  induction n with
  | zero =>
      intro X M h0 _ _ _
      exfalso
      have hp := Nat.card_pos (α := ↥X)
      omega
  | succ n ih =>
      intro X M hle hX3 hM hXM
      by_cases hsmall : Nat.card X ≤ n
      · exact ih X M hsmall hX3 hM hXM
      · have hcardX : Nat.card X = n + 1 := by omega
        by_cases hXbot : X = ⊥
        · rw [hXbot, centralizer_bot_eq_top, inf_top_eq]
          obtain ⟨g, rfl⟩ := hM
          exact (conj_stronglyEmbedded hH g).2.1
        · have hcard1 : 1 < Nat.card X :=
            (Subgroup.one_lt_card_iff_ne_bot X).mpr hXbot
          have hoddX : Odd (Nat.card X) := odd_card_of_fixes_three hH hX3
          have hsolv : Group.IsSolvable ↥X := hFT ↥X hoddX
          obtain ⟨p, Y, P, hp, hp2, hYX, hYN, hYidx, hPX, hPp, hXYP⟩ :=
            exists_normal_sylow_data hoddX hsolv hcard1
          have hY3 : 3 ≤ (fixedPts H Y).ncard :=
            le_trans hX3 (Set.ncard_le_ncard (fixedPts_mono hYX))
          have hYne : Y ≠ X := by
            intro h
            rw [h] at hYidx
            rw [Subgroup.subgroupOf_self, Subgroup.index_top] at hYidx
            exact hp.ne_one hYidx.symm
          have hYlt : Nat.card Y ≤ n := by
            have hc : Nat.card Y < Nat.card X :=
              Subgroup.card_lt_of_lt (lt_of_le_of_ne hYX hYne)
            omega
          have hIHY : ∀ M' : Subgroup G, (∃ g' : G, M' = conj g' H) → Y ≤ M' →
              Even (Nat.card (M' ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G)) :=
            fun M' hM' hYM' => ih Y M' hYlt hY3 hM' hYM'
          set C₁ : Subgroup G := Subgroup.centralizer (Y : Set G) with hC₁
          set F₁ : Subgroup G := C₁ ⊔ P with hF₁
          have hC₁leF₁ : C₁ ≤ F₁ := by rw [hF₁]; exact le_sup_left
          have hPleF₁ : P ≤ F₁ := by rw [hF₁]; exact le_sup_right
          have hF₁N : F₁ ≤ Subgroup.normalizer (Y : Set G) := by
            rw [hF₁]
            exact sup_le (Subgroup.centralizer_le_normalizer (Y : Set G)) (hPX.trans hYN)
          have hYP : Y ≤ M := hYX.trans hXM
          have hFXinv : involutions (Subgroup.centralizer (Y : Set G) : Set G) ⊆ F₁ :=
            fun u hu => hC₁leF₁ hu.1
          have hK₁strong : IsStronglyEmbedded ((F₁ ⊓ M).subgroupOf F₁) :=
            stronglyEmbedded_subgroupOf_inf_conj_of_even_card_at hH hY3 hFXinv hYP hM hIHY
          set K₁ : Subgroup ↥F₁ := (F₁ ⊓ M).subgroupOf F₁ with hK₁
          have hKstrong : IsStronglyEmbedded K₁ := by rw [hK₁]; exact hK₁strong
          set P₀ : Subgroup ↥F₁ := P.subgroupOf F₁ with hP₀
          have hP₀p : IsPGroup p P₀ := hPp.comap_of_injective F₁.subtype Subtype.coe_injective
          have hP₀K₁ : P₀ ≤ K₁ := by
            rw [hP₀, hK₁]
            intro x hx
            rw [Subgroup.mem_subgroupOf] at hx ⊢
            exact ⟨x.2, hXM (hPX hx)⟩
          -- `P₀` fixes `≥ 3` points of `↥F₁ ⧸ K₁`
          have h3fp : 3 ≤ (fixedPts K₁ P₀).ncard := by
            have hfin : (fixedPts H X).Finite := Set.toFinite _
            have h2 : 1 < (fixedPts H X).ncard := by omega
            obtain ⟨ω₁, hω₁, ω₂, hω₂, hω₁₂⟩ := (Set.one_lt_ncard hfin).mp h2
            have hd : 1 < ((fixedPts H X) \ {ω₁}).ncard := by
              have h := Set.ncard_sdiff_singleton_add_one hω₁ hfin
              omega
            obtain ⟨ω₃, hω₃, hω₃₂⟩ := Set.exists_ne_of_one_lt_ncard hd ω₂
            have hω₃₁ : ω₃ ≠ ω₁ := hω₃.2
            have hω₃mem : ω₃ ∈ fixedPts H X := hω₃.1
            obtain ⟨g₁, hg₁⟩ := QuotientGroup.mk_surjective ω₁
            obtain ⟨g₂, hg₂⟩ := QuotientGroup.mk_surjective ω₂
            obtain ⟨g₃, hg₃⟩ := QuotientGroup.mk_surjective ω₃
            have hM₁ : X ≤ conj g₁ H := by
              rw [← stabilizer_mk H g₁, hg₁]
              exact mem_fixedPts_iff_le_stabilizer.mp hω₁
            have hM₂ : X ≤ conj g₂ H := by
              rw [← stabilizer_mk H g₂, hg₂]
              exact mem_fixedPts_iff_le_stabilizer.mp hω₂
            have hM₃ : X ≤ conj g₃ H := by
              rw [← stabilizer_mk H g₃, hg₃]
              exact mem_fixedPts_iff_le_stabilizer.mp hω₃mem
            have hY₁ : Y ≤ conj g₁ H := hYX.trans hM₁
            have hY₂ : Y ≤ conj g₂ H := hYX.trans hM₂
            have hY₃ : Y ≤ conj g₃ H := hYX.trans hM₃
            obtain ⟨f₁, hf₁F, hf₁⟩ := inf_conj_class_of_even hH hFXinv hIHY hM hYP ⟨g₁, rfl⟩ hY₁
            obtain ⟨f₂, hf₂F, hf₂⟩ := inf_conj_class_of_even hH hFXinv hIHY hM hYP ⟨g₂, rfl⟩ hY₂
            obtain ⟨f₃, hf₃F, hf₃⟩ := inf_conj_class_of_even hH hFXinv hIHY hM hYP ⟨g₃, rfl⟩ hY₃
            have hmem₁ : ((⟨f₁, hf₁F⟩ : ↥F₁) : ↥F₁ ⧸ K₁) ∈ fixedPts K₁ P₀ := by
              rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk]
              intro y hy
              rw [mem_conj_iff, Subgroup.mem_subgroupOf]
              have hyP : (y : G) ∈ P := Subgroup.mem_subgroupOf.mp hy
              have hyconj : (y : G) ∈ conj f₁ (F₁ ⊓ M) := by
                rw [hf₁]
                exact ⟨hPleF₁ hyP, hM₁ (hPX hyP)⟩
              rw [mem_conj_iff] at hyconj
              simpa using hyconj
            have hmem₂ : ((⟨f₂, hf₂F⟩ : ↥F₁) : ↥F₁ ⧸ K₁) ∈ fixedPts K₁ P₀ := by
              rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk]
              intro y hy
              rw [mem_conj_iff, Subgroup.mem_subgroupOf]
              have hyP : (y : G) ∈ P := Subgroup.mem_subgroupOf.mp hy
              have hyconj : (y : G) ∈ conj f₂ (F₁ ⊓ M) := by
                rw [hf₂]
                exact ⟨hPleF₁ hyP, hM₂ (hPX hyP)⟩
              rw [mem_conj_iff] at hyconj
              simpa using hyconj
            have hmem₃ : ((⟨f₃, hf₃F⟩ : ↥F₁) : ↥F₁ ⧸ K₁) ∈ fixedPts K₁ P₀ := by
              rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk]
              intro y hy
              rw [mem_conj_iff, Subgroup.mem_subgroupOf]
              have hyP : (y : G) ∈ P := Subgroup.mem_subgroupOf.mp hy
              have hyconj : (y : G) ∈ conj f₃ (F₁ ⊓ M) := by
                rw [hf₃]
                exact ⟨hPleF₁ hyP, hM₃ (hPX hyP)⟩
              rw [mem_conj_iff] at hyconj
              simpa using hyconj
            have hne12 : ((⟨f₁, hf₁F⟩ : ↥F₁) : ↥F₁ ⧸ K₁) ≠
                ((⟨f₂, hf₂F⟩ : ↥F₁) : ↥F₁ ⧸ K₁) := by
              intro hcon
              have h1 : (⟨f₁, hf₁F⟩ : ↥F₁)⁻¹ * ⟨f₂, hf₂F⟩ ∈ K₁ := QuotientGroup.eq.mp hcon
              have hk : f₁⁻¹ * f₂ ∈ F₁ ⊓ M := Subgroup.mem_subgroupOf.mp h1
              have hconj : F₁ ⊓ conj g₁ H = F₁ ⊓ conj g₂ H := by
                rw [← hf₁, ← hf₂]
                rw [show f₂ = f₁ * (f₁⁻¹ * f₂) from by group, conj_mul,
                  conj_eq_self_of_mem hk]
              have := inf_inj_of_even hH hFXinv hIHY ⟨g₁, rfl⟩ hY₁ ⟨g₂, rfl⟩ hY₂ hconj
              exact hω₁₂ (hg₁.symm.trans ((mk_eq_of_conj_eq hH this).trans hg₂))
            have hne13 : ((⟨f₁, hf₁F⟩ : ↥F₁) : ↥F₁ ⧸ K₁) ≠
                ((⟨f₃, hf₃F⟩ : ↥F₁) : ↥F₁ ⧸ K₁) := by
              intro hcon
              have h1 : (⟨f₁, hf₁F⟩ : ↥F₁)⁻¹ * ⟨f₃, hf₃F⟩ ∈ K₁ := QuotientGroup.eq.mp hcon
              have hk : f₁⁻¹ * f₃ ∈ F₁ ⊓ M := Subgroup.mem_subgroupOf.mp h1
              have hconj : F₁ ⊓ conj g₁ H = F₁ ⊓ conj g₃ H := by
                rw [← hf₁, ← hf₃]
                rw [show f₃ = f₁ * (f₁⁻¹ * f₃) from by group, conj_mul,
                  conj_eq_self_of_mem hk]
              have := inf_inj_of_even hH hFXinv hIHY ⟨g₁, rfl⟩ hY₁ ⟨g₃, rfl⟩ hY₃ hconj
              exact hω₃₁ (hg₁.symm.trans ((mk_eq_of_conj_eq hH this).trans hg₃)).symm
            have hne23 : ((⟨f₂, hf₂F⟩ : ↥F₁) : ↥F₁ ⧸ K₁) ≠
                ((⟨f₃, hf₃F⟩ : ↥F₁) : ↥F₁ ⧸ K₁) := by
              intro hcon
              have h1 : (⟨f₂, hf₂F⟩ : ↥F₁)⁻¹ * ⟨f₃, hf₃F⟩ ∈ K₁ := QuotientGroup.eq.mp hcon
              have hk : f₂⁻¹ * f₃ ∈ F₁ ⊓ M := Subgroup.mem_subgroupOf.mp h1
              have hconj : F₁ ⊓ conj g₂ H = F₁ ⊓ conj g₃ H := by
                rw [← hf₂, ← hf₃]
                rw [show f₃ = f₂ * (f₂⁻¹ * f₃) from by group, conj_mul,
                  conj_eq_self_of_mem hk]
              have := inf_inj_of_even hH hFXinv hIHY ⟨g₂, rfl⟩ hY₂ ⟨g₃, rfl⟩ hY₃ hconj
              exact hω₃₂ (hg₂.symm.trans ((mk_eq_of_conj_eq hH this).trans hg₃)).symm
            have hsub : ({((⟨f₁, hf₁F⟩ : ↥F₁) : ↥F₁ ⧸ K₁),
                ((⟨f₂, hf₂F⟩ : ↥F₁) : ↥F₁ ⧸ K₁),
                ((⟨f₃, hf₃F⟩ : ↥F₁) : ↥F₁ ⧸ K₁)} : Set (↥F₁ ⧸ K₁)) ⊆
                fixedPts K₁ P₀ := by
              intro y hy
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
              rcases hy with rfl | rfl | rfl
              · exact hmem₁
              · exact hmem₂
              · exact hmem₃
            have hcard3 : ({((⟨f₁, hf₁F⟩ : ↥F₁) : ↥F₁ ⧸ K₁),
                ((⟨f₂, hf₂F⟩ : ↥F₁) : ↥F₁ ⧸ K₁),
                ((⟨f₃, hf₃F⟩ : ↥F₁) : ↥F₁ ⧸ K₁)} : Set (↥F₁ ⧸ K₁)).ncard = 3 := by
              rw [Set.ncard_insert_of_notMem (by
                    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
                    exact ⟨hne12, hne13⟩),
                Set.ncard_insert_of_notMem (by
                    simp only [Set.mem_singleton_iff]
                    exact hne23),
                Set.ncard_singleton]
            have hle3 := Set.ncard_le_ncard hsub
            rw [hcard3] at hle3
            exact hle3
          -- existence of a maximal such `Q`
          obtain ⟨Q, hQ1, hQ2, hQ3p, hQ3, hQmax⟩ : ∃ Q : Subgroup ↥F₁,
              P₀ ≤ Q ∧ Q ≤ K₁ ∧ IsPGroup p Q ∧ 3 ≤ (fixedPts K₁ Q).ncard ∧
              (∀ R : Subgroup ↥F₁, Q ≤ R → R ≤ K₁ → IsPGroup p R →
                3 ≤ (fixedPts K₁ R).ncard → R = Q) := by
            classical
            set S : Set (Subgroup ↥F₁) :=
              {R | P₀ ≤ R ∧ R ≤ K₁ ∧ IsPGroup p R ∧ 3 ≤ (fixedPts K₁ R).ncard} with hS
            have hSne : ((fun R : Subgroup ↥F₁ => Nat.card R) '' S).Nonempty :=
              ⟨Nat.card P₀, P₀, by rw [hS]; exact ⟨le_rfl, hP₀K₁, hP₀p, h3fp⟩, rfl⟩
            have hSbdd : BddAbove ((fun R : Subgroup ↥F₁ => Nat.card R) '' S) :=
              ⟨Nat.card ↥F₁, by
                rintro x ⟨R, -, rfl⟩
                exact Nat.card_le_card_of_injective (fun y : ↥R => (y : ↥F₁))
                  (fun a b hab => Subtype.ext hab)⟩
            obtain ⟨Q, hQS, hQsup⟩ := Nat.sSup_mem hSne hSbdd
            rw [hS] at hQS
            have hmax : ∀ R ∈ S, Nat.card R ≤ Nat.card Q := by
              intro R hR
              change (fun R : Subgroup ↥F₁ => Nat.card R) R ≤
                (fun R : Subgroup ↥F₁ => Nat.card R) Q
              rw [hQsup]
              exact le_csSup hSbdd ⟨R, hR, rfl⟩
            exact ⟨Q, hQS.1, hQS.2.1, hQS.2.2.1, hQS.2.2.2,
              fun R hQR hRK hRp hR3 =>
                (Subgroup.eq_of_le_of_card_ge hQR
                  (hmax R (by rw [hS]; exact ⟨hQS.1.trans hQR, hRK, hRp, hR3⟩))).symm⟩
          -- extract the involution from `hS4`
          obtain ⟨u, huK, huN, hu2⟩ :=
            exists_involution_normalizer_of_maximal_p_subgroup_brsz hS4 hKstrong p hp hp2 Q
              hQ2 hQ3p hQ3 hQmax
          set Qb : Subgroup G := Q.map F₁.subtype with hQb
          have hQbF₁ : Qb ≤ F₁ := Subgroup.map_subtype_le Q
          have hsub : Qb.subgroupOf F₁ = Q := by
            rw [hQb]
            ext x
            rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
            constructor
            · rintro ⟨y, hy, hyx⟩
              have : y = x := Subtype.ext hyx
              rwa [← this]
            · intro hx; exact ⟨x, hx, rfl⟩
          have hQbK : Qb ≤ F₁ ⊓ M := by
            intro x hx
            rw [hQb, Subgroup.mem_map] at hx
            obtain ⟨y, hy, hyx⟩ := hx
            rw [← hyx]
            exact Subgroup.mem_subgroupOf.mp (hK₁ ▸ hQ2 hy)
          have hPQb : P ≤ Qb := by
            intro q hq
            exact Subgroup.mem_map.mpr
              ⟨⟨q, hPleF₁ hq⟩, hQ1 (Subgroup.mem_subgroupOf.mpr hq), rfl⟩
          set uh : G := (u : G) with huh
          have hu2' : orderOf uh = 2 := (Subgroup.orderOf_coe u).trans hu2
          have huhM : uh ∈ M := by
            have h : u ∈ (F₁ ⊓ M).subgroupOf F₁ := by rw [← hK₁]; exact huK
            exact (Subgroup.mem_subgroupOf.mp h).2
          have huhNQb : uh ∈ Subgroup.normalizer (Qb : Set G) :=
            (mem_normalizer_subgroupOf hQbF₁).mp (by rw [hsub]; exact huN)
          -- a second fixed point of `Q`: a conjugate of `M` containing `Qb`
          have hbase : (((1 : ↥F₁)) : ↥F₁ ⧸ K₁) ∈ fixedPts K₁ Q := by
            rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk, conj_one]
            exact hQ2
          have hQ1lt : 1 < (fixedPts K₁ Q).ncard := by omega
          obtain ⟨ω', hω'mem, hω'ne⟩ :=
            Set.exists_ne_of_one_lt_ncard hQ1lt (((1 : ↥F₁)) : ↥F₁ ⧸ K₁)
          obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective ω'
          have hQle : Q ≤ conj x K₁ := by
            have h1 := mem_fixedPts_iff_le_stabilizer.mp hω'mem
            rw [← hx, stabilizer_mk] at h1
            exact h1
          have hxK₁ : x ∉ K₁ := by
            intro hxin
            apply hω'ne
            have hx1 : (x : ↥F₁ ⧸ K₁) = ((1 : ↥F₁) : ↥F₁ ⧸ K₁) := by
              rw [QuotientGroup.eq]
              simpa using K₁.inv_mem hxin
            rw [← hx]
            exact hx1
          have hxGnotM : (x : G) ∉ M := by
            intro hxM
            apply hxK₁
            have h : x ∈ (F₁ ⊓ M).subgroupOf F₁ :=
              Subgroup.mem_subgroupOf.mpr ⟨x.2, hxM⟩
            rwa [← hK₁] at h
          have hQbM' : Qb ≤ conj (x : G) M := by
            intro z hz
            rw [hQb, Subgroup.mem_map] at hz
            obtain ⟨y, hy, hyz⟩ := hz
            rw [← hyz]
            refine mem_conj_iff.mpr ?_
            have h1 : x⁻¹ * y * x ∈ K₁ := mem_conj_iff.mp (hQle hy)
            have h1' : x⁻¹ * y * x ∈ (F₁ ⊓ M).subgroupOf F₁ := by rw [← hK₁]; exact h1
            have h2 : (↑(x⁻¹ * y * x) : G) ∈ M := (Subgroup.mem_subgroupOf.mp h1').2
            simpa using h2
          -- Theorem C: `uh` centralises `Qb`
          have hMstrong : IsStronglyEmbedded M := by
            obtain ⟨gM, hgM⟩ := hM
            rw [hgM]
            exact conj_stronglyEmbedded hH gM
          have hcentral : ∀ w ∈ Qb, uh * w = w * uh :=
            hC G hS M hMstrong (x : G) hxGnotM uh ⟨huhM, hu2'⟩ Qb
              (le_inf (hQbK.trans inf_le_right) hQbM') huhNQb
          have huhCQb : uh ∈ Subgroup.centralizer (Qb : Set G) :=
            Subgroup.mem_centralizer_iff.mpr fun w hw => (hcentral w hw).symm
          have huhCP : uh ∈ Subgroup.centralizer (P : Set G) :=
            Subgroup.centralizer_le (fun z hz => hPQb hz) huhCQb
          -- `uh ∈ C_G(Y)`
          have hC₁norm : (C₁.subgroupOf F₁).Normal :=
            (Subgroup.normal_subgroupOf_iff_le_normalizer hC₁leF₁).mpr
              (hF₁N.trans (normalizer_le_normalizer_centralizer Y))
          have hC₁sup : (C₁.subgroupOf F₁) ⊔ P₀ = ⊤ := by
            rw [hP₀, ← Subgroup.subgroupOf_sup hC₁leF₁ hPleF₁, hF₁]
            exact Subgroup.subgroupOf_self (C₁ ⊔ P)
          have huhC₁ : uh ∈ C₁ := by
            have h1 : u ∈ C₁.subgroupOf F₁ :=
              mem_centralizer_of_sq_one_of_mem_sup hC₁norm hp hp2 hP₀p hC₁sup
                (mul_self_eq_one_of_orderOf_eq_two hu2)
            exact Subgroup.mem_subgroupOf.mp h1
          -- conclude
          rw [even_iff_two_dvd]
          have huhCYP : uh ∈ Subgroup.centralizer (((Y ⊔ P : Subgroup G)) : Set G) :=
            (centralizer_sup Y P) ▸ ⟨huhC₁, huhCP⟩
          have huhCX : uh ∈ Subgroup.centralizer (X : Set G) :=
            Subgroup.centralizer_le (fun z hz => hXYP hz) huhCYP
          have hmem : uh ∈ (M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) :=
            ⟨huhM, huhCX⟩
          have hdvd := orderOf_dvd_natCard
            (⟨uh, hmem⟩ : ↥(M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G))
          rwa [Subgroup.orderOf_mk, hu2'] at hdvd

end Work.ThreePoints.Prop1aBrSz
