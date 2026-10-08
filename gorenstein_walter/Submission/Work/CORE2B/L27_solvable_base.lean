import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.t_central_in_S
import Submission.Work.BMAX.InvolutionInverts
import Submission.Work.RED.OddCoreFacts

namespace Work.CORE2B

open Subgroup
open scoped commutatorElement

set_option linter.unusedVariables false

/-!
# CORE2B — base lemmas for Lemma 2.7 (`M` solvable)

These are the auxiliary facts about `t`, `F_{π'}(M)` and `F_{2'}(M)` that the proofs of
Lemma 2.7 (a) (`⁅M,t⁆ ≤ F_{π'}(M)`) and of Lemma 2.7 (c) (`M` solvable) share.
-/

/-! ## 1. The factorization lemma -/

/-- **Factorization (ambient form).**  Let `G` be a finite group, `t ∈ G` an involution,
`X ≤ M ≤ G` with `X ◁ M` of odd order, `t` inverting `X` pointwise, and `⁅M,t⁆ ≤ X`.  Then
`M ≤ C_G(t)·X`.

For `x = ⁅m,t⁆ ∈ X` the element `g = m⁻¹ x m ∈ X` has odd order, so it has a square root
`f = g^{(|X|+1)/2}` in `X`; then `t·(m·f)·t⁻¹ = (x·m)·f⁻¹ = m·f` because `x = m·f²·m⁻¹`, so
`m·f ∈ C_G(t)` and `m = (m·f)·f⁻¹`. -/
theorem exists_mul_of_mem_of_inverts {G : Type} [Group G] [Finite G] (t : G) (ht : t * t = 1)
    (M X : Subgroup G) (hXM : X ≤ M) (hXn : (X.subgroupOf M).Normal) (hXodd : Odd (Nat.card X))
    (hinv : ∀ x ∈ X, t * x * t⁻¹ = x⁻¹)
    (hcomm : ⁅M, Subgroup.zpowers t⁆ ≤ X) :
    ∀ m ∈ M, ∃ c ∈ Subgroup.centralizer ({t} : Set G), ∃ x ∈ X, c * x = m := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  intro m hm
  -- the commutator `⁅t,m⁆` lies in `X`
  have hx : ⁅t, m⁆ ∈ X := by
    have h1 : ⁅t, m⁆ ∈ ⁅Subgroup.zpowers t, M⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers t) hm
    rw [Subgroup.commutator_comm] at h1
    exact hcomm h1
  -- `X ◁ M`, so `m⁻¹ g m ∈ X` for `g ∈ X`
  have hconj : ∀ y ∈ X, m⁻¹ * y * m ∈ X := by
    intro y hy
    exact Subgroup.mem_subgroupOf.mp (by
      simpa using hXn.conj_mem (⟨y, hXM hy⟩ : ↥M) (Subgroup.mem_subgroupOf.mpr hy)
        (⟨m, hm⟩ : ↥M)⁻¹)
  have hg : m⁻¹ * ⁅t, m⁆ * m ∈ X := hconj _ hx
  set g : G := m⁻¹ * ⁅t, m⁆ * m with hgdef
  set f : G := g ^ ((Nat.card X + 1) / 2) with hfdef
  have hfX : f ∈ X := X.pow_mem hg _
  have hff : f * f = g := by
    rw [hfdef, ← pow_two, ← pow_mul]
    have h2 : 2 * ((Nat.card X + 1) / 2) = Nat.card X + 1 := by
      obtain ⟨k, hk⟩ := hXodd.add_one
      omega
    have hgpow : g ^ Nat.card X = 1 := by
      obtain ⟨k, hk⟩ := Subgroup.orderOf_dvd_natCard X hg
      rw [hk, pow_mul, pow_orderOf_eq_one, one_pow]
    rw [mul_comm, h2, pow_succ, hgpow, one_mul]
  have htm : t * m * t⁻¹ = ⁅t, m⁆ * m := by
    rw [commutatorElement_def]; group
  have hfix : t * (m * f) * t⁻¹ = m * f := by
    rw [show t * (m * f) * t⁻¹ = (t * m * t⁻¹) * (t * f * t⁻¹) by group, htm,
      hinv f hfX]
    have hxf : ⁅t, m⁆ = m * (f * f) * m⁻¹ := by rw [hff, hgdef]; group
    rw [hxf]
    group
  have hfix' : t * (m * f) = (m * f) * t := by
    have h : t * (m * f) * t = m * f := by simpa [htinv] using hfix
    calc t * (m * f) = t * (m * f) * (t * t) := by rw [ht, mul_one]
      _ = (t * (m * f) * t) * t := by group
      _ = (m * f) * t := by rw [h]
  have hmem : m * f ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hfix'
  exact ⟨m * f, hmem, f⁻¹, X.inv_mem hfX, by group⟩

/-- An involution which inverts a subgroup pointwise makes it commutative. -/
theorem commute_of_forall_inverts {M : Type} [Group M] (t : M) (X : Subgroup M)
    (hinv : ∀ x ∈ X, t * x * t⁻¹ = x⁻¹) : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
  intro x hx y hy
  have h1 : t * (x * y) * t⁻¹ = (x * y)⁻¹ := hinv _ (X.mul_mem hx hy)
  have h2 : t * (x * y) * t⁻¹ = x⁻¹ * y⁻¹ := by
    rw [show t * (x * y) * t⁻¹ = (t * x * t⁻¹) * (t * y * t⁻¹) by group, hinv x hx,
      hinv y hy]
  rw [h2, mul_inv_rev] at h1
  have h3 : y⁻¹ * x⁻¹ = x⁻¹ * y⁻¹ := h1.symm
  have h4 := congrArg (fun w : M => w⁻¹) h3
  simpa using h4

/-! ## 2. Monotonicity of `F_π` -/

/-- Monotonicity of `F_π` in `π`. -/
theorem fittingPi_mono' {G : Type} [Group G] {π₁ π₂ : Set ℕ} (h : π₁ ⊆ π₂) :
    Work.GW2.fittingPi π₁ G ≤ Work.GW2.fittingPi π₂ G := by
  unfold Work.GW2.fittingPi
  refine Subgroup.map_mono ?_
  rw [Work.GW2.piCore, Work.GW2.piCore]
  refine Subgroup.normalCore_mono (sSup_le ?_)
  rintro N ⟨hN, hpi⟩
  exact le_sSup ⟨hN, fun q hq => h (hpi q hq)⟩

theorem fittingPiIn_mono' {G : Type} [Group G] {π₁ π₂ : Set ℕ} (h : π₁ ⊆ π₂)
    (K : Subgroup G) :
    Work.GW2.fittingPiIn π₁ K ≤ Work.GW2.fittingPiIn π₂ K := by
  unfold Work.GW2.fittingPiIn
  exact Subgroup.map_mono (fittingPi_mono' h)


/-! ## 2. The bridge to the odd-order library's `O_π` -/

/-- `O_π(G)` (area CORE2B's definition, a supremum of normal `π`-subgroups) is the odd-order
library's `O_π(G)`. -/
theorem piCore_eq_oPiCore_local {G : Type} [Group G] (π : Set ℕ) :
    Work.GW2.piCore π G = OddOrder.Isaacs.Ch03.oPiCore π G := by
  change (sSup {N : Subgroup G | N.Normal ∧ Subgroup.IsPiSubgroup π N}).normalCore
      = OddOrder.Isaacs.Ch03.oPiCore π G
  rw [Work.RED.GW2.sSup_normal_isPiSubgroup_eq_oPiCore π, Work.RED.GW2.normalCore_oPiCore]

/-- `O_π(G)` is a `π`-group. -/
theorem isPiSubgroup_piCore_local {G : Type} [Group G] [Finite G] (π : Set ℕ) :
    Subgroup.IsPiSubgroup π (Work.GW2.piCore π G) := by
  rw [piCore_eq_oPiCore_local π]
  exact OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (G := G) π

/-- `O_p(G) ≤ F(G)`: a normal `p`-subgroup is nilpotent. -/
theorem pCore_le_fitting_local {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] :
    Work.GW2.pCore p G ≤ Work.GW2.fitting G := by
  rw [Work.GW2.pCore, Work.GW2.fitting]
  refine Subgroup.normalCore_mono (sSup_le ?_)
  rintro N ⟨hN, hpg⟩
  exact le_sSup ⟨hN, hpg.isNilpotent⟩

/-- `F_π(K) = O_π(F(K))` is normal in the abstract group `↥K` (it is characteristic in the
normal subgroup `F(K)`). -/
theorem fittingPi_normal_local {G : Type} [Group G] (π : Set ℕ) (K : Subgroup G) :
    (Work.GW2.fittingPi π K).Normal := by
  haveI hFK : (Work.GW2.fitting K).Normal := Subgroup.normalCore_normal _
  haveI hchar : (Work.GW2.piCore π ↥(Work.GW2.fitting K)).Characteristic := by
    rw [piCore_eq_oPiCore_local π]
    exact OddOrder.Isaacs.Ch03.oPiCore.characteristic π ↥(Work.GW2.fitting K)
  exact ConjAct.normal_of_characteristic_of_normal

/-- If `N ⊴ ↥K` then `K` normalizes the image of `N` in `G` along `K.subtype`. -/
theorem le_normalizer_map_subtype_local {G : Type} [Group G] (K : Subgroup G)
    (N : Subgroup ↥K) (hN : N.Normal) :
    K ≤ Subgroup.normalizer ((N.map K.subtype : Subgroup G) : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨k, hk⟩ * y * ⟨k, hk⟩⁻¹, hN.conj_mem y hy ⟨k, hk⟩, ?_⟩
    have hyx' : (y : G) = x := hyx
    show k * (y : G) * k⁻¹ = k * x * k⁻¹
    rw [hyx']
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨⟨k, hk⟩⁻¹ * y * ⟨k, hk⟩,
      (by simpa using hN.conj_mem y hy ⟨k, hk⟩⁻¹), ?_⟩
    have hyx' : (y : G) = k * x * k⁻¹ := hyx
    show k⁻¹ * (y : G) * k = x
    rw [hyx']
    group

/-- `K` normalizes `F_π(K) = O_π(F(K))` (viewed inside `G`). -/
theorem le_normalizer_fittingPiIn_local {G : Type} [Group G] (π : Set ℕ) (K : Subgroup G) :
    K ≤ Subgroup.normalizer ((Work.GW2.fittingPiIn π K : Subgroup G) : Set G) := by
  simpa only [Work.GW2.fittingPiIn] using
    le_normalizer_map_subtype_local K (Work.GW2.fittingPi π K) (fittingPi_normal_local π K)

/-- Theorem 2.6: `O₂(Ĥ) = S ⊓ C(U) ≠ 1`, hence `2 ∈ π(F(Ĥ))`. -/
theorem two_mem_pi_local {G : Type} [Group G] [Finite G] (h26 : Work.GW2.Thm26Prop)
    (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) : 2 ∈ B.pi := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hSC, -⟩ := h26 G hFT hCtx B
  have ht : B.t ∈ Work.GW2.pCoreIn 2 B.Hhat := by
    rw [← hSC]
    refine ⟨B.S0_le B.t_mem, ?_⟩
    show B.t ∈ Subgroup.centralizer (B.U : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have huH : u ∈ B.H := Subgroup.map_subtype_le _ hu
    exact (Subgroup.mem_centralizer_iff.mp huH B.t rfl).symm
  have h2p : 2 ∣ Nat.card (Work.GW2.pCoreIn 2 B.Hhat) := by
    have h := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr ht)
    rwa [Nat.card_zpowers, B.t_order] at h
  have hle : Work.GW2.pCoreIn 2 B.Hhat ≤ Work.GW2.fittingIn B.Hhat := by
    rw [Work.GW2.pCoreIn, Work.GW2.fittingIn]
    exact Subgroup.map_mono (pCore_le_fitting_local (G := ↥B.Hhat) 2)
  have hdvd : Nat.card (Work.GW2.pCoreIn 2 B.Hhat) ∣ Nat.card (Work.GW2.fittingIn B.Hhat) :=
    Subgroup.card_dvd_of_le hle
  rw [Work.GW2.BenderSetup.pi, Work.GW2.primesOf]
  exact Nat.Prime.mem_primeFactors Nat.prime_two (h2p.trans hdvd)
    (Nat.card_ne_zero.mpr ⟨⟨B.t, hle ht⟩, inferInstance⟩)

/-- `F_{π'}(K)` has odd order (a `π'`-group, and `2 ∈ π`). -/
theorem odd_card_fittingPiIn_pi_compl_local {G : Type} [Group G] [Finite G]
    (h26 : Work.GW2.Thm26Prop) (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (K : Subgroup G) :
    Odd (Nat.card (Work.GW2.fittingPiIn B.piᶜ K)) := by
  have hcard : Nat.card (Work.GW2.fittingPiIn B.piᶜ K)
      = Nat.card (Work.GW2.piCore B.piᶜ ↥(Work.GW2.fitting K)) := by
    rw [Work.GW2.fittingPiIn, Work.GW2.fittingPi,
      Subgroup.card_map_of_injective K.subtype_injective]
    exact Subgroup.card_map_of_injective (Work.GW2.fitting K).subtype_injective
  rw [hcard]
  refine (Work.RED.GW2.odd_iff_isPiSubgroup_ne_two _).mpr ?_
  refine Subgroup.IsPiSubgroup.mono ?_ (isPiSubgroup_piCore_local (G := ↥(Work.GW2.fitting K)) B.piᶜ)
  intro q hq hq2
  rw [Set.mem_compl_iff] at hq
  exact hq (hq2 ▸ two_mem_pi_local h26 hFT hCtx B)

/-! ## 3. `2 ∈ π` and `t` inverts `F_{2'}(M)` -/

/-- Bender 1981, Lemma 2.7 (step 3): `t` inverts `F_{π'}(M)`.

By Lemma 2.3(ii), `F_{π'}(M) ⊓ Ĥ = ⊥`; since `t ∈ M` normalizes the characteristic subgroup
`F_{π'}(M) ≤ M` and the fixed points of `t` in `G` lie in `C_G(t) = B.H ≤ Ĥ`, the involution `t`
acts fixed-point-freely on `F_{π'}(M)`, hence inverts it (`Work.BMAX.InvolutionInverts`). -/
theorem inverts_fittingPiIn_pi_compl_local {G : Type} [Group G] [Finite G]
    (h23 : Work.GW2.Lemma23Prop) (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (M : Subgroup G) (hD : L27Hyp B M) :
    Work.GW2.Inverts B.t (Work.GW2.fittingPiIn B.piᶜ M) := by
  have hdisj : Work.GW2.fittingPiIn B.piᶜ M ⊓ B.Hhat = ⊥ :=
    (h23 G hFT hCtx B M hD.M_ne_top hD.rel).2.1
  have ht2 : B.t * B.t = 1 := by
    have h : B.t ^ 2 = 1 := by
      have := pow_orderOf_eq_one B.t
      rwa [B.t_order] at this
    simpa [pow_two] using h
  have htN : B.t ∈ Subgroup.normalizer
      ((Work.GW2.fittingPiIn B.piᶜ M : Subgroup G) : Set G) :=
    le_normalizer_fittingPiIn_local B.piᶜ M hD.t_mem
  refine Work.BMAX.InvolutionInverts _ B.t ht2 htN ?_
  intro x hx hxfix
  have hxH : x ∈ B.Hhat := B.H_le_Hhat (by
    show x ∈ Subgroup.centralizer ({B.t} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have h2 := congrArg (· * B.t) hxfix
    simpa [mul_assoc] using h2)
  have hmem : x ∈ Work.GW2.fittingPiIn B.piᶜ M ⊓ B.Hhat := ⟨hx, hxH⟩
  rw [hdisj] at hmem
  exact Subgroup.mem_bot.mp hmem



end Work.CORE2B
