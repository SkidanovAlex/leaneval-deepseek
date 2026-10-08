import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.oddCore_odd
import Submission.Work.CORE2B.BenderCtx_sylow_not_cyclic
import Submission.Work.CORE2B.dihedral_index_two
import Submission.Work.CORE2B.t_central_in_S
import Submission.Work.BMAX.InvolutionInverts
import Submission.Work.RED.even_dihedral_param_of_isPGroup_two_not_isCyclic
import Submission.OddOrder.GroupTheory.FittingSelfCentralizing
import Submission.OddOrder.Isaacs.Ch01_Sylow.Main
import Submission.Work.CORE2B.L27_solvable_base

/-!
# AREA CORE2B — `I_U(s)` is a Hall subgroup of `F(U)` (Bender 1981, Theorem 2.10, first half)

This module holds the group-theoretic pieces of the target
`Work.CORE2B.Thm210_hall_and_normal` that do not mention Bender's configuration.

The mathematical content is Bender's proof of the first half of Theorem 2.10 (p. 222):

* for each prime `p`, `s` centralizes or inverts `O_p(U)` (Bender's per-prime step);
* hence (the key step) every `x ∈ I_U(s)` centralizes `F(U)`, so `I_U(s) ⊆ F(U)`;
* and then `I_U(s) = I_{F(U)}(s) = ∏_{p inverted} O_p(U)` is a Hall subgroup of `F(U)`,
  normal in `U`.

The key step is proved with the conjugation automorphism `α = conj x` of `O_p(U)`: since
`s x s⁻¹ = x⁻¹` one has `σ α σ⁻¹ = α⁻¹` for `σ = conj s`, and since `σ` is the identity or the
inversion one gets `α = α⁻¹`; as `x` has odd order, `α² = 1` and `ord(α) ∣ ord(x)` force
`α = 1`.
-/

open scoped MatrixGroups

namespace Work.CORE2B

open Subgroup

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## 1. The bridge to the odd-order library's Fitting subgroup -/

/-- `Work.GW2.fitting G` is `OddOrder.Isaacs.Ch01.fitting G`, the join of the normal nilpotent
subgroups. -/
theorem hall_fitting_eq_isaacsFitting {G : Type} [Group G] [Finite G] :
    Work.GW2.fitting G = OddOrder.Isaacs.Ch01.fitting G := by
  have hS : sSup {N : Subgroup G | N.Normal ∧ Group.IsNilpotent N}
      = OddOrder.Isaacs.Ch01.fitting G := by
    refine le_antisymm (sSup_le ?_) (le_sSup ?_)
    · rintro N ⟨hN, hnil⟩
      haveI : N.Normal := hN
      haveI : Group.IsNilpotent ↥N := hnil
      exact OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
    · exact ⟨OddOrder.Isaacs.Ch01.fitting.normal G,
        OddOrder.Isaacs.Ch01.fitting.isNilpotent⟩
  haveI : (OddOrder.Isaacs.Ch01.fitting G).Normal :=
    OddOrder.Isaacs.Ch01.fitting.normal G
  rw [Work.GW2.fitting, hS]
  exact Subgroup.normalCore_eq_self _

/-- The Fitting subgroup is nilpotent. -/
theorem hall_isNilpotent_fitting {G : Type} [Group G] [Finite G] :
    Group.IsNilpotent ↥(Work.GW2.fitting G) :=
  (Group.isNilpotent_congr (MulEquiv.subgroupCongr (hall_fitting_eq_isaacsFitting (G := G)))).mpr
    (OddOrder.Isaacs.Ch01.fitting.isNilpotent (G := G))

/-- `Work.GW2.pCore p G = O_p(G)` in the odd-order library's sense. -/
theorem hall_pCore_eq_opCore {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    Work.GW2.pCore p G = OddOrder.Isaacs.Ch01.opCore p G := by
  have h1 : sSup {N : Subgroup G | N.Normal ∧ IsPGroup p N}
      ≤ OddOrder.Isaacs.Ch01.opCore p G := by
    refine sSup_le ?_
    rintro N ⟨hN, hpg⟩
    haveI : N.Normal := hN
    exact OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore hpg
  have h2 : OddOrder.Isaacs.Ch01.opCore p G
      ≤ sSup {N : Subgroup G | N.Normal ∧ IsPGroup p N} :=
    le_sSup ⟨OddOrder.Isaacs.Ch01.opCore.normal p G,
      OddOrder.Isaacs.Ch01.opCore_isPGroup p G⟩
  have hEq : sSup {N : Subgroup G | N.Normal ∧ IsPGroup p N}
      = OddOrder.Isaacs.Ch01.opCore p G := le_antisymm h1 h2
  rw [Work.GW2.pCore, hEq]
  exact Subgroup.normalCore_eq_self _

/-- `O_p(G)` (area CORE2B) is characteristic. -/
theorem hall_pCore_characteristic {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    (Work.GW2.pCore p G).Characteristic := by
  rw [hall_pCore_eq_opCore]
  exact OddOrder.Isaacs.Ch01.opCore.characteristic p G

/-! ## 2. Conjugation invariance of `N.map U.subtype` for characteristic `N ≤ ↥U` -/

/-- If `N` is characteristic in `↥U` and `g ∈ N_G(U)`, then conjugation by `g` fixes the
subgroup `N.map U.subtype` of the ambient group. -/
theorem map_conj_map_subtype_eq_of_characteristic {G : Type} [Group G]
    {U : Subgroup G} {N : Subgroup ↥U} (hN : N.Characteristic) {g : G}
    (hg : g ∈ Subgroup.normalizer (U : Set G)) :
    (N.map U.subtype).map (MulAut.conj g).toMonoidHom = N.map U.subtype := by
  have hmapU : U.map (MulAut.conj g).toMonoidHom = U :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  let σ : ↥U ≃* ↥U :=
    (Subgroup.equivMapOfInjective U (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr hmapU)
  have hσ : N.map σ.toMonoidHom = N := (Subgroup.characteristic_iff_map_eq.mp hN) σ
  have hcomp : ((MulAut.conj g).toMonoidHom.comp U.subtype) = (U.subtype.comp σ.toMonoidHom) := by
    ext x
    rfl
  calc (N.map U.subtype).map (MulAut.conj g).toMonoidHom
      = N.map ((MulAut.conj g).toMonoidHom.comp U.subtype) := Subgroup.map_map _ _ _
    _ = N.map (U.subtype.comp σ.toMonoidHom) := by rw [hcomp]
    _ = (N.map σ.toMonoidHom).map U.subtype := (Subgroup.map_map _ _ _).symm
    _ = N.map U.subtype := by rw [hσ]


/-- `U` normalizes `O_p(U)` (as a subgroup of the ambient group). -/
theorem le_normalizer_pCoreIn_local {G : Type} [Group G] (p : ℕ) (U : Subgroup G) :
    U ≤ Subgroup.normalizer ((Work.GW2.pCoreIn p U : Subgroup G) : Set G) := by
  simpa only [Work.GW2.pCoreIn] using
    le_normalizer_map_subtype_local U (Work.GW2.pCore p U) (Work.GW2.pCore_normal p U)

/-- If `g ∈ N_G(U)` then conjugation by `g` fixes `Work.GW2.pCoreIn p U`. -/
theorem map_conj_pCoreIn {G : Type} [Group G] [Finite G] {U : Subgroup G} {p : ℕ}
    [Fact p.Prime] {g : G} (hg : g ∈ Subgroup.normalizer (U : Set G)) :
    (Work.GW2.pCoreIn p U).map (MulAut.conj g).toMonoidHom = Work.GW2.pCoreIn p U := by
  rw [Work.GW2.pCoreIn]
  exact map_conj_map_subtype_eq_of_characteristic (hall_pCore_characteristic (G := ↥U) (p := p)) hg


/-! ## 3. `F(U)` is the join of the `O_p(U)` -/

/-- `F(U) = ⨆_p O_p(U)` (over the primes). -/
theorem fittingIn_eq_iSup_pCoreIn {G : Type} [Group G] [Finite G] (U : Subgroup G) :
    Work.GW2.fittingIn U = ⨆ p : Nat.Primes, Work.GW2.pCoreIn (p : ℕ) U := by
  rw [Work.GW2.fittingIn, hall_fitting_eq_isaacsFitting]
  rw [show OddOrder.Isaacs.Ch01.fitting ↥U
        = ⨆ p : Nat.Primes, OddOrder.Isaacs.Ch01.opCore (p : ℕ) ↥U from rfl]
  rw [Subgroup.map_iSup]
  refine iSup_congr fun p => ?_
  haveI : Fact (Nat.Prime (p : ℕ)) := ⟨p.2⟩
  rw [Work.GW2.pCoreIn, hall_pCore_eq_opCore (G := ↥U) (p := (p : ℕ))]

/-! ## 4. The key step: `x ∈ I_U(s)` commutes with `O_p(U)` -/

/-- **The key step of Bender's argument.**  If the involution `s` centralizes or inverts
`O_p(U)`, then every `x ∈ I_U(s)` commutes with every element of `O_p(U)`.

Indeed `σ := conj s` and `α := conj x` are automorphisms of `O_p(U)` with `σ α σ⁻¹ = α⁻¹`
(because `s x s⁻¹ = x⁻¹`), and `σ` is the identity or the inversion, so `α² = 1`; as `x` has odd
order, `ord α ∣ ord x` is odd and `α = 1`. -/
theorem invSet_commute_pCore {G : Type} [Group G] [Finite G]
    (U : Subgroup G) (s x y : G) (p : ℕ) [Fact p.Prime]
    (hoddU : Odd (Nat.card U)) (hs2 : s * s = 1)
    (hsN : s ∈ Subgroup.normalizer (U : Set G))
    (hx : x ∈ Work.GW2.invSet U s) (hy : y ∈ Work.GW2.pCoreIn p U)
    (hact : (∀ z ∈ Work.GW2.pCoreIn p U, s * z * s⁻¹ = z) ∨
            (∀ z ∈ Work.GW2.pCoreIn p U, s * z * s⁻¹ = z⁻¹)) :
    x * y = y * x := by
  have hoddx : Odd (orderOf x) :=
    Odd.of_dvd_nat hoddU (Subgroup.orderOf_dvd_natCard U hx.1)
  have hxinv : s * x * s⁻¹ = x⁻¹ := hx.2
  have hsxinv : s * x⁻¹ * s⁻¹ = x := by
    have h' : (s * x * s⁻¹)⁻¹ = s * x⁻¹ * s⁻¹ := by group
    rw [hxinv, inv_inv] at h'
    exact h'.symm
  have hxP : x ∈ Subgroup.normalizer ((Work.GW2.pCoreIn p U : Subgroup G) : Set G) :=
    le_normalizer_pCoreIn_local p U hx.1
  have hsP : s ∈ Subgroup.normalizer ((Work.GW2.pCoreIn p U : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (map_conj_pCoreIn (U := U) (p := p) hsN)
  have key : ∀ z ∈ Work.GW2.pCoreIn p U, x * z * x⁻¹ = x⁻¹ * z * x := by
    intro z hz
    have hzP : s * z * s⁻¹ ∈ Work.GW2.pCoreIn p U :=
      (Subgroup.mem_normalizer_iff.mp hsP z).mp hz
    have hzP' : x * z * x⁻¹ ∈ Work.GW2.pCoreIn p U :=
      (Subgroup.mem_normalizer_iff.mp hxP z).mp hz
    rcases hact with hcen | hinv
    · have h1 : s * (x * z * x⁻¹) * s⁻¹ = x⁻¹ * z * x := by
        rw [show s * (x * z * x⁻¹) * s⁻¹
              = (s * x * s⁻¹) * (s * z * s⁻¹) * (s * x⁻¹ * s⁻¹) by group,
            hxinv, hcen z hz, hsxinv]
      have h2 : s * (x * z * x⁻¹) * s⁻¹ = x * z * x⁻¹ := hcen _ hzP'
      exact h2.symm.trans h1
    · have hzinv : z⁻¹ ∈ Work.GW2.pCoreIn p U := inv_mem hz
      have hzP'' : x * z⁻¹ * x⁻¹ ∈ Work.GW2.pCoreIn p U :=
        (Subgroup.mem_normalizer_iff.mp hxP z⁻¹).mp hzinv
      have h1 : s * (x * z⁻¹ * x⁻¹) * s⁻¹ = x⁻¹ * z * x := by
        rw [show s * (x * z⁻¹ * x⁻¹) * s⁻¹
              = (s * x * s⁻¹) * (s * z⁻¹ * s⁻¹) * (s * x⁻¹ * s⁻¹) by group,
            hxinv, hinv z⁻¹ hzinv, hsxinv]
        simp
      have h2 : s * (x * z⁻¹ * x⁻¹) * s⁻¹ = (x * z⁻¹ * x⁻¹)⁻¹ := hinv _ hzP''
      have h3 : (x * z⁻¹ * x⁻¹)⁻¹ = x * z * x⁻¹ := by group
      exact h3.symm.trans (h2.symm.trans h1)
  have hkey2 : ∀ z ∈ Work.GW2.pCoreIn p U, x * x * z = z * (x * x) := by
    intro z hz
    have h := key z hz
    have h2 : x * (x * z * x⁻¹) * x = x * (x⁻¹ * z * x) * x := by rw [h]
    have h3 : x * (x * z * x⁻¹) * x = x * x * z := by group
    have h4 : x * (x⁻¹ * z * x) * x = z * (x * x) := by group
    rw [h3, h4] at h2
    exact h2
  obtain ⟨k, hk⟩ := hoddx
  have hpow : (x * x) ^ (k + 1) = x := by
    have h1 : (x * x) ^ (k + 1) = x ^ (2 * (k + 1)) := by rw [← pow_two, ← pow_mul]
    rw [h1, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, pow_succ,
      show x ^ (2 * k + 1) = 1 by rw [← hk, pow_orderOf_eq_one], one_mul]
  have hcomm : Commute (x * x) y := hkey2 y hy
  have hxx := (hcomm.pow_left (k + 1)).eq
  rwa [hpow] at hxx

/-- `I_U(s)` centralizes `F(U)` (Bender's step 3, first half). -/
theorem invSet_le_centralizer_fittingIn {G : Type} [Group G] [Finite G]
    (U : Subgroup G) (s : G) (hoddU : Odd (Nat.card U)) (hs2 : s * s = 1)
    (hsN : s ∈ Subgroup.normalizer (U : Set G))
    (hact : ∀ p : ℕ, Nat.Prime p →
      (∀ z ∈ Work.GW2.pCoreIn p U, s * z * s⁻¹ = z) ∨
      (∀ z ∈ Work.GW2.pCoreIn p U, s * z * s⁻¹ = z⁻¹)) :
    ∀ x ∈ Work.GW2.invSet U s, ∀ y ∈ Work.GW2.fittingIn U, x * y = y * x := by
  intro x hx y hy
  have hle : (⨆ p : Nat.Primes, Work.GW2.pCoreIn (p : ℕ) U) ≤
      Subgroup.centralizer ({x} : Set G) := by
    refine iSup_le fun p => ?_
    have hp : Nat.Prime (p : ℕ) := p.2
    haveI : Fact (Nat.Prime (p : ℕ)) := ⟨hp⟩
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact invSet_commute_pCore U s x z (p : ℕ) hoddU hs2 hsN hx hz (hact (p : ℕ) hp)
  have hy' : y ∈ Subgroup.centralizer ({x} : Set G) := by
    rw [fittingIn_eq_iSup_pCoreIn U] at hy
    exact hle hy
  rw [Subgroup.mem_centralizer_iff] at hy'
  exact hy' x (by simp)

/-- Hence `I_U(s) ⊆ F(U)` (Bender's step 3, using P. Hall's `C_U(F(U)) ≤ F(U)`). -/
theorem invSet_le_fittingIn {G : Type} [Group G] [Finite G] (U : Subgroup G) (s : G)
    (hsolv : Group.IsSolvable ↥U)
    (hC : ∀ x ∈ Work.GW2.invSet U s, ∀ y ∈ Work.GW2.fittingIn U, x * y = y * x) :
    ∀ x ∈ Work.GW2.invSet U s, x ∈ Work.GW2.fittingIn U := by
  intro x hx
  have hxU : x ∈ U := hx.1
  have hcen : (⟨x, hxU⟩ : ↥U) ∈
      Subgroup.centralizer ((Work.GW2.fitting ↥U : Subgroup ↥U) : Set ↥U) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    have hy' : (y : G) ∈ Work.GW2.fittingIn U := Subgroup.mem_map.mpr ⟨y, hy, rfl⟩
    exact (hC x hx (y : G) hy').symm
  have hcen' : (⟨x, hxU⟩ : ↥U) ∈
      Subgroup.centralizer
        ((OddOrder.Isaacs.Ch01.fitting ↥U : Subgroup ↥U) : Set ↥U) := by
    rw [← hall_fitting_eq_isaacsFitting]
    exact hcen
  have hle := OddOrder.GroupTheory.centralizer_fitting_le_fitting (G := ↥U)
  have hmem : (⟨x, hxU⟩ : ↥U) ∈ Work.GW2.fitting ↥U := by
    have := hle hcen'
    rwa [← hall_fitting_eq_isaacsFitting] at this
  exact Subgroup.mem_map.mpr ⟨⟨x, hxU⟩, hmem, rfl⟩


/-! ## 5. Glue with the `BenderSetup` configuration -/

/-- `S` is dihedral: the Sylow 2-subgroup of a `BenderCtx` is non-cyclic, and the context gives
`DihOrCycSylow`, so `S ≅ DihedralGroup n` for an even `n ≥ 2`. -/
theorem S_dihedral_iso {G : Type} [Group G] [Finite G] (hCtx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) :
    ∃ n : ℕ, 2 ≤ n ∧ Nonempty ((B.S : Subgroup G) ≃* DihedralGroup n) := by
  have hnc : ¬ IsCyclic ↥(B.S : Subgroup G) := BenderCtx_sylow_not_cyclic hCtx B.S
  rcases hCtx.sylow B.S with hcyc | ⟨n, hn⟩
  · exact absurd hcyc hnc
  · obtain ⟨heven, hne⟩ :=
      Work.RED.even_dihedral_param_of_isPGroup_two_not_isCyclic hn.some B.S.isPGroup' hnc
    refine ⟨n, ?_, hn⟩
    obtain ⟨k, hk⟩ := heven
    have hne0 : n ≠ 0 := NeZero.ne n
    omega

/-- `B.t` is the central involution of `S`. -/
theorem S_le_H_setup {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G) :
    (B.S : Subgroup G) ≤ B.H := by
  intro x hx
  have hcomm : x * B.t = B.t * x := t_central_in_S B x hx
  rw [Work.GW2.BenderSetup.H, Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact hcomm.symm

/-- `U` has odd order. -/
theorem odd_card_U_setup {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G) :
    Odd (Nat.card B.U) := by
  rw [Work.GW2.BenderSetup.U, Work.GW2.oddCoreIn,
    Subgroup.card_map_of_injective B.H.subtype_injective]
  exact oddCore_odd (G := ↥B.H)

/-- `S` normalises `U = O(H)`. -/
theorem mem_normalizer_U_of_mem_S {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    {s : G} (hs : s ∈ (B.S : Subgroup G)) : s ∈ Subgroup.normalizer (B.U : Set G) := by
  have hH : B.H ≤ Subgroup.normalizer (B.U : Set G) := by
    have h := le_normalizer_map_subtype_local B.H (Work.GW2.oddCore ↥B.H)
      (Work.GW2.oddCore_normal ↥B.H)
    simpa [Work.GW2.BenderSetup.U, Work.GW2.oddCoreIn] using h
  exact hH (S_le_H_setup B hs)

/-- Every element of `S \ S₀` is an involution. -/
theorem orderOf_eq_two_of_mem_S_notMem_S0 {G : Type} [Group G] [Finite G]
    (hCtx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) {s : G}
    (hs : s ∈ (B.S : Subgroup G)) (hs0 : s ∉ B.S0) : orderOf s = 2 := by
  obtain ⟨n, hn2, ⟨e⟩⟩ := S_dihedral_iso hCtx B
  exact dihedral_index_two n hn2 (B.S : Subgroup G) B.S0 ⟨e⟩ B.S0_le B.S0_cyclic B.S0_index s hs hs0

/-! ## 6. From the per-prime dichotomy to "centralizes or inverts" -/

/-- If an involution `s` normalising `K` fixes `K ∩ C_G(s)` at `1`, then it inverts `K`. -/
theorem hall_inverts_of_inf_centralizer_eq_bot {G : Type} [Group G] [Finite G]
    (K : Subgroup G) (s : G) (hs : s * s = 1) (hsN : s ∈ Subgroup.normalizer (K : Set G))
    (hbot : K ⊓ Subgroup.centralizer ({s} : Set G) = ⊥) :
    ∀ x ∈ K, s * x * s⁻¹ = x⁻¹ := by
  refine Work.BMAX.InvolutionInverts K s hs hsN ?_
  intro x hx hcon
  have hsx : s * x = x * s := by
    have hs1 : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
    have hcon' : s * x * s = x := by simpa [hs1] using hcon
    calc s * x = (s * x) * 1 := (mul_one _).symm
      _ = (s * x) * (s * s) := by rw [hs]
      _ = (s * x * s) * s := by group
      _ = x * s := by rw [hcon']
  have hmem : x ∈ K ⊓ Subgroup.centralizer ({s} : Set G) :=
    ⟨hx, Subgroup.mem_centralizer_iff.mpr (by
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact hsx)⟩
  rw [hbot] at hmem
  simpa using hmem

/-- `C_K(s) = ⊥` or `C_K(s) = K` for an involution `s` normalising `K` gives: `s` centralizes or
inverts `K`. -/
theorem centralizes_or_inverts_of_dichotomy {G : Type} [Group G] [Finite G]
    (K : Subgroup G) (s : G) (hs : s * s = 1) (hsN : s ∈ Subgroup.normalizer (K : Set G))
    (hdich : K ≤ Subgroup.centralizer ({s} : Set G) ∨
      K ⊓ Subgroup.centralizer ({s} : Set G) = ⊥) :
    (∀ x ∈ K, s * x * s⁻¹ = x) ∨ (∀ x ∈ K, s * x * s⁻¹ = x⁻¹) := by
  rcases hdich with hle | hbot
  · left
    intro x hx
    have hxs : s * x = x * s :=
      (Subgroup.mem_centralizer_iff.mp (hle hx)) s (Set.mem_singleton s)
    rw [show s * x * s⁻¹ = (s * x) * s⁻¹ from by group, hxs, mul_assoc,
      show s * s⁻¹ = 1 from mul_inv_cancel s, mul_one]
  · exact Or.inr (hall_inverts_of_inf_centralizer_eq_bot K s hs hsN hbot)

end Work.CORE2B
