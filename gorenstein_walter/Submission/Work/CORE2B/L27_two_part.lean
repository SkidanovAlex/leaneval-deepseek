import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.t_central_in_S
import Submission.Work.CORE2B.isPGroup_pCoreIn_two
import Submission.Work.CORE2B.BenderCtx_sylow_not_cyclic
import Submission.Work.CORE2B.sylow_central_of_large_inter
import Submission.Work.CORE2B.sylow_central_of_mem_twoResidual
import Submission.Work.RED.DihedralSubgroup
import Submission.Work.RED.DihOrCycSubgroup
import Submission.Work.Dihedral.Defs
import Submission.OddOrder.Isaacs.Ch01_Sylow.Basic
import Submission.OddOrder.Isaacs.Ch03_SplitExtensions.Theorem315
import Submission.OddOrder.GroupTheory.SubgroupInAmbient

/-!
# CORE2B — Bender 1981, Lemma 2.7, step 3, first half: `t` centralizes `F₂(M)`

The leaf `Work.CORE2B.L27_two_part_centralized` says: for a minimal counterexample `G`, a
`BenderSetup B` and a subgroup `M` satisfying `L27Hyp B M`, the central involution `t` of the
dihedral Sylow 2-subgroup `S` centralizes `F₂(M) = O₂(F(M))` (realized in `G` as
`Work.GW2.fittingPiIn {2} M`).

The proof has three ingredients.

* `F₂(M) = O₂(F(M)) ≤ O₂(M)`: `O₂(F(M))` is characteristic in the normal subgroup
  `F(M) ◁ M`, hence a normal 2-subgroup of `M`; so it lies in the largest normal 2-subgroup
  `O₂(M)` of `M` (`fitting_two_le_two_core`).
* `O₂(M) ≤ C_G(t)`: a normal 2-subgroup lies in every Sylow 2-subgroup of `M`, so it suffices
  that some Sylow 2-subgroup of `M` commutes with `t`, i.e. that `t` is 2-central in `M`
  (`pCoreIn_two_le_centralizer_of_sylow`).  This is the group-theoretic crux, isolated in
  `sylow_central_of_large_inter` (the case `8 ≤ |S ⊓ M|`) and
  `sylow_central_of_mem_twoResidual` (the case `t ∈ O²(M)`); the third alternative of
  `L27Hyp.size`, `|S| = 4`, is elementary because then every 2-subgroup of `G` is abelian
  (`sylow_central_of_card_four`).
* `S ≤ C_G(t)` is `Work.CORE2B.t_central_in_S`.

None of `h23`, `h26`, the toolkit `T`, `FeitThompsonProp` or `BenderCtx` (except for the fact
that the Sylow 2-subgroups of `G` are dihedral) is used.
-/

namespace Work.CORE2B

open Subgroup

set_option linter.style.haveILetI false

namespace L27two

/-! ## 1. Local copies of the core bridges

`Submission.Work.CORE2B.L27_api` carries the same bridges, but it is under revision; the
short copies below keep this file self-contained.  They use only the ported odd-order library,
which cannot be imported next to `Submission.Work.GLUE.*` / `Submission.Work.BMAX.*`
(those re-declare the `Work.GW2` vocabulary of `Submission.Work.CORE2B.Defs`). -/

/-- `Work.GW2.pCore p G` is the library's `O_p(G)`. -/
theorem pCore_eq_opCore {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    Work.GW2.pCore p G = OddOrder.Isaacs.Ch01.opCore p G := by
  have hS : sSup {N : Subgroup G | N.Normal ∧ IsPGroup p N}
      = OddOrder.Isaacs.Ch01.opCore p G := by
    refine le_antisymm (sSup_le ?_) (le_sSup ?_)
    · rintro N ⟨hN, hpN⟩
      exact OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore (N := N) hpN
    · exact ⟨OddOrder.Isaacs.Ch01.opCore.normal p G,
        OddOrder.Isaacs.Ch01.opCore_isPGroup p G⟩
  rw [Work.GW2.pCore, hS, Subgroup.normalCore_eq_self]

/-- `O_p(G)` is characteristic in `G`. -/
theorem pCore_characteristic {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    (Work.GW2.pCore p G).Characteristic := by
  rw [pCore_eq_opCore]
  exact OddOrder.Isaacs.Ch01.opCore.characteristic p G

/-- `O_p(G)` is a `p`-group. -/
theorem pCore_isPGroup {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    IsPGroup p ↥(Work.GW2.pCore p G) := by
  rw [pCore_eq_opCore]
  exact OddOrder.Isaacs.Ch01.opCore_isPGroup p G

/-- Universal property of `O_p(G)`: every normal `p`-subgroup lies in it. -/
theorem le_pCore_of_normal_isPGroup {G : Type} [Group G] {p : ℕ} {N : Subgroup G} [N.Normal]
    (hN : IsPGroup p ↥N) : N ≤ Work.GW2.pCore p G :=
  Subgroup.normal_le_normalCore.mpr (le_sSup ⟨‹N.Normal›, hN⟩)

/-- `Work.GW2.piCore π G` is the library's `O_π(G)`. -/
theorem piCore_eq_oPiCore {G : Type} [Group G] (π : Set ℕ) :
    Work.GW2.piCore π G = OddOrder.Isaacs.Ch03.oPiCore π G := by
  have h1 : sSup {N : Subgroup G | N.Normal ∧
      OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π N} ≤ OddOrder.Isaacs.Ch03.oPiCore π G := by
    rw [OddOrder.Isaacs.Ch03.oPiCore]
    exact sSup_le (fun N hN => le_iSup (fun H : {H : Subgroup G // H.Normal ∧
      OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π H} => (H.val : Subgroup G)) ⟨N, hN⟩)
  have h2 : OddOrder.Isaacs.Ch03.oPiCore π G ≤ (sSup {N : Subgroup G | N.Normal ∧
      OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π N}).normalCore := by
    haveI : (OddOrder.Isaacs.Ch03.oPiCore π G).Normal :=
      OddOrder.Isaacs.Ch03.oPiCore.normal π G
    refine Subgroup.normal_le_normalCore.mpr ?_
    rw [OddOrder.Isaacs.Ch03.oPiCore]
    exact iSup_le (fun H => le_sSup H.property)
  refine le_antisymm ?_ ?_
  · calc Work.GW2.piCore π G
        = (sSup {N : Subgroup G | N.Normal ∧
            OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π N}).normalCore := rfl
      _ ≤ sSup {N : Subgroup G | N.Normal ∧
            OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π N} := Subgroup.normalCore_le _
      _ ≤ OddOrder.Isaacs.Ch03.oPiCore π G := h1
  · calc OddOrder.Isaacs.Ch03.oPiCore π G
        ≤ (sSup {N : Subgroup G | N.Normal ∧
            OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π N}).normalCore := h2
      _ = Work.GW2.piCore π G := rfl

/-- `O_π(G)` is characteristic in `G`. -/
theorem piCore_characteristic {G : Type} [Group G] [Finite G] (π : Set ℕ) :
    (Work.GW2.piCore π G).Characteristic := by
  rw [piCore_eq_oPiCore]
  exact OddOrder.Isaacs.Ch03.oPiCore.characteristic π G

/-- `O_{2}(-)` is a 2-group. -/
theorem piCore_two_isPGroup {G : Type} [Group G] [Finite G] (H : Subgroup G) :
    IsPGroup 2 ↥(Work.GW2.piCore ({2} : Set ℕ) H) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [piCore_eq_oPiCore]
  exact OddOrder.GroupTheory.isPGroup_of_isPiSubgroup_singleton
    (OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (G := H) ({2} : Set ℕ))

/-- `F_π(K) = O_π(F(K))` is normal in `↥K`. -/
theorem fittingPi_normal {G : Type} [Group G] [Finite G] (π : Set ℕ) (K : Subgroup G) :
    (Work.GW2.fittingPi π K).Normal := by
  haveI hFK : (Work.GW2.fitting K).Normal := Subgroup.normalCore_normal _
  haveI hchar : (Work.GW2.piCore π ↥(Work.GW2.fitting K)).Characteristic :=
    piCore_characteristic π
  exact ConjAct.normal_of_characteristic_of_normal

/-- A group of order at most four is commutative. -/
theorem isMulCommutative_of_card_le_four {X : Type} [Group X] [Finite X]
    (h : Nat.card X ≤ 4) :
    IsMulCommutative X := by
  by_cases hcyc : IsCyclic X
  · exact hcyc.isMulCommutative
  · have htwo : ∀ x : X, orderOf x ∣ 2 := by
      intro x
      have hdvd : orderOf x ∣ Nat.card X := orderOf_dvd_natCard x
      have hne : orderOf x ≠ Nat.card X := fun hc =>
        hcyc (isCyclic_iff_exists_orderOf_eq_natCard.mpr ⟨x, hc⟩)
      have hcard : Nat.card X = 1 ∨ Nat.card X = 2 ∨ Nat.card X = 3 ∨ Nat.card X = 4 := by
        have := Nat.card_pos (α := X)
        omega
      rcases hcard with hc | hc | hc | hc
      · rw [hc, Nat.dvd_one] at hdvd
        rw [hdvd]; exact one_dvd 2
      · rw [hc] at hdvd
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
        · rw [h1]; exact one_dvd 2
        · exact absurd (by rw [hc, h2]) hne
      · rw [hc] at hdvd
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
        · rw [h1]; exact one_dvd 2
        · exact absurd (by rw [hc, h3]) hne
      · rw [hc] at hdvd
        rcases (Nat.dvd_prime_pow (p := 2) (m := 2) Nat.prime_two).mp (by simpa using hdvd) with
          ⟨k, hk, hkx⟩
        interval_cases k
        · rw [show orderOf x = 1 from by simpa using hkx]; exact one_dvd 2
        · rw [show orderOf x = 2 from by simpa using hkx]
        · exact absurd (by rw [hc]; simpa using hkx) hne
    have hsq : ∀ x : X, x * x = 1 := by
      intro x
      rw [← pow_two]
      exact (orderOf_dvd_iff_pow_eq_one (n := 2)).mp (htwo x)
    refine ⟨⟨fun a b => ?_⟩⟩
    have hab : (a * b) * (a * b) = 1 := hsq (a * b)
    calc a * b = ((a * b) * (a * b)) * (a * b) := by rw [hab, one_mul]
      _ = (a * b)⁻¹ := by rw [hab, one_mul, inv_eq_of_mul_eq_one_right hab]
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by
          rw [inv_eq_of_mul_eq_one_right (hsq a), inv_eq_of_mul_eq_one_right (hsq b)]

/-! ## 2. `F₂(M) ≤ O₂(M)` -/

/-- `F₂(M) = O₂(F(M)) ≤ O₂(M)`: `O₂(F(M))` is characteristic in the normal subgroup `F(M)`,
hence a normal 2-subgroup of `↥M`. -/
theorem fitting_two_le_two_core {G : Type} [Group G] [Finite G] (M : Subgroup G) :
    Work.GW2.fittingPiIn {2} M ≤ Work.GW2.pCoreIn 2 M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmain : (Work.GW2.piCore ({2} : Set ℕ) ↥(Work.GW2.fitting ↥M)).map
      (Work.GW2.fitting ↥M).subtype ≤ Work.GW2.pCore 2 ↥M := by
    haveI hFK : (Work.GW2.fitting ↥M).Normal := Subgroup.normalCore_normal _
    haveI hchar : (Work.GW2.piCore ({2} : Set ℕ) ↥(Work.GW2.fitting ↥M)).Characteristic :=
      piCore_characteristic {2}
    haveI hnorm : ((Work.GW2.piCore ({2} : Set ℕ) ↥(Work.GW2.fitting ↥M)).map
        (Work.GW2.fitting ↥M).subtype).Normal := ConjAct.normal_of_characteristic_of_normal
    exact le_pCore_of_normal_isPGroup
      ((piCore_two_isPGroup (G := ↥M) (H := Work.GW2.fitting ↥M)).map
        (Work.GW2.fitting ↥M).subtype)
  calc Work.GW2.fittingPiIn {2} M
      = ((Work.GW2.piCore ({2} : Set ℕ) ↥(Work.GW2.fitting ↥M)).map
          (Work.GW2.fitting ↥M).subtype).map M.subtype := rfl
    _ ≤ (Work.GW2.pCore 2 ↥M).map M.subtype := Subgroup.map_mono hmain
    _ = Work.GW2.pCoreIn 2 M := rfl

/-! ## 3. `O₂(M) ≤ C_G(t)` from a Sylow 2-subgroup of `M` commuting with `t` -/

/-- A normal 2-subgroup of `M` lies in every Sylow 2-subgroup of `M`; hence `O₂(M)` is
centralized by `t` as soon as some Sylow 2-subgroup of `M` is. -/
theorem pCoreIn_two_le_centralizer_of_sylow {G : Type} [Group G] [Finite G] (M : Subgroup G)
    (t : G) (P : Sylow 2 M) (hP : ∀ x ∈ (P : Subgroup M), (x : G) * t = t * (x : G)) :
    Work.GW2.pCoreIn 2 M ≤ Subgroup.centralizer ({t} : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : Work.GW2.pCore 2 ↥M ≤ (P : Subgroup M) :=
    IsPGroup.le_sylow_of_normal (pCore_isPGroup (G := ↥M) (p := 2)) P
  intro x hx
  rw [Work.GW2.pCoreIn] at hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst hz
  exact (hP y (hle hy)).symm

/-! ## 4. The case `|S| = 4`: all 2-subgroups of `G` are abelian -/

/-- If `S` is a Sylow 2-subgroup of `G` of order `4`, every 2-subgroup of `G` has order at
most `4`, hence is abelian; a Sylow 2-subgroup of `M ∋ t` therefore centralizes `t`. -/
theorem sylow_central_of_card_four {G : Type} [Group G] [Finite G] (S : Sylow 2 G) (t : G)
    (ht : orderOf t = 2) (hcard : Nat.card (S : Subgroup G) = 4) (M : Subgroup G)
    (htM : t ∈ M) (hnc : ∀ P : Sylow 2 M, ¬ IsCyclic P) :
    ∃ P : Sylow 2 M, ∀ x ∈ (P : Subgroup M), (x : G) * t = t * (x : G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hgen : IsPGroup 2 ↥(Subgroup.zpowers (⟨t, htM⟩ : M)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, ht]
    norm_num
  obtain ⟨P, hP⟩ := hgen.exists_le_sylow
  refine ⟨P, ?_⟩
  have hPcard : Nat.card ↥(P : Subgroup M) ≤ 4 := by
    obtain ⟨Q, hQ⟩ := (P.isPGroup'.map M.subtype).exists_le_sylow
    have hQS : Nat.card ↥(Q : Subgroup G) = 4 := by
      haveI : Finite (Sylow 2 G) := inferInstance
      rw [← hcard]
      exact Nat.card_congr (Sylow.equiv Q S).toEquiv
    calc Nat.card ↥(P : Subgroup M)
        = Nat.card ↥(((P : Subgroup M)).map M.subtype) :=
          (Subgroup.card_map_of_injective M.subtype_injective).symm
      _ ≤ Nat.card ↥(Q : Subgroup G) := Subgroup.card_le_of_le hQ
      _ = 4 := hQS
  haveI : IsMulCommutative ↥(P : Subgroup M) := isMulCommutative_of_card_le_four hPcard
  intro x hx
  have htP : (⟨t, htM⟩ : M) ∈ (P : Subgroup M) := hP (Subgroup.mem_zpowers (⟨t, htM⟩ : M))
  have hcommP : (⟨x, hx⟩ : ↥(P : Subgroup M)) * ⟨⟨t, htM⟩, htP⟩
      = ⟨⟨t, htM⟩, htP⟩ * ⟨x, hx⟩ := mul_comm' _ _
  exact congrArg (fun y : ↥(P : Subgroup M) => ((y : M) : G)) hcommP

/-! ## 5. The two hard cases of the size hypothesis

Under `L27Hyp B M` the Sylow 2-subgroup `S` of `G` is dihedral, `t` is central in `S`, and
`M ∋ t` has non-cyclic Sylow 2-subgroups.  The two lemmas below assert that `t` is 2-central
in `M` in the two remaining cases of `L27Hyp.size`. -/

/-- **Case `8 ≤ |S ⊓ M|`.** -/
theorem sylow_central_of_large_inter {G : Type} [Group G] [Finite G] (S : Sylow 2 G) (n : ℕ)
    (hS : Nonempty ((S : Subgroup G) ≃* DihedralGroup n)) (t : G) (ht : orderOf t = 2)
    (htc : ∀ x ∈ (S : Subgroup G), x * t = t * x) (M : Subgroup G) (htM : t ∈ M)
    (hnc : ∀ P : Sylow 2 M, ¬ IsCyclic P)
    (hbig : 8 ≤ Nat.card ((S : Subgroup G) ⊓ M : Subgroup G)) :
    ∃ P : Sylow 2 M, ∀ x ∈ (P : Subgroup M), (x : G) * t = t * (x : G) :=
  Work.CORE2B.sylow_central_of_large_inter S n hS t ht htc M htM hnc hbig

/-- **Case `t ∈ O²(M)`.** -/
theorem sylow_central_of_mem_twoResidual {G : Type} [Group G] [Finite G] (S : Sylow 2 G)
    (n : ℕ) (hS : Nonempty ((S : Subgroup G) ≃* DihedralGroup n)) (t : G)
    (ht : orderOf t = 2) (htc : ∀ x ∈ (S : Subgroup G), x * t = t * x) (M : Subgroup G)
    (htM : t ∈ M) (hnc : ∀ P : Sylow 2 M, ¬ IsCyclic P)
    (hres : t ∈ Work.GW2.twoResidualIn M) :
    ∃ P : Sylow 2 M, ∀ x ∈ (P : Subgroup M), (x : G) * t = t * (x : G) :=
  Work.CORE2B.sylow_central_of_mem_twoResidual S n hS t ht htc M htM hnc hres

end L27two

/-! ## 6. The leaf -/

theorem L27_two_part : Work.CORE2B.L27_two_part_centralized := by
  intro T h23 h26 G _ _ hFT hCtx B M hM
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hncS : ¬ IsCyclic ↥(B.S : Subgroup G) := BenderCtx_sylow_not_cyclic hCtx B.S
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Nonempty (↥(B.S : Subgroup G) ≃* DihedralGroup n) := by
    rcases hCtx.sylow B.S with h | h
    · exact absurd h hncS
    · exact h
  have htc : ∀ x ∈ (B.S : Subgroup G), x * B.t = B.t * x := t_central_in_S B
  have key : ∀ P : Sylow 2 M, (∀ x ∈ (P : Subgroup M), (x : G) * B.t = B.t * (x : G)) →
      Work.GW2.fittingPiIn {2} M ≤ Subgroup.centralizer ({B.t} : Set G) :=
    fun P hP => (L27two.fitting_two_le_two_core M).trans
      (L27two.pCoreIn_two_le_centralizer_of_sylow M B.t P hP)
  rcases hM.size with h8 | h4 | hres
  · obtain ⟨P, hP⟩ := L27two.sylow_central_of_large_inter B.S n hn B.t B.t_order htc M hM.t_mem
      hM.sylow_nc h8
    exact key P hP
  · obtain ⟨P, hP⟩ := L27two.sylow_central_of_card_four B.S B.t B.t_order h4 M hM.t_mem
      hM.sylow_nc
    exact key P hP
  · obtain ⟨P, hP⟩ := L27two.sylow_central_of_mem_twoResidual B.S n hn B.t B.t_order htc M
      hM.t_mem hM.sylow_nc hres
    exact key P hP

end Work.CORE2B
