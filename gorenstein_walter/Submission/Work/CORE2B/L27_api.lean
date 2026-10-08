/-
# CORE2B — support API for the leaf `L27_commutator_le`

This module collects the elementary (Mathlib + Feit–Thompson-closure level) facts about the
`Work.GW2` vocabulary that the proof of Bender 1981, Lemma 2.7 (a) needs.  Nothing here uses
another area's *contract* `Prop`s: the lemmas are either copies of the (short, self-contained)
bridges of `GLUE`, or new.

Contents:

* `piCore_eq_oPiCore`, `oddCore_eq_oPiCore`, `pCore_eq_opCore`, `fitting_eq_isaacsFitting` —
  the dictionary between `Work.GW2`'s `sSup`-definitions and the Feit–Thompson library's
  `OddOrder.Isaacs` notions (needed to use `IsPiSubgroup`-API, nilpotency of `F`, …).
* the universal properties of `O_p`, `O_π`, `O` and their monotonicity;
* `K ≤ N_G(O_π(F(K)))` / `K ≤ N_G(F_π(K))`: the relative cores are normal in the ambient
  subgroup;
* `t_mem_pCoreIn_two`, `two_mem_pi`: Theorem 2.6 gives `t ∈ O₂(Ĥ) ≠ 1`, whence `2 ∈ π(F(Ĥ))`;
* `normalizer_pCoreIn_two_eq_Hhat`: `N_G(O₂(Ĥ)) = Ĥ` (coatomicity of `Ĥ` + simplicity of `G`);
* `t_inverts_fittingPiIn_compl`: `t` inverts `F_{2'}(M)` (Lemma 2.3(ii) + fixed points).
-/import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.BMAX.InvolutionInverts
import Submission.Work.Dihedral.Defs
import Submission.Work.FUS.Dihedral
import Submission.Work.RED.Basic
import Submission.Work.RED.DihedralSubgroup
import Submission.Work.RED.DihOrCycSubgroup
import Submission.Work.RED.DihedralFacts
import Submission.Work.RED.le_center_of_card_eq_two
import Submission.Work.RED.even_dihedral_param_of_isPGroup_two_not_isCyclic
import Submission.OddOrder.FeitThompson
import Submission.Work.CORE2B.oddCore_odd

namespace Work.CORE2B

open Subgroup

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## 1. Dictionary with the Feit–Thompson closure -/

/-- `Work.GW2.piCore π G` is the library's `O_π(G)`. -/
theorem piCore_eq_oPiCore {G : Type*} [Group G] (π : Set ℕ) :
    Work.GW2.piCore π G = OddOrder.Isaacs.Ch03.oPiCore π G := by
  refine le_antisymm ?_ ?_
  · refine (Subgroup.normalCore_le _).trans ?_
    exact sSup_le (fun N hN =>
      le_iSup (fun H : {H : Subgroup G // H.Normal ∧
        OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup π H} => (H.val : Subgroup G)) ⟨N, hN⟩)
  · refine Subgroup.normal_le_normalCore.mpr ?_
    exact iSup_le (fun H => le_sSup H.property)


/-- `sSup` of the normal `π`-subgroups is `O_π(G)`. -/
theorem sSup_normal_isPiSubgroup_eq_oPiCore {G : Type*} [Group G] (π : Set ℕ) :
    sSup {N : Subgroup G | N.Normal ∧ Subgroup.IsPiSubgroup π N}
      = OddOrder.Isaacs.Ch03.oPiCore π G := by
  rw [OddOrder.Isaacs.Ch03.oPiCore]
  refine le_antisymm (sSup_le ?_) (iSup_le ?_)
  · rintro N ⟨hN, hpN⟩
    exact le_iSup_of_le ⟨N, hN, hpN⟩ le_rfl
  · rintro ⟨N, hN1, hN2⟩
    exact le_sSup ⟨hN1, hN2⟩

/-- `Work.GW2.oddCore G = O_{2'}(G)`. -/
theorem oddCore_eq_oPiCore {G : Type*} [Group G] [Finite G] :
    Work.GW2.oddCore G = OddOrder.Isaacs.Ch03.oPiCore {q : ℕ | q ≠ 2} G := by
  have hset : {N : Subgroup G | N.Normal ∧ Odd (Nat.card N)}
      = {N : Subgroup G | N.Normal ∧ Subgroup.IsPiSubgroup ({q : ℕ | q ≠ 2}) N} := by
    ext N
    exact and_congr_right fun _ => odd_iff_isPiSubgroup_ne_two N
  rw [Work.GW2.oddCore, hset, sSup_normal_isPiSubgroup_eq_oPiCore,
    Subgroup.normalCore_eq_self _]

/-- `Work.GW2.pCore p G = O_p(G)`. -/
theorem pCore_eq_opCore {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    Work.GW2.pCore p G = OddOrder.Isaacs.Ch01.opCore p G := by
  have hS : sSup {N : Subgroup G | N.Normal ∧ IsPGroup p N}
      = OddOrder.Isaacs.Ch01.opCore p G := by
    refine le_antisymm (sSup_le ?_) (le_sSup ?_)
    · rintro N ⟨hN, hpN⟩
      exact OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore (N := N) hpN
    · exact ⟨OddOrder.Isaacs.Ch01.opCore.normal p G,
        OddOrder.Isaacs.Ch01.opCore_isPGroup p G⟩
  rw [Work.GW2.pCore, hS]
  exact Subgroup.normalCore_eq_self _

/-- `Work.GW2.fitting G` is the library's `F(G)`. -/
theorem fitting_eq_isaacsFitting {G : Type*} [Group G] [Finite G] :
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
  rw [Work.GW2.fitting, hS]
  exact Subgroup.normalCore_eq_self _

/-! ## 2. Universal properties and monotonicity -/

/-- **Universal property of `O_p(G)`.** -/
theorem le_pCore_of_normal_isPGroup {G : Type*} [Group G] {p : ℕ} {N : Subgroup G} [N.Normal]
    (hN : IsPGroup p N) : N ≤ Work.GW2.pCore p G :=
  Subgroup.normal_le_normalCore.mpr (le_sSup ⟨‹N.Normal›, hN⟩)

-- Note: the universal property of `O_π(G)` (`le_piCore_of_normal_isPiGroup`) is proved in
-- `Submission.Work.CORE2B.L27_fittingPi_compl_of_odd` and is deliberately not repeated here, to
-- avoid a duplicate declaration when both modules are imported.

/-- **Universal property of `O(G)`.** -/
theorem le_oddCore_of_odd_normal {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (hN : Odd (Nat.card N)) : N ≤ Work.GW2.oddCore G :=
  Subgroup.normal_le_normalCore.mpr (le_sSup ⟨‹N.Normal›, hN⟩)

/-- `O_π` is monotone in `π`. -/
theorem piCore_mono {G : Type*} [Group G] {π₁ π₂ : Set ℕ} (h : π₁ ⊆ π₂) :
    Work.GW2.piCore π₁ G ≤ Work.GW2.piCore π₂ G := by
  rw [Work.GW2.piCore, Work.GW2.piCore]
  refine Subgroup.normalCore_mono (sSup_le ?_)
  rintro N ⟨hN, hpi⟩
  exact le_sSup ⟨hN, fun q hq => h (hpi q hq)⟩

/-- `F_π(G) ≤ F(G)`. -/
theorem fittingPi_le {G : Type*} [Group G] (π : Set ℕ) :
    Work.GW2.fittingPi π G ≤ Work.GW2.fitting G :=
  Subgroup.map_subtype_le _

/-- `pCore p G ≤ fitting G`. -/
theorem pCore_le_fitting {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    Work.GW2.pCore p G ≤ Work.GW2.fitting G := by
  refine Subgroup.normal_le_normalCore.mpr ?_
  refine (Subgroup.normalCore_le _).trans ?_
  refine sSup_le ?_
  intro N hN
  exact le_sSup ⟨hN.1, hN.2.isNilpotent⟩

/-- `fittingPiIn` is monotone in `π`. -/
theorem fittingPiIn_mono {G : Type*} [Group G] {π₁ π₂ : Set ℕ} (h : π₁ ⊆ π₂)
    (K : Subgroup G) : Work.GW2.fittingPiIn π₁ K ≤ Work.GW2.fittingPiIn π₂ K := by
  rw [Work.GW2.fittingPiIn, Work.GW2.fittingPiIn, Work.GW2.fittingPi, Work.GW2.fittingPi]
  exact Subgroup.map_mono (Subgroup.map_mono (piCore_mono h))

/-- `F_{2'}(M) = O_{2'}(F(M))` for the standard `π`-notation. -/
theorem fittingPiIn_eq_map_oPiCore {G : Type*} [Group G] (π : Set ℕ) (K : Subgroup G) :
    Work.GW2.fittingPiIn π K
      = (OddOrder.Isaacs.Ch03.oPiCore π ↥(Work.GW2.fitting ↥K)).map
          (K.subtype.comp (Work.GW2.fitting ↥K).subtype) := by
  rw [Work.GW2.fittingPiIn, Work.GW2.fittingPi, piCore_eq_oPiCore, Subgroup.map_map]

/-! ## 3. Normality of the relative cores in the ambient subgroup -/

/-- The image of a normal subgroup of `↥K` under `K.subtype` is normalized by `K`. -/
theorem le_normalizer_map_subtype {G : Type*} [Group G] (K : Subgroup G) (N : Subgroup ↥K)
    (hN : N.Normal) : K ≤ Subgroup.normalizer ((N.map K.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro k hk y hy
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
  exact Subgroup.mem_map.mpr ⟨(⟨k, hk⟩ : ↥K) * z * (⟨k, hk⟩ : ↥K)⁻¹, hN.conj_mem z hz _, rfl⟩

/-! ## 4. Theorem 2.6: `t ∈ O₂(Ĥ)`, `2 ∈ π` and `N_G(O₂(Ĥ)) = Ĥ` -/

/-- Theorem 2.6 gives `O₂(Ĥ) = S ⊓ C(U)`, and `t` lies in both factors. -/
theorem t_mem_pCoreIn_two {G : Type} [Group G] [Finite G] (h26 : Work.GW2.Thm26Prop)
    (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) : B.t ∈ Work.GW2.pCoreIn 2 B.Hhat := by
  obtain ⟨-, hSC, -⟩ := h26 G hFT hCtx B
  rw [← hSC]
  refine ⟨B.S0_le B.t_mem, ?_⟩
  show B.t ∈ Subgroup.centralizer (B.U : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have huH : u ∈ B.H := Subgroup.map_subtype_le _ hu
  exact (Subgroup.mem_centralizer_iff.mp huH B.t rfl).symm

/-- `O₂(Ĥ) ≠ 1`, hence `2 ∈ π(F(Ĥ))`. -/
theorem two_mem_pi {G : Type} [Group G] [Finite G] (h23 : Work.GW2.Lemma23Prop)
    (h26 : Work.GW2.Thm26Prop) (hFT : Work.GW2.FeitThompsonProp)
    (hCtx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) : 2 ∈ B.pi := by
  have ht : B.t ∈ Work.GW2.pCoreIn 2 B.Hhat := t_mem_pCoreIn_two h26 hFT hCtx B
  have h2p : 2 ∣ Nat.card (Work.GW2.pCoreIn 2 B.Hhat) := by
    have h := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr ht)
    rwa [Nat.card_zpowers, B.t_order] at h
  have hle : Work.GW2.pCoreIn 2 B.Hhat ≤ Work.GW2.fittingIn B.Hhat := by
    rw [Work.GW2.pCoreIn, Work.GW2.fittingIn]
    exact Subgroup.map_mono (pCore_le_fitting (G := ↥B.Hhat))
  have hdvd : Nat.card (Work.GW2.pCoreIn 2 B.Hhat) ∣ Nat.card (Work.GW2.fittingIn B.Hhat) :=
    Subgroup.card_dvd_of_le hle
  rw [Work.GW2.BenderSetup.pi, Work.GW2.primesOf]
  exact Nat.Prime.mem_primeFactors Nat.prime_two (h2p.trans hdvd)
    (Nat.card_ne_zero.mpr ⟨⟨B.t, hle ht⟩, inferInstance⟩)

/-- `N_G(O₂(Ĥ)) = Ĥ`: `O₂(Ĥ) ⊴ Ĥ` is nontrivial and `G` is simple, so `O₂(Ĥ)` cannot be
normal in `G`; maximality of `Ĥ` then forces the normalizer to be `Ĥ`. -/
theorem normalizer_pCoreIn_two_eq_Hhat {G : Type} [Group G] [Finite G]
    (hCtx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (h4 : Work.GW2.IsFourGroup (Work.GW2.pCoreIn 2 B.Hhat)) :
    Subgroup.normalizer ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) = B.Hhat := by
  haveI : IsSimpleGroup G := hCtx.simple
  have hle : Work.GW2.pCoreIn 2 B.Hhat ≤ B.Hhat := Subgroup.map_subtype_le _
  have hnorm : B.Hhat ≤
      Subgroup.normalizer ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) := by
    simpa [Work.GW2.pCoreIn] using
      le_normalizer_map_subtype B.Hhat (Work.GW2.pCore 2 ↥B.Hhat)
        (Subgroup.normalCore_normal _)
  refine le_antisymm ?_ hnorm
  by_contra hcon
  have hne : B.Hhat ≠ Subgroup.normalizer ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) :=
    fun heq => hcon (le_of_eq heq.symm)
  have htop : Subgroup.normalizer ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) = ⊤ :=
    (B.Hhat_coatom.lt_iff).mp (lt_of_le_of_ne hnorm hne)
  have hVn : (Work.GW2.pCoreIn 2 B.Hhat : Subgroup G).Normal :=
    Subgroup.normalizer_eq_top_iff.mp htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Work.GW2.pCoreIn 2 B.Hhat) with hb | ht
  · have h1 : Nat.card (Work.GW2.pCoreIn 2 B.Hhat) = 1 := by rw [hb]; exact Subgroup.card_bot
    exact absurd (h4.1.symm.trans h1) (by norm_num)
  · exact B.Hhat_coatom.ne_top (top_le_iff.mp (ht ▸ hle))

/-! ## 5. The relative cores are normalized by the ambient subgroup -/

/-- `O_π` of a finite group is invariant under automorphisms: an automorphism permutes the
normal `π`-subgroups. -/
theorem oPiCore_map_mulAut {X : Type} [Group X] [Finite X] (π : Set ℕ) (e : MulAut X) :
    (OddOrder.Isaacs.Ch03.oPiCore π X).map e.toMonoidHom
      = OddOrder.Isaacs.Ch03.oPiCore π X := by
  haveI hN : (OddOrder.Isaacs.Ch03.oPiCore π X).Normal :=
    OddOrder.Isaacs.Ch03.oPiCore.normal π X
  have hN1 : ((OddOrder.Isaacs.Ch03.oPiCore π X).map e.toMonoidHom).Normal :=
    hN.map e.toMonoidHom e.surjective
  refine le_antisymm ?_ ?_
  · haveI := hN1
    exact OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.le_oPiCore
      (OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.map_equiv e
        (OddOrder.Isaacs.Ch03.oPiCore.isPiGroup π))
  · have hN2 : ((OddOrder.Isaacs.Ch03.oPiCore π X).map (e.symm).toMonoidHom).Normal :=
      hN.map (e.symm).toMonoidHom e.symm.surjective
    have h2 : (OddOrder.Isaacs.Ch03.oPiCore π X).map (e.symm).toMonoidHom ≤
        OddOrder.Isaacs.Ch03.oPiCore π X := by
      haveI := hN2
      exact OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.le_oPiCore
        (OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.map_equiv e.symm
          (OddOrder.Isaacs.Ch03.oPiCore.isPiGroup π))
    have h3 := Subgroup.map_mono (f := e.toMonoidHom) h2
    rw [Subgroup.map_map] at h3
    have hid : (e.toMonoidHom.comp (e.symm).toMonoidHom) = MonoidHom.id X := by
      ext x; simp
    rw [hid, Subgroup.map_id] at h3
    exact h3

/-- `F_π(K) = O_π(F(K))` is normalized by `K`. -/
theorem le_normalizer_fittingPiIn {G : Type} [Group G] [Finite G] (π : Set ℕ)
    (K : Subgroup G) :
    K ≤ Subgroup.normalizer ((Work.GW2.fittingPiIn π K : Subgroup G) : Set G) := by
  have hF : (Work.GW2.fitting ↥K).Normal := Subgroup.normalCore_normal _
  rw [Subgroup.le_normalizer_iff]
  intro k hk y hy
  rw [fittingPiIn_eq_map_oPiCore] at hy ⊢
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
  haveI := hF
  have hz' : (MulAut.conjNormal (⟨k, hk⟩ : ↥K)) z ∈
      (OddOrder.Isaacs.Ch03.oPiCore π ↥(Work.GW2.fitting ↥K)).map
        (MulAut.conjNormal (⟨k, hk⟩ : ↥K)).toMonoidHom := ⟨z, hz, rfl⟩
  rw [oPiCore_map_mulAut π (MulAut.conjNormal (⟨k, hk⟩ : ↥K))] at hz'
  refine Subgroup.mem_map.mpr ⟨MulAut.conjNormal (⟨k, hk⟩ : ↥K) z, hz', ?_⟩
  simpa using congrArg (fun t : G => k * t * k⁻¹) hzy

/-! ## 6. `t` inverts `F_{π'}(M)` -/

/-- Bender 1981, Lemma 2.7 (and Lemma 2.3(ii)): the involution `t` inverts `F_{π'}(M)`.

Indeed `F_{π'}(M) ⊓ Ĥ = ⊥`, and `C(t) = H ≤ Ĥ`, so `t` acts fixed-point-freely on `F_{π'}(M)`;
an involution acting fixed-point-freely on a finite group inverts it (Burnside). -/
theorem t_inverts_fittingPiIn (h23 : Work.GW2.Lemma23Prop) {G : Type} [Group G] [Finite G]
    (hFT : Work.GW2.FeitThompsonProp) (hCtx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (M : Subgroup G) (hD : L27Hyp B M) :
    Work.GW2.Inverts B.t (Work.GW2.fittingPiIn B.piᶜ M) := by
  have hdisj : Work.GW2.fittingPiIn B.piᶜ M ⊓ B.Hhat = ⊥ :=
    (h23 G hFT hCtx B M hD.M_ne_top hD.rel).2.1
  have ht2 : B.t * B.t = 1 := by
    have h : B.t ^ 2 = 1 := by
      have := pow_orderOf_eq_one B.t
      rwa [B.t_order] at this
    simpa [pow_two] using h
  have hti : B.t⁻¹ = B.t := inv_eq_of_mul_eq_one_right ht2
  have hnorm : B.t ∈ Subgroup.normalizer
      ((Work.GW2.fittingPiIn B.piᶜ M : Subgroup G) : Set G) :=
    le_normalizer_fittingPiIn B.piᶜ M hD.t_mem
  have hfix : ∀ x ∈ Work.GW2.fittingPiIn B.piᶜ M, B.t * x * B.t⁻¹ = x → x = 1 := by
    intro x hx hxfix
    have hxH : x ∈ B.Hhat := by
      refine B.H_le_Hhat ?_
      show x ∈ Subgroup.centralizer ({B.t} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      rw [hti] at hxfix
      calc B.t * x = (B.t * x * B.t) * B.t := by rw [mul_assoc, mul_assoc, ht2, mul_one]
        _ = x * B.t := by rw [hxfix]
    have : x ∈ Work.GW2.fittingPiIn B.piᶜ M ⊓ B.Hhat := ⟨hx, hxH⟩
    rw [hdisj] at this
    exact Subgroup.mem_bot.mp this
  exact Work.BMAX.InvolutionInverts _ B.t ht2 hnorm hfix

end Work.CORE2B
