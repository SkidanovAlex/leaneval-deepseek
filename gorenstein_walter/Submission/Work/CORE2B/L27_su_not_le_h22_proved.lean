import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.t_central_in_S
import Submission.Work.CORE2B.UNeBotProp_of_h22_proved
import Submission.Work.CORE2B.BenderCtx_sylow_not_cyclic
import Submission.Work.CORE2B.L29_contra_proved
import Submission.Work.CORE2B.L27_fourGroup_in_C_M_t
import Submission.Work.CORE2B.L27su_utils
import Submission.Work.CORE2B.L27su_transport2
import Submission.Work.CORE2B.L27su_fittingPiIn_compl_ne_bot2
import Submission.Work.BMAX.InvolutionInverts
import Submission.Work.RED.DihedralSubgroup
import Submission.Work.RED.even_dihedral_param_of_isPGroup_two_not_isCyclic
import Submission.Work.Dihedral.Defs

/-!
# CORE2B — `L27_su_not_le_h22` (Bender 1981, Lemma 2.7 (b), with Bender 2.2 available)

Route (Bender's proof of `[S,U] ⊄ F(U)`, `NOTES_CORE2B.md` §3, `NOTES_LEAD_gw_design3.md` §7a):

* `h22` (Bender 2.2) gives `U = O(H) ≠ ⊥` (`UNeBotProp_of_h22_proved`).
* `A := F_{π'}(M) = fittingPiIn B.piᶜ M` is nontrivial (Bender's step `[M,t] ⊆ F_{π'}(M) ≠ 1`),
  meets `Ĥ` trivially (`h23`), is inverted by `t`, and is a `π'`-group; it is normal in `M`.
* There is a Klein four-group `V = ⟨t, v⟩ ≤ C_M(t)` (`v` an involution of `M` commuting with `t`),
  and `V ≤ M` acts on `A`.  1.1(iii) (`T.c11iii`) gives `A = ⨆_{w ∈ V#} (A ⊓ C(w))`; since
  `A ⊓ C(t) = ⊥` and `A ≠ ⊥`, some `w ∈ V#`, `w ≠ t`, satisfies `A ⊓ C(w) ≠ ⊥`.
* Choose `h ∈ N_G(V)` with `h t h⁻¹ = w` (fusion of involutions inside a four-group, `T.fus`);
  then `X := (A ⊓ C(w))` conjugated by `h⁻¹` is a nontrivial `π'`-subgroup of `U = O(H)` that is
  inverted by `t^{h⁻¹} ∈ V ≤ C(t) = H`; conjugating by an element of `H` puts the inverting
  involution into `S` (a Sylow 2-subgroup of `H`).
* Hence `[S,U]` contains a nontrivial `π'`-subgroup, while `F(U) ≤ F(Ĥ)` is a `π`-group
  (`U = O(Ĥ)`, `h26`).  Therefore `[S,U] ⊄ F(U)`.
-/

open scoped MatrixGroups commutatorElement

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.CORE2B

open Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## 1. Elementary consequences of the `BenderSetup` fields, and odd subgroups of `H`

The lemmas `L27su_S_le_H`, `L27su_H_le_normalizer_U`, `L27su_S_le_normalizer_U`,
`L27su_S_dihedral`, `L27su_le_of_sup_isPGroup` and `L27su_odd_subgroup_le_U` now live in
`Submission.Work.CORE2B.L27su_utils` (imported above): the transport module
`Submission.Work.CORE2B.L27su_transport` needs them but is imported *by* this file. -/

/-! ## 3. `F(U) ≤ F(Ĥ)` (so that `F(U)` is a `π`-group) -/

/-- The Feit–Thompson closure's `F(X) = ⨆_p O_p(X)` agrees with the area's `Work.GW2.fitting X`. -/
theorem L27su_fitting_eq_isaacs {H : Type} [Group H] [Finite H] :
    Work.GW2.fitting H = OddOrder.Isaacs.Ch01.fitting H := by
  have hS : sSup {N : Subgroup H | N.Normal ∧ Group.IsNilpotent N}
      = OddOrder.Isaacs.Ch01.fitting H := by
    refine le_antisymm (sSup_le ?_) (le_sSup ?_)
    · rintro N ⟨hN, hnil⟩
      haveI : N.Normal := hN
      haveI : Group.IsNilpotent ↥N := hnil
      exact OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
    · exact ⟨OddOrder.Isaacs.Ch01.fitting.normal H,
        OddOrder.Isaacs.Ch01.fitting.isNilpotent⟩
  rw [Work.GW2.fitting, hS]
  exact Subgroup.normalCore_eq_self _

/-- **A characteristic subgroup of a normal subgroup is normal.** -/
theorem L27su_normal_of_characteristic {X : Type} [Group X] {K : Subgroup X} [K.Normal]
    {N : Subgroup ↥K} (hN : N.Characteristic) : (N.map K.subtype).Normal := by
  haveI := hN
  exact ConjAct.normal_of_characteristic_of_normal (K := N)

/-- The image of a characteristic subgroup under a multiplicative equivalence of the ambient
group is characteristic. -/
theorem L27su_characteristic_map_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {N : Subgroup X} (hN : N.Characteristic) : (N.map e.toMonoidHom).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq] at hN ⊢
  intro φ
  have hcomp : φ.toMonoidHom.comp e.toMonoidHom
      = e.toMonoidHom.comp (e.trans (φ.trans e.symm)).toMonoidHom := by
    ext x
    simp [MulEquiv.trans_apply]
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hN (e.trans (φ.trans e.symm))]

/-- `O_p(K) ≤ O_p(X)` for `K ◁ X` (as subgroups of the ambient group). -/
theorem L27su_opCore_le_opCore {G : Type} [Group G] [Finite G] {K X : Subgroup G}
    (hKX : K ≤ X) (hKnorm : (K.subgroupOf X).Normal) (p : ℕ) [Fact p.Prime] :
    (OddOrder.Isaacs.Ch01.opCore p ↥K).map K.subtype ≤
      (OddOrder.Isaacs.Ch01.opCore p ↥X).map X.subtype := by
  haveI : (K.subgroupOf X).Normal := hKnorm
  let σ : ↥(K.subgroupOf X) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKX
  let N : Subgroup ↥(K.subgroupOf X) :=
    (OddOrder.Isaacs.Ch01.opCore p ↥K).map σ.symm.toMonoidHom
  have hNchar : N.Characteristic :=
    L27su_characteristic_map_equiv σ.symm (OddOrder.Isaacs.Ch01.opCore.characteristic p ↥K)
  haveI := hNchar
  have hNnorm : (N.map (K.subgroupOf X).subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal (H := K.subgroupOf X) (K := N)
  haveI := hNnorm
  have hNp : IsPGroup p ↥(N.map (K.subgroupOf X).subtype) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := p)
      (G := ↥(OddOrder.Isaacs.Ch01.opCore p ↥K))).mp
      (OddOrder.Isaacs.Ch01.opCore_isPGroup p ↥K)
    refine IsPGroup.of_card (n := n) ?_
    rw [Nat.card_congr (Subgroup.equivMapOfInjective _ (K.subgroupOf X).subtype
          (K.subgroupOf X).subtype_injective).symm.toEquiv,
        Nat.card_congr (Subgroup.equivMapOfInjective _ σ.symm.toMonoidHom
          σ.symm.injective).symm.toEquiv]
    exact hn
  have hle : N.map (K.subgroupOf X).subtype ≤ OddOrder.Isaacs.Ch01.opCore p ↥X :=
    OddOrder.Isaacs.Ch01.normal_pgroup_le_opCore hNp
  have hcomp : (X.subtype.comp (K.subgroupOf X).subtype).comp σ.symm.toMonoidHom = K.subtype := by
    ext k; rfl
  have hkey : (OddOrder.Isaacs.Ch01.opCore p ↥K).map K.subtype
      = (N.map (K.subgroupOf X).subtype).map X.subtype := by
    rw [← hcomp, Subgroup.map_map, Subgroup.map_map]
  rw [hkey]
  exact Subgroup.map_mono hle

/-- **`F(K) ≤ F(X)` for `K ◁ X`**: every `O_p(K)` is a normal `p`-subgroup of `X`. -/
theorem L27su_fittingIn_le_of_normal {G : Type} [Group G] [Finite G] {K X : Subgroup G}
    (hKX : K ≤ X) (hKnorm : (K.subgroupOf X).Normal) :
    Work.GW2.fittingIn K ≤ Work.GW2.fittingIn X := by
  have key : ∀ p : Nat.Primes,
      ((OddOrder.Isaacs.Ch01.opCore (p : ℕ) ↥K).map K.subtype) ≤ Work.GW2.fittingIn X := by
    intro p
    haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
    refine le_trans (L27su_opCore_le_opCore hKX hKnorm (p : ℕ)) ?_
    rw [Work.GW2.fittingIn, L27su_fitting_eq_isaacs]
    exact Subgroup.map_mono (OddOrder.Isaacs.Ch01.opCore_le_fitting p ↥X)
  calc Work.GW2.fittingIn K
      = (OddOrder.Isaacs.Ch01.fitting ↥K).map K.subtype := by
        rw [Work.GW2.fittingIn, L27su_fitting_eq_isaacs]
    _ = (⨆ p : Nat.Primes, OddOrder.Isaacs.Ch01.opCore (p : ℕ) ↥K).map K.subtype := rfl
    _ = ⨆ p : Nat.Primes,
          ((OddOrder.Isaacs.Ch01.opCore (p : ℕ) ↥K).map K.subtype) := by
        rw [Subgroup.map_iSup]
    _ ≤ Work.GW2.fittingIn X := iSup_le key

/-- `F(U) ≤ F(Ĥ)` since `U = O(Ĥ) ◁ Ĥ` (`h26`). -/
theorem L27su_fittingIn_U_le_fittingIn_Hhat {G : Type} [Group G] [Finite G]
    (h26 : Work.GW2.Thm26Prop) (hFT : Work.GW2.FeitThompsonProp)
    (hCtx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) :
    Work.GW2.fittingIn B.U ≤ Work.GW2.fittingIn B.Hhat := by
  have hUeq : B.U = Work.GW2.oddCoreIn B.Hhat := (h26 G hFT hCtx B).1.symm
  have hUB : B.U ≤ B.Hhat := hUeq ▸ Subgroup.map_subtype_le _
  have hUsub : B.U.subgroupOf B.Hhat = Work.GW2.oddCore ↥B.Hhat := by
    rw [hUeq, Work.GW2.oddCoreIn, Subgroup.subgroupOf]
    exact Subgroup.comap_map_eq_self_of_injective B.Hhat.subtype_injective _
  exact L27su_fittingIn_le_of_normal hUB (hUsub ▸ Work.GW2.oddCore_normal ↥B.Hhat)

/-- Every element of `F(U)` has `π`-order, `π = B.pi = π(F(Ĥ))`. -/
theorem L27su_primeFactors_fittingIn_U {G : Type} [Group G] [Finite G]
    (h26 : Work.GW2.Thm26Prop) (hFT : Work.GW2.FeitThompsonProp)
    (hCtx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) :
    ∀ p : ℕ, p.Prime → p ∣ Nat.card (Work.GW2.fittingIn B.U) → p ∈ B.pi := by
  intro p hp hdvd
  have hle := L27su_fittingIn_U_le_fittingIn_Hhat h26 hFT hCtx B
  have hdvd' : p ∣ Nat.card (Work.GW2.fittingIn B.Hhat) :=
    hdvd.trans (Subgroup.card_dvd_of_le hle)
  rw [Work.GW2.BenderSetup.pi, Work.GW2.primesOf]
  exact Nat.mem_primeFactors.mpr ⟨hp, hdvd', Nat.card_pos.ne'⟩

/-! ## 4. `A = F_{π'}(M)`: disjoint from `Ĥ`, inverted by `t`, a `π'`-group -/

variable {G : Type} [Group G] [Finite G]

/-- `A = F_{π'}(M)` meets `Ĥ` trivially (Lemma 2.3(ii), `h23`). -/
theorem L27su_A_inf_Hhat_eq_bot (h23 : Work.GW2.Lemma23Prop) (hFT : Work.GW2.FeitThompsonProp)
    (hCtx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (M : Subgroup G)
    (hD : L27Hyp B M) :
    Work.GW2.fittingPiIn B.piᶜ M ⊓ B.Hhat = ⊥ :=
  (h23 G hFT hCtx B M hD.M_ne_top hD.rel).2.1

/-- `A = F_{π'}(M) ≤ M` and `A ◁ M`. -/
theorem L27su_A_normal_in_M (B : Work.GW2.BenderSetup G) (M : Subgroup G) :
    Work.GW2.fittingPiIn B.piᶜ M ≤ M ∧
      ((Work.GW2.fittingPiIn B.piᶜ M).subgroupOf M).Normal := by
  have hsub : (Work.GW2.fittingPiIn B.piᶜ M).subgroupOf M = Work.GW2.fittingPi B.piᶜ ↥M := by
    rw [Work.GW2.fittingPiIn, ← Subgroup.comap_subtype,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  exact ⟨Subgroup.map_subtype_le _,
    hsub ▸ fittingPi_normal_local B.piᶜ (G := G) M⟩

/-- `A = F_{π'}(M)` is a `π'`-group. -/
theorem L27su_A_primeFactors (B : Work.GW2.BenderSetup G) (M : Subgroup G) :
    ∀ p : ℕ, p.Prime → p ∣ Nat.card (Work.GW2.fittingPiIn B.piᶜ M) → p ∉ B.pi := by
  intro p hp hdvd
  have hcard : Nat.card (Work.GW2.fittingPiIn B.piᶜ M)
      = Nat.card ↥(Work.GW2.piCore B.piᶜ ↥(Work.GW2.fitting ↥M)) := by
    rw [Work.GW2.fittingPiIn, Work.GW2.fittingPi,
      Subgroup.card_map_of_injective M.subtype_injective,
      Subgroup.card_map_of_injective (Work.GW2.fitting ↥M).subtype_injective]
  rw [hcard] at hdvd
  have hmem := isPiSubgroup_piCore_local (G := ↥(Work.GW2.fitting ↥M)) B.piᶜ p
    (Nat.mem_primeFactors.mpr ⟨hp, hdvd, Nat.card_pos.ne'⟩)
  simpa using hmem

/-- **The final step of Bender's argument.**  If `[S,U] ≤ F(U)` then `[S,U]` contains no
nontrivial `π'`-subgroup of `U`: `F(U)` is a `π`-group (`F(U) ≤ F(Ĥ)`, `U = O(Ĥ)`) while the
elements of a `π'`-subgroup of `U` have `π'`-order. -/
theorem L27su_inf_eq_bot_of_le_fittingIn {G : Type} [Group G] [Finite G]
    (h26 : Work.GW2.Thm26Prop) (hFT : Work.GW2.FeitThompsonProp)
    (hCtx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (hle : ⁅(B.S : Subgroup G), B.U⁆ ≤ Work.GW2.fittingIn B.U) (X : Subgroup G)
    (hXπ' : ∀ p : ℕ, p.Prime → p ∣ Nat.card X → p ∉ B.pi) :
    X ⊓ ⁅(B.S : Subgroup G), B.U⁆ = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro x ⟨hxX, hxS⟩
  by_contra hx1
  have hdvdX : orderOf x ∣ Nat.card X := Subgroup.orderOf_dvd_natCard X hxX
  have hdvdF : orderOf x ∣ Nat.card (Work.GW2.fittingIn B.U) :=
    Subgroup.orderOf_dvd_natCard _ (hle hxS)
  have hnot : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hnot
  exact (hXπ' p hp (hpdvd.trans hdvdX))
    (L27su_primeFactors_fittingIn_U h26 hFT hCtx B p hp (hpdvd.trans hdvdF))

/-! ## 5. Assembly of the target from the three gaps -/

/-- **Bender 1981, Lemma 2.7 (b)** (`[S,U] ⊄ F(U)`) follows from the three mathematical inputs:
`F_{π'}(M) ≠ ⊥` (Bender's `[M,t] ⊆ F_{π'}(M) ≠ 1`), the existence of an involution `v ∈ M`,
`v ≠ t`, commuting with `t`, and the transport step `L27su_transport`. -/
theorem L27su_of_gaps
    (hAne : ∀ (T : Work.GW2.LocalToolkit) (h22 : Work.GW2.Lemma22Prop)
      (h23 : Work.GW2.Lemma23Prop) (h26 : Work.GW2.Thm26Prop) (G : Type) [Group G] [Finite G],
      Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G), L27Hyp B M →
        Work.GW2.fittingPiIn B.piᶜ M ≠ ⊥)
    (hfour : ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G), L27Hyp B M →
        ∃ V : Subgroup G, V ≤ M ∧ V ≤ Subgroup.centralizer ({B.t} : Set G) ∧
          Work.GW2.IsFourGroup V ∧ B.t ∈ V)
    (htrans : ∀ (T : Work.GW2.LocalToolkit) (h23 : Work.GW2.Lemma23Prop)
      (h26 : Work.GW2.Thm26Prop) (G : Type) [Group G] [Finite G],
      Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G), L27Hyp B M →
      (∃ v ∈ M, orderOf v = 2 ∧ v ≠ B.t ∧ v * B.t = B.t * v) →
      ∀ Y : Subgroup G, Y ≤ M → (Y.subgroupOf M).Normal → Y ≠ ⊥ → Y ⊓ B.Hhat = ⊥ →
        Work.GW2.Inverts B.t Y →
        (∀ p : ℕ, p.Prime → p ∣ Nat.card Y → p ∉ B.pi) →
        ∃ X : Subgroup G, X ≠ ⊥ ∧ X ≤ B.U ∧
          (∀ p : ℕ, p.Prime → p ∣ Nat.card X → p ∉ B.pi) ∧
          X ≤ ⁅(B.S : Subgroup G), B.U⁆) :
    Work.CORE2B.L27_su_not_le_h22 := by
  intro T h22 h23 h26 G _ _ hFT hCtx B M hD hle
  have ht1 : B.t ≠ 1 := (BenderSetup_basics B).2.2.2.2.2.2.2
  -- the four-group `V ≤ C_M(t)`, and an involution `v ∈ V ∖ {1, t}`
  obtain ⟨V, hVleM, hVleC, hVfour, htV⟩ := hfour G hCtx B M hD
  obtain ⟨hVcard, hVsq⟩ := hVfour
  obtain ⟨v, hvV, hv1, hvne⟩ : ∃ v ∈ V, v ≠ 1 ∧ v ≠ B.t := by
    by_contra hcon
    push_neg at hcon
    have hsub : (V : Set G) ⊆ ({1, B.t} : Set G) := fun x hx => by
      by_cases hx1 : x = 1
      · simp [hx1]
      · simp [hcon x hx hx1]
    have hle2 : Nat.card V ≤ 2 := by
      calc Nat.card V = (V : Set G).ncard := Nat.card_coe_set_eq _
        _ ≤ ({1, B.t} : Set G).ncard := Set.ncard_le_ncard hsub (by simp)
        _ ≤ 2 := by
            have h1 : ({1, B.t} : Set G).ncard ≤ ({B.t} : Set G).ncard + 1 :=
              Set.ncard_insert_le _ _
            rw [Set.ncard_singleton] at h1
            omega
    omega
  have hv2 : orderOf v = 2 := by
    have h2 : v * v = 1 := by simpa [pow_two] using hVsq v hvV
    have hdvd : orderOf v ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      simpa [pow_two] using h2
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hv1
    · exact h
  have hvt : v * B.t = B.t * v :=
    ((Subgroup.mem_centralizer_iff.mp (hVleC hvV)) B.t (by simp)).symm
  -- the transport step
  obtain ⟨Yle, Ynorm⟩ := L27su_A_normal_in_M (G := G) B M
  obtain ⟨X, hXne, hXU, hXπ', hXle⟩ :=
    htrans T h23 h26 G hFT hCtx B M hD ⟨v, hVleM hvV, hv2, hvne, hvt⟩
      (Work.GW2.fittingPiIn B.piᶜ M) Yle Ynorm (hAne T h22 h23 h26 G hFT hCtx B M hD)
      (L27su_A_inf_Hhat_eq_bot h23 hFT hCtx B M hD)
      (inverts_fittingPiIn_pi_compl_local h23 hFT hCtx B M hD)
      (L27su_A_primeFactors B M)
  -- contradiction with `[S,U] ≤ F(U)`
  have hbot := L27su_inf_eq_bot_of_le_fittingIn h26 hFT hCtx B hle X hXπ'
  exact hXne ((inf_eq_left.mpr hXle).symm.trans hbot)

/-- **The target from the single missing input.**  `L27_su_not_le_h22` follows from Bender's
input `F(U) ≤ M` ("`O₂(M)` centralizes `M ∩ F(U)`", p. 221) alone: `F(U) ≤ M` gives
`O₂(M) ≤ C_G(F(U))` (`L27su_pCore_le_centralizer_U`), hence `[O₂(M),U] = 1`, hence
`O₂(M) ≤ O₂(Ĥ) = C_S(U)` (Theorem 2.6), hence `O₂(M) = ⊥` (the coatom argument
`L27su_eq_bot_of_le_pCoreIn_Hhat`), and then the sorry-free `L27su_fittingPiIn_compl_ne_bot_aux2`
gives Bender's `F_{π'}(M) ≠ 1`, which is the remaining input of `L27su_of_gaps`.

Under `L27HypS` the input `F(U) ≤ M` is itself provable (see
`Submission.Work.CORE2B.L27_su_not_le_h22S_proved`, where this is packaged as
`L27_su_not_le_h22S_proved`); under the printed hypotheses `L27Hyp` it is the missing input. -/
theorem L27su_of_fittingIn_U_le_M
    (hinput : ∀ (T : Work.GW2.LocalToolkit) (h22 : Work.GW2.Lemma22Prop)
      (h23 : Work.GW2.Lemma23Prop) (h26 : Work.GW2.Thm26Prop) (G : Type) [Group G] [Finite G],
      Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G), L27Hyp B M →
        Work.GW2.fittingIn B.U ≤ M) :
    Work.CORE2B.L27_su_not_le_h22 := by
  refine L27su_of_gaps ?_ L27_fourGroup_in_C_M_t L27su_transport2
  intro T h22 h23 h26 G _ _ hFT hCtx B M hD
  have hFM : Work.GW2.fittingIn B.U ≤ M := hinput T h22 h23 h26 G hFT hCtx B M hD
  have hC : Work.GW2.pCoreIn 2 M ≤ Subgroup.centralizer ({B.t} : Set G) :=
    L27_O2_centralized_by_t T h23 h26 G hFT hCtx B M hD
  have hCU : Work.GW2.pCoreIn 2 M ≤ Subgroup.centralizer (B.U : Set G) :=
    L27su_pCore_le_centralizer_U T G hFT hCtx B M hC hFM
  have hle : Work.GW2.pCoreIn 2 M ≤ Work.GW2.pCoreIn 2 B.Hhat :=
    L27su_two_core_le_pCoreIn_Hhat2 T h26 G hFT hCtx B (Work.GW2.pCoreIn 2 M)
      (isPGroup_pCoreIn_two M) hCU hC
  have hO2 : Work.GW2.pCoreIn 2 M = ⊥ :=
    L27su_eq_bot_of_le_pCoreIn_Hhat T h22 h26 G hFT hCtx B M hD hle
  have hnot : ¬ ∃ p : ℕ, p.Prime ∧ IsPGroup p (Work.GW2.fstarIn B.Hhat) :=
    L27su_hnot T h22 h26 G hFT hCtx B
  exact L27su_fittingPiIn_compl_ne_bot_aux2 T h22 h23 h26 G hFT hCtx B M hD hnot hO2

/-! ## 6. The target declaration — RETIRED (statement kept, declaration removed)

```
theorem L27_su_not_le_h22_proved : Work.CORE2B.L27_su_not_le_h22
```

— Bender 1981, Lemma 2.7 (b) `[S,U] ⊄ F(U)`, assembled as
`L27su_of_gaps · L27_fourGroup_in_C_M_t · L27su_transport2` with the first gap supplied by the
(now retired) `L27su_fittingPiIn_compl_ne_bot2`.  The live, hole-free proof of the same statement is
`Work.CORE2B.L27_su_not_le_h22_v12` (`Submission/Work/CORE2B/L27su_assembly.lean`), where the first
gap is `L27su_A_ne_bot_v12` (derived from conclusion (a), design pass 18); `Work.CORE2B.lemma27` is
built from it.  The declaration has been **removed** so that no module on the delivered path contains
an unproved statement; `L27su_of_gaps` (proved above, with its inputs as hypotheses),
`L27su_of_fittingIn_U_le_M` and the rest of the file stay available. -/

end Work.CORE2B
