import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.SixThree
import Submission.Work.CORE4.OddDihActionInvolution
import Submission.Work.CORE4.Case2LayerOneInvClass
import Submission.Work.CORE4.Case2NotHLeM
import Submission.Work.CORE4.Case2Setup9Odd
import Submission.Work.CORE4.LayerCtx6
import Submission.Work.CORE4.DihOrCycSub
import Submission.Work.L2F.Dihedral.dihedral_oddSubgroup
import Submission.Work.CORE4.CoreOddAction
import Submission.Work.CORE4.TransferLayerInf
import Submission.Work.CORE4.LayerInSylow

namespace Work.CORE4

open scoped MatrixGroups
open Subgroup

/-- **The layer of a coatom with `t ∈ E(M)` is quasisimple with odd centre and `E/Z(E) ≅ A₇` or
`PSL(2,q)`.**  This is `Work.CORE4.LayerCtx6` with the `Case2Ctx6` hypothesis replaced by the two
facts its proof actually uses (`IsCoatom M`, `B.t ∈ layerIn M`): `↥M` has dihedral/cyclic Sylow
2-subgroups (`DihOrCycSub`) and is a D-group (`hbc.ih`), so `I.toolkit.lay` applies to a normal
quasisimple subgroup of `↥M`, and `quasisimple_shape_map` transports the conclusion along
`M.subtype`. -/
private theorem layerIn_structure {G : Type} [Group G] [Finite G]
    (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (M : Subgroup G) (hcoat : IsCoatom M) (ht : B.t ∈ Work.GW2.layerIn M) :
    Odd (Nat.card ↥(Subgroup.center ↥(Work.GW2.layerIn M))) ∧
      (Nonempty ((↥(Work.GW2.layerIn M) ⧸ Subgroup.center ↥(Work.GW2.layerIn M)) ≃*
          alternatingGroup (Fin 7)) ∨
        ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
          Nonempty ((↥(Work.GW2.layerIn M) ⧸ Subgroup.center ↥(Work.GW2.layerIn M)) ≃*
            Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) := by
  classical
  have ht1 : B.t ≠ 1 := by
    intro h1
    have h2 := B.t_order
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hEne : Work.GW2.layerIn M ≠ ⊥ := by
    intro h
    have h' : B.t ∈ (⊥ : Subgroup G) := h ▸ ht
    exact ht1 (Subgroup.mem_bot.mp h')
  have hlayer_ne : Work.GW2.layer ↥M ≠ ⊥ := by
    intro h
    apply hEne
    show Work.GW2.layerIn M = ⊥
    rw [Work.GW2.layerIn, h, Subgroup.map_bot]
  obtain ⟨E', hE'norm, hE'q⟩ : ∃ E' : Subgroup ↥M, E'.Normal ∧ Work.GW2.IsQuasisimple E' := by
    by_contra hcon
    apply hlayer_ne
    rw [Work.GW2.layer, sSup_eq_bot]
    intro F hF
    by_contra hFne
    exact hcon ⟨F, hF.1, hF.2⟩
  have hD : Work.GW2.DihOrCycSylow ↥M := DihOrCycSub hbc.sylow M
  have hcard : Nat.card ↥M < Nat.card G := card_lt_card_of_ne_top hcoat.ne_top
  have hIsD : Work.GW2.IsDGroup ↥M := hbc.ih ↥M hcard hD
  obtain ⟨hlayer, hodd, hshape⟩ := I.toolkit.lay ↥M I.toolkit.ft hD hIsD E' hE'norm hE'q
  have hEq : Work.GW2.layerIn M = E'.map (M.subtype) := by
    rw [Work.GW2.layerIn, hlayer]
  rw [hEq]
  exact (quasisimple_shape_map (M.subtype) (Subgroup.subtype_injective M) hE'q hodd hshape).2

/-! ## The companion lemma

The statement used below is exactly `Work.CORE4.OddDihActionInvolution`
(`Submission/Work/CORE4/OddDihActionInvolution.lean`), the proved form of
`Work.CORE4.CoreOddActionGroupTheory`.  The partial decomposition it uses lives in
`Submission/Work/CORE4/COAGT/`.  (This file previously carried a local `sorry` stub for it.) -/

/-- Bender 1981, §4 (1)–(2) (p. 224–225), with Bender's choice of the Sylow 2-subgroup.

Let `BenderCtx G`, `B : BenderSetup G`, and `M : Subgroup G` a coatom with `t := B.t ∈ E := layerIn M`,
`M = E · C_G(t)`, and let `P ≤ M ⊓ B.H = C_M(t)` be a Sylow 2-subgroup of `M` (so `t ∈ P`, and
`P ⊓ E` is a Sylow 2-subgroup of `E`, because `E ⊴ M`).

Conclusion: there is an involution `s ∈ P ⊓ E` such that, writing
`K := ⁅P ⊓ E, U ⊓ M⁆` (the commutator subgroup, `U = O(H) = B.U`),

* `K = I_{U ⊓ M}(s) = {x ∈ U ⊓ M | s x s⁻¹ = x⁻¹}` as sets — Bender's (1);
* `K` is cyclic — Bender's (1);
* `C_{U ⊓ M}(s) = C_{U ⊓ M}(P ⊓ E)` — the second half of Bender's (2);
* `U ⊓ M = K ⊔ C_{U ⊓ M}(s)` — Bender's (2), `U ∩ M = K B`.

Route (Bender p. 224): by the structure of `A₇` and `L₂(q)`, `(U ⊓ E) Z(E)/Z(E)` is a *cyclic*
subgroup of `C_{E/Z(E)}(t Z(E))` — in both cases `C(t̄)` has cyclic odd part (`U ⊓ E` is odd
because `U = O(H)` has odd order) — and it is *inverted* by an involution of a Sylow 2-subgroup of
`E`, realised by `s`. Lifting `s` from `E/Z(E)` to `E` and adjusting by an element of `Z(E)`
(`Z(E)` has odd order, so squaring is onto) gives the required involution, which can be chosen
inside the prescribed Sylow `P ⊓ E`. The available inputs are `I.toolkit.lay` (`E/Z(E) ≅ A₇` or
`PSL(2,q)`, `Z(E)` odd), `I.toolkit.a7`, `I.toolkit.l2cent`, `I.toolkit.l2centOdd`
(`L2CentOddCyclicProp`: for odd `Y ≤ C_L(t')` in `L₂(q)`, `Y` is cyclic and inverted by an
involution of `C_L(t')`), `I.toolkit.l2ti`, `I.toolkit.l2four`, `I.toolkit.autL2`,
`I.layerOneInvClass`.  `IsQuasisimple (layerIn M)` (needed to apply `I.toolkit.lay` to `X = M`) is
derivable from `IsCoatom M` and `t ∈ layerIn M` as in
`Submission.Work.CORE4.Case2NotHLeM.layer_facts`.

Once `s` is fixed, `K = I_{U ⊓ M}(s)` is a subgroup of the odd group `U ⊓ M` inverted by `s`, and
`U ⊓ M = C_{U ⊓ M}(s) · I_{U ⊓ M}(s)` (Bender 1.5(ii), `I.toolkit.c15`); `[P ⊓ E, U ⊓ M] ≤ E`
because `E ⊴ M`, so `K ≤ U ⊓ E`; and `K` is cyclic because its image in `E/Z(E)` lies in the
cyclic odd part of `C(t̄)`.
Useful existing files: `Submission.Work.CORE4.SixThree`,
`Submission.Work.CORE4.Case2CountSetup`, `Submission.Work.CORE4.API`,
`Submission.Work.CORE4.Case2LayerOneInvClass`. -/
theorem Case2Setup9S (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (M P : Subgroup G),
        IsCoatom M → B.t ∈ Work.GW2.layerIn M →
        M = Work.GW2.layerIn M ⊔ (M ⊓ B.H) →
        IsPGroup 2 P → P ≤ M ⊓ B.H → ¬ 2 ∣ P.relIndex M →
        ∃ s ∈ P ⊓ Work.GW2.layerIn M, orderOf s = 2 ∧
          (Work.GW2.invSet (B.U ⊓ M) s : Set G) =
            ((⁅P ⊓ Work.GW2.layerIn M, B.U ⊓ M⁆ : Subgroup G) : Set G) ∧
          IsCyclic (⁅P ⊓ Work.GW2.layerIn M, B.U ⊓ M⁆ : Subgroup G) ∧
          ((B.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G)) =
            (B.U ⊓ M) ⊓ Subgroup.centralizer (((P ⊓ Work.GW2.layerIn M : Subgroup G)) : Set G) ∧
          B.U ⊓ M = (⁅P ⊓ Work.GW2.layerIn M, B.U ⊓ M⁆ : Subgroup G) ⊔
            ((B.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G)) := by
  intro G _ _ hbc B M P hcoat ht _hsup hP2 hPle hPidx
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- ## 0. The layer `E := layerIn M` and its structure
  obtain ⟨hZodd, hshape⟩ := layerIn_structure I hbc B M hcoat ht
  -- ## 1. Bender's Sylow choice: `t ∈ P`, `Q = P ⊓ E ∈ Syl₂(E)` and `Q ≅ D_n`
  obtain ⟨htP, hQpg, _hQidx, n, hn2, hQdih⟩ :=
    LayerInSylow I G hbc B M P hcoat ht hP2 hPle hPidx hZodd hshape
  -- ## 2. The objects at the level of `G`
  set E : Subgroup G := Work.GW2.layerIn M with hEdef
  have hEM : E ≤ M := by rw [hEdef]; exact layerIn_le M
  have hEnorm : (E.subgroupOf M).Normal := by
    rw [hEdef]; exact layerIn_subgroupOf_normal_gen M
  set Q : Subgroup G := P ⊓ E with hQdef
  set X : Subgroup G := B.U ⊓ M with hXdef
  have hQE : Q ≤ E := by rw [hQdef]; exact inf_le_right
  have hXM : X ≤ M := by rw [hXdef]; exact inf_le_right
  have hXodd : Odd (Nat.card ↥X) := by
    rw [hXdef]
    exact Odd.of_dvd_nat B.U_odd (Subgroup.card_dvd_of_le inf_le_left)
  have htQ : B.t ∈ Q := htP
  have hQ2 : IsPGroup 2 Q := by
    rw [hQdef]; exact IsPGroup.to_le hP2 inf_le_left
  -- `Q ≤ H` normalises `U` (as `U ⊴ H`), and `Q ≤ M`
  have hQU : Q ≤ Subgroup.normalizer ((B.U : Subgroup G) : Set G) := by
    intro q hq
    have hqP : q ∈ P := (Subgroup.mem_inf.mp (hQdef ▸ hq)).1
    have hqH : q ∈ B.H := (hPle hqP).2
    rw [Subgroup.mem_normalizer_iff]
    refine fun u => ⟨fun hu => ?_, fun hu => ?_⟩
    · exact (Subgroup.normal_subgroupOf_iff B.U_le_H).mp B.U_normal u q hu hqH
    · have h1 : q⁻¹ * (q * u * q⁻¹) * q ∈ B.U := by
        have h := (Subgroup.normal_subgroupOf_iff B.U_le_H).mp B.U_normal (q * u * q⁻¹) q⁻¹ hu
          (B.H.inv_mem hqH)
        simpa using h
      have h2 : q⁻¹ * (q * u * q⁻¹) * q = u := by group
      rwa [h2] at h1
  have hQM : Q ≤ Subgroup.normalizer ((M : Subgroup G) : Set G) := by
    intro q hq
    have hqP : q ∈ P := (Subgroup.mem_inf.mp (hQdef ▸ hq)).1
    have hqM : q ∈ M := (hPle hqP).1
    rw [Subgroup.mem_normalizer_iff]
    refine fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · exact M.mul_mem (M.mul_mem hqM hx) (M.inv_mem hqM)
    · have h : q⁻¹ * (q * x * q⁻¹) * q = x := by group
      rw [← h]
      exact M.mul_mem (M.mul_mem (M.inv_mem hqM) hx) hqM
  have hQnormalizesX : Q ≤ Subgroup.normalizer (X : Set G) := by
    rw [hXdef]
    intro q hq
    have h1 : q ∈ Subgroup.normalizer ((B.U : Subgroup G) : Set G) := hQU hq
    have h2 : q ∈ Subgroup.normalizer ((M : Subgroup G) : Set G) := hQM hq
    rw [Subgroup.mem_normalizer_iff] at h1 h2
    refine fun x => ⟨fun hx => ?_, fun hx => ?_⟩
    · obtain ⟨hxU, hxM⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨(h1 x).mp hxU, (h2 x).mp hxM⟩
    · obtain ⟨hxU, hxM⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨(h1 x).mpr hxU, (h2 x).mpr hxM⟩
  -- ## 3. The objects inside the group `↥E`
  have htE : B.t ∈ E := hEdef ▸ ht
  set Q' : Subgroup ↥E := Q.subgroupOf E with hQ'def
  set Y : Subgroup G := B.U ⊓ E with hYdef
  set Y' : Subgroup ↥E := Y.subgroupOf E with hY'def
  have hYE : Y ≤ E := by rw [hYdef]; exact inf_le_right
  have hYodd : Odd (Nat.card ↥Y) := by
    rw [hYdef]
    exact Odd.of_dvd_nat B.U_odd (Subgroup.card_dvd_of_le inf_le_left)
  have hXY : X ⊓ E = Y := by
    rw [hXdef, hYdef, inf_assoc, inf_eq_right.mpr hEM]
  have hY'mem : ∀ y : ↥E, y ∈ Y' ↔ (y : G) ∈ Y := fun y => by
    rw [hY'def, Subgroup.mem_subgroupOf]
  have hQ'mem : ∀ q : ↥E, q ∈ Q' ↔ (q : G) ∈ Q := fun q => by
    rw [hQ'def, Subgroup.mem_subgroupOf]
  have ht'ord : orderOf (⟨B.t, htE⟩ : ↥E) = 2 := by
    rw [Subgroup.orderOf_mk, B.t_order]
  have ht'Q : (⟨B.t, htE⟩ : ↥E) ∈ Q' := (hQ'mem _).mpr htQ
  have ht'cen : ∀ q ∈ Q', q * (⟨B.t, htE⟩ : ↥E) = (⟨B.t, htE⟩ : ↥E) * q := by
    intro q hq
    have hqP : (q : G) ∈ P := (Subgroup.mem_inf.mp ((hQ'mem q).mp hq)).1
    have hqH : (q : G) ∈ B.H := (hPle hqP).2
    apply Subtype.ext
    have hcomm : (q : G) * B.t = B.t * (q : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp hqH
    simpa [Subgroup.coe_mul] using hcomm
  have hY'odd : Odd (Nat.card ↥Y') := by
    have hcard : Nat.card ↥Y' = Nat.card ↥Y :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYE).toEquiv
    rw [hcard]; exact hYodd
  have hY't' : Y' ≤ Subgroup.centralizer ({⟨B.t, htE⟩} : Set ↥E) := by
    intro y hy
    have hyU : (y : G) ∈ B.U := (Subgroup.mem_inf.mp ((hY'mem y).mp hy)).1
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hcomm : (y : G) * B.t = B.t * (y : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp (B.U_le_H hyU)
    simpa [Subgroup.coe_mul] using hcomm
  have hQN : Q' ≤ Subgroup.normalizer ((Y' : Subgroup ↥E) : Set ↥E) := by
    intro q hq
    have hqQ : (q : G) ∈ Q := (hQ'mem q).mp hq
    have hqE : (q : G) ∈ E := hQE hqQ
    have hqn : ∀ x : G, x ∈ X ↔ (q : G) * x * (q : G)⁻¹ ∈ X :=
      Subgroup.mem_normalizer_iff.mp (hQnormalizesX hqQ)
    rw [Subgroup.mem_normalizer_iff]
    refine fun y => ⟨fun hy => ?_, fun hy => ?_⟩
    · have hyY : (y : G) ∈ Y := (hY'mem y).mp hy
      have hyX : (y : G) ∈ X := (hXY ▸ hyY).1
      have hconjX : (q : G) * (y : G) * (q : G)⁻¹ ∈ X := (hqn _).mp hyX
      refine (hY'mem _).mpr ?_
      have hcoe : ((q * y * q⁻¹ : ↥E) : G) = (q : G) * (y : G) * (q : G)⁻¹ := by
        simp [Subgroup.coe_mul]
      rw [hcoe, ← hXY]
      refine Subgroup.mem_inf.mpr ⟨hconjX, ?_⟩
      exact E.mul_mem (E.mul_mem hqE (hYE hyY)) (E.inv_mem hqE)
    · have hYmem : ((q * y * q⁻¹ : ↥E) : G) ∈ Y := (hY'mem _).mp hy
      have hcoe : ((q * y * q⁻¹ : ↥E) : G) = (q : G) * (y : G) * (q : G)⁻¹ := by
        simp [Subgroup.coe_mul]
      have hyX : (y : G) ∈ X := by
        have h1 : (q : G) * (y : G) * (q : G)⁻¹ ∈ X := by
          have h2 : (q : G) * (y : G) * (q : G)⁻¹ ∈ Y := by
            rw [← hcoe]; exact hYmem
          rw [← hXY] at h2; exact h2.1
        exact (hqn (y : G)).mpr h1
      exact (hY'mem y).mpr (by rw [← hXY]; exact ⟨hyX, y.2⟩)
  -- ## 4. Bender's structure input: `Y Z(E)/Z(E)` is cyclic, `Q'` acts on it by `±1`
  have hQpg' : IsPGroup 2 Q' := by rw [hQ'def, hQdef, hEdef]; exact hQpg
  obtain ⟨hYcyc, hpm⟩ :=
    CoreOddAction I ↥E hZodd hshape Q' hQpg' ⟨B.t, htE⟩ ht'Q ht'ord ht'cen Y' hY'odd hY't' hQN
  -- ## 5. Bender's (1)–(2) inside `↥E`
  have hQdih' : ∃ m : ℕ, 2 ≤ m ∧ Nonempty (Q' ≃* DihedralGroup m) := by
    refine ⟨n, hn2, ?_⟩
    rw [hQ'def, hQdef, hEdef]
    exact hQdih
  obtain ⟨s', hs'Q, hs'ord, hs'inv, _hs'cen, hs'cyc⟩ :=
    Work.CORE4.OddDihActionInvolution I (Subgroup.center ↥E) le_rfl Q' Y' hQN hQpg' hY'odd
      hQdih' hYcyc hpm
  -- ## 6. Transfer to `G`
  have hs'QG : (s' : G) ∈ Q := (hQ'mem s').mp hs'Q
  have hs'ord' : orderOf (s' : G) = 2 := by
    rw [Subgroup.orderOf_coe]; exact hs'ord
  have hmapQ : Q'.map E.subtype = Q := by
    rw [hQ'def]; exact Subgroup.map_subgroupOf_eq_of_le hQE
  have hmapY : Y'.map E.subtype = Y := by
    rw [hY'def]; exact Subgroup.map_subgroupOf_eq_of_le hYE
  have hmapComm : (⁅Q', Y'⁆ : Subgroup ↥E).map E.subtype = (⁅Q, Y⁆ : Subgroup G) := by
    rw [Subgroup.map_commutator, hmapQ, hmapY]
  have hYinv : ((⁅Q, Y⁆ : Subgroup G) : Set G) = Work.GW2.invSet Y (s' : G) := by
    rw [← hmapComm]
    ext z
    constructor
    · intro hz
      obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
      have hz'' : z' ∈ Work.GW2.invSet Y' s' := by rw [← hs'inv]; exact hz'
      obtain ⟨hz'Y, hz'conj⟩ := hz''
      refine ⟨(hY'mem z').mp hz'Y, ?_⟩
      have h1 : ((s' * z' * s'⁻¹ : ↥E) : G) = ((z'⁻¹ : ↥E) : G) := congrArg Subtype.val hz'conj
      simpa [Subgroup.coe_mul] using h1
    · intro hz
      obtain ⟨hzY, hzconj⟩ := hz
      rw [← hmapY] at hzY
      obtain ⟨z', hz'Y, hz'eq⟩ := Subgroup.mem_map.mp hzY
      refine Subgroup.mem_map.mpr ⟨z', ?_, hz'eq⟩
      have hmem : z' ∈ Work.GW2.invSet Y' s' := by
        refine ⟨hz'Y, ?_⟩
        apply Subtype.ext
        have h2 : (z' : G) = z := hz'eq
        have h1 : (s' : G) * (z' : G) * (s' : G)⁻¹ = (z' : G)⁻¹ := by
          rw [h2]
          exact hzconj
        simpa using h1
      rw [← hs'inv] at hmem
      exact hmem
  have hYcyc' : IsCyclic (⁅Q, Y⁆ : Subgroup G) := by
    rw [← hmapComm]
    exact (MulEquiv.isCyclic (Subgroup.equivMapOfInjective (⁅Q', Y'⁆ : Subgroup ↥E) E.subtype
      (Subgroup.subtype_injective E))).mp hs'cyc
  -- ## 7. The transfer `U ⊓ E ↝ U ⊓ M`
  have hXinv : (((⁅Q, X ⊓ E⁆ : Subgroup G) : Set G) = Work.GW2.invSet (X ⊓ E) (s' : G)) := by
    rw [hXY]; exact hYinv
  have hXcyc : IsCyclic (⁅Q, X ⊓ E⁆ : Subgroup G) := by
    rw [hXY]; exact hYcyc'
  obtain ⟨_hcommX, hinvX, hcycX, hcenX, hsupX⟩ :=
    TransferLayerInf I E M Q X (s' : G) hEM hEnorm hQE hXM hQnormalizesX hQ2 hXodd
      hs'QG hs'ord' hXinv hXcyc
  -- ## 8. Conclusion
  refine ⟨(s' : G), ?_, hs'ord', ?_, ?_, ?_, ?_⟩
  · exact hs'QG
  · exact hinvX.symm
  · exact hcycX
  · exact hcenX
  · exact hsupX

end Work.CORE4
