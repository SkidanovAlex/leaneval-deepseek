import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.LayerCtx6
import Submission.Work.CORE4.Case2NotHLeM
import Submission.Work.CORE4.SixThree
import Submission.Work.CORE4.Case2LayerOneInvClass
import Submission.Work.CORE4.LayerInSylow
import Submission.Work.CORE4.Case2KOddCommutator
import Submission.Work.CORE4.CoreQuotientSetup
import Submission.Work.CORE4.CoreA7OddCentralizer
import Submission.Work.CORE4.CoreL2OddCentralizer
import Submission.Work.CORE4.Case2Setup9S2OddAct
import Submission.Work.CORE4.Case2Setup9S2CoreGT
import Submission.Work.BSW.Api.card_sup_of_le_normalizer_of_inf_eq_bot

namespace Work.CORE4

open Subgroup
open scoped commutatorElement
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

/-! ## The layer of the coatom: `E(M)` is quasisimple, with odd centre and `A₇`/`L₂(q)` shape

This is the argument of `Submission/Work/CORE4/Case2NotHLeM.lean` (`layer_facts`) and
`Submission/Work/CORE4/LayerCtx6.lean`, with `IsCoatom M` and `t ∈ E(M)` in place of the
`Case2Ctx`/`Case2Ctx6` hypothesis (whose `M = E·C_M(t)` is not needed for this part). -/

theorem Case2S2_layer (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    {B : Work.GW2.BenderSetup G} {M : Subgroup G} (hcoat : IsCoatom M)
    (ht : B.t ∈ Work.GW2.layerIn M) :
    Work.GW2.IsQuasisimple (Work.GW2.layerIn M) ∧
      Odd (Nat.card (Subgroup.center ↥(Work.GW2.layerIn M))) ∧
      (Nonempty ((↥(Work.GW2.layerIn M) ⧸ Subgroup.center ↥(Work.GW2.layerIn M)) ≃*
          alternatingGroup (Fin 7)) ∨
        ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
          Nonempty ((↥(Work.GW2.layerIn M) ⧸ Subgroup.center ↥(Work.GW2.layerIn M)) ≃*
            Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) := by
  classical
  have ht1 : B.t ≠ 1 := by
    intro h1
    have ht2 := B.t_order
    rw [h1, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have hlayer_ne : Work.GW2.layer ↥M ≠ ⊥ := by
    intro hbot
    have hbot' : Work.GW2.layerIn M = ⊥ := by
      rw [Work.GW2.layerIn, hbot, Subgroup.map_bot]
    exact ht1 (Subgroup.mem_bot.mp (hbot' ▸ ht))
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
  obtain ⟨hlayerEq, hodd, hshape⟩ := I.toolkit.lay ↥M I.toolkit.ft hD hIsD E' hE'norm hE'q
  have hEq : Work.GW2.layerIn M = E'.map (M.subtype) := by
    rw [Work.GW2.layerIn, hlayerEq]
  rw [hEq]
  exact quasisimple_shape_map (M.subtype) (Subgroup.subtype_injective M) hE'q hodd hshape

/-- **Bender's Sylow choice** in the form used below: with `E := layerIn M` and `Q := P ⊓ E`, one
has `t ∈ Q`, `Q` is a `2`-group, and `Q ≅ DihedralGroup n` with `n ≥ 2`.

This is `Submission/Work/CORE4/LayerInSylow.lean` (proved), transported from the subgroup
`Q.subgroupOf E` of `↥E` to the subgroup `Q` of `G`. -/
theorem Case2S2_Q_dihedral (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    {B : Work.GW2.BenderSetup G} {M P : Subgroup G} (hcoat : IsCoatom M)
    (ht : B.t ∈ Work.GW2.layerIn M) (hP2 : IsPGroup 2 P) (hPM : P ≤ M ⊓ B.H)
    (hrel : ¬ 2 ∣ P.relIndex M)
    (hZ : Odd (Nat.card (Subgroup.center ↥(Work.GW2.layerIn M))))
    (hshape : (Nonempty ((↥(Work.GW2.layerIn M) ⧸ Subgroup.center ↥(Work.GW2.layerIn M)) ≃*
          alternatingGroup (Fin 7)) ∨
        ∃ p k : ℕ, ∃ _ : Fact p.Prime, Odd p ∧ 5 ≤ p ^ k ∧
          Nonempty ((↥(Work.GW2.layerIn M) ⧸ Subgroup.center ↥(Work.GW2.layerIn M)) ≃*
            Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)))) :
    B.t ∈ P ⊓ Work.GW2.layerIn M ∧ IsPGroup 2 ↥(P ⊓ Work.GW2.layerIn M) ∧
      ∃ n : ℕ, 2 ≤ n ∧ Nonempty ((P ⊓ Work.GW2.layerIn M : Subgroup G) ≃* DihedralGroup n) := by
  obtain ⟨htP, hQ2, -, n, hn2, ⟨e⟩⟩ :=
    LayerInSylow I G hbc B M P hcoat ht hP2 hPM hrel hZ hshape
  exact ⟨htP, hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right), n, hn2,
    ⟨(Subgroup.subgroupOfEquivOfLe inf_le_right).symm.trans e⟩⟩

/-- **The `E`-internal part of Bender's (1),(2)**: the same statement with `U ⊓ M` replaced by
`U ⊓ E(M)`.

This is where the structure of `A₇`/`L₂(q)` enters: `(U ⊓ E) Z(E)/Z(E)` is cyclic (its image is an
odd-order subgroup of `C_{E/Z(E)}(t Z(E))`), and every `q ∈ P ⊓ E` acts on it by `± 1` modulo
`Z(E)` — because `C_{E/Z(E)}(t Z(E))` is `S₄` (odd part `C₃`, all automorphisms `±1`) or a dihedral
group `D_n` (odd subgroups lie in the abelian rotation group, on which `D_n` acts by `±1`).  The
abstract group theory producing `s` and the two eigenspaces is
`Work.CORE4.Case2Setup9S2CoreGT`. -/
theorem Case2S2_Einternal (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    {B : Work.GW2.BenderSetup G} {M P : Subgroup G} (hcoat : IsCoatom M)
    (ht : B.t ∈ Work.GW2.layerIn M) (hP2 : IsPGroup 2 P) (hPM : P ≤ M ⊓ B.H)
    (hrel : ¬ 2 ∣ P.relIndex M) :
    ∃ s ∈ P ⊓ Work.GW2.layerIn M, orderOf s = 2 ∧
      (Work.GW2.invSet (B.U ⊓ Work.GW2.layerIn M) s : Set G) =
        ((⁅P ⊓ Work.GW2.layerIn M, B.U ⊓ Work.GW2.layerIn M⁆ : Subgroup G) : Set G) ∧
      IsCyclic (⁅P ⊓ Work.GW2.layerIn M, B.U ⊓ Work.GW2.layerIn M⁆ : Subgroup G) ∧
      ((B.U ⊓ Work.GW2.layerIn M) ⊓ Subgroup.centralizer ({s} : Set G) =
        (B.U ⊓ Work.GW2.layerIn M) ⊓
          Subgroup.centralizer (((P ⊓ Work.GW2.layerIn M : Subgroup G)) : Set G)) := by
  classical
  obtain ⟨-, hZ, hshape⟩ := Case2S2_layer I hbc hcoat ht
  obtain ⟨htQ, hQ2, n, hn2, hQdih⟩ := Case2S2_Q_dihedral I hbc hcoat ht hP2 hPM hrel hZ hshape
  -- work in the group `↥E`
  set t' : ↥(Work.GW2.layerIn M) := ⟨B.t, ht⟩ with ht'def
  set Q' : Subgroup ↥(Work.GW2.layerIn M) :=
    (P ⊓ Work.GW2.layerIn M).subgroupOf (Work.GW2.layerIn M) with hQ'def
  set X' : Subgroup ↥(Work.GW2.layerIn M) :=
    (B.U ⊓ Work.GW2.layerIn M).subgroupOf (Work.GW2.layerIn M) with hX'def
  set Z : Subgroup ↥(Work.GW2.layerIn M) := Subgroup.center ↥(Work.GW2.layerIn M) with hZdef
  have ht'ord : orderOf t' = 2 := by
    rw [ht'def, ← Subgroup.orderOf_coe (⟨B.t, ht⟩ : ↥(Work.GW2.layerIn M))]
    exact B.t_order
  have ht'Q : t' ∈ Q' := by
    rw [hQ'def, ht'def]
    exact Subgroup.mem_subgroupOf.mpr htQ
  have hQ'cent : Q' ≤ Subgroup.centralizer ({t'} : Set ↥(Work.GW2.layerIn M)) := by
    intro q hq
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    apply Subtype.ext
    have hqG : (q : G) ∈ P ⊓ Work.GW2.layerIn M := Subgroup.mem_subgroupOf.mp (hQ'def ▸ hq)
    have hqH : (q : G) ∈ B.H := (hPM (Subgroup.mem_inf.mp hqG).1).2
    simpa using (Subgroup.mem_centralizer_iff.mp hqH) B.t (Set.mem_singleton B.t)
  have hX'cent : X' ≤ Subgroup.centralizer ({t'} : Set ↥(Work.GW2.layerIn M)) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    apply Subtype.ext
    have hyG : (y : G) ∈ B.U ⊓ Work.GW2.layerIn M := Subgroup.mem_subgroupOf.mp (hX'def ▸ hy)
    have hyH : (y : G) ∈ B.H := B.U_le_H (Subgroup.mem_inf.mp hyG).1
    simpa using (Subgroup.mem_centralizer_iff.mp hyH) B.t (Set.mem_singleton B.t)
  have hX'odd : Odd (Nat.card ↥X') := by
    rw [hX'def,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_right : B.U ⊓ Work.GW2.layerIn M ≤ Work.GW2.layerIn M)).toEquiv]
    exact Odd.of_dvd_nat B.U_odd (Subgroup.card_dvd_of_le inf_le_left)
  -- `Q` normalises `X` in `G`, hence `Q'` normalises `X'` in `↥E`
  have hQNinf : ∀ q ∈ P ⊓ Work.GW2.layerIn M, ∀ y ∈ B.U ⊓ Work.GW2.layerIn M,
      q * y * q⁻¹ ∈ B.U ⊓ Work.GW2.layerIn M := by
    intro q hq y hy
    obtain ⟨hqP, -⟩ := Subgroup.mem_inf.mp hq
    obtain ⟨hyU, hyE⟩ := Subgroup.mem_inf.mp hy
    have hqH : q ∈ B.H := (hPM hqP).2
    exact Subgroup.mem_inf.mpr
      ⟨(Subgroup.normal_subgroupOf_iff B.U_le_H).mp B.U_normal y q hyU hqH,
       (Subgroup.le_normalizer_iff.mp (Work.CORE4.layerIn_le_normalizer M) q (hPM hqP).1) y hyE⟩
  have hQ'N' : Q' ≤ Subgroup.normalizer (X' : Set ↥(Work.GW2.layerIn M)) := by
    rw [Subgroup.le_normalizer_iff]
    intro q hq y hy
    have hqG : (q : G) ∈ P ⊓ Work.GW2.layerIn M := Subgroup.mem_subgroupOf.mp (hQ'def ▸ hq)
    have hyG : (y : G) ∈ B.U ⊓ Work.GW2.layerIn M := Subgroup.mem_subgroupOf.mp (hX'def ▸ hy)
    rw [hX'def]
    exact Subgroup.mem_subgroupOf.mpr (hQNinf (q : G) hqG (y : G) hyG)
  -- the `A₇`/`L₂(q)` input: `X'Z/Z` is cyclic and `Q'` acts on it by `±1`
  obtain ⟨hcycX, hpm⟩ :=
    Case2Setup9S2OddAct I ↥(Work.GW2.layerIn M) hZ hshape t' ht'ord Q' X' ht'Q hQ'cent
      hX'cent hX'odd hQ'N'
  -- the abstract group theory
  have hQ2' : IsPGroup 2 ↥Q' :=
    hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : P ⊓ Work.GW2.layerIn M ≤ Work.GW2.layerIn M)).symm
  have hQdih' : ∃ m : ℕ, 2 ≤ m ∧ Nonempty (Q' ≃* DihedralGroup m) :=
    ⟨n, hn2, hQdih.map (fun e =>
      (Subgroup.subgroupOfEquivOfLe
        (inf_le_right : P ⊓ Work.GW2.layerIn M ≤ Work.GW2.layerIn M)).trans e)⟩
  obtain ⟨s', hs'Q', hs'2, hEs', hcen', hcyc'⟩ :=
    Case2Setup9S2CoreGT I Z le_rfl Q' X' hQ'N' hQ2' hX'odd hQdih' hcycX hpm
  set s : G := (s' : G) with hsdef
  have hs'Q : (s' : G) ∈ P ⊓ Work.GW2.layerIn M :=
    Subgroup.mem_subgroupOf.mp (hQ'def ▸ hs'Q')
  refine ⟨s, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsdef]
    exact hs'Q
  · rw [hsdef, Subgroup.orderOf_coe s']
    exact hs'2
  · -- Bender's (1): `I_{U⊓E}(s) = ⁅Q, U⊓E⁆`
    have hmap := Subgroup.map_commutator Q' X' (Work.GW2.layerIn M).subtype
    rw [Subgroup.map_subgroupOf_eq_of_le
          (inf_le_right : P ⊓ Work.GW2.layerIn M ≤ Work.GW2.layerIn M),
        Subgroup.map_subgroupOf_eq_of_le
          (inf_le_right : B.U ⊓ Work.GW2.layerIn M ≤ Work.GW2.layerIn M)] at hmap
    ext x
    constructor
    · intro hx
      obtain ⟨hxX, hxinv⟩ := hx
      have hxE : x ∈ Work.GW2.layerIn M := (Subgroup.mem_inf.mp hxX).2
      have hx' : (⟨x, hxE⟩ : ↥(Work.GW2.layerIn M)) ∈ Work.GW2.invSet X' s' := by
        refine ⟨Subgroup.mem_subgroupOf.mpr hxX, ?_⟩
        apply Subtype.ext
        rw [hsdef] at hxinv
        simpa using hxinv
      rw [← hEs'] at hx'
      rw [← hmap]
      exact Subgroup.mem_map.mpr ⟨⟨x, hxE⟩, hx', rfl⟩
    · intro hx
      rw [← hmap] at hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
      rw [← hyx]
      have hy' : y ∈ Work.GW2.invSet X' s' := by rw [← hEs']; exact hy
      obtain ⟨hyX, hyinv⟩ := hy'
      refine ⟨Subgroup.mem_subgroupOf.mp hyX, ?_⟩
      have h2 := congrArg (fun z : ↥(Work.GW2.layerIn M) => (z : G)) hyinv
      rw [hsdef]
      simpa using h2
  · -- `⁅Q, U⊓E⁆` is cyclic
    have hmap := Subgroup.map_commutator Q' X' (Work.GW2.layerIn M).subtype
    rw [Subgroup.map_subgroupOf_eq_of_le
          (inf_le_right : P ⊓ Work.GW2.layerIn M ≤ Work.GW2.layerIn M),
        Subgroup.map_subgroupOf_eq_of_le
          (inf_le_right : B.U ⊓ Work.GW2.layerIn M ≤ Work.GW2.layerIn M)] at hmap
    rw [← hmap]
    exact (MulEquiv.isCyclic (Subgroup.equivMapOfInjective (⁅Q', X'⁆)
      (Work.GW2.layerIn M).subtype (Subgroup.subtype_injective _))).mp hcyc'
  · -- Bender's (2): `C_{U⊓E}(s) = C_{U⊓E}(Q)`
    apply le_antisymm
    · intro x hx
      obtain ⟨hxX, hxcen⟩ := Subgroup.mem_inf.mp hx
      have hxE : x ∈ Work.GW2.layerIn M := (Subgroup.mem_inf.mp hxX).2
      have hx' : (⟨x, hxE⟩ : ↥(Work.GW2.layerIn M)) ∈
          X' ⊓ Subgroup.centralizer ({s'} : Set ↥(Work.GW2.layerIn M)) := by
        refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr hxX, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        apply Subtype.ext
        have h1 := (Subgroup.mem_centralizer_iff.mp hxcen) s (Set.mem_singleton s)
        rw [hsdef] at h1
        simpa using h1
      rw [hcen'] at hx'
      obtain ⟨-, hxQ'⟩ := Subgroup.mem_inf.mp hx'
      refine Subgroup.mem_inf.mpr ⟨hxX, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hzQ : z ∈ P ⊓ Work.GW2.layerIn M := hz
      have h2 := (Subgroup.mem_centralizer_iff.mp hxQ')
        (⟨z, (Subgroup.mem_inf.mp hzQ).2⟩ : ↥(Work.GW2.layerIn M))
        (Subgroup.mem_subgroupOf.mpr hzQ)
      have h3 := congrArg (fun w : ↥(Work.GW2.layerIn M) => (w : G)) h2
      simpa using h3
    · intro x hx
      obtain ⟨hxX, hxcen⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨hxX, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      rw [hsdef]
      exact (Subgroup.mem_centralizer_iff.mp hxcen) (s' : G) hs'Q


/-- Bender 1981, §4 (1)–(2) (p. 224–225), with Bender's choice of the Sylow 2-subgroup.

NOTE: this is a deliberate duplicate of `Submission/Work/CORE4/Case2Setup9S.lean` (whose prover
is no longer running, the file is statement + `sorry`); the owner of `Work.CORE4.Case2Setup9`
imports *this* path. Do not edit `Case2Setup9S.lean`.

Let `BenderCtx G`, `B : BenderSetup G`, and `M : Subgroup G` a coatom with `t := B.t ∈ E := layerIn M`,
`M = E · (M ⊓ C_G(t))`, and let `P ≤ M ⊓ B.H = C_M(t)` be a Sylow 2-subgroup of `M` (hypotheses
`IsPGroup 2 P`, `P ≤ M ⊓ B.H`, `¬ 2 ∣ P.relIndex M`), so `t ∈ P` and `P ⊓ E ∈ Syl₂(E)` (`E ⊴ M`).

Conclusion: there is an involution `s ∈ P ⊓ E` such that, writing `K := ⁅P ⊓ E, U ⊓ M⁆`
(`U = O(H) = B.U`),

* `K = I_{U ⊓ M}(s) = {x ∈ U ⊓ M | s x s⁻¹ = x⁻¹}` as *sets* — Bender's (1);
* `K` is cyclic;
* `C_{U ⊓ M}(s) = C_{U ⊓ M}(P ⊓ E)` — second half of (2);
* `U ⊓ M = K ⊔ C_{U ⊓ M}(s)` — Bender's (2), `U ∩ M = K B`.

Route (Bender p. 224). By the structure of `A₇` and `L₂(q)`, `(U ⊓ E) Z(E)/Z(E)` is a *cyclic*
subgroup of `C_{E/Z(E)}(t Z(E))`, and it is *inverted* by an involution of `S ⊓ E`, realised by `s`.
Lifting `s` from `E/Z(E)` to `E` and adjusting by an element of `Z(E)` (`Z(E)` odd, so squaring is
onto on the cyclic `Z(E)`) gives an involution inside the prescribed Sylow `P ⊓ E`. Then
`K = I_{U⊓M}(s)` is an odd-order subgroup inverted by `s`, so `U ⊓ M = K · C_{U⊓M}(s)`
(`I.toolkit.c15`/`Coprime15Prop`, which also gives `K ⊴ U ⊓ M` and `K ≤ F(U ⊓ M)`), and `K` is
cyclic because its image in `E/Z(E)` lies in the cyclic odd part of `C(t̄)`.

Available inputs and practicalities.
* `E := layerIn M` is quasisimple, `Odd |Z(E)|`, and `E/Z(E) ≅ A₇` or `≅ PSL(2,q)` (`q = p^k ≥ 5`,
  `p` odd). `Work.CORE4.LayerCtx6` proves exactly this but takes a `Case2Ctx6`; its proof body uses
  only `M ≠ ⊤`, `t ∈ layerIn M`, `hbc.ih` and `Work.CORE4.DihOrCycSub hbc.sylow M`, so **copy that
  proof** (or `Case2NotHLeM.layer_facts`) with `IsCoatom M` + `B.t ∈ layerIn M` in place of the
  `Case2Ctx6` hypothesis. (`Work.CORE4.DihOrCycSub` gives `DihOrCycSylow ↥M` for any subgroup.)
* `t ∈ P`: `t ∈ M` (from `t ∈ layerIn M`), `t` is central in `B.S` and `P` is a 2-subgroup of `M`
  of full 2-part, so `t ∈ P`; in any case `t ∈ E` and `E ⊴ M` give `t ∈ P ⊓ E`.
* For the `A₇` case: `I.toolkit.a7` (`|C_{A₇}(x)| = 24` for involutions `x`, odd subgroups have order
  `≤ 21`); for the `L₂(q)` case: `I.toolkit.l2cent`, `I.toolkit.l2centOdd` (odd subgroups of a
  centralizer `C_L(t')` are cyclic and inverted by an involution of `C_L(t')`), `I.toolkit.l2ti`,
  `I.toolkit.l2four`, `I.toolkit.autL2`, `I.toolkit.autA7`, and `I.layerOneInvClass`.
* The relevant `P`-vs-`S` bookkeeping is in `Work.CORE4.Case2CountSetup` (`relIndex` toolkit,
  `S_le_H`, `inter_H_M`, second-isomorphism helpers).
* `U ⊓ M = K ⊔ C_{U⊓M}(s)`: with `hI : (I : Set G) = invSet (U⊓M) s` a subgroup, `c15` gives
  `|I|·|C_{U⊓M}(s)| = |U⊓M|` and `I ⊓ C = ⊥`, so `⊔` (not `·`) is the right form. -/
theorem Case2Setup9S2 (I : Work.GW2.C4Inputs) :
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
  intro G _ _ hbc B M P hcoat ht _hsup hP2 hPM hrel
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- §4 (1),(2) with `U ⊓ M` replaced by `U ⊓ E(M)`
  obtain ⟨s, hsQ, hs2, hEs, hcycE, hcenE⟩ :=
    Case2S2_Einternal I hbc hcoat ht hP2 hPM hrel
  -- `E ⊴ M` and `U ⊴ H`
  have hEM : Work.GW2.layerIn M ≤ M := Work.CORE4.layerIn_le M
  have hEMnorm : ∀ g ∈ M, ∀ x ∈ Work.GW2.layerIn M, g * x * g⁻¹ ∈ Work.GW2.layerIn M :=
    fun g hg x hx => (Subgroup.le_normalizer_iff.mp (Work.CORE4.layerIn_le_normalizer M) g hg) x hx
  have hUnorm : ∀ u ∈ B.U, ∀ h ∈ B.H, h * u * h⁻¹ ∈ B.U :=
    fun u hu h hh => (Subgroup.normal_subgroupOf_iff B.U_le_H).mp B.U_normal u h hu hh
  -- `Q ≤ N(Y)`: `q ∈ Q ⊆ M ⊓ H` normalises `M` and (via `U ⊴ H`) `U`
  have hQN : P ⊓ Work.GW2.layerIn M ≤
      Subgroup.normalizer ((B.U ⊓ M : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro q hq y hy
    obtain ⟨hqP, -⟩ := Subgroup.mem_inf.mp hq
    obtain ⟨hyU, hyM⟩ := Subgroup.mem_inf.mp hy
    have hqH : q ∈ B.H := (hPM hqP).2
    have hqM : q ∈ M := (hPM hqP).1
    exact Subgroup.mem_inf.mpr
      ⟨hUnorm y hyU q hqH, M.mul_mem (M.mul_mem hqM hyM) (M.inv_mem hqM)⟩
  -- `⁅Q, Y⁆ ≤ U` (because `Q ≤ H`, `Y ≤ U ⊴ H`) and `⁅Q, Y⁆ ≤ E` (because `Q ≤ E ⊴ M`, `Y ≤ M`)
  have hQYX : ⁅P ⊓ Work.GW2.layerIn M, B.U ⊓ M⁆ ≤ B.U ⊓ Work.GW2.layerIn M := by
    rw [Subgroup.commutator_le]
    intro q hq y hy
    obtain ⟨hqP, hqE⟩ := Subgroup.mem_inf.mp hq
    obtain ⟨hyU, hyM⟩ := Subgroup.mem_inf.mp hy
    have hqH : q ∈ B.H := (hPM hqP).2
    have hmemU : ⁅q, y⁆ ∈ B.U := by
      rw [commutatorElement_def]
      exact B.U.mul_mem (hUnorm y hyU q hqH) (B.U.inv_mem hyU)
    have hmemE : ⁅q, y⁆ ∈ Work.GW2.layerIn M := by
      rw [commutatorElement_def]
      rw [show q * y * q⁻¹ * y⁻¹ = q * (y * q⁻¹ * y⁻¹) by group]
      exact (Work.GW2.layerIn M).mul_mem hqE
        (hEMnorm y hyM q⁻¹ ((Work.GW2.layerIn M).inv_mem hqE))
    exact Subgroup.mem_inf.mpr ⟨hmemU, hmemE⟩
  -- `t ∈ Q` and `Q ≅ DihedralGroup n` (`n ≥ 2`)
  obtain ⟨-, hZ, hshape⟩ := Case2S2_layer I hbc hcoat ht
  obtain ⟨-, hQ2, n, hn2, hQdih⟩ :=
    Case2S2_Q_dihedral I hbc hcoat ht hP2 hPM hrel hZ hshape
  have hYodd : Odd (Nat.card ↥(B.U ⊓ M)) :=
    Odd.of_dvd_nat B.U_odd (Subgroup.card_dvd_of_le inf_le_left)
  -- Bender 1.1(i): `⁅Q, Y⁆ = ⁅Q, ⁅Q, Y⁆⁆` and `⁅Q, Y⁆ ⊔ C_Y(Q) = Y`
  obtain ⟨hcomm2, hsup2⟩ := I.toolkit.c11i G 2 (P ⊓ Work.GW2.layerIn M) (B.U ⊓ M) hQ2
    (Nat.coprime_two_left.mpr hYodd) hQN
  -- hence `⁅Q, Y⁆ = ⁅Q, X⁆` with `X = U ⊓ E`
  have hXY : B.U ⊓ Work.GW2.layerIn M ≤ B.U ⊓ M :=
    le_inf inf_le_left (le_trans inf_le_right hEM)
  have hKXY : ⁅P ⊓ Work.GW2.layerIn M, B.U ⊓ M⁆ =
      ⁅P ⊓ Work.GW2.layerIn M, B.U ⊓ Work.GW2.layerIn M⁆ := by
    refine le_antisymm ?_ (Subgroup.commutator_mono le_rfl hXY)
    rw [← hcomm2]
    exact Subgroup.commutator_mono le_rfl hQYX
  -- (a) `I_{U⊓M}(s) = ⁅Q, U⊓M⁆` as sets
  have hInvY : (Work.GW2.invSet (B.U ⊓ M) s : Set G) =
      ((⁅P ⊓ Work.GW2.layerIn M, B.U ⊓ M⁆ : Subgroup G) : Set G) := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨hxY, hxinv⟩ := hx
      have hxodd : Odd (orderOf x) :=
        Odd.of_dvd_nat B.U_odd
          (Subgroup.orderOf_dvd_natCard B.U (Subgroup.mem_inf.mp hxY).1)
      have hmem : ⁅s, x⁆ ∈ ⁅P ⊓ Work.GW2.layerIn M, B.U ⊓ M⁆ :=
        Subgroup.commutator_mem_commutator hsQ hxY
      have hval : ⁅s, x⁆ = x⁻¹ * x⁻¹ := by rw [commutatorElement_def, hxinv]
      have hx2 : x ^ 2 ∈ ⁅P ⊓ Work.GW2.layerIn M, B.U ⊓ M⁆ := by
        have h1 : x ^ 2 = (x⁻¹ * x⁻¹)⁻¹ := by group
        rw [h1, ← hval]
        exact Subgroup.inv_mem _ hmem
      exact mem_of_sq_mem_of_odd_order hxodd hx2
    · intro x hx
      rw [hKXY] at hx
      have hxE : x ∈ Work.GW2.invSet (B.U ⊓ Work.GW2.layerIn M) s := by
        rw [hEs]
        exact hx
      exact ⟨hXY hxE.1, hxE.2⟩
  -- (b) `⁅Q, U⊓M⁆` is cyclic
  have hcycY : IsCyclic (⁅P ⊓ Work.GW2.layerIn M, B.U ⊓ M⁆ : Subgroup G) :=
    hKXY.symm ▸ hcycE
  -- the two eigenspaces of `s` on `Y = U ⊓ M`
  have hAbot : (⁅P ⊓ Work.GW2.layerIn M, B.U ⊓ M⁆ : Subgroup G) ⊓
      ((B.U ⊓ M) ⊓
        Subgroup.centralizer (((P ⊓ Work.GW2.layerIn M : Subgroup G)) : Set G)) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxA, hxC⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨hxY, hxcen⟩ := Subgroup.mem_inf.mp hxC
    have hinv : s * x * s⁻¹ = x⁻¹ := by
      have h1 : x ∈ Work.GW2.invSet (B.U ⊓ M) s := by
        rw [hInvY]
        exact hxA
      exact h1.2
    have hfix : s * x * s⁻¹ = x := by
      rw [(Subgroup.mem_centralizer_iff.mp hxcen) s hsQ, mul_assoc, mul_inv_cancel, mul_one]
    have hxinv : x = x⁻¹ := by rw [← hinv, hfix]
    have hx2 : x * x = 1 := by
      have h2 : x * x = x * x⁻¹ := congrArg (fun t => x * t) hxinv
      rwa [mul_inv_cancel] at h2
    have hdvd2 : orderOf x ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_two]
      exact hx2
    have hodd : Odd (orderOf x) :=
      Odd.of_dvd_nat B.U_odd
        (Subgroup.orderOf_dvd_natCard B.U (Subgroup.mem_inf.mp hxY).1)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · rw [h1] at hodd
      exact absurd hodd (by decide)
  -- `C_Y(Q)` normalises `⁅Q, Y⁆`: conjugation by `c ∈ Y` with `[c,Q] = 1`
  have hCnorm : ((B.U ⊓ M) ⊓
        Subgroup.centralizer (((P ⊓ Work.GW2.layerIn M : Subgroup G)) : Set G)) ≤
      Subgroup.normalizer ((⁅P ⊓ Work.GW2.layerIn M, B.U ⊓ M⁆ : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro c hc a ha
    obtain ⟨hcY, hccen⟩ := Subgroup.mem_inf.mp hc
    have hcQ : ∀ q ∈ P ⊓ Work.GW2.layerIn M, c * q * c⁻¹ = q := by
      intro q hq
      have h1 := (Subgroup.mem_centralizer_iff.mp hccen) q hq
      rw [← h1, mul_assoc, mul_inv_cancel, mul_one]
    have hcY' : ∀ y ∈ B.U ⊓ M, c * y * c⁻¹ ∈ B.U ⊓ M := by
      intro y hy
      obtain ⟨hyU, hyM⟩ := Subgroup.mem_inf.mp hy
      obtain ⟨hcU, hcM⟩ := Subgroup.mem_inf.mp hcY
      exact Subgroup.mem_inf.mpr
        ⟨B.U.mul_mem (B.U.mul_mem hcU hyU) (B.U.inv_mem hcU),
         M.mul_mem (M.mul_mem hcM hyM) (M.inv_mem hcM)⟩
    have hmapQ : Subgroup.map (MulAut.conj c).toMonoidHom (P ⊓ Work.GW2.layerIn M)
        = P ⊓ Work.GW2.layerIn M := by
      apply le_antisymm
      · rintro x ⟨q, hq, rfl⟩
        show c * q * c⁻¹ ∈ P ⊓ Work.GW2.layerIn M
        rw [hcQ q hq]
        exact hq
      · intro q hq
        exact ⟨q, hq, by simpa [MulAut.conj_apply] using hcQ q hq⟩
    have hmapY : Subgroup.map (MulAut.conj c).toMonoidHom (B.U ⊓ M) = B.U ⊓ M := by
      apply le_antisymm
      · rintro x ⟨y, hy, rfl⟩
        show c * y * c⁻¹ ∈ B.U ⊓ M
        exact hcY' y hy
      · intro y hy
        exact ⟨c⁻¹ * y * c, by
            obtain ⟨hyU, hyM⟩ := Subgroup.mem_inf.mp hy
            obtain ⟨hcU, hcM⟩ := Subgroup.mem_inf.mp hcY
            exact Subgroup.mem_inf.mpr
              ⟨B.U.mul_mem (B.U.mul_mem (B.U.inv_mem hcU) hyU) hcU,
               M.mul_mem (M.mul_mem (M.inv_mem hcM) hyM) hcM⟩,
          by show c * (c⁻¹ * y * c) * c⁻¹ = y; group⟩
    have hca : c * a * c⁻¹ ∈ ⁅P ⊓ Work.GW2.layerIn M, B.U ⊓ M⁆ := by
      have hmem : MulAut.conj c a ∈ Subgroup.map (MulAut.conj c).toMonoidHom
          (⁅P ⊓ Work.GW2.layerIn M, B.U ⊓ M⁆) := Subgroup.mem_map_of_mem _ ha
      rw [Subgroup.map_commutator, hmapQ, hmapY] at hmem
      simpa [MulAut.conj_apply] using hmem
    exact hca
  -- `Y = A · C` (internal product), from `A ⊔ C = Y`, `A ⊓ C = ⊥`, `C ≤ N(A)`
  have hcoe : (((⁅P ⊓ Work.GW2.layerIn M, B.U ⊓ M⁆ : Subgroup G) ⊔ ((B.U ⊓ M) ⊓
        Subgroup.centralizer (((P ⊓ Work.GW2.layerIn M : Subgroup G)) : Set G)) :
        Subgroup G) : Set G) =
      ((⁅P ⊓ Work.GW2.layerIn M, B.U ⊓ M⁆ : Subgroup G) : Set G) *
        (((B.U ⊓ M) ⊓
          Subgroup.centralizer (((P ⊓ Work.GW2.layerIn M : Subgroup G)) : Set G) :
          Subgroup G) : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ hCnorm
  have hfactor : ∀ y ∈ B.U ⊓ M, ∃ k ∈ (⁅P ⊓ Work.GW2.layerIn M, B.U ⊓ M⁆ : Subgroup G),
      ∃ c ∈ (B.U ⊓ M) ⊓
        Subgroup.centralizer (((P ⊓ Work.GW2.layerIn M : Subgroup G)) : Set G), k * c = y := by
    intro y hy
    have hz : y ∈ ((⁅P ⊓ Work.GW2.layerIn M, B.U ⊓ M⁆ : Subgroup G) : Set G) *
        (((B.U ⊓ M) ⊓
          Subgroup.centralizer (((P ⊓ Work.GW2.layerIn M : Subgroup G)) : Set G) :
          Subgroup G) : Set G) := by
      rw [← hcoe]
      exact hsup2.symm ▸ hy
    obtain ⟨k, hk, c, hc, hkc⟩ := Set.mem_mul.mp hz
    exact ⟨k, hk, c, hc, hkc⟩
  -- (c) `C_Y(s) = C_Y(Q)`
  have hCenY : (B.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G) =
      (B.U ⊓ M) ⊓
        Subgroup.centralizer (((P ⊓ Work.GW2.layerIn M : Subgroup G)) : Set G) := by
    refine le_antisymm ?_ ?_
    · intro y hy
      obtain ⟨hyY, hyC⟩ := Subgroup.mem_inf.mp hy
      obtain ⟨k, hk, c, hc, hkc⟩ := hfactor y hyY
      obtain ⟨hcY, hccen⟩ := Subgroup.mem_inf.mp hc
      have hkA : s * k * s⁻¹ = k⁻¹ := by
        have h1 : k ∈ Work.GW2.invSet (B.U ⊓ M) s := by
          rw [hInvY]
          exact hk
        exact h1.2
      have hcs : s * c * s⁻¹ = c := by
        have h1 := (Subgroup.mem_centralizer_iff.mp hccen) s hsQ
        rw [h1, mul_assoc, mul_inv_cancel, mul_one]
      have hsy : s * y * s⁻¹ = y := by
        have h1 := (Subgroup.mem_centralizer_iff.mp hyC) s (Set.mem_singleton s)
        rw [h1, mul_assoc, mul_inv_cancel, mul_one]
      have hy_eq : y = k⁻¹ * c := by
        have h2 : y = (s * k * s⁻¹) * (s * c * s⁻¹) := by
          calc y = s * y * s⁻¹ := hsy.symm
            _ = s * (k * c) * s⁻¹ := by rw [← hkc]
            _ = (s * k * s⁻¹) * (s * c * s⁻¹) := by group
        rw [hkA, hcs] at h2
        exact h2
      have hkk : k = k⁻¹ := by
        have h3 : k * c = k⁻¹ * c := by rw [hkc, hy_eq]
        exact mul_right_cancel h3
      have hk1 : k = 1 := by
        have hk2 : k * k = 1 := by
          have h4 : k * k = k * k⁻¹ := by rw [← hkk]
          rwa [mul_inv_cancel] at h4
        have hdvd : orderOf k ∣ 2 := by
          rw [orderOf_dvd_iff_pow_eq_one, pow_two]
          exact hk2
        have hoddk : Odd (orderOf k) :=
          Odd.of_dvd_nat B.U_odd
            (Subgroup.orderOf_dvd_natCard B.U (Subgroup.mem_inf.mp (hQYX hk)).1)
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
        · exact orderOf_eq_one_iff.mp h1
        · rw [h1] at hoddk
          exact absurd hoddk (by decide)
      rw [hk1, one_mul] at hkc
      rw [hkc.symm]
      exact hc
    · refine inf_le_inf_left _ ?_
      refine Subgroup.centralizer_le ?_
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hsQ
  exact ⟨s, hsQ, hs2, hInvY, hcycY, hCenY, by rw [hCenY]; exact hsup2.symm⟩

end Work.CORE4
