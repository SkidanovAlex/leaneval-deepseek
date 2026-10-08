import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.CountSetup
import Submission.Work.CORE4.SixThree
import Submission.Work.CORE4.Case2NotHLeM
import Submission.Work.CORE4.LayerCtx6
import Submission.Work.CORE4.Case2K1_ne_bot
import Submission.Work.CORE4.DihOrCycSub
import Submission.Work.CORE4.KFP.SubgroupOf
import Submission.Work.CORE4.FpropsAux.le_map_piCore_of_isPiSubgroup_of_isNilpotent
import Submission.Work.CORE4.FpropsAux.le_of_isCyclic_inf_of_normalizer_le
import Submission.Work.CORE4.FpropsAux.mem_fittingIn_of_le_of_normal_isNilpotent

open scoped MatrixGroups

namespace Work.CORE4

open Work.GW2 Subgroup

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## Auxiliary lemmas for `Case2Setup9Fprops` -/

/-- A finite subgroup has odd order if and only if it is a `{2}ᶜ`-subgroup. -/
theorem odd_iff_isPiSubgroup_two_compl {G : Type*} [Group G] [Finite G] (N : Subgroup G) :
    Odd (Nat.card N) ↔ Subgroup.IsPiSubgroup ({q : ℕ | q ≠ 2}) N := by
  unfold Subgroup.IsPiSubgroup
  have hne : Nat.card ↥N ≠ 0 := (Nat.card_pos (α := ↥N)).ne'
  constructor
  · intro hodd q hq hq2
    rw [hq2] at hq
    exact (Nat.not_even_iff_odd.mpr hodd)
      (even_iff_two_dvd.mpr (Nat.mem_primeFactors.mp hq).2.1)
  · intro h
    rw [← Nat.not_even_iff_odd]
    intro heven
    exact h 2 (Nat.mem_primeFactors.mpr
      ⟨by norm_num, even_iff_two_dvd.mp heven, hne⟩) rfl

/-- **An element of odd order of the Fitting subgroup lies in `F_{2'}`.**

`K := ⟨x⟩ ≤ F(M₀)` has odd order, hence corresponds to a `{2}ᶜ`-subgroup of the nilpotent group
`F(M₀)`, and a `π`-subgroup of a finite nilpotent group lies in `O_π`
(`FpropsAux.le_map_piCore_of_isPiSubgroup_of_isNilpotent`). -/
theorem mem_fittingPiIn_of_odd_mem_fittingIn {G : Type} [Group G] [Finite G]
    (M₀ : Subgroup G) {x : G} (hx : x ∈ Work.GW2.fittingIn M₀) (hodd : Odd (orderOf x)) :
    x ∈ Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ) M₀ := by
  set K : Subgroup G := Subgroup.zpowers x with hK
  have hxK : x ∈ K := hK.symm ▸ Subgroup.mem_zpowers x
  have hKM : K ≤ Work.GW2.fittingIn M₀ := by
    rw [hK]; exact Subgroup.zpowers_le.mpr hx
  have hKF : K ≤ M₀ := hKM.trans (Subgroup.map_subtype_le _)
  have hcardK : Nat.card ↥K = orderOf x := by rw [hK]; exact Nat.card_zpowers x
  have hKFin : K.subgroupOf M₀ ≤ Work.GW2.fitting ↥M₀ := by
    intro y hy
    have hyK : (y : G) ∈ K := Subgroup.mem_subgroupOf.mp hy
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp (hKM hyK)
    rw [← Subtype.ext hzy]
    exact hz
  have hcardSub : Nat.card ↥(K.subgroupOf M₀) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKF).toEquiv
  have hoddSub : Odd (Nat.card ↥(K.subgroupOf M₀)) := by rw [hcardSub, hcardK]; exact hodd
  have hNpi : Subgroup.IsPiSubgroup ({2}ᶜ : Set ℕ) (K.subgroupOf M₀) :=
    (odd_iff_isPiSubgroup_two_compl (K.subgroupOf M₀)).mp hoddSub
  haveI : Group.IsNilpotent ↥(Work.GW2.fitting ↥M₀) := SevenX.PiFU.isNilpotent_fitting (G := ↥M₀)
  have hstep : K.subgroupOf M₀ ≤ Work.GW2.fittingPi ({2}ᶜ : Set ℕ) ↥M₀ :=
    FpropsAux.le_map_piCore_of_isPiSubgroup_of_isNilpotent (Work.GW2.fitting ↥M₀)
      ({2}ᶜ : Set ℕ) hKFin hNpi
  rw [Work.GW2.fittingPiIn]
  exact Subgroup.mem_map.mpr
    ⟨⟨x, hKF hxK⟩, hstep (Subgroup.mem_subgroupOf.mpr hxK), rfl⟩

/-- Bender 1981, §4 (3)–(4), the three Facts that do **not** need the `B = C_U(s)` identification:
`F ≠ ⊥`, `F ≤ C_G(E(M))` and `N_G(F) = M`.  (The fourth conjunct of Bender's (5), `B = C_U(s)`,
is the separate leaf `Work.CORE4.Case2CU_s`.)

Notation as in §4: `E := layerIn M`, `H = C_G(t)`, `U = O(H)`, `P ≤ M ⊓ H` a Sylow 2-subgroup of
`M`, `s ∈ P ⊓ E` an involution with Bender's (1),(2):

* `(invSet (U ⊓ M) s : Set G) = ⁅P ⊓ E, U ⊓ M⁆`, `K := ⁅P ⊓ E, U ⊓ M⁆` cyclic;
* `(U ⊓ M) ⊓ C_G(s) = (U ⊓ M) ⊓ C_G(P ⊓ E)`;
* `U ⊓ M = K ⊔ ((U ⊓ M) ⊓ C_G(s))` (so `B₀ := (U ⊓ M) ⊓ C_G(s)` and `F := B₀ ⊓ F(U)`).

Extra hypotheses: `X ≠ ⊥ ≤ F(U)` with `N_G(X) ≤ M` (Theorem 2.10 (2)), `¬ H ≤ M` (Theorem 2.6),
`M = E ⊔ (M ⊓ H)` (one class of involutions in `E`), Bender's (3) as a hypothesis
(`F(U) ⊓ M = (F(U) ⊓ K) ⊔ F`, proved for the raw data in `Work.CORE4.Case2SixThreeRaw`), and the
structure input `hEcent` of `Work.CORE4.Case2Setup9Ecent2` (`e ∈ E`, `e^m ∈ C_G(E)` for odd `m`,
`e ∈ C_G(P ⊓ E)` ⟹ `e ∈ C_G(E)`).  (Importable as the proved `Work.CORE4.Case2Setup9Ecent`, whose
hypothesis `Odd (orderOf e)` follows from `e^m ∈ C_G(E)` for odd `m`: then `e^{m·|Z(E)|} = 1` and
`|Z(E)|` is odd — see `Work.CORE4.LayerCtx6`/`I.toolkit.lay`.)

Routes.

* **`F ≠ ⊥`** (Bender: "as `H ≰ M` and `M ⊇ N_G(X)` for some `X ≤ F(U)`, `F(U) ∩ M` is not
  cyclic; it follows that `F ≠ 1`").  `A := F(U) ⊴ H` is nilpotent
  (`SevenX.PiFU.isNilpotent_fittingIn`).  Let `Y := A ⊓ M`; then `X ≤ Y` (`X ≤ A` and
  `X ≤ N_G(X) ≤ M`), and if `Y` were cyclic then `X` would be the unique subgroup of `Y` of order
  `|X|`, hence characteristic in `Y`, so `N_G(Y) ≤ N_G(X) ≤ M` and
  `N_A(Y) = A ⊓ N_G(Y) ≤ Y`, i.e. `Y` is self-normalising in the nilpotent `A`, so `Y = A`
  (`normalizerCondition_iff_only_full_group_self_normalizing`, as in
  `Work.CORE4.Case2K1_ne_bot`).  Then `A = Y` is cyclic and `N_G(A) ≤ N_G(X) ≤ M`, while
  `Work.CORE4.BenderSetup.H_le_normalizer_fittingIn` gives `H ≤ N_G(A)`, contradicting `¬ H ≤ M`.
  So `Y` is not cyclic; but `Y = (A ⊓ K) ⊔ F` by hypothesis and `A ⊓ K ≤ K` is cyclic, so `F ≠ ⊥`.
* **`F ≤ C_G(E)`** (Bender: "centralizing `S ∩ E` and inducing inner automorphisms on `E` by
  1.10.ii, `F` centralizes `E`").  Let `x ∈ F`.  Then `x ∈ F(U) ⊓ M ⊓ H` is odd and lies in
  `Fitting(C_M(t))` (it is in `F(U) ⊓ (M ⊓ H)`, normal in and nilpotent inside `M ⊓ H`), so
  `x ∈ F_{2'}(C_M(t))`; `I.toolkit.d110ii` applied to the D-group `↥M` (with
  `Work.CORE4.DihOrCycSub hbc.sylow M` and `hbc.ih`) gives `e ∈ layer ↥M = E` with
  `x y x⁻¹ = e y e⁻¹` for all `y ∈ E`.  Since `F ≤ B₀ = C_{U⊓M}(P ⊓ E)` (the (2) clause plus
  `B0_def`), `x` centralises `P ⊓ E`, hence so does `e`; and `e^{orderOf x} ∈ C_G(E)` because
  `x^{orderOf x} = 1`.  `orderOf x` is odd (`F ≤ U = O(H)`), so `hEcent` gives `e ∈ C_G(E)`, hence
  `x ∈ C_G(E)`.
* **`N_G(F) = M`** (Bender: "`F` centralizes `E`, hence is normal in `E(H ∩ M) = M` ... hence
  `N_G(F) = M`").  First `F ⊴ M`: `E ≤ N_G(F)` (from `F ≤ C_G(E)`); and for `h ∈ M ⊓ H` one has
  `F^h = (A ⊓ (U ⊓ M) ⊓ C(s))^h = A ⊓ (U ⊓ M) ⊓ C(s^h)` (as `U^h = U`, `A^h = A`, `M^h = M`),
  and `F ≤ C(s^h)` because `F ≤ C_G(E) ∋ s^h ∈ E`, so `F ≤ F^h` and `|F| = |F^h|` give `F = F^h`.
  Since `M = E ⊔ (M ⊓ H)`, this gives `M ≤ N_G(F)`.  Then `N_G(F) ≠ ⊤`: otherwise `F ⊴ G` with
  `F` odd and `F ≠ ⊥`, so `G = F` (simplicity), whence `G ≤ H = C_G(t)` and `t ∈ Z(G) = 1`,
  contradicting `orderOf B.t = 2`; with `M` a coatom, `N_G(F) = M`. -/
theorem Case2Setup9Fprops (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (M X P : Subgroup G) (s : G),
        IsCoatom M → B.t ∈ Work.GW2.layerIn M →
        X ≠ ⊥ → X ≤ Work.GW2.fittingIn B.U → Subgroup.normalizer (X : Set G) ≤ M →
        ¬ B.H ≤ M →
        M = Work.GW2.layerIn M ⊔ (M ⊓ B.H) →
        IsPGroup 2 P → P ≤ M ⊓ B.H → ¬ 2 ∣ P.relIndex M →
        s ∈ P ⊓ Work.GW2.layerIn M → orderOf s = 2 →
        (Work.GW2.invSet (B.U ⊓ M) s : Set G) =
            ((⁅P ⊓ Work.GW2.layerIn M, B.U ⊓ M⁆ : Subgroup G) : Set G) →
        IsCyclic (⁅P ⊓ Work.GW2.layerIn M, B.U ⊓ M⁆ : Subgroup G) →
        ((B.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G)) =
            (B.U ⊓ M) ⊓ Subgroup.centralizer (((P ⊓ Work.GW2.layerIn M : Subgroup G)) : Set G) →
        B.U ⊓ M = (⁅P ⊓ Work.GW2.layerIn M, B.U ⊓ M⁆ : Subgroup G) ⊔
            ((B.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G)) →
        Work.GW2.fittingIn B.U ⊓ M =
          (Work.GW2.fittingIn B.U ⊓ ⁅P ⊓ Work.GW2.layerIn M, B.U ⊓ M⁆) ⊔
            (((B.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G)) ⊓ Work.GW2.fittingIn B.U) →
        (∀ e ∈ Work.GW2.layerIn M, (∃ m : ℕ, Odd m ∧
            e ^ m ∈ Subgroup.centralizer ((Work.GW2.layerIn M : Subgroup G) : Set G)) →
          e ∈ Subgroup.centralizer (((P ⊓ Work.GW2.layerIn M : Subgroup G)) : Set G) →
          e ∈ Subgroup.centralizer ((Work.GW2.layerIn M : Subgroup G) : Set G)) →
        (((B.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G)) ⊓ Work.GW2.fittingIn B.U) ≠ ⊥ ∧
        (((B.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G)) ⊓ Work.GW2.fittingIn B.U) ≤
            Subgroup.centralizer ((Work.GW2.layerIn M : Subgroup G) : Set G) ∧
        Subgroup.normalizer (((((B.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G)) ⊓
            Work.GW2.fittingIn B.U) : Subgroup G) : Set G) = M := by
  intro G _ _ hbc B M X P s hcoat htM hXne hXle hNX hnotH hsup hPp hPle hPidx
    hs_mem hs_ord hKdef hKcyc hB0def hB0split hFUsplit hEcent
  classical
  let A : Subgroup G := Work.GW2.fittingIn B.U
  let E : Subgroup G := Work.GW2.layerIn M
  let B0 : Subgroup G := (B.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G)
  let F : Subgroup G := B0 ⊓ A
  change F ≠ ⊥ ∧ F ≤ Subgroup.centralizer ((E : Subgroup G) : Set G) ∧
    Subgroup.normalizer (F : Set G) = M
  haveI hsimple : IsSimpleGroup G := hbc.simple
  -- ## Elementary consequences of the hypotheses
  have hEM : E ≤ M := layerIn_le M
  have hME : M ≤ Subgroup.normalizer (E : Set G) := layerIn_le_normalizer M
  have hMt : B.t ∈ M := hEM htM
  have hsE : s ∈ E := (Subgroup.mem_inf.mp hs_mem).2
  have hsH : s ∈ B.H := (Subgroup.mem_inf.mp (hPle (Subgroup.mem_inf.mp hs_mem).1)).2
  have hF_le_B0 : F ≤ B0 := inf_le_left
  have hF_le_A : F ≤ A := inf_le_right
  have hB0_le_UM : B0 ≤ B.U ⊓ M :=
    inf_le_left
  have hB0_le_Cs : B0 ≤ Subgroup.centralizer ({s} : Set G) :=
    inf_le_right
  have hF_le_U : F ≤ B.U := hF_le_B0.trans (hB0_le_UM.trans (inf_le_left))
  have hF_le_M : F ≤ M := hF_le_B0.trans (hB0_le_UM.trans (inf_le_right))
  have hF_le_H : F ≤ B.H := hF_le_U.trans B.U_le_H
  have hB0_def' : B0 = (B.U ⊓ M) ⊓
      Subgroup.centralizer (((P ⊓ E : Subgroup G)) : Set G) := hB0def
  have hB0_le_CPE : B0 ≤ Subgroup.centralizer (((P ⊓ E : Subgroup G)) : Set G) := by
    rw [hB0_def']; exact inf_le_right
  have hF_le_CPE : F ≤ Subgroup.centralizer (((P ⊓ E : Subgroup G)) : Set G) :=
    hF_le_B0.trans hB0_le_CPE
  have hAnil : Group.IsNilpotent ↥A := SevenX.PiFU.isNilpotent_fittingIn B.U
  -- `K ≤ U ⊓ M`, from Bender's (1)
  have hK_le_UM : (⁅P ⊓ E, B.U ⊓ M⁆ : Subgroup G) ≤ B.U ⊓ M := by
    intro z hz
    have hz' : z ∈ Work.GW2.invSet (B.U ⊓ M) s := by rw [hKdef]; exact hz
    exact hz'.1
  -- ## (1) `F ≠ ⊥`
  have hFne : F ≠ ⊥ := by
    intro hFbot
    have hAM : A ⊓ M = A ⊓ (⁅P ⊓ E, B.U ⊓ M⁆ : Subgroup G) := by
      have h1 : ((B.U ⊓ M) ⊓ Subgroup.centralizer ({s} : Set G)) ⊓
          Work.GW2.fittingIn B.U = ⊥ := hFbot
      rw [hFUsplit, h1, sup_bot_eq]
    have hcycAM : IsCyclic ↥(A ⊓ M) := by
      rw [hAM]
      exact @Subgroup.isCyclic_of_le G _ (A ⊓ (⁅P ⊓ E, B.U ⊓ M⁆ : Subgroup G))
        (⁅P ⊓ E, B.U ⊓ M⁆ : Subgroup G) inf_le_right hKcyc
    have hXM : X ≤ M := (Subgroup.le_normalizer (H := X)).trans hNX
    have hXAM : X ≤ A ⊓ M := le_inf hXle hXM
    have hAleM : A ≤ M :=
      FpropsAux.le_of_isCyclic_inf_of_normalizer_le (A := A) (M := M) (X := X)
        hAnil hcycAM hXAM hXne hNX
    have hcycA : IsCyclic ↥A := by
      have hAeq : A = A ⊓ M := (inf_eq_left.mpr hAleM).symm
      rwa [hAeq]
    have hNA : Subgroup.normalizer (A : Set G) ≤ M :=
      (FpropsAux.normalizer_le_normalizer_of_isCyclic (B := A) (X := X) hcycA hXle).trans hNX
    exact hnotH ((BenderSetup.H_le_normalizer_fittingIn B).trans hNA)
  -- ## (2) `F ≤ C_G(E)`
  have hFcent : F ≤ Subgroup.centralizer ((E : Subgroup G) : Set G) := by
    intro x hxF
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hxA : x ∈ A := hF_le_A hxF
    have hxU : x ∈ B.U := hF_le_U hxF
    have hxM : x ∈ M := hF_le_M hxF
    have hxH : x ∈ B.H := hF_le_H hxF
    have hxCPE : x ∈ Subgroup.centralizer (((P ⊓ E : Subgroup G)) : Set G) :=
      hB0_le_CPE (hF_le_B0 hxF)
    have hxodd : Odd (orderOf x) :=
      Odd.of_dvd_nat B.U_odd (Subgroup.orderOf_dvd_natCard B.U hxU)
    have hxMH : x ∈ M ⊓ B.H := Subgroup.mem_inf.mpr ⟨hxM, hxH⟩
    -- `x` lies in `F(M ⊓ C_G(t))`
    have hYnorm : ((A ⊓ (M ⊓ B.H)).subgroupOf (M ⊓ B.H)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff (inf_le_right)]
      intro h k hh hk
      refine Subgroup.mem_inf.mpr ⟨?_, (M ⊓ B.H).mul_mem
        ((M ⊓ B.H).mul_mem hk (Subgroup.mem_inf.mp hh).2) ((M ⊓ B.H).inv_mem hk)⟩
      exact (Subgroup.le_normalizer_iff.mp (BenderSetup.H_le_normalizer_fittingIn B)) k
        (Subgroup.mem_inf.mp hk).2 h (Subgroup.mem_inf.mp hh).1
    have hYnil : Group.IsNilpotent ↥(A ⊓ (M ⊓ B.H)) :=
      Group.nilpotent_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (inf_le_left))
    have hxFitting : x ∈ Work.GW2.fittingIn (M ⊓ B.H) :=
      FpropsAux.mem_fittingIn_of_le_of_normal_isNilpotent
        (M₀ := M ⊓ B.H) (Y := A ⊓ (M ⊓ B.H)) (inf_le_right)
        hYnorm hYnil (Subgroup.mem_inf.mpr ⟨hxA, hxMH⟩)
    have hxPiInM : x ∈ Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ) (M ⊓ B.H) :=
      mem_fittingPiIn_of_odd_mem_fittingIn (M ⊓ B.H) hxFitting hxodd
    have hxSub : (⟨x, hxM⟩ : ↥M) ∈
        Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ) ((M ⊓ B.H).subgroupOf M) :=
      KFP.fittingPiIn_subgroupOf (M ⊓ B.H) M (inf_le_left) x hxMH hxPiInM
    -- Bender's `1.10(ii)` applied to the D-group `↥M`
    have hcenEq : Subgroup.centralizer ({⟨B.t, hMt⟩} : Set ↥M) = (M ⊓ B.H).subgroupOf M := by
      ext z
      constructor
      · intro hz
        have hz' : (z : G) * B.t = B.t * (z : G) :=
          congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hz)
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        exact ⟨z.2, Subgroup.mem_centralizer_singleton_iff.mpr hz'⟩
      · intro hz
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hz
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hz.2)
    have hxcen : (⟨x, hxM⟩ : ↥M) ∈ Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ)
        (Subgroup.centralizer ({⟨B.t, hMt⟩} : Set ↥M)) := by
      rw [hcenEq]
      exact hxSub
    have hDsyl : Work.GW2.DihOrCycSylow ↥M := DihOrCycSub hbc.sylow M
    have hDisD : Work.GW2.IsDGroup ↥M :=
      hbc.ih ↥M (card_lt_card_of_ne_top hcoat.ne_top) hDsyl
    obtain ⟨e0, he0mem, he0conj⟩ :=
      I.toolkit.d110ii ↥M I.toolkit.ft hDsyl hDisD (⟨B.t, hMt⟩ : ↥M)
        ((Subgroup.orderOf_coe (⟨B.t, hMt⟩ : ↥M)).symm.trans B.t_order)
        (⟨x, hxM⟩ : ↥M) hxcen
    have heE : (e0 : G) ∈ E :=
      Subgroup.mem_map_of_mem M.subtype he0mem
    have he_conj : ∀ z ∈ E, x * z * x⁻¹ = (e0 : G) * z * (e0 : G)⁻¹ := by
      intro z hz
      obtain ⟨z0, hz0mem, hz0eq⟩ :=
        Subgroup.mem_map.mp (show z ∈ (Work.GW2.layer ↥M).map M.subtype from hz)
      have h := he0conj z0 hz0mem
      have h' : x * (z0 : G) * x⁻¹ = (e0 : G) * (z0 : G) * (e0 : G)⁻¹ :=
        congrArg (fun w : ↥M => (w : G)) h
      have hz0eq' : (z0 : G) = z := hz0eq
      rw [hz0eq'] at h'
      exact h'
    have hpow : ∀ n : ℕ, ∀ z ∈ E,
        x ^ n * z * (x ^ n)⁻¹ = (e0 : G) ^ n * z * ((e0 : G) ^ n)⁻¹ := by
      intro n
      induction n with
      | zero => intro z hz; simp
      | succ k ih =>
          intro z hz
          have hz1 : x * z * x⁻¹ ∈ E := (Subgroup.le_normalizer_iff.mp hME) x hxM z hz
          have hkey : x * z * x⁻¹ = (e0 : G) * z * (e0 : G)⁻¹ := he_conj z hz
          calc x ^ (k + 1) * z * (x ^ (k + 1))⁻¹
              = x ^ k * (x * z * x⁻¹) * (x ^ k)⁻¹ := by rw [pow_succ]; group
            _ = x ^ k * ((e0 : G) * z * (e0 : G)⁻¹) * (x ^ k)⁻¹ := by rw [hkey]
            _ = (e0 : G) ^ k * ((e0 : G) * z * (e0 : G)⁻¹) * ((e0 : G) ^ k)⁻¹ :=
                  ih ((e0 : G) * z * (e0 : G)⁻¹) (by rw [← hkey]; exact hz1)
            _ = (e0 : G) ^ (k + 1) * z * ((e0 : G) ^ (k + 1))⁻¹ := by rw [pow_succ]; group
    have he_pow : (e0 : G) ^ orderOf x ∈
        Subgroup.centralizer ((E : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have h0 : z = (e0 : G) ^ orderOf x * z * ((e0 : G) ^ orderOf x)⁻¹ := by
        have h := hpow (orderOf x) z hz
        rw [pow_orderOf_eq_one] at h
        simpa using h
      have h0' : (e0 : G) ^ orderOf x * z * ((e0 : G) ^ orderOf x)⁻¹ = z := h0.symm
      calc z * (e0 : G) ^ orderOf x
          = ((e0 : G) ^ orderOf x * z * ((e0 : G) ^ orderOf x)⁻¹)
              * (e0 : G) ^ orderOf x := by rw [h0']
        _ = (e0 : G) ^ orderOf x * z := by group
    have he_CPE : (e0 : G) ∈ Subgroup.centralizer (((P ⊓ E : Subgroup G)) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hzE : z ∈ E := (Subgroup.mem_inf.mp hz).2
      have h1 : x * z * x⁻¹ = (e0 : G) * z * (e0 : G)⁻¹ := he_conj z hzE
      have h2 : x * z * x⁻¹ = z := by
        have h3 : z * x = x * z := (Subgroup.mem_centralizer_iff.mp hxCPE) z hz
        calc x * z * x⁻¹ = (z * x) * x⁻¹ := by rw [h3]
          _ = z := by group
      have h4 : (e0 : G) * z * (e0 : G)⁻¹ = z := h1 ▸ h2
      calc z * (e0 : G) = ((e0 : G) * z * (e0 : G)⁻¹) * (e0 : G) := by rw [h4]
        _ = (e0 : G) * z := by group
    have heC : (e0 : G) ∈ Subgroup.centralizer ((E : Subgroup G) : Set G) :=
      hEcent (e0 : G) heE ⟨orderOf x, hxodd, he_pow⟩ he_CPE
    have h5 : (e0 : G) * y * (e0 : G)⁻¹ = y := by
      have hc : y * (e0 : G) = (e0 : G) * y := (Subgroup.mem_centralizer_iff.mp heC) y hy
      rw [← hc]; group
    calc y * x = (x * y * x⁻¹) * x := by rw [he_conj y hy |>.trans h5]
      _ = x * y := by group
  -- ## (3) `N_G(F) = M`
  have hE_le_NF : E ≤ Subgroup.normalizer (F : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha z hz
    have hc : a * z = z * a := (Subgroup.mem_centralizer_iff.mp (hFcent hz)) a ha
    rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    exact hz
  have hMH_le_NF : M ⊓ B.H ≤ Subgroup.normalizer (F : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro h hh z hz
    have hmM : h ∈ M := (Subgroup.mem_inf.mp hh).1
    have hmH : h ∈ B.H := (Subgroup.mem_inf.mp hh).2
    have hzB0 : z ∈ B0 := (Subgroup.mem_inf.mp hz).1
    have hzA : z ∈ A := (Subgroup.mem_inf.mp hz).2
    have hzU : z ∈ B.U := (Subgroup.mem_inf.mp (hB0_le_UM hzB0)).1
    have hzM : z ∈ M := (Subgroup.mem_inf.mp (hB0_le_UM hzB0)).2
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · exact (Subgroup.normal_subgroupOf_iff B.U_le_H).mp B.U_normal z h hzU hmH
        · exact M.mul_mem (M.mul_mem hmM hzM) (M.inv_mem hmM)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        have hs'E : h⁻¹ * s * h ∈ E := by
          simpa using (Subgroup.le_normalizer_iff.mp hME) h⁻¹ (M.inv_mem hmM) s hsE
        have hzC : z ∈ Subgroup.centralizer ((E : Subgroup G) : Set G) := hFcent hz
        have hconj : z * (h⁻¹ * s * h) * z⁻¹ = h⁻¹ * s * h := by
          have hcy := (Subgroup.mem_centralizer_iff.mp hzC) (h⁻¹ * s * h) hs'E
          rw [← hcy]; group
        have hz5 : h * z * h⁻¹ * s * (h * z * h⁻¹)⁻¹ = s := by
          calc h * z * h⁻¹ * s * (h * z * h⁻¹)⁻¹
              = h * (z * (h⁻¹ * s * h) * z⁻¹) * h⁻¹ := by group
            _ = h * (h⁻¹ * s * h) * h⁻¹ := by rw [hconj]
            _ = s := by group
        calc (h * z * h⁻¹) * s
            = ((h * z * h⁻¹) * s * (h * z * h⁻¹)⁻¹) * (h * z * h⁻¹) := by group
          _ = s * (h * z * h⁻¹) := by rw [hz5]
    · exact (Subgroup.le_normalizer_iff.mp (BenderSetup.H_le_normalizer_fittingIn B)) h hmH z hzA
  have hM_le_NF : M ≤ Subgroup.normalizer (F : Set G) :=
    calc M = E ⊔ (M ⊓ B.H) := hsup
      _ ≤ Subgroup.normalizer (F : Set G) := sup_le hE_le_NF hMH_le_NF
  have hNF_ne_top : Subgroup.normalizer (F : Set G) ≠ ⊤ := by
    intro htop
    haveI hFn : F.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases Subgroup.Normal.eq_bot_or_eq_top F with hb | htp
    · exact hFne hb
    · have hHtop : B.H = ⊤ := top_le_iff.mp (htp ▸ hF_le_H)
      have ht_center : B.t ∈ Subgroup.center G := by
        rw [Subgroup.mem_center_iff]
        intro g
        have hg : g ∈ Subgroup.centralizer ({B.t} : Set G) :=
          (le_of_eq hHtop.symm) (Subgroup.mem_top g)
        exact Subgroup.mem_centralizer_singleton_iff.mp hg
      have ht_ne : B.t ≠ 1 := by
        intro h1
        have h2 := B.t_order
        rw [h1, orderOf_one] at h2
        exact absurd h2 (by norm_num)
      have hcenter_ne : Subgroup.center G ≠ ⊥ := by
        intro hbot
        have : B.t ∈ (⊥ : Subgroup G) := hbot ▸ ht_center
        exact ht_ne (Subgroup.mem_bot.mp this)
      haveI : (Subgroup.center G).Normal := inferInstance
      have hcentertop : Subgroup.center G = ⊤ :=
        (Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center G)).resolve_left hcenter_ne
      obtain ⟨a, b, hab⟩ := hbc.nonab
      have hba : b * a = a * b :=
        (Subgroup.mem_center_iff.mp (hcentertop.symm ▸ Subgroup.mem_top a)) b
      exact hab hba.symm
  have hFnorm : Subgroup.normalizer (F : Set G) = M := by
    refine le_antisymm ?_ hM_le_NF
    by_contra hcon
    have hlt : M < Subgroup.normalizer (F : Set G) :=
      lt_of_le_of_ne hM_le_NF (fun hh => hcon (le_of_eq hh.symm))
    exact hNF_ne_top (hcoat.2 _ hlt)
  exact ⟨hFne, hFcent, hFnorm⟩

end Work.CORE4
