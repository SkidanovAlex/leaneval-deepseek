import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.isPGroup_pCoreIn_two
import Submission.Work.CORE2B.oddCore_odd
import Submission.Work.CORE2B.L27cf_helpers
import Submission.Work.CORE2B.fittingIn_U_normalizer
import Submission.OddOrder.GroupTheory.FittingSelfCentralizing

/-!
# CORE2B — Bender 1981, Lemma 2.7: `O₂(M) ≤ C_G(U)` from `F(U) ≤ M`

With `B` Bender's setup (`U = O(H)`, `H = C_G(t)`) and `M ≤ G` a subgroup, the statement proved
here is

  `O₂(M) ≤ C_G(U)`   whenever   `O₂(M) ≤ H`   and   `F(U) ≤ M`.

Mathematically this is the step that the sibling module
`Submission/Work/CORE2B/L27su_two_core_centralizes_U.lean` identifies as the missing input for
Bender's sentence "*As `O₂(M)` centralizes `M ∩ F(U)`, 1.1.iv implies `[O₂(M), U] = 1`*": the
hypothesis `F(U) ≤ M` is exactly what supplies `O₂(M) ≤ C_G(F(U))`.  (In the paper the subgroup
`M` satisfies `M ∩ F(Ĥ) = M ∩ F(U)` because `F(U) ≤ F(Ĥ)`, so `F(U) ≤ M` is Bender's
`M ∩ F(U)`.)

## The argument

Write `P := O₂(M)` and `F := F(U)` (the Fitting subgroup of `↥U`).

* `P` is a `2`-group and `F` has odd order (as `F ≤ U`, and `U = O(H)` is odd).
* `P ◁ M` (`O₂(M)` is the image of the normal subgroup `O₂(↥M)`), so `M ≤ N_G(P)`;
  with `F ≤ M` this gives `⁅P, F⁆ ≤ P` (Bender 1.1(iv) notation `[P, K₀] ≤ P`).
* `U ◁ H` (as `U = O(H)`), so `H ≤ N_G(U)`, and `F = F(U)` is characteristic in `U`, so
  `N_G(U) ≤ N_G(F)`; since `P ≤ H` we get `⁅P, F⁆ ≤ F`.
* Hence `⁅P, F⁆ ≤ P ⊓ F = ⊥` (`P` is a `2`-group, `F` has odd order), i.e. `P ≤ C_G(F)`.
* Finally `U ⊓ C_U(F(U)) ≤ F(U)`: `U` has odd order, hence is solvable by Feit–Thompson, and
  P. Hall's theorem `C_G(F(G)) ≤ F(G)` (`OddOrder.GroupTheory.centralizer_fitting_le_fitting`)
  applies.
* Bender 1.1(iv) (`T.c11iv`) with `K = U`, `K₀ = F(U)` now yields `P ≤ C_G(U)`.

Note that the whole argument is local: `BenderCtx` enters only through the Feit–Thompson
hypothesis (solvability of the odd-order group `↥U`), and the toolkit `T` only for the
coprime-action input `1.1.iv`.
-/

open scoped MatrixGroups commutatorElement

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.CORE2B

open Subgroup

/-! ## 1. `U = O(H)` has odd order -/

/-- `U = O(C_G(t))` has odd order (`U` is the largest normal odd-order subgroup of `H`). -/
theorem L27su_odd_card_U_aux {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G) :
    Odd (Nat.card ↥B.U) := by
  rw [Work.GW2.BenderSetup.U, Work.GW2.oddCoreIn,
    Subgroup.card_map_of_injective B.H.subtype_injective]
  exact oddCore_odd (G := ↥B.H)

/-! ## 2. The normalizer of the image of a normal subgroup -/

/-- If `N ⊴ ↥K` then `K` normalizes the image of `N` in the ambient group along `K.subtype`,
i.e. `↥K ≤ N_G(N.map K.subtype)`. -/
theorem L27su_le_normalizer_map_subtype {G : Type} [Group G] (K : Subgroup G)
    (N : Subgroup ↥K) (hN : N.Normal) :
    K ≤ Subgroup.normalizer ((N.map K.subtype : Subgroup G) : Set G) := by
  have hle : (N.map K.subtype : Subgroup G) ≤ K := Subgroup.map_subtype_le N
  have hsub : ((N.map K.subtype : Subgroup G).subgroupOf K).Normal := by
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
    exact hN
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hsub

/-! ## 3. P. Hall: `C_U(F(U)) ≤ F(U)` for the odd group `U` -/

/-- **P. Hall's self-centralizing theorem for `U`**: `U ⊓ C_G(F(U)) ≤ F(U)`.

`U` has odd order, hence is solvable by Feit–Thompson (`hFT`), and for a finite solvable group
`G` the Fitting subgroup self-centralizes
(`OddOrder.GroupTheory.centralizer_fitting_le_fitting`).  The two Fitting subgroups agree by
`L27cf_fitting_eq_isaacsFitting`, and `F(U) ≤ G` is the image of the Fitting subgroup of `↥U`
along `U.subtype`. -/
theorem L27su_U_inf_centralizer_fittingIn_le {G : Type} [Group G] [Finite G]
    (T : Work.GW2.LocalToolkit) (hFT : Work.GW2.FeitThompsonProp)
    (hCtx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) :
    B.U ⊓ Subgroup.centralizer ((Work.GW2.fittingIn B.U : Subgroup G) : Set G) ≤
      Work.GW2.fittingIn B.U := by
  have hodd : Odd (Nat.card ↥B.U) := L27su_odd_card_U_aux B
  haveI : Group.IsSolvable ↥B.U := hFT ↥B.U hodd
  have hfit : Work.GW2.fitting ↥B.U = OddOrder.Isaacs.Ch01.fitting ↥B.U :=
    L27cf_fitting_eq_isaacsFitting
  rintro x ⟨hxU, hxc⟩
  -- `x`, viewed in `↥U`, centralizes the Fitting subgroup of `↥U`
  have hmem : (⟨x, hxU⟩ : ↥B.U) ∈
      Subgroup.centralizer
        ((OddOrder.Isaacs.Ch01.fitting ↥B.U : Subgroup ↥B.U) : Set ↥B.U) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    refine Subtype.ext ?_
    refine Subgroup.mem_centralizer_iff.mp hxc (y : G) ?_
    have hy' : (y : G) ∈ (Work.GW2.fitting ↥B.U).map B.U.subtype := by
      rw [hfit]
      exact Subgroup.mem_map_of_mem B.U.subtype hy
    exact hy'
  -- P. Hall
  have hx' : (⟨x, hxU⟩ : ↥B.U) ∈ Work.GW2.fitting ↥B.U := by
    rw [hfit]
    exact OddOrder.GroupTheory.centralizer_fitting_le_fitting hmem
  exact Subgroup.mem_map_of_mem B.U.subtype hx'

/-! ## 4. The target -/

theorem L27su_pCore_le_centralizer_U :
    ∀ (T : Work.GW2.LocalToolkit) (G : Type) [Group G] [Finite G],
      Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (M : Subgroup G),
        Work.GW2.pCoreIn 2 M ≤ B.H →
        Work.GW2.fittingIn B.U ≤ M →
        Work.GW2.pCoreIn 2 M ≤ Subgroup.centralizer (B.U : Set G) := by
  intro T G _ _ hFT hCtx B M hPH hFM
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Subgroup G := Work.GW2.pCoreIn 2 M
  let F : Subgroup G := Work.GW2.fittingIn B.U
  -- `P = O₂(M)` is a `2`-group, and `F = F(U)` has odd order
  have hP2 : IsPGroup 2 P := isPGroup_pCoreIn_two M
  have hFU : F ≤ B.U := Subgroup.map_subtype_le _
  have hFodd : Odd (Nat.card F) :=
    Odd.of_dvd_nat (L27su_odd_card_U_aux B) (Subgroup.card_dvd_of_le hFU)
  -- `P ⊓ F = ⊥`
  have hPFbot : P ⊓ F = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxP, hxF⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP2
    have hdvd : orderOf x ∣ 2 ^ n := by
      rw [← hn]
      exact Subgroup.orderOf_dvd_natCard P hxP
    have hodd : Odd (orderOf x) :=
      hFodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard F hxF)
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp
      (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hodd)) hdvd))
  -- normalizers: `M ≤ N_G(P)`, `H ≤ N_G(U)`, `H ≤ N_G(F)`
  have hMnormP : M ≤ Subgroup.normalizer (P : Set G) :=
    L27su_le_normalizer_map_subtype M (Work.GW2.pCore 2 ↥M) (Work.GW2.pCore_normal 2 ↥M)
  have hHnormU : B.H ≤ Subgroup.normalizer (B.U : Set G) :=
    L27su_le_normalizer_map_subtype B.H (Work.GW2.oddCore ↥B.H) (Work.GW2.oddCore_normal ↥B.H)
  have hHnormF : B.H ≤ Subgroup.normalizer (F : Set G) :=
    le_normalizer_fittingIn_of_le_normalizer_local hHnormU
  have hPnormF : P ≤ Subgroup.normalizer (F : Set G) := hPH.trans hHnormF
  have hFnormP : F ≤ Subgroup.normalizer (P : Set G) := hFM.trans hMnormP
  -- hence `⁅P, F⁆ ≤ P ⊓ F = ⊥`, i.e. `P ≤ C_G(F)`
  have hPcentF : P ≤ Subgroup.centralizer (F : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact le_bot_iff.mp ((le_inf
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hFnormP)
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hPnormF)).trans_eq hPFbot)
  -- Bender 1.1(iv) with `K = U`, `K₀ = F(U)`
  have hUCF : B.U ⊓ Subgroup.centralizer (F : Set G) ≤ F :=
    L27su_U_inf_centralizer_fittingIn_le T hFT hCtx B
  have hPnormU : P ≤ Subgroup.normalizer (B.U : Set G) := hPH.trans hHnormU
  have hcopU : Nat.Coprime 2 (Nat.card ↥B.U) :=
    (Nat.coprime_two_right.mpr (L27su_odd_card_U_aux B)).symm
  have hFUnorm : (F.subgroupOf B.U).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFU).mpr
      (le_normalizer_fittingIn_of_le_normalizer_local (K := B.U) (C := B.U) Subgroup.le_normalizer)
  exact T.c11iv G 2 P B.U F hP2 hcopU hPnormU hFU hFUnorm hPcentF hUCF

end Work.CORE2B
