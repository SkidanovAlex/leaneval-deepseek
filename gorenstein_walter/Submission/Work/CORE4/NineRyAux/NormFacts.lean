import Mathlib
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2SevenAux
import Submission.Work.CORE4.Case2K1_ne_bot

/-!
# `Work.CORE4.NineRyAux.NormFacts` — the normalizer facts of Bender §4, N5d

This file supplies the five normalizer statements that the N5d leaf (`Work.CORE4.NineRy`)
consumes: for `r ∈ S ⊓ M` (with `M, K, B₀` the objects of Bender §4 and
`F(U) = O₂'(F(C_G(t)))` the Fitting subgroup of `U`),

* `r ∈ N_G(B₀)`, `r ∈ N_G(K)`, `r ∈ N_G(F(U))`,
* `B₀ ≤ N_G(K)` and `B₀ ≤ N_G(F(U))`.

The mathematical content is entirely elementary; the point is that each of the three subgroups
is described in a way that is manifestly invariant under the relevant conjugations:

* `B₀ = (U ⊓ M) ⊓ C_G(S ⊓ E(M))` (Bender §4 (2), `Case2PrePlus`), and `r ∈ S ⊓ M` normalises both
  `U ⊓ M` (because `U ⊴ H` and `r ∈ S ≤ H`) and `S ⊓ E(M)` (because `r ∈ S` normalises `S`, and
  `r ∈ M` normalises the normal subgroup `E(M) ⊴ M`);
* `K = [S ⊓ E(M), U ⊓ M]` (Bender §4 (1), `Case2PrePlus`), so `r` normalises `K` as well;
* `F(U)` is characteristic in `U`, and `r ∈ S ≤ H` with `U ⊴ H`; this is the existing lemma
  `Work.CORE4.BenderSetup.H_le_normalizer_fittingIn`;
* `B₀ ≤ U ⊓ M`, so `B₀` normalises `K` by the `(∓1)`-eigenspace computation of `s` on `U ⊓ M`
  (Bender §4 (2)) and `F(U)` because `B₀ ≤ U ≤ H`.

Everything is proved from `Case2Data`/`Case2PrePlus` alone — no `BenderCtx` and no `C4Inputs`
are used, so the hypotheses of `NormFacts` are exactly the ones needed.
-/

open scoped MatrixGroups

-- `I : C4Inputs` is part of the frozen signature of `NormFacts` but is not used by the proof.
set_option linter.unusedVariables false

namespace Work.CORE4.NineRyAux

open Subgroup

/-! ## General normalizer lemmas -/

/-- **Normalizer of `A ⊓ C_G(K)`.**  If `g` normalises both `A` and `K`, then it normalises
`A ⊓ C_G(K)`: conjugation by `g` restricts to an automorphism of `K`, hence of `C_G(K)`, and it
preserves the intersection with `A`. -/
theorem MemNormInfCentralizer {G : Type} [Group G] {A K : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) : Set G) := by
  have hC : Subgroup.centralizer (K : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.centralizer_le_normalizer (K : Set G)
  have hN : Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (K : Set G) : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hC).mp
      (Subgroup.normal_subgroupOf_centralizer_normalizer (K : Set G))
  exact Subgroup.inf_normalizer_le_normalizer_inf (H := A)
    (K := Subgroup.centralizer (K : Set G)) (Subgroup.mem_inf.mpr ⟨hA, hN hK⟩)

/-- **Normalizer of a commutator.**  If `g` normalises both `A` and `K`, then it normalises
`⁅A, K⁆`: conjugation is an automorphism and commutes with the commutator of subgroups
(`Subgroup.map_commutator`). -/
theorem MemNormCommutator {G : Type} [Group G] {A K : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hK : g ∈ Subgroup.normalizer (K : Set G)) :
    g ∈ Subgroup.normalizer ((⁅A, K⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hK ⊢
  rw [Subgroup.map_commutator, hA, hK]

/-- If `X ≤ N_G(A)` and `Y ≤ N_G(K)`, then `X ⊓ Y ≤ N_G(A ⊓ K)`. -/
theorem inf_le_normalizer_inf {G : Type} [Group G] {A K X Y : Subgroup G}
    (hA : X ≤ Subgroup.normalizer (A : Set G)) (hK : Y ≤ Subgroup.normalizer (K : Set G)) :
    X ⊓ Y ≤ Subgroup.normalizer ((A ⊓ K : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro x hx y hy
  obtain ⟨hxX, hxY⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨hyA, hyK⟩ := Subgroup.mem_inf.mp hy
  exact Subgroup.mem_inf.mpr ⟨(Subgroup.le_normalizer_iff.mp hA) x hxX y hyA,
    (Subgroup.le_normalizer_iff.mp hK) x hxY y hyK⟩

/-- If `A ⊴ H` (as a subgroup of `H`) and `M` is any subgroup, then `H ⊓ M ≤ N_G(A ⊓ M)`. -/
theorem inf_le_normalizer_inf_of_normal_subgroupOf {G : Type} [Group G] {A H M : Subgroup G}
    (hAH : A ≤ H) (hn : (A.subgroupOf H).Normal) :
    H ⊓ M ≤ Subgroup.normalizer ((A ⊓ M : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro x hx y hy
  obtain ⟨hxH, hxM⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨hyA, hyM⟩ := Subgroup.mem_inf.mp hy
  exact Subgroup.mem_inf.mpr ⟨(Subgroup.normal_subgroupOf_iff hAH).mp hn y x hyA hxH,
    M.mul_mem (M.mul_mem hxM hyM) (M.inv_mem hxM)⟩

/-- **Bender §4 (2)**: `B₀ = C_{U ⊓ M}(s)` normalises `K = I_{U ⊓ M}(s)`.

If `b ∈ B₀` commutes with `s` and `x ∈ U ⊓ M` is inverted by `s`, then `b x b⁻¹ ∈ U ⊓ M` and
`s (b x b⁻¹) s⁻¹ = b x⁻¹ b⁻¹ = (b x b⁻¹)⁻¹`, because `s` commutes with `b`.  Hence `K ⊴ U ⊓ M`.

This is `Work.CORE4.Case2KB0_b0_le_normalizer`, restated for `Case2Data` alone (that proof only
uses `K_def`, `B0_def` and the fact that `B₀ ⊆ U ⊓ M`). -/
theorem B0_le_normalizer_K {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    (D : Work.GW2.Case2Data B) : D.B0 ≤ Subgroup.normalizer (D.K : Set G) := by
  -- `D.K_def` is an equality of *sets*, so convert it to a membership test first.
  have hKdef : ∀ y : G, y ∈ D.K ↔ y ∈ Work.GW2.invSet (B.U ⊓ D.M) D.s :=
    fun y => Set.ext_iff.mp D.K_def y
  rw [Subgroup.le_normalizer_iff]
  intro b hb x hx
  obtain ⟨hxA, hxinv⟩ := (hKdef x).mp hx
  have hb' : b ∈ (B.U ⊓ D.M) ⊓ Subgroup.centralizer ({D.s} : Set G) := by
    rw [← D.B0_def]; exact hb
  obtain ⟨hbA, hbC⟩ := Subgroup.mem_inf.mp hb'
  have hbs : D.s * b = b * D.s :=
    (Subgroup.mem_centralizer_iff.mp hbC) D.s (Set.mem_singleton D.s)
  have hbs_inv : b⁻¹ * D.s⁻¹ = D.s⁻¹ * b⁻¹ := by rw [← mul_inv_rev, hbs, mul_inv_rev]
  refine (hKdef (b * x * b⁻¹)).mpr ⟨?_, ?_⟩
  · exact (B.U ⊓ D.M).mul_mem ((B.U ⊓ D.M).mul_mem hbA hxA) ((B.U ⊓ D.M).inv_mem hbA)
  · calc D.s * (b * x * b⁻¹) * D.s⁻¹ = (D.s * b) * x * (b⁻¹ * D.s⁻¹) := by group
      _ = (b * D.s) * x * (D.s⁻¹ * b⁻¹) := by rw [hbs, hbs_inv]
      _ = b * (D.s * x * D.s⁻¹) * b⁻¹ := by group
      _ = b * x⁻¹ * b⁻¹ := by rw [hxinv]
      _ = (b * x * b⁻¹)⁻¹ := by group

/-- **N5d normalizer facts.**  For `r ∈ S ⊓ M`, where `M, K, B₀` are Bender's §4 objects and
`Case2PrePlus` supplies Bender's descriptions (1) and (2) of `K` and `B₀`: `r` normalises `B₀`,
`K` and `F(U)`, and `B₀` normalises `K` and `F(U)`.

The hypothesis `r ∈ S ⊓ M` is used only through the two conjugation facts `r ∈ N_G(S ⊓ E(M))`
(from `r ∈ S`, `E(M) ⊴ M`) and `r ∈ N_G(U ⊓ M)` (from `r ∈ S ≤ H`, `U ⊴ H`). -/
theorem NormFacts (I : Work.GW2.C4Inputs) {G : Type} [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B) (hpp : Work.GW2.Case2PrePlus B C.D)
    (r : G) (hr : r ∈ (B.S : Subgroup G) ⊓ C.D.M) :
    r ∈ Subgroup.normalizer (C.D.B0 : Set G) ∧ r ∈ Subgroup.normalizer (C.D.K : Set G) ∧
    r ∈ Subgroup.normalizer ((Work.GW2.fittingIn B.U : Subgroup G) : Set G) ∧
    C.D.B0 ≤ Subgroup.normalizer (C.D.K : Set G) ∧
    C.D.B0 ≤ Subgroup.normalizer ((Work.GW2.fittingIn B.U : Subgroup G) : Set G) := by
  have hrS : r ∈ (B.S : Subgroup G) := (Subgroup.mem_inf.mp hr).1
  have hrM : r ∈ C.D.M := (Subgroup.mem_inf.mp hr).2
  have hrH : r ∈ B.H := B.S_le_H hrS
  -- `r ∈ S ⊓ M ⊆ H ⊓ M`, and `U ⊓ M ⊴ H ⊓ M` because `U ⊴ H`.
  have hrU : r ∈ Subgroup.normalizer ((B.U ⊓ C.D.M : Subgroup G) : Set G) :=
    inf_le_normalizer_inf_of_normal_subgroupOf B.U_le_H B.U_normal
      (Subgroup.mem_inf.mpr ⟨hrH, hrM⟩)
  -- `r ∈ S ⊓ M` normalises `S` and `E(M) = layerIn M`, hence `S ⊓ E(M)`.
  have hSS : (B.S : Subgroup G) ≤ Subgroup.normalizer ((B.S : Subgroup G) : Set G) :=
    Subgroup.le_normalizer
  have hME : C.D.M ≤ Subgroup.normalizer ((Work.GW2.layerIn C.D.M : Subgroup G) : Set G) :=
    Work.CORE4.layerIn_le_normalizer C.D.M
  have hrSE : r ∈ Subgroup.normalizer
      ((((B.S : Subgroup G) ⊓ Work.GW2.layerIn C.D.M : Subgroup G)) : Set G) :=
    inf_le_normalizer_inf (A := (B.S : Subgroup G)) (X := (B.S : Subgroup G))
      (Y := C.D.M) (K := (Work.GW2.layerIn C.D.M)) hSS hME
      (Subgroup.mem_inf.mpr ⟨hrS, hrM⟩)
  -- (1) `B₀ = (U ⊓ M) ⊓ C_G(S ⊓ E(M))` — Bender §4 (2), `Case2PrePlus`.
  have hrB0 : r ∈ Subgroup.normalizer (C.D.B0 : Set G) := by
    rw [hpp.2.2]
    exact MemNormInfCentralizer hrU hrSE
  -- (2) `K = [S ⊓ E(M), U ⊓ M]` — Bender §4 (1), `Case2PrePlus`.
  have hrK : r ∈ Subgroup.normalizer (C.D.K : Set G) := by
    rw [hpp.2.1]
    exact MemNormCommutator hrSE hrU
  -- (3) `r ∈ S ≤ H` and `H ≤ N_G(F(U))` (`U ⊴ H`, `F(U)` characteristic in `U`).
  have hrFU : r ∈ Subgroup.normalizer ((Work.GW2.fittingIn B.U : Subgroup G) : Set G) :=
    Work.CORE4.BenderSetup.H_le_normalizer_fittingIn B hrH
  -- (4) `B₀ ≤ N_G(K)`: Bender §4 (2).
  have hB0K : C.D.B0 ≤ Subgroup.normalizer (C.D.K : Set G) := B0_le_normalizer_K B C.D
  -- (5) `B₀ ≤ U ⊓ M ≤ U ≤ H ≤ N_G(F(U))`.
  have hB0FU : C.D.B0 ≤ Subgroup.normalizer ((Work.GW2.fittingIn B.U : Subgroup G) : Set G) :=
    le_trans (C.D.B0_le B) (le_trans inf_le_left
      (le_trans B.U_le_H (Work.CORE4.BenderSetup.H_le_normalizer_fittingIn B)))
  exact ⟨hrB0, hrK, hrFU, hB0K, hB0FU⟩

end Work.CORE4.NineRyAux
