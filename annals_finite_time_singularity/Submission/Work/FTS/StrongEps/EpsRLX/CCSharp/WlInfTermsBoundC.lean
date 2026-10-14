import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.EpsRLX.LGTDiffClassC
import Submission.Work.FTS.StrongEps.H5.HAtoms5
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.N_b4_s =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `N_aux.N_b4_s` — the ten star (`s`) pieces of the level-`4` pricing of `blkN`

This file prices the ten odd-indexed pieces of the twenty-piece decomposition
`Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k` (`k ∈ {1,3,5,7,9,11,13,15,17,19}`) at level `4`,
with a constant `K` independent of `α ∈ (0,1]`.

These ten pieces are exactly those in which the star (`Φ_s`) coefficients, the fixed `F_*`-atoms,
the `FK`-coefficients and the angular profile `-sin²θ` occur:

| `k` | piece | coefficient (α-small) | factor |
|---|---|---|---|
| 1  | `2·(F_*·Rop Φ̃_g)`      | `F_*` (`WlInf ≤ Cα`)     | `Rop Φ̃_g` (`Xn ≤ Cα²`) |
| 3  | `2·(Rs·φF_*)`           | `Rs` (`WlInf ≤ Cα`)      | `φF_*` (`Xn ≤ C`) |
| 5  | `-2·(D_θF_*·Uc)`        | `D_θF_*` (`WlInf ≤ Cα²`) | `Uc` (`Xn ≤ Cα²`) |
| 7  | `-2·(Us·φD_θF_*)`       | `Us` (`WlInf ≤ Cα`)      | `φD_θF_*` (`Xn ≤ C`) |
| 9  | `-2α·(D_zF_*·Vc)`       | `D_zF_*` (`WlInf ≤ Cα`)  | `Vc` (`Xn ≤ Cα²`) |
| 11 | `-2α·(Vs·φD_zF_*)`      | `Vs` (`WlInf ≤ Cα`)      | `φD_zF_*` (`Xn ≤ C`) |
| 13 | `-½·(D_θF_*·FK w)`      | `D_θF_*` (`WlInf ≤ Cα²`) | `FK w` (`Xn ≤ Cα²`) |
| 15 | `-½·(FK(F_*)·D_θF_*)`   | fixed atom (`Xn ≤ C`)    | const |
| 17 | `-sin²θ·(F_*·FK w)`     | `F_*`                    | `FK w` |
| 19 | `-sin²θ·(FK(F_*)·F_*)`  | fixed atom               | const |

Every coefficient is `α`-small (`WlInf α 4 · ≤ bF·α^s` with `s ≥ 1`) or a plain constant, so the
`α^{-1/2}` of the `𝒲^{4,∞}×ℋ⁴` product rule `NB4Ctx.hPW` is absorbed (`mulW_absorb`); the two
`-sin²θ`-pieces are finished with `NB4Ctx.hSinMul`, and piece 15 is a pure scalar multiple.  All
resulting constants are products of at most four factors `C` (`C ≥ 1`), so **`K := 8·C⁴ + 1`**
works for the whole batch.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## Arithmetic helpers for the single constant `8·C⁴ + 1` (`C ≥ 1`) -/

private lemma two_cube_le (C : ℝ) (hC : 1 ≤ C) : 2 * C * C * C ≤ 8 * C ^ 4 + 1 := by
  have h0 : (0 : ℝ) ≤ C := le_trans zero_le_one hC
  have h3 : C ^ 3 ≤ C ^ 4 := by
    calc C ^ 3 = C ^ 3 * 1 := (mul_one _).symm
      _ ≤ C ^ 3 * C := mul_le_mul_of_nonneg_left hC (pow_nonneg h0 3)
      _ = C ^ 4 := by ring
  have h4 : (0 : ℝ) ≤ C ^ 4 := pow_nonneg h0 4
  nlinarith [h3, h4]

private lemma half_cube_le (C : ℝ) (hC : 1 ≤ C) : (1 / 2) * C * C * C ≤ 8 * C ^ 4 + 1 := by
  have h0 : (0 : ℝ) ≤ C := le_trans zero_le_one hC
  have h3 : C ^ 3 ≤ C ^ 4 := by
    calc C ^ 3 = C ^ 3 * 1 := (mul_one _).symm
      _ ≤ C ^ 3 * C := mul_le_mul_of_nonneg_left hC (pow_nonneg h0 3)
      _ = C ^ 4 := by ring
  have h4 : (0 : ℝ) ≤ C ^ 4 := pow_nonneg h0 4
  nlinarith [h3, h4]

private lemma half_le (C : ℝ) (hC : 1 ≤ C) : (1 / 2) * C ≤ 8 * C ^ 4 + 1 := by
  have h0 : (0 : ℝ) ≤ C := le_trans zero_le_one hC
  have h4 : C ≤ C ^ 4 := by
    have h1 : (1 : ℝ) ≤ C ^ 3 := one_le_pow₀ hC
    calc C = C * 1 := (mul_one C).symm
      _ ≤ C * C ^ 3 := mul_le_mul_of_nonneg_left h1 h0
      _ = C ^ 4 := by ring
  have h5 : (0 : ℝ) ≤ C ^ 4 := pow_nonneg h0 4
  nlinarith [h4, h0, h5]

private lemma fourth_le (C : ℝ) : C * C * C * C ≤ 8 * C ^ 4 + 1 := by
  nlinarith [sq_nonneg (C ^ 2)]

private lemma square_le (C : ℝ) (hC : 1 ≤ C) : C * C ≤ 8 * C ^ 4 + 1 := by
  have h0 : (0 : ℝ) ≤ C := le_trans zero_le_one hC
  have h2 : (1 : ℝ) ≤ C ^ 2 := one_le_pow₀ hC
  have h5 : (0 : ℝ) ≤ C ^ 4 := pow_nonneg h0 4
  have h3 : C ^ 2 ≤ C ^ 4 := by
    calc C ^ 2 = C ^ 2 * 1 := (mul_one _).symm
      _ ≤ C ^ 2 * C ^ 2 := mul_le_mul_of_nonneg_left h2 (sq_nonneg C)
      _ = C ^ 4 := by ring
  nlinarith [h3, h5]

private lemma alpha_two_cube_le (α C : ℝ) (hα1 : α ≤ 1) (hC : 1 ≤ C) :
    2 * α * C * C * C ≤ 8 * C ^ 4 + 1 := by
  have h0 : (0 : ℝ) ≤ C := le_trans zero_le_one hC
  have h : (0 : ℝ) ≤ C ^ 3 * (1 - α) := mul_nonneg (pow_nonneg h0 3) (by linarith)
  nlinarith [h, two_cube_le C hC]

/-- **The ten star pieces of the `N`-block at level `4`, with an `α`-free constant.** -/
theorem N_b4_s (C C₀ Ce Cs : ℝ) : ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ (Φs w Φg : ℝ → ℝ → ℝ),
    Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.NB4Ctx C C₀ Ce Cs α Φs w Φg →
    ∀ k ∈ ({1, 3, 5, 7, 9, 11, 13, 15, 17, 19} : Finset ℕ),
      Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k)
        ≤ K * (1 + Work.Spaces.HkNorm α 5 w) := by
  refine ⟨8 * C ^ 4 + 1, by positivity, ?_⟩
  intro α hαmem Φs w Φg ctx k hk
  have hα0 : 0 < α := hαmem.1
  have hα1 : α ≤ 1 := hαmem.2
  have hCpos : (0 : ℝ) < C := ctx.hCpos
  have hC1 : (1 : ℝ) ≤ C := ctx.hCone
  have hKnn : (0 : ℝ) ≤ 8 * C ^ 4 + 1 := by positivity
  -- the packaging combinator: `HkMem` plus a bound `≤ B`, `B ≤ 8C⁴+1`, give the goal shape
  have pack : ∀ {j : ℕ} {B : ℝ},
      Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg j) →
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg j) ≤ B →
      B ≤ 8 * C ^ 4 + 1 →
      Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg j) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg j)
        ≤ (8 * C ^ 4 + 1) * (1 + Work.Spaces.HkNorm α 5 w) :=
    fun hm hb hBK => ⟨hm, le_trans hb (le_mul_G (K := 8 * C ^ 4 + 1) hBK hKnn)⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- ## piece 1 : `2·(F_*·Rop Φ̃_g)`
    have hbF : Work.Spaces.WlInf α 4 (Work.Construction.Fstar α) ≤ C * α ^ 1 := by
      simpa only [pow_one] using ctx.FWW
    have hbG : Work.FTS.Nonlin.Xn α
        (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg)) ≤ C :=
      le_trans ctx.RX (mul_pow_le_self hα0 hα1 hCpos.le 2)
    have h := mulW_absorb hα0 hα1 hCpos ctx.hPW (c := 2) (s := 1) (by norm_num)
      hCpos.le hCpos.le ctx.FWsm ctx.FWWm ctx.Rqo hbF hbG
    rw [show |(2 : ℝ)| = 2 by norm_num] at h
    exact pack (by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.1)
      (by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.2) (two_cube_le C hC1)
  · -- ## piece 3 : `2·(Rs·φF_*)`
    have h := mulW_absorb hα0 hα1 hCpos ctx.hPW (c := 2) (s := 1) (by norm_num)
      hCpos.le hCpos.le ctx.Rssm ctx.RsWm ctx.phiFsqo
      (by simpa only [pow_one] using ctx.RsW) ctx.phiFsX
    rw [show |(2 : ℝ)| = 2 by norm_num] at h
    exact pack (by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.1)
      (by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.2) (two_cube_le C hC1)
  · -- ## piece 5 : `-2·(D_θF_*·Uc)`
    have hbG : Work.FTS.Nonlin.Xn α (fun z θ =>
        Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α w Φg) z θ
          / Work.Construction.s2 θ) ≤ C :=
      le_trans ctx.UX (mul_pow_le_self hα0 hα1 hCpos.le 2)
    have h := mulW_absorb hα0 hα1 hCpos ctx.hPW (c := -2) (s := 2) (by norm_num)
      hCpos.le hCpos.le ctx.DthFssm ctx.DthFsWm ctx.Uqo ctx.DthFsW hbG
    rw [show |(-2 : ℝ)| = 2 by norm_num] at h
    exact pack (by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.1)
      (by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.2) (two_cube_le C hC1)
  · -- ## piece 7 : `-2·(Us·φD_θF_*)`
    have h := mulW_absorb hα0 hα1 hCpos ctx.hPW (c := -2) (s := 1) (by norm_num)
      hCpos.le hCpos.le ctx.Ussm ctx.UsWm ctx.phiDthFsqo
      (by simpa only [pow_one] using ctx.UsW) ctx.phiDthFsX
    rw [show |(-2 : ℝ)| = 2 by norm_num] at h
    exact pack (by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.1)
      (by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.2) (two_cube_le C hC1)
  · -- ## piece 9 : `-2α·(D_zF_*·Vc)`
    have hbG : Work.FTS.Nonlin.Xn α
        (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg)) ≤ C :=
      le_trans ctx.VX (mul_pow_le_self hα0 hα1 hCpos.le 2)
    have h := mulW_absorb hα0 hα1 hCpos ctx.hPW (c := -(2 * α)) (s := 1) (by norm_num)
      hCpos.le hCpos.le ctx.DzFssm ctx.DzFsWm ctx.Vqo
      (by simpa only [pow_one] using ctx.DzFsW) hbG
    rw [abs_neg, abs_of_pos (by linarith : (0 : ℝ) < 2 * α)] at h
    exact pack (by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.1)
      (by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.2)
      (alpha_two_cube_le α C hα1 hC1)
  · -- ## piece 11 : `-2α·(Vs·φD_zF_*)`
    have h := mulW_absorb hα0 hα1 hCpos ctx.hPW (c := -(2 * α)) (s := 1) (by norm_num)
      hCpos.le hCpos.le ctx.Vssm ctx.VsWm ctx.phiDzFsqo
      (by simpa only [pow_one] using ctx.VsW) ctx.phiDzFsX
    rw [abs_neg, abs_of_pos (by linarith : (0 : ℝ) < 2 * α)] at h
    exact pack (by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.1)
      (by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.2)
      (alpha_two_cube_le α C hα1 hC1)
  · -- ## piece 13 : `-½·(D_θF_*·FK w)`
    have hbG : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.FK w z) ≤ C :=
      le_trans ctx.FKwX (mul_pow_le_self hα0 hα1 hCpos.le 2)
    have h := mulW_absorb hα0 hα1 hCpos ctx.hPW (c := -(1 / 2)) (s := 2) (by norm_num)
      hCpos.le hCpos.le ctx.DthFssm ctx.DthFsWm ctx.FKwqo ctx.DthFsW hbG
    rw [show |(-(1 / 2) : ℝ)| = 1 / 2 by norm_num] at h
    exact pack (by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.1)
      (by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.2) (half_cube_le C hC1)
  · -- ## piece 15 : `-½·(FK(F_*)·D_θF_*)` (a fixed atom, pure scalar)
    have hmem : Work.Spaces.HkMem α 4 (fun z θ =>
        Work.Construction.FK (Work.Construction.Fstar α) z
          * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) := ctx.prodFKDthFSqo.2
    have hXn : Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 15)
        = (1 / 2) * Work.FTS.Nonlin.Xn α (fun z θ =>
            Work.Construction.FK (Work.Construction.Fstar α) z
              * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) := by
      simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]
      rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul]
      norm_num
    refine ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using
      Work.FTS.LocData.HkMem_const_mul α 4 (-(1 / 2)) hmem, ?_⟩
    rw [hXn]
    exact le_trans (mul_le_mul_of_nonneg_left ctx.prodFKDthFSX (by norm_num))
      (le_mul_G (K := 8 * C ^ 4 + 1) (half_le C hC1) hKnn)
  · -- ## piece 17 : `-sin²θ·(F_*·FK w)`
    have hbG : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.FK w z) ≤ C :=
      le_trans ctx.FKwX (mul_pow_le_self hα0 hα1 hCpos.le 2)
    have hinner := mulW_absorb hα0 hα1 hCpos ctx.hPW (c := 1) (s := 1) (by norm_num)
      hCpos.le hCpos.le ctx.FWsm ctx.FWWm ctx.FKwqo
      (by simpa only [pow_one] using ctx.FWW) hbG
    have hXin : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.Fstar α z θ
        * Work.Construction.FK w z) ≤ C * C * C := by
      have h := hinner.2
      rw [show |(1 : ℝ)| = 1 by norm_num] at h
      simpa only [one_mul] using h
    have hmem : Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.Fstar α z θ
        * Work.Construction.FK w z) := by simpa only [one_mul] using hinner.1
    have hsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.Fstar α z θ
        * Work.Construction.FK w z) :=
      Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl ctx.FWsm ctx.FKwqo.1
    have h := ctx.hSinMul (fun z θ => Work.Construction.Fstar α z θ
      * Work.Construction.FK w z) hsm ⟨hsm, hmem⟩
    have h2' : Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 17)
        ≤ C * Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.Fstar α z θ
            * Work.Construction.FK w z) := by
      simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.2
    refine ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.1, ?_⟩
    refine le_trans ?_ (le_mul_G (K := 8 * C ^ 4 + 1) (fourth_le C) hKnn)
    calc Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 17)
        ≤ C * Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.Fstar α z θ
            * Work.Construction.FK w z) := h2'
      _ ≤ C * (C * C * C) := mul_le_mul_of_nonneg_left hXin hCpos.le
      _ = C * C * C * C := by ring
  · -- ## piece 19 : `-sin²θ·(FK(F_*)·F_*)`
    have hmem : Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.FK
        (Work.Construction.Fstar α) z * Work.Construction.Fstar α z θ) := ctx.prodFKFSqo.2
    have hsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.FK
        (Work.Construction.Fstar α) z * Work.Construction.Fstar α z θ) :=
      Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl ctx.FKFSsm ctx.FWsm
    have h := ctx.hSinMul (fun z θ => Work.Construction.FK (Work.Construction.Fstar α) z
      * Work.Construction.Fstar α z θ) hsm ⟨hsm, hmem⟩
    have h2' : Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 19)
        ≤ C * Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.FK
            (Work.Construction.Fstar α) z * Work.Construction.Fstar α z θ) := by
      simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.2
    refine ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk] using h.1, ?_⟩
    refine le_trans ?_ (le_mul_G (K := 8 * C ^ 4 + 1) (square_le C hC1) hKnn)
    calc Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 19)
        ≤ C * Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.FK
            (Work.Construction.Fstar α) z * Work.Construction.Fstar α z θ) := h2'
      _ ≤ C * C := mul_le_mul_of_nonneg_left ctx.prodFKFSX hCpos.le

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.CCSharp.WlInfTermsBoundC =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsRLX.CCSharp

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

-- `CCSharp/WlInfTermsBoundC` — the ten `𝒲^{4,∞}`-priced term bounds at the `ClassC` level.
--
-- This is the `ClassC`-port of `Work.FTS.GalFields.RHS.SharpAux.WlInfTermsBound`: the ten
-- monomials `TRA`, `TUA`, `TVA`, `TRC`, `TUC`, `TVC`, `TDA`, `TDC`, `TEA`, `TEC` of the sharp
-- telescoping, each of the shape `a·(f·u)` with `f` a `𝒲^{4,∞}`-coefficient and `u` an honest
-- `ℋ⁴`-function, are `SmoothOpen` + `HkMem α 4` and priced by `K·(1+|W₁|_{ℋ⁵}+|W₂|_{ℋ⁵})·|W₁-W₂|_{ℋ⁵}`
-- for a single constant `K`, with the *difference* datum `h := W₁ - W₂` produced from
-- `ClassC α W₁`, `ClassC α W₂` (`CCSharp.sub_classC`) rather than from `GalClass α h`.
--
-- The port follows the substitution list recorded in `CCSharp/Base`: every honest atom that the
-- original reads off `GalClass α h` is read off `ClassC α h` (via `CCSharp.cSmooth`, `cMem`,
-- `cHQo`), the elliptic outputs come from `hEll h (sub_classC hW₁ hW₂)` instead of `hell h hh`,
-- and the `FK`-atom comes from `ClassCRHS.smoothOpen_FKw_of_classC` (the `ClassC`-strength
-- replacement for `RHS.smoothOpen_FK_of_pkg_gal`).
theorem WlInfTermsBoundC {α α₂ Ci Ce Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u))
    (hα : 0 < α) (hαα₂ : α ≤ α₂) :
    ∃ K : ℝ, 0 < K ∧ ∀ {W₁ W₂ : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α W₁ → Work.FTS.ClassC.ClassC α W₂ → α ≤ 1 →
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TRA α Φs (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TRA α Φs (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TRA α Φs (fun z θ => W₁ z θ - W₂ z θ))
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TUA α Φs (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TUA α Φs (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TUA α Φs (fun z θ => W₁ z θ - W₂ z θ))
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TVA α Φs (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TVA α Φs (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TVA α Φs (fun z θ => W₁ z θ - W₂ z θ))
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TRC α E (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TRC α E (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TRC α E (fun z θ => W₁ z θ - W₂ z θ))
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TUC α E (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TUC α E (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TUC α E (fun z θ => W₁ z θ - W₂ z θ))
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TVC α E (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TVC α E (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TVC α E (fun z θ => W₁ z θ - W₂ z θ))
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TDA α (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TDA α (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TDA α (fun z θ => W₁ z θ - W₂ z θ))
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TDC α (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TDC α (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TDC α (fun z θ => W₁ z θ - W₂ z θ))
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TEA α (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TEA α (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TEA α (fun z θ => W₁ z θ - W₂ z θ))
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) ∧
      (Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.TEC α (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Sharp.TEC α (fun z θ => W₁ z θ - W₂ z θ)) ∧
        Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TEC α (fun z θ => W₁ z θ - W₂ z θ))
          ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂) * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ))
      := by
  -- the fixed constants of the chapter
  obtain ⟨Cφ, hCφpos, hCφ⟩ := Work.FTS.NonlinRows.NRow10aux.mul_phi_Hk
  obtain ⟨B, hBpos, hBSI, hBbnd, hBdth⟩ :=
    Work.FTS.Nonlinear.Pieces.RNP.RNP24.angProfile_sinSq
  obtain ⟨_Cfs, _hCfs, hFstarW⟩ := Work.FTS.Nonlin.Fstar_W
  obtain ⟨_Cdth, _hCdth, hDthW⟩ := Work.FTS.Nonlin.DthFstar_W
  obtain ⟨_Cdz, _hCdz, hDzW⟩ := Work.FTS.Nonlin.DzFstar_W
  -- the ten amplitude expressions
  set A1 : ℝ := |(2 : ℝ)| * (Ci * α ^ (-(1 / 2 : ℝ))
    * Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.StarH α Φs) * Cφ) with hA1
  set A2 : ℝ := |(-2 : ℝ)| * (Ci * α ^ (-(1 / 2 : ℝ))
    * Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.UsPhi α Φs) * 1) with hA2
  set A3 : ℝ := |(-(2 * α))| * (Ci * α ^ (-(1 / 2 : ℝ))
    * Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.Vstar α Φs) * 1) with hA3
  set A4 : ℝ := |(2 : ℝ)| * (Ci * α ^ (-(1 / 2 : ℝ))
    * Work.Spaces.WlInf α 4 (Work.Construction.Fstar α) * max Ce 0) with hA4
  set A5 : ℝ := |(-2 : ℝ)| * (Ci * α ^ (-(1 / 2 : ℝ))
    * Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.DthFstar α) * max Ce 0) with hA5
  set A6 : ℝ := |(-(2 * α))| * (Ci * α ^ (-(1 / 2 : ℝ))
    * Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.DzFstar α) * max Ce 0) with hA6
  set A7 : ℝ := |(-(1 / 2 : ℝ))| * (Ci * α ^ (-(1 / 2 : ℝ))
    * Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.Fkstar α) * 1) with hA7
  set A8 : ℝ := |(-(1 / 2 : ℝ))| * (Ci * α ^ (-(1 / 2 : ℝ))
    * Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.DthFstar α) * Ci) with hA8
  set A9 : ℝ := |(-1 : ℝ)| * (Ci * α ^ (-(1 / 2 : ℝ))
    * Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.Fkstar α) * (B * Ci * 1)) with hA9
  set A10 : ℝ := |(-1 : ℝ)| * (Ci * α ^ (-(1 / 2 : ℝ))
    * Work.Spaces.WlInf α 4 (Work.Construction.Fstar α) * (B * Ci * Ci)) with hA10
  set K : ℝ := 1 + (|A1| + |A2| + |A3| + |A4| + |A5| + |A6| + |A7| + |A8| + |A9| + |A10|)
    with hK
  have hKpos : 0 < K := by
    rw [hK]
    linarith [abs_nonneg A1, abs_nonneg A2, abs_nonneg A3, abs_nonneg A4, abs_nonneg A5,
      abs_nonneg A6, abs_nonneg A7, abs_nonneg A8, abs_nonneg A9, abs_nonneg A10]
  have hA1K : A1 ≤ K := by
    rw [hK]
    linarith [le_abs_self A1, abs_nonneg A2, abs_nonneg A3, abs_nonneg A4, abs_nonneg A5,
      abs_nonneg A6, abs_nonneg A7, abs_nonneg A8, abs_nonneg A9, abs_nonneg A10]
  have hA2K : A2 ≤ K := by
    rw [hK]
    linarith [le_abs_self A2, abs_nonneg A1, abs_nonneg A3, abs_nonneg A4, abs_nonneg A5,
      abs_nonneg A6, abs_nonneg A7, abs_nonneg A8, abs_nonneg A9, abs_nonneg A10]
  have hA3K : A3 ≤ K := by
    rw [hK]
    linarith [le_abs_self A3, abs_nonneg A1, abs_nonneg A2, abs_nonneg A4, abs_nonneg A5,
      abs_nonneg A6, abs_nonneg A7, abs_nonneg A8, abs_nonneg A9, abs_nonneg A10]
  have hA4K : A4 ≤ K := by
    rw [hK]
    linarith [le_abs_self A4, abs_nonneg A1, abs_nonneg A2, abs_nonneg A3, abs_nonneg A5,
      abs_nonneg A6, abs_nonneg A7, abs_nonneg A8, abs_nonneg A9, abs_nonneg A10]
  have hA5K : A5 ≤ K := by
    rw [hK]
    linarith [le_abs_self A5, abs_nonneg A1, abs_nonneg A2, abs_nonneg A3, abs_nonneg A4,
      abs_nonneg A6, abs_nonneg A7, abs_nonneg A8, abs_nonneg A9, abs_nonneg A10]
  have hA6K : A6 ≤ K := by
    rw [hK]
    linarith [le_abs_self A6, abs_nonneg A1, abs_nonneg A2, abs_nonneg A3, abs_nonneg A4,
      abs_nonneg A5, abs_nonneg A7, abs_nonneg A8, abs_nonneg A9, abs_nonneg A10]
  have hA7K : A7 ≤ K := by
    rw [hK]
    linarith [le_abs_self A7, abs_nonneg A1, abs_nonneg A2, abs_nonneg A3, abs_nonneg A4,
      abs_nonneg A5, abs_nonneg A6, abs_nonneg A8, abs_nonneg A9, abs_nonneg A10]
  have hA8K : A8 ≤ K := by
    rw [hK]
    linarith [le_abs_self A8, abs_nonneg A1, abs_nonneg A2, abs_nonneg A3, abs_nonneg A4,
      abs_nonneg A5, abs_nonneg A6, abs_nonneg A7, abs_nonneg A9, abs_nonneg A10]
  have hA9K : A9 ≤ K := by
    rw [hK]
    linarith [le_abs_self A9, abs_nonneg A1, abs_nonneg A2, abs_nonneg A3, abs_nonneg A4,
      abs_nonneg A5, abs_nonneg A6, abs_nonneg A7, abs_nonneg A8, abs_nonneg A10]
  have hA10K : A10 ≤ K := by
    rw [hK]
    linarith [le_abs_self A10, abs_nonneg A1, abs_nonneg A2, abs_nonneg A3, abs_nonneg A4,
      abs_nonneg A5, abs_nonneg A6, abs_nonneg A7, abs_nonneg A8, abs_nonneg A9]
  refine ⟨K, hKpos, ?_⟩
  intro W₁ W₂ hW₁ hW₂ hα1
  -- the difference datum
  set h : Fn := fun z θ => W₁ z θ - W₂ z θ with hh
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  have hY : 0 ≤ Work.FTS.GalFields.Xn5 α W₁ := Real.sqrt_nonneg _
  have hY' : 0 ≤ Work.FTS.GalFields.Xn5 α W₂ := Real.sqrt_nonneg _
  have hYh : 0 ≤ Work.FTS.GalFields.Xn5 α h := Real.sqrt_nonneg _
  -- the `ClassC` facts about the difference datum `h`
  have hhC : Work.FTS.ClassC.ClassC α h := sub_classC hW₁ hW₂
  have hhl12 : Work.Construction.L12 h 0 = 0 := sub_L12_zero hW₁ hW₂
  have hPhS : Work.FTS.EllipticEst.SmoothOpen h := cSmooth hhC
  have hPh5 : Work.Spaces.HkMem α 5 h := cMem hhC (by norm_num)
  have hPhQ : Work.FTS.VocabO.HQo α 4 h := cHQo hhC
  have hXh : Work.FTS.Nonlin.Xn α h ≤ Work.FTS.GalFields.Xn5 α h :=
    Work.FTS.GalFields.RHS.SharpAux.Xn_le_Xn5_aux hPh5
  have hXh0 : 0 ≤ Work.FTS.Nonlin.Xn α h := Real.sqrt_nonneg _
  -- ### the coefficient atoms
  have hStarH_sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.StarH α Φs) :=
    Work.FTS.NonlinRows.NRow10aux.starH_smoothOpen hα hα1 hstar.toStarPkgo
  have hStarH_mem : Work.Spaces.WlInfMem α 4 (Work.FTS.GalFields.RHS.Sharp.StarH α Φs) :=
    hstar.RW.1
  have hfields := Work.FTS.PhiStar.CoreAux.fields_smooth hα hα1 hstar.toStarPkgo.smooth
  have hUs_sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.UsPhi α Φs) :=
    hfields.2.2.2.2.1
  have hUs_mem : Work.Spaces.WlInfMem α 4 (Work.FTS.GalFields.RHS.Sharp.UsPhi α Φs) :=
    hstar.UsW.1
  have hVs_sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.Vstar α Φs) :=
    hfields.2.2.1
  have hVs_mem : Work.Spaces.WlInfMem α 4 (Work.FTS.GalFields.RHS.Sharp.Vstar α Φs) :=
    hstar.VW.1
  have hFstar_sm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)
  have hFstar_mem : Work.Spaces.WlInfMem α 4 (Work.Construction.Fstar α) :=
    (hFstarW α hα hα1).1
  have hDthF_sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.DthFstar α) :=
    Work.FTS.EllipticEst.SmoothOpen.Dth hFstar_sm
  have hDthF_mem : Work.Spaces.WlInfMem α 4 (Work.FTS.GalFields.RHS.Sharp.DthFstar α) :=
    (hDthW α hα hα1).1
  have hDzF_sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.DzFstar α) :=
    Work.FTS.EllipticEst.SmoothOpen.Dz hFstar_sm
  have hDzF_mem : Work.Spaces.WlInfMem α 4 (Work.FTS.GalFields.RHS.Sharp.DzFstar α) :=
    (hDzW α hα hα1).1
  have hFk_sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.GalFields.RHS.Sharp.Fkstar α) := by
    show Work.FTS.EllipticEst.SmoothOpen (fun z _ => 2 * α * Work.Spaces.hKer z)
    refine Work.FTS.NonlinRows.smoothOpen_radial
      (r := fun z : ℝ => 2 * α * Work.Spaces.hKer z) ?_
    intro n
    have hker : ContDiffOn ℝ n (fun z : ℝ => Work.Spaces.hKer z) (Set.Ioi 0) := by
      simp only [Work.Spaces.hKer_apply]
      exact contDiffOn_id.div
        (((contDiffOn_const (c := (1 : ℝ)) (s := Set.Ioi 0)).add
          (contDiffOn_id (𝕜 := ℝ) (s := Set.Ioi 0))).pow 2)
        (fun z hz => pow_ne_zero 2 (by have hz' : (0 : ℝ) < z := hz; linarith))
    exact (contDiffOn_const (𝕜 := ℝ) (c := 2 * α) (s := Set.Ioi 0)).mul hker
  have hFk_mem : Work.Spaces.WlInfMem α 4 (Work.FTS.GalFields.RHS.Sharp.Fkstar α) :=
    (Work.FTS.Nonlinear.Pieces.RNP.hKerConstWlInf α (2 * α)).1
  -- ### the honest atoms
  have hDth_sm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth h) :=
    Work.FTS.EllipticEst.SmoothOpen.Dth hPhS
  have hDth_mem : Work.Spaces.HkMem α 4 (Work.Spaces.Dth h) :=
    Work.FTS.IPGen.HkMem_Dth_le (by linarith : -(1 / 10 : ℝ) ≤ α) hPhS hPh5
  have hDth_bnd : Work.FTS.Nonlin.Xn α (Work.Spaces.Dth h) ≤ 1 * Work.FTS.GalFields.Xn5 α h := by
    rw [one_mul]
    exact Work.FTS.GalFields.Xn_Dth_le_Xn5 hα hPh5
  have hDz_sm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz h) :=
    Work.FTS.EllipticEst.SmoothOpen.Dz hPhS
  have hDz_mem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz h) :=
    Work.FTS.IPGen.HkMem_Dz_le hPhS hPh5
  have hDz_bnd : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz h) ≤ 1 * Work.FTS.GalFields.Xn5 α h := by
    rw [one_mul]
    exact Work.FTS.GalFields.Xn_Dz_le_Xn5 hα hPhS hPh5
  have hpf_sm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.GalFields.RHS.Sharp.pfac z * h z θ) :=
    Work.FTS.NonlinRows.smoothOpen_mul
      Work.FTS.NonlinRows.NRow10aux.phiSelf_smoothOpen hPhS
  have hpf_mem : Work.Spaces.HkMem α 4
      (fun z θ => Work.FTS.GalFields.RHS.Sharp.pfac z * h z θ) := by
    simpa only [Work.FTS.GalFields.RHS.Sharp.pfac] using (hCφ hα hα1 hPhQ).1
  have hpf_bnd : Work.FTS.Nonlin.Xn α
      (fun z θ => Work.FTS.GalFields.RHS.Sharp.pfac z * h z θ)
      ≤ Cφ * Work.FTS.GalFields.Xn5 α h := by
    have h1 : Work.FTS.Nonlin.Xn α (fun z θ => z / (1 + z) * h z θ)
        ≤ Cφ * Work.FTS.Nonlin.Xn α h := (hCφ hα hα1 hPhQ).2
    have h2 : Cφ * Work.FTS.Nonlin.Xn α h ≤ Cφ * Work.FTS.GalFields.Xn5 α h :=
      mul_le_mul_of_nonneg_left hXh (le_of_lt hCφpos)
    simpa only [Work.FTS.GalFields.RHS.Sharp.pfac] using le_trans h1 h2
  have hFKh_sm : Work.FTS.EllipticEst.SmoothOpen
      (fun z _ => Work.Construction.FK h z) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_FKw_of_classC hhC
  have hFKh_mem : Work.Spaces.HkMem α 4 (fun z _ => Work.Construction.FK h z) :=
    (hN.fkH α hIoc h hPhQ hhl12).1
  have hFKh_bnd : Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK h z)
      ≤ Ci * Work.FTS.GalFields.Xn5 α h :=
    le_trans (hN.fkH α hIoc h hPhQ hhl12).2
      (mul_le_mul_of_nonneg_left hXh (le_of_lt hN.pos.1))
  -- the `Φ̃_h`-atoms (the elliptic outputs of `hEll`)
  have hRop_sm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Rop α (Work.FTS.GalFields.RHS.Sharp.Dof α E h)) :=
    (hEll h hhC).R.1.1
  have hRop_mem : Work.Spaces.HkMem α 4
      (Work.Construction.Rop α (Work.FTS.GalFields.RHS.Sharp.Dof α E h)) :=
    (hEll h hhC).R.1.2
  have hRop_bnd : Work.FTS.Nonlin.Xn α
      (Work.Construction.Rop α (Work.FTS.GalFields.RHS.Sharp.Dof α E h))
      ≤ max Ce 0 * Work.FTS.GalFields.Xn5 α h :=
    Work.FTS.GalFields.RHS.SharpAux.scale_le_max (Real.sqrt_nonneg _) hXh0 hYh
      (hEll h hhC).R.2 hXh
  have hUop_sm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.Uop α (Work.FTS.GalFields.RHS.Sharp.Dof α E h) z θ
        / Work.Construction.s2 θ) := (hEll h hhC).U.1.1
  have hUop_mem : Work.Spaces.HkMem α 4
      (fun z θ => Work.Construction.Uop α (Work.FTS.GalFields.RHS.Sharp.Dof α E h) z θ
        / Work.Construction.s2 θ) := (hEll h hhC).U.1.2
  have hUop_bnd : Work.FTS.Nonlin.Xn α
      (fun z θ => Work.Construction.Uop α (Work.FTS.GalFields.RHS.Sharp.Dof α E h) z θ
        / Work.Construction.s2 θ) ≤ max Ce 0 * Work.FTS.GalFields.Xn5 α h :=
    Work.FTS.GalFields.RHS.SharpAux.scale_le_max (Real.sqrt_nonneg _) hXh0 hYh
      (hEll h hhC).U.2 hXh
  have hVop_sm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.Vop (Work.FTS.GalFields.RHS.Sharp.Dof α E h)) := (hEll h hhC).V.1.1
  have hVop_mem : Work.Spaces.HkMem α 4
      (Work.Construction.Vop (Work.FTS.GalFields.RHS.Sharp.Dof α E h)) := (hEll h hhC).V.1.2
  have hVop_bnd : Work.FTS.Nonlin.Xn α
      (Work.Construction.Vop (Work.FTS.GalFields.RHS.Sharp.Dof α E h))
      ≤ max Ce 0 * Work.FTS.GalFields.Xn5 α h :=
    Work.FTS.GalFields.RHS.SharpAux.scale_le_max (Real.sqrt_nonneg _) hXh0 hYh
      (hEll h hhC).V.2 hXh
  -- the two `sin²θ`-atoms
  obtain ⟨hSqHsm, hSqHmem, hSqHbd⟩ := Work.FTS.GalFields.RHS.SharpAux.sinSq_mul_bound
    hN hα hαα₂ hBpos hBSI hBbnd hBdth hPhS hPhQ.2 (Bu := 1) (by rw [one_mul]; exact hXh)
  obtain ⟨hSqFsm, hSqFmem, hSqFbd⟩ := Work.FTS.GalFields.RHS.SharpAux.sinSq_mul_bound
    hN hα hαα₂ hBpos hBSI hBbnd hBdth hFKh_sm hFKh_mem (Bu := Ci) hFKh_bnd
  -- ### the ten term bounds
  obtain ⟨hTRAsm, hTRAmem, hTRAbd⟩ := Work.FTS.GalFields.RHS.SharpAux.wl_term_bound
    hN hα hαα₂ hStarH_sm hStarH_mem hpf_sm hpf_mem
    (le_rfl : Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.StarH α Φs)
      ≤ Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.StarH α Φs)) hpf_bnd (2 : ℝ)
  have hTRA : Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TRA α Φs h)
      ≤ A1 * Work.FTS.GalFields.Xn5 α h := by
    rw [hA1]
    exact hTRAbd
  obtain ⟨hTUAsm, hTUAmem, hTUAbd⟩ := Work.FTS.GalFields.RHS.SharpAux.wl_term_bound
    hN hα hαα₂ hUs_sm hUs_mem hDth_sm hDth_mem
    (le_rfl : Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.UsPhi α Φs)
      ≤ Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.UsPhi α Φs)) hDth_bnd (-2 : ℝ)
  have hTUA : Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TUA α Φs h)
      ≤ A2 * Work.FTS.GalFields.Xn5 α h := by
    rw [hA2]
    exact hTUAbd
  obtain ⟨hTVAsm, hTVAmem, hTVAbd⟩ := Work.FTS.GalFields.RHS.SharpAux.wl_term_bound
    hN hα hαα₂ hVs_sm hVs_mem hDz_sm hDz_mem
    (le_rfl : Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.Vstar α Φs)
      ≤ Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.Vstar α Φs)) hDz_bnd (-(2 * α))
  have hTVA : Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TVA α Φs h)
      ≤ A3 * Work.FTS.GalFields.Xn5 α h := by
    rw [hA3]
    exact hTVAbd
  obtain ⟨hTRCsm, hTRCmem, hTRCbd⟩ := Work.FTS.GalFields.RHS.SharpAux.wl_term_bound
    hN hα hαα₂ hFstar_sm hFstar_mem hRop_sm hRop_mem
    (le_rfl : Work.Spaces.WlInf α 4 (Work.Construction.Fstar α)
      ≤ Work.Spaces.WlInf α 4 (Work.Construction.Fstar α)) hRop_bnd (2 : ℝ)
  have hTRC : Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TRC α E h)
      ≤ A4 * Work.FTS.GalFields.Xn5 α h := by
    rw [hA4]
    exact hTRCbd
  obtain ⟨hTUCsm, hTUCmem, hTUCbd⟩ := Work.FTS.GalFields.RHS.SharpAux.wl_term_bound
    hN hα hαα₂ hDthF_sm hDthF_mem hUop_sm hUop_mem
    (le_rfl : Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.DthFstar α)
      ≤ Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.DthFstar α)) hUop_bnd (-2 : ℝ)
  have hTUC : Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TUC α E h)
      ≤ A5 * Work.FTS.GalFields.Xn5 α h := by
    rw [hA5]
    exact hTUCbd
  obtain ⟨hTVCsm, hTVCmem, hTVCbd⟩ := Work.FTS.GalFields.RHS.SharpAux.wl_term_bound
    hN hα hαα₂ hDzF_sm hDzF_mem hVop_sm hVop_mem
    (le_rfl : Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.DzFstar α)
      ≤ Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.DzFstar α)) hVop_bnd (-(2 * α))
  have hTVC : Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TVC α E h)
      ≤ A6 * Work.FTS.GalFields.Xn5 α h := by
    rw [hA6]
    exact hTVCbd
  obtain ⟨hTDAsm, hTDAmem, hTDAbd⟩ := Work.FTS.GalFields.RHS.SharpAux.wl_term_bound
    hN hα hαα₂ hFk_sm hFk_mem hDth_sm hDth_mem
    (le_rfl : Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.Fkstar α)
      ≤ Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.Fkstar α)) hDth_bnd (-(1 / 2))
  have hTDA : Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TDA α h)
      ≤ A7 * Work.FTS.GalFields.Xn5 α h := by
    rw [hA7]
    exact hTDAbd
  obtain ⟨hTDCsm, hTDCmem, hTDCbd⟩ := Work.FTS.GalFields.RHS.SharpAux.wl_term_bound
    hN hα hαα₂ hDthF_sm hDthF_mem hFKh_sm hFKh_mem
    (le_rfl : Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.DthFstar α)
      ≤ Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.DthFstar α)) hFKh_bnd (-(1 / 2))
  have hTDC : Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TDC α h)
      ≤ A8 * Work.FTS.GalFields.Xn5 α h := by
    rw [hA8]
    exact hTDCbd
  obtain ⟨hTEAsm, hTEAmem, hTEAbd⟩ := Work.FTS.GalFields.RHS.SharpAux.wl_term_bound
    hN hα hαα₂ hFk_sm hFk_mem hSqHsm hSqHmem
    (le_rfl : Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.Fkstar α)
      ≤ Work.Spaces.WlInf α 4 (Work.FTS.GalFields.RHS.Sharp.Fkstar α)) hSqHbd (-1 : ℝ)
  have hTEA : Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TEA α h)
      ≤ A9 * Work.FTS.GalFields.Xn5 α h := by
    rw [hA9]
    exact hTEAbd
  obtain ⟨hTECsm, hTECmem, hTECbd⟩ := Work.FTS.GalFields.RHS.SharpAux.wl_term_bound
    hN hα hαα₂ hFstar_sm hFstar_mem hSqFsm hSqFmem
    (le_rfl : Work.Spaces.WlInf α 4 (Work.Construction.Fstar α)
      ≤ Work.Spaces.WlInf α 4 (Work.Construction.Fstar α)) hSqFbd (-1 : ℝ)
  have hTEC : Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Sharp.TEC α h)
      ≤ A10 * Work.FTS.GalFields.Xn5 α h := by
    rw [hA10]
    exact hTECbd
  -- ### the assembly
  have hK0 : 0 ≤ K := le_of_lt hKpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨hTRAsm, hTRAmem,
      le_trans hTRA (Work.FTS.GalFields.RHS.SharpAux.le_K_mul_Xn5 hK0 hA1K)⟩
  · exact ⟨hTUAsm, hTUAmem,
      le_trans hTUA (Work.FTS.GalFields.RHS.SharpAux.le_K_mul_Xn5 hK0 hA2K)⟩
  · exact ⟨hTVAsm, hTVAmem,
      le_trans hTVA (Work.FTS.GalFields.RHS.SharpAux.le_K_mul_Xn5 hK0 hA3K)⟩
  · exact ⟨hTRCsm, hTRCmem,
      le_trans hTRC (Work.FTS.GalFields.RHS.SharpAux.le_K_mul_Xn5 hK0 hA4K)⟩
  · exact ⟨hTUCsm, hTUCmem,
      le_trans hTUC (Work.FTS.GalFields.RHS.SharpAux.le_K_mul_Xn5 hK0 hA5K)⟩
  · exact ⟨hTVCsm, hTVCmem,
      le_trans hTVC (Work.FTS.GalFields.RHS.SharpAux.le_K_mul_Xn5 hK0 hA6K)⟩
  · exact ⟨hTDAsm, hTDAmem,
      le_trans hTDA (Work.FTS.GalFields.RHS.SharpAux.le_K_mul_Xn5 hK0 hA7K)⟩
  · exact ⟨hTDCsm, hTDCmem,
      le_trans hTDC (Work.FTS.GalFields.RHS.SharpAux.le_K_mul_Xn5 hK0 hA8K)⟩
  · exact ⟨hTEAsm, hTEAmem,
      le_trans hTEA (Work.FTS.GalFields.RHS.SharpAux.le_K_mul_Xn5 hK0 hA9K)⟩
  · exact ⟨hTECsm, hTECmem,
      le_trans hTEC (Work.FTS.GalFields.RHS.SharpAux.le_K_mul_Xn5 hK0 hA10K)⟩

end Work.FTS.StrongEps.EpsRLX.CCSharp
end
end
