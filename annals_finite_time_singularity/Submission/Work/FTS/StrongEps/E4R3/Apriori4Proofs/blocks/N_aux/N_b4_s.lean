import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.Trigonometric
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N_aux.NB4Aux

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
