/-
# `E4R3/N4C/PairingT/RowInputs` — the honest per-piece table of §8 and its construction

This module contains, in the honest (`HQo α 4 = SmoothOpen ∧ HkMem α 4`) vocabulary of the
`N4C` interface `N4ExtraH`:

* `RowInputsTO IP α C g Φs Φg` — the honest analogue of `Open2.RowInputs2'`: the twenty-seven
  piece estimates of §8 (with the smoothness of each piece attached), the `AK`-row, the three
  `L₁₂`-rows, the two exact splits of `N₀`/`N` and the `N_*`-collapse, and the `HQo`-honesty of
  the two blocks and of `D_z g`;
* `rowInputsTO_of_rows` — its construction from the three row groups (`N0Rows`, `VocabO2.NRows2`,
  `AuxRows`) of the honest row table `N4C.RowsT`, the two smoothness bundles
  (`PairingT.smoothOpen_pieces_N0`, `PairingT.smoothOpen_pieces_N`) and the `ℋ⁴`-honesty table
  `PiecesHk`;
* the shared context `BlkCtxO` of the honest assembly, and the two per-piece helpers
  `pieceBdO` / `pieceDirO` (the `N4ExtraH`/`HQo` analogues of `Open2.pieceBd` / `pieceDir`).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.E4R3.N4C.PairingT.Atoms
import Submission.Work.FTS.Nonlinear.Mu
import Submission.Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS
import Submission.Work.FTS.StrongPersist.H6Rows.AK6Row
import Submission.Work.FTS.Nonlinear.Pieces.Rows
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.NonlinRows.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.N4C

open Work.FTS.Galerkin (Fn)
open Work.FTS.VocabO (HQo)
open Work.FTS.Nonlin

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The honest per-piece table of §8.**  Field for field this is `Open2.RowInputs2'`, with the
`HkMem α 4`-hypotheses on the first arguments replaced by the honest class `GoodO α = HQo α 4`
(interior `C^∞` plus honesty), which is what the `N4ExtraH` interface consumes. -/
structure RowInputsTO (IP : ℝ → Fn → Fn → ℝ) (α C : ℝ) (g Φs Φg : Fn) : Prop where
  r1 : GoodO α (N0fix α) ∧ Xn α (N0fix α) ≤ C * α ^ 2
  r2 : GoodO α (N03g α g) ∧ Xn α (N03g α g) ≤ C * (α ^ (-(1 : ℝ)) * Xn α g ^ 2)
  r3 : GoodO α (N04aF α g) ∧ Xn α (N04aF α g) ≤ C * (Real.sqrt α * Xn α g)
  r4 : GoodO α (N04bF α g) ∧ |IP α (N04bF α g) g| ≤ C * (α ^ (-(3 / 2 : ℝ)) * Xn α g ^ 3)
  r5 : GoodO α (N05aF α g) ∧ Xn α (N05aF α g) ≤ C * (Real.sqrt α * Xn α g)
  r6 : GoodO α (N05bF α g) ∧ |IP α (N05bF α g) g| ≤ C * (α ^ (-(1 / 2 : ℝ)) * Xn α g ^ 3)
  r7 : GoodO α (N06F α g) ∧ |IP α (N06F α g) g| ≤ C * (Real.sqrt α * Xn α g ^ 2)
  r8 : GoodO α (N1gg α g Φg) ∧ Xn α (N1gg α g Φg) ≤ C * (α ^ (-(1 / 2 : ℝ)) * Xn α g ^ 2)
  r9 : GoodO α (N1gs α g Φg) ∧ Xn α (N1gs α g Φg) ≤ C * (Real.sqrt α * Xn α g)
  r10 : GoodO α (N1sg α Φs g) ∧ Xn α (N1sg α Φs g) ≤ C * (Real.sqrt α * Xn α g)
  r11 : GoodO α (N1ss α Φs) ∧ Xn α (N1ss α Φs) ≤ C * α ^ 2
  r12 : GoodO α (N2gg α g Φg) ∧ |IP α (N2gg α g Φg) g| ≤ C * (α ^ (-(1 / 2 : ℝ)) * Xn α g ^ 3)
  r13 : GoodO α (N2gs α g Φg) ∧ Xn α (N2gs α g Φg) ≤ C * (α ^ (3 / 2 : ℝ) * Xn α g)
  r14 : GoodO α (N2sg α Φs g) ∧ |IP α (N2sg α Φs g) g| ≤ C * (Real.sqrt α * Xn α g ^ 2)
  r15 : GoodO α (N2ss α Φs) ∧ Xn α (N2ss α Φs) ≤ C * α ^ 2
  r16 : GoodO α (N3gg α g Φg) ∧ |IP α (N3gg α g Φg) g| ≤ C * Xn α g ^ 3
  r17 : GoodO α (N3gs α g Φg) ∧ Xn α (N3gs α g Φg) ≤ C * (α ^ (3 / 2 : ℝ) * Xn α g)
  r18 : GoodO α (N3sg α Φs g) ∧ |IP α (N3sg α Φs g) g| ≤ C * (α ^ (3 / 2 : ℝ) * Xn α g ^ 2)
  r19 : GoodO α (N3ss α Φs) ∧ Xn α (N3ss α Φs) ≤ C * α ^ 3
  r20 : GoodO α (N4gg α g) ∧ |IP α (N4gg α g) g| ≤ C * (α ^ (-(1 / 2 : ℝ)) * Xn α g ^ 3)
  r21 : GoodO α (N4gs α g) ∧ Xn α (N4gs α g) ≤ C * (α ^ (3 / 2 : ℝ) * Xn α g)
  r22 : GoodO α (N4sg α g) ∧ |IP α (N4sg α g) g| ≤ C * (Real.sqrt α * Xn α g ^ 2)
  r23 : GoodO α (N4ss α) ∧ Xn α (N4ss α) ≤ C * α ^ 3
  r24 : GoodO α (N5gg g) ∧ Xn α (N5gg g) ≤ C * Xn α g ^ 2
  r25 : GoodO α (N5gs α g) ∧ GoodO α (N5sg α g) ∧
    Xn α (N5gs α g) + Xn α (N5sg α g) ≤ C * (Real.sqrt α * Xn α g)
  r26 : GoodO α (N5ss α) ∧ Xn α (N5ss α) ≤ C * α ^ 2
  rak : GoodO α (Work.Construction.AK α) ∧ Xn α (Work.Construction.AK α) ≤ C
  rl0 : |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α g) g) 0|
    ≤ C * (α ^ 2 + Real.sqrt α * Xn α g + α ^ (-(3 / 2 : ℝ)) * Xn α g ^ 2)
  rl1 : |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + Φg z θ)) 0|
    ≤ C * (α ^ 2 + Real.sqrt α * Xn α g + α ^ (-(3 / 2 : ℝ)) * Xn α g ^ 2)
  rl2 : |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0| ≤ C * Xn α g
  hN0 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    Work.Construction.N0 α (Work.Construction.Ftot α g) g z θ
      = N0fix α z θ + (N03g α g z θ + N04aF α g z θ + N04bF α g z θ
          + N05aF α g z θ + N05bF α g z θ + N06F α g z θ)
  hN : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
    Work.Construction.N α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ) z θ
      = (N1gg α g Φg z θ + N1gs α g Φg z θ + N1sg α Φs g z θ + N1ss α Φs z θ)
        + (N2gg α g Φg z θ + N2gs α g Φg z θ + N2sg α Φs g z θ + N2ss α Φs z θ)
        + (N3gg α g Φg z θ + N3gs α g Φg z θ + N3sg α Φs g z θ + N3ss α Φs z θ)
        + (N4gg α g z θ + N4gs α g z θ + N4sg α g z θ + N4ss α z θ)
        + (N5gg g z θ + N5gs α g z θ + N5sg α g z θ + N5ss α z θ)
  hNs : ∀ μ : ℝ, μ ≠ -1 → ∀ z θ,
    Work.Construction.Nstar μ (Work.Construction.lamfun μ) g z θ = NstarLam μ g z θ
  hkN0 : GoodO α (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
  hkN : GoodO α (Work.Construction.N α (Work.Construction.Ftot α g)
    (fun z θ => Φs z θ + Φg z θ))
  hkDz : GoodO α (Work.Spaces.Dz g)

/-- **The honest per-piece table from the honest row table.** -/
theorem rowInputsTO_of_rows {IP : ℝ → Fn → Fn → ℝ} {α₂ Ce Cs α C K₁ K₂ K₃ : ℝ} {g Φs Φg : Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hαα₂ : α ≤ α₂)
    (hgC : Work.FTS.ClassC.ClassC α g) (hco : Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α g)
    (hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg)
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hrowsN0 : Work.FTS.Nonlinear.Pieces.N0Rows IP α K₁ g Φs Φg)
    (hrowsN : Work.FTS.VocabO2.NRows2 IP α K₂ g Φs Φg)
    (hrowsAux : Work.FTS.Nonlinear.Pieces.AuxRows IP α K₃ g Φs Φg)
    (hK1 : K₁ ≤ C) (hK2 : K₂ ≤ C) (hK3 : K₃ ≤ C)
    (hk : Work.FTS.OpenPkg.PiecesHk α g Φs Φg)
    (hspl : Work.FTS.NonlinRows.SplitsData α g Φs Φg)
    (hsmN0 : Work.FTS.EllipticEst.SmoothOpen (N0fix α) ∧
      Work.FTS.EllipticEst.SmoothOpen (N03g α g) ∧
      Work.FTS.EllipticEst.SmoothOpen (N04aF α g) ∧
      Work.FTS.EllipticEst.SmoothOpen (N04bF α g) ∧
      Work.FTS.EllipticEst.SmoothOpen (N05aF α g) ∧
      Work.FTS.EllipticEst.SmoothOpen (N05bF α g) ∧
      Work.FTS.EllipticEst.SmoothOpen (N06F α g))
    (hsmN : Work.FTS.EllipticEst.SmoothOpen (N1gg α g Φg) ∧
      Work.FTS.EllipticEst.SmoothOpen (N1gs α g Φg) ∧
      Work.FTS.EllipticEst.SmoothOpen (N1sg α Φs g) ∧
      Work.FTS.EllipticEst.SmoothOpen (N1ss α Φs) ∧
      Work.FTS.EllipticEst.SmoothOpen (N2gg α g Φg) ∧
      Work.FTS.EllipticEst.SmoothOpen (N2gs α g Φg) ∧
      Work.FTS.EllipticEst.SmoothOpen (N2sg α Φs g) ∧
      Work.FTS.EllipticEst.SmoothOpen (N2ss α Φs) ∧
      Work.FTS.EllipticEst.SmoothOpen (N3gg α g Φg) ∧
      Work.FTS.EllipticEst.SmoothOpen (N3gs α g Φg) ∧
      Work.FTS.EllipticEst.SmoothOpen (N3sg α Φs g) ∧
      Work.FTS.EllipticEst.SmoothOpen (N3ss α Φs) ∧
      Work.FTS.EllipticEst.SmoothOpen (N4gg α g) ∧
      Work.FTS.EllipticEst.SmoothOpen (N4gs α g) ∧
      Work.FTS.EllipticEst.SmoothOpen (N4sg α g) ∧
      Work.FTS.EllipticEst.SmoothOpen (N4ss α) ∧
      Work.FTS.EllipticEst.SmoothOpen (N5gg g) ∧
      Work.FTS.EllipticEst.SmoothOpen (N5gs α g) ∧
      Work.FTS.EllipticEst.SmoothOpen (N5sg α g) ∧
      Work.FTS.EllipticEst.SmoothOpen (N5ss α)) :
    RowInputsTO IP α C g Φs Φg := by
  obtain ⟨hs0, hs1, hs2⟩ := hspl
  obtain ⟨m1, m2, m3, m4, m5, m6, m7⟩ := hsmN0
  obtain ⟨m8, m9, m10, m11, m12, m13, m14, m15, m16, m17, m18, m19, m20, m21, m22, m23,
    m24, m25, m26, m27⟩ := hsmN
  have hα0 : (0 : ℝ) ≤ α := hα.le
  have hX0 : (0 : ℝ) ≤ Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hsq0 : (0 : ℝ) ≤ Real.sqrt α := Real.sqrt_nonneg α
  have hX2 : (0 : ℝ) ≤ Xn α g ^ 2 := pow_nonneg hX0 2
  have hX3 : (0 : ℝ) ≤ Xn α g ^ 3 := pow_nonneg hX0 3
  have hr1 : (0 : ℝ) ≤ α ^ (-(1 : ℝ)) := Real.rpow_nonneg hα0 _
  have hr12 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα0 _
  have hr32 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hα0 _
  have h32 : (0 : ℝ) ≤ α ^ (3 / 2 : ℝ) := Real.rpow_nonneg hα0 _
  refine
    { r1 := ⟨⟨m1, hk.p1⟩, le_trans hrowsN0.r1 (mul_le_mul_of_nonneg_right hK1 (pow_nonneg hα0 2))⟩
      r2 := ⟨⟨m2, hk.p2⟩,
        le_trans hrowsN0.r2 (mul_le_mul_of_nonneg_right hK1 (mul_nonneg hr1 hX2))⟩
      r3 := ⟨⟨m3, hk.p3⟩,
        le_trans hrowsN0.r3 (mul_le_mul_of_nonneg_right hK1 (mul_nonneg hsq0 hX0))⟩
      r4 := ⟨⟨m4, hk.p4⟩,
        le_trans hrowsN0.r4 (mul_le_mul_of_nonneg_right hK1 (mul_nonneg hr32 hX3))⟩
      r5 := ⟨⟨m5, hk.p5⟩,
        le_trans hrowsN0.r5 (mul_le_mul_of_nonneg_right hK1 (mul_nonneg hsq0 hX0))⟩
      r6 := ⟨⟨m6, hk.p6⟩,
        le_trans hrowsN0.r6 (mul_le_mul_of_nonneg_right hK1 (mul_nonneg hr12 hX3))⟩
      r7 := ⟨⟨m7, hk.p7⟩,
        le_trans hrowsN0.r7 (mul_le_mul_of_nonneg_right hK1 (mul_nonneg hsq0 hX2))⟩
      r8 := ⟨⟨m8, hk.p8⟩,
        le_trans hrowsN.r8 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg hr12 hX2))⟩
      r9 := ⟨⟨m9, hk.p9⟩,
        le_trans hrowsN.r9 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg hsq0 hX0))⟩
      r10 := ⟨⟨m10, hk.p10⟩,
        le_trans hrowsN.r10 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg hsq0 hX0))⟩
      r11 := ⟨⟨m11, hk.p11⟩,
        le_trans hrowsN.r11 (mul_le_mul_of_nonneg_right hK2 (pow_nonneg hα0 2))⟩
      r12 := ⟨⟨m12, hk.p12⟩,
        le_trans hrowsN.r12 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg hr12 hX3))⟩
      r13 := ⟨⟨m13, hk.p13⟩,
        le_trans hrowsN.r13 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg h32 hX0))⟩
      r14 := ⟨⟨m14, hk.p14⟩,
        le_trans hrowsN.r14 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg hsq0 hX2))⟩
      r15 := ⟨⟨m15, hk.p15⟩,
        le_trans hrowsN.r15 (mul_le_mul_of_nonneg_right hK2 (pow_nonneg hα0 2))⟩
      r16 := ⟨⟨m16, hk.p16⟩, le_trans hrowsN.r16 (mul_le_mul_of_nonneg_right hK2 hX3)⟩
      r17 := ⟨⟨m17, hk.p17⟩,
        le_trans hrowsN.r17 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg h32 hX0))⟩
      r18 := ⟨⟨m18, hk.p18⟩,
        le_trans hrowsN.r18 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg h32 hX2))⟩
      r19 := ⟨⟨m19, hk.p19⟩,
        le_trans hrowsN.r19 (mul_le_mul_of_nonneg_right hK2 (pow_nonneg hα0 3))⟩
      r20 := ⟨⟨m20, hk.p20⟩,
        le_trans hrowsN.r20 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg hr12 hX3))⟩
      r21 := ⟨⟨m21, hk.p21⟩,
        le_trans hrowsN.r21 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg h32 hX0))⟩
      r22 := ⟨⟨m22, hk.p22⟩,
        le_trans hrowsN.r22 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg hsq0 hX2))⟩
      r23 := ⟨⟨m23, hk.p23⟩,
        le_trans hrowsN.r23 (mul_le_mul_of_nonneg_right hK2 (pow_nonneg hα0 3))⟩
      r24 := ⟨⟨m24, hk.p24⟩, le_trans hrowsN.r24 (mul_le_mul_of_nonneg_right hK2 hX2)⟩
      r25 := ⟨⟨m25, hk.p25⟩, ⟨m26, hk.p26⟩,
        le_trans hrowsN.r25 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg hsq0 hX0))⟩
      r26 := ⟨⟨m27, hk.p27⟩,
        le_trans hrowsN.r26 (mul_le_mul_of_nonneg_right hK2 (pow_nonneg hα0 2))⟩
      rak := ⟨⟨Work.FTS.StrongPersist.AK_smoothO α, hk.pAK⟩,
        le_trans hrowsAux.rak hK3⟩
      rl0 := le_trans hrowsAux.rl0 (mul_le_mul_of_nonneg_right hK3 (by positivity))
      rl1 := le_trans hrowsAux.rl1 (mul_le_mul_of_nonneg_right hK3 (by positivity))
      rl2 := le_trans hrowsAux.rl2 (mul_le_mul_of_nonneg_right hK3 hX0)
      hN0 := hs0
      hN := hs1
      hNs := hs2
      hkN0 := ⟨Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS hα hα1 hgC hell hstar |>.2.2.2.1,
        hk.pN0⟩
      hkN := ⟨Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS hα hα1 hgC hell hstar |>.2.2.2.2,
        hk.pN⟩
      hkDz := ⟨hgC.reg.Dz, hk.pDz⟩ }

/-- **The shared context of the honest §8 assembly**: the `IP`-interface `N4ExtraH`, the ranges
of `α`, the class-`C` data (whose coercivity field supplies the `D_z`-self-pairing), the honest
row table and the constant bookkeeping.  This is the honest analogue of `Open2.BlkCtx`. -/
structure BlkCtxO (IP : ℝ → Fn → Fn → ℝ) (α₂ Ct K₀ C C₀ α : ℝ) (g Φs Φg : Fn) : Prop where
  hE : N4ExtraH IP α₂ Ct
  hα : 0 < α
  hαα₂ : α ≤ α₂
  hα1 : α ≤ 1
  hgC : Work.FTS.ClassC.ClassC α g
  hco : Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α g
  hR : RowInputsTO IP α C g Φs Φg
  hCt : 0 < Ct
  hK₀pos : 0 < K₀
  hK₀Ct : Ct ≤ K₀
  hK₀one : 1 ≤ K₀
  hC : 0 < C
  hbigK : K₀ * (C + 1) ≤ C₀ * C

namespace BlkCtxO

variable {IP : ℝ → Fn → Fn → ℝ} {α₂ Ct K₀ C C₀ α : ℝ} {g Φs Φg : Fn}

theorem hαIoc (h : BlkCtxO IP α₂ Ct K₀ C C₀ α g Φs Φg) : α ∈ Set.Ioc 0 α₂ :=
  ⟨h.hα, h.hαα₂⟩

theorem hg4 (h : BlkCtxO IP α₂ Ct K₀ C C₀ α g Φs Φg) : HQo α 4 g :=
  classC_hqo4 h.hgC

theorem hreg5 (h : BlkCtxO IP α₂ Ct K₀ C C₀ α g Φs Φg) :
    Work.FTS.StrongEps.EpsE4Thr.RegQo α 5 g := h.hco.1

end BlkCtxO

/-- **The per-piece bound from an `ℋ⁴`-estimate**, honest version of `Open2.pieceBd`. -/
theorem pieceBdO {IP : ℝ → Fn → Fn → ℝ} {α₂ Ct K₀ C α : ℝ} {g : Fn}
    (hE : N4ExtraH IP α₂ Ct) (hαIoc : α ∈ Set.Ioc 0 α₂) (hg : HQo α 4 g) (hCt : 0 < Ct)
    (hK₀Ct : Ct ≤ K₀) (hX0 : 0 ≤ Xn α g) (hPbd0 : 0 ≤ Pbd α (Xn α g)) (hC : 0 < C)
    (f : Fn) (B : ℝ) (hf : Xn α f ≤ C * B) (hB : B * Xn α g ≤ Pbd α (Xn α g))
    (hk : HQo α 4 f) :
    |IP α f g| ≤ K₀ * (C + 1) * Pbd α (Xn α g) := by
  set X := Xn α g with hXdef
  have hK₀pos : 0 < K₀ := lt_of_lt_of_le hCt hK₀Ct
  have h1 : |IP α f g| ≤ Ct * Xn α f * X := hE.cs α hαIoc f g hk hg
  have h2 : Ct * Xn α f * X ≤ Ct * (C * B) * X :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf hCt.le) hX0
  have h3 : Ct * (C * B) * X = Ct * C * (B * X) := by ring
  have h4 : Ct * C * (B * X) ≤ Ct * C * Pbd α X :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  have h5 : Ct * C * Pbd α X ≤ K₀ * C * Pbd α X :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK₀Ct hC.le) hPbd0
  have h6 : K₀ * C * Pbd α X ≤ K₀ * (C + 1) * Pbd α X := by
    have h := mul_le_mul_of_nonneg_right (by linarith : C ≤ C + 1) hPbd0
    nlinarith [h, hK₀pos.le, hPbd0]
  linarith [h1, h2, h3.le, h3.ge, h4, h5, h6]

/-- **The per-piece bound from a direct pairing estimate**, honest version of
`Open2.pieceDir`. -/
theorem pieceDirO {IP : ℝ → Fn → Fn → ℝ} {K₀ C α : ℝ} {g : Fn}
    (f : Fn) (m : ℝ) (hf : |IP α f g| ≤ C * m) (hm : m ≤ Pbd α (Xn α g))
    (hPbd0 : 0 ≤ Pbd α (Xn α g)) (hC : 0 < C) (hK₀one : 1 ≤ K₀) :
    |IP α f g| ≤ K₀ * (C + 1) * Pbd α (Xn α g) := by
  set X := Xn α g with hXdef
  have h1 : C * m ≤ C * Pbd α X := mul_le_mul_of_nonneg_left hm hC.le
  have h2 : C * Pbd α X ≤ K₀ * C * Pbd α X := by
    have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK₀one hC.le) hPbd0
    nlinarith [h]
  have h3 : K₀ * C * Pbd α X ≤ K₀ * (C + 1) * Pbd α X := by
    have h := mul_le_mul_of_nonneg_right (by linarith : C ≤ C + 1) hPbd0
    nlinarith [h, hPbd0]
  linarith [hf, h1, h2, h3]

end Work.FTS.StrongEps.E4R3.N4C
