/-
# `Work.FTS.StrongPersist.L3Rhs.L3RhsNssBlock` — the pure-star block of the right-hand side

The block `NSsSum α Φs = N₁^{**} + N₂^{**} + N₃^{**} + N₄^{**} + N₅^{**}` of
`Submission/Work/FTS/StrongPersist/L3Rhs/Defs.lean` consists of the five terms of the paper's
table in which both the elliptic residual and the transported profile are the *star* quantities
(`Φ̃_*` and `F_*`).  Nothing in it depends on the modulation `g` or on the perturbation residual
`Φ̃_g`; the only datum is the star package `StarPkgo2 α Cs Φs`.

This file proves the priced statement of the block: for `0 < α ≤ α₂` and every star datum, the
block is `C³` on the open quadrant, in `ℋ³`, and

  `|NSsSum α Φs|_{ℋ³} ≤ C · (1 + |Cs|) ^ 4 · α ^ (-Cpow)`

with `C`, `Cpow` **uniform in the data** (`α₂ = 1/2`, `Cpow = 0`).  The uniformity in `Cs` is
what distinguishes this from the per-row statements of `FTS/NonlinRows`, whose constants are
existential in `Cs`; it is obtained by pricing each row directly (the five sibling modules
`N1ssPriced … N5ssPriced`):

* `N₁^{**}`, `N₂^{**}`, `N₃^{**}` are the star-coefficient rows 11, 15, 19, bounded by
  `Cᵢ (1 + |Cs|) α^{pᵢ}` with `pᵢ = 2, 2, 3` (fields `RW`, `UszW`, `VzW` of `StarPkgo2`);
* `N₄^{**}`, `N₅^{**}` are the explicit profile rows 23, 26, bounded by `Cᵢ α^{pᵢ}` with
  `pᵢ = 3, 2` and no dependence on the data at all;

the five smoothness facts (all finite orders on the open quadrant) come from `PieceSmooth`.

The assembly only uses that `ℋ³`-membership descends from `ℋ⁴`
(`OpenPkg.HkMem_mono_open`), that `HkNorm α 3 ≤ HkNorm α 4` on `ℋ⁴`-data
(`StrongLWP.HkNorm_mono_of_mem`), and the triangle inequality `HkNorm_add_le`; the five partial
sums are combined with the crude constant `16 = 2⁴ ⊇ (√2)⁴`.

Everything is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.N1ssPriced
import Submission.Work.FTS.StrongPersist.L3Rhs.N2ssPriced
import Submission.Work.FTS.StrongPersist.L3Rhs.N3ssPriced
import Submission.Work.FTS.StrongPersist.L3Rhs.N4ssPriced
import Submission.Work.FTS.StrongPersist.L3Rhs.N5ssPriced
import Submission.Work.FTS.StrongPersist.L3Rhs.PieceSmooth
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.StrongLWP.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

theorem L3RhsNssBlock : ∃ C Cpow α₂ : ℝ, 0 < C ∧ 0 ≤ Cpow ∧ 0 < α₂ ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ (Cs : ℝ) (Φs : Work.FTS.Galerkin.Fn),
      Work.FTS.VocabO2.StarPkgo2 α Cs Φs →
      ContDiffOn ℝ 3 (Function.uncurry (Work.FTS.StrongPersist.L3Rhs.NSsSum α Φs)) Work.FTS.EllipticEst.Q0 ∧
      Work.Spaces.HkMem α 3 (Work.FTS.StrongPersist.L3Rhs.NSsSum α Φs) ∧
      Work.Spaces.HkNorm α 3 (Work.FTS.StrongPersist.L3Rhs.NSsSum α Φs)
        ≤ C * (1 + |Cs|) ^ 4 * α ^ (-Cpow) := by
  obtain ⟨C1, hC1pos, hbody1⟩ := N1ssPriced
  obtain ⟨C2, hC2pos, hbody2⟩ := N2ssPriced
  obtain ⟨C3, hC3pos, hbody3⟩ := N3ssPriced
  obtain ⟨C4, hC4pos, hbody4⟩ := N4ssPriced
  obtain ⟨C5, hC5pos, hbody5⟩ := N5ssPriced
  refine ⟨16 * (C1 + C2 + C3 + C4 + C5) + 1, 0, 1 / 2, ?_, le_refl 0, by norm_num, ?_⟩
  · have h1' : (0 : ℝ) < 16 * (C1 + C2 + C3 + C4 + C5) := by linarith
    linarith
  intro α hαmem Cs Φs hstar
  obtain ⟨hα0, hαhalf⟩ := hαmem
  have hα : 0 < α := hα0
  have hα1 : α ≤ 1 := by linarith
  have hαIoc : α ∈ Set.Ioc 0 1 := ⟨hα, hα1⟩
  -- the five pieces, and the four partial sums
  set S1 : Fn := Work.FTS.Nonlin.N1ss α Φs with hS1
  set S2 : Fn := Work.FTS.Nonlin.N2ss α Φs with hS2
  set S3 : Fn := Work.FTS.Nonlin.N3ss α Φs with hS3
  set S4 : Fn := Work.FTS.Nonlin.N4ss α with hS4
  set S5 : Fn := Work.FTS.Nonlin.N5ss α with hS5
  set P12 : Fn := fun z θ => S1 z θ + S2 z θ with hP12
  set P123 : Fn := fun z θ => P12 z θ + S3 z θ with hP123
  set P1234 : Fn := fun z θ => P123 z θ + S4 z θ with hP1234
  set Pall : Fn := fun z θ => P1234 z θ + S5 z θ with hPall
  have hsum : NSsSum α Φs = Pall := by
    rw [hPall, hP1234, hP123, hP12, hS1, hS2, hS3, hS4, hS5]
    rfl
  -- the six delegated inputs, instantiated (the `set`-definitions `Sᵢ` are definitionally the
  -- pieces, so the statements transfer without rewriting)
  have hmem4_1 : Work.Spaces.HkMem α 4 S1 := (hbody1 α hαIoc Cs Φs hstar).1
  have hmem4_2 : Work.Spaces.HkMem α 4 S2 := (hbody2 α hαIoc Cs Φs hstar).1
  have hmem4_3 : Work.Spaces.HkMem α 4 S3 := (hbody3 α hαIoc Cs Φs hstar).1
  have hmem4_4 : Work.Spaces.HkMem α 4 S4 := (hbody4 α hαIoc).1
  have hmem4_5 : Work.Spaces.HkMem α 4 S5 := (hbody5 α hαIoc).1
  have hbnd1 : Work.Spaces.HkNorm α 4 S1 ≤ C1 * (1 + |Cs|) * α ^ 2 :=
    (hbody1 α hαIoc Cs Φs hstar).2
  have hbnd2 : Work.Spaces.HkNorm α 4 S2 ≤ C2 * (1 + |Cs|) * α ^ 2 :=
    (hbody2 α hαIoc Cs Φs hstar).2
  have hbnd3 : Work.Spaces.HkNorm α 4 S3 ≤ C3 * (1 + |Cs|) * α ^ 3 :=
    (hbody3 α hαIoc Cs Φs hstar).2
  have hbnd4 : Work.Spaces.HkNorm α 4 S4 ≤ C4 * α ^ 3 := (hbody4 α hαIoc).2
  have hbnd5 : Work.Spaces.HkNorm α 4 S5 ≤ C5 * α ^ 2 := (hbody5 α hαIoc).2
  obtain ⟨hSO1, hSO2, hSO3, hSO4, hSO5⟩ := PieceSmooth α hαIoc Cs Φs hstar
  -- level-3 honesty of the pieces
  have hmem3_1 : Work.Spaces.HkMem α 3 S1 :=
    Work.FTS.OpenPkg.HkMem_mono_open hSO1 3 (by norm_num) hmem4_1
  have hmem3_2 : Work.Spaces.HkMem α 3 S2 :=
    Work.FTS.OpenPkg.HkMem_mono_open hSO2 3 (by norm_num) hmem4_2
  have hmem3_3 : Work.Spaces.HkMem α 3 S3 :=
    Work.FTS.OpenPkg.HkMem_mono_open hSO3 3 (by norm_num) hmem4_3
  have hmem3_4 : Work.Spaces.HkMem α 3 S4 :=
    Work.FTS.OpenPkg.HkMem_mono_open hSO4 3 (by norm_num) hmem4_4
  have hmem3_5 : Work.Spaces.HkMem α 3 S5 :=
    Work.FTS.OpenPkg.HkMem_mono_open hSO5 3 (by norm_num) hmem4_5
  -- level-4 honesty of the partial sums
  have hmem4_12 : Work.Spaces.HkMem α 4 P12 := by
    rw [hP12]
    exact Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four (f := S1) (g := S2)
      (hSO1.forall 4) (hSO2.forall 4) hmem4_1 hmem4_2
  have hmem4_123 : Work.Spaces.HkMem α 4 P123 := by
    rw [hP123]
    exact Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four (f := P12) (g := S3)
      ((Work.FTS.EllipticEst.smoothOpen_add hSO1 hSO2).forall 4) (hSO3.forall 4)
      hmem4_12 hmem4_3
  have hSO12 : Work.FTS.EllipticEst.SmoothOpen P12 := by
    rw [hP12]; exact Work.FTS.EllipticEst.smoothOpen_add hSO1 hSO2
  have hSO123 : Work.FTS.EllipticEst.SmoothOpen P123 := by
    rw [hP123]; exact Work.FTS.EllipticEst.smoothOpen_add hSO12 hSO3
  have hmem4_1234 : Work.Spaces.HkMem α 4 P1234 := by
    rw [hP1234]
    exact Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four (f := P123) (g := S4)
      (hSO123.forall 4) (hSO4.forall 4) hmem4_123 hmem4_4
  have hSO1234 : Work.FTS.EllipticEst.SmoothOpen P1234 := by
    rw [hP1234]; exact Work.FTS.EllipticEst.smoothOpen_add hSO123 hSO4
  have hmem4_Pall : Work.Spaces.HkMem α 4 Pall := by
    rw [hPall]
    exact Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four (f := P1234) (g := S5)
      (hSO1234.forall 4) (hSO5.forall 4) hmem4_1234 hmem4_5
  have hSO_Pall : Work.FTS.EllipticEst.SmoothOpen Pall := by
    rw [hPall]; exact Work.FTS.EllipticEst.smoothOpen_add hSO1234 hSO5
  have hmem3_12 : Work.Spaces.HkMem α 3 P12 :=
    Work.FTS.OpenPkg.HkMem_mono_open hSO12 3 (by norm_num) hmem4_12
  have hmem3_123 : Work.Spaces.HkMem α 3 P123 :=
    Work.FTS.OpenPkg.HkMem_mono_open hSO123 3 (by norm_num) hmem4_123
  have hmem3_1234 : Work.Spaces.HkMem α 3 P1234 :=
    Work.FTS.OpenPkg.HkMem_mono_open hSO1234 3 (by norm_num) hmem4_1234
  -- the triangle inequalities for the norm at level 3
  have hs2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have htri12 : Work.Spaces.HkNorm α 3 P12
      ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 3 S1 + Work.Spaces.HkNorm α 3 S2) := by
    rw [hP12]
    exact Work.FTS.EllipticEst.HkNorm_add_le α 3 (hSO1.forall) (hSO2.forall) hmem3_1 hmem3_2
  have htri123 : Work.Spaces.HkNorm α 3 P123
      ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 3 P12 + Work.Spaces.HkNorm α 3 S3) := by
    rw [hP123]
    exact Work.FTS.EllipticEst.HkNorm_add_le α 3 (hSO12.forall) (hSO3.forall) hmem3_12 hmem3_3
  have htri1234 : Work.Spaces.HkNorm α 3 P1234
      ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 3 P123 + Work.Spaces.HkNorm α 3 S4) := by
    rw [hP1234]
    exact Work.FTS.EllipticEst.HkNorm_add_le α 3 (hSO123.forall) (hSO4.forall) hmem3_123 hmem3_4
  have htriPall : Work.Spaces.HkNorm α 3 Pall
      ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α 3 P1234 + Work.Spaces.HkNorm α 3 S5) := by
    rw [hPall]
    exact Work.FTS.EllipticEst.HkNorm_add_le α 3 (hSO1234.forall) (hSO5.forall) hmem3_1234 hmem3_5
  -- the monotonicity `3 ≤ 4`
  have hmono1 : Work.Spaces.HkNorm α 3 S1 ≤ Work.Spaces.HkNorm α 4 S1 :=
    Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 4) (k' := 3) (by norm_num) hmem4_1
  have hmono2 : Work.Spaces.HkNorm α 3 S2 ≤ Work.Spaces.HkNorm α 4 S2 :=
    Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 4) (k' := 3) (by norm_num) hmem4_2
  have hmono3 : Work.Spaces.HkNorm α 3 S3 ≤ Work.Spaces.HkNorm α 4 S3 :=
    Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 4) (k' := 3) (by norm_num) hmem4_3
  have hmono4 : Work.Spaces.HkNorm α 3 S4 ≤ Work.Spaces.HkNorm α 4 S4 :=
    Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 4) (k' := 3) (by norm_num) hmem4_4
  have hmono5 : Work.Spaces.HkNorm α 3 S5 ≤ Work.Spaces.HkNorm α 4 S5 :=
    Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 4) (k' := 3) (by norm_num) hmem4_5
  -- arithmetic
  have hX1 : (0 : ℝ) ≤ (1 : ℝ) + |Cs| := by positivity
  have hX1ge : (1 : ℝ) ≤ 1 + |Cs| := by linarith [abs_nonneg Cs]
  have hX4 : (1 : ℝ) + |Cs| ≤ (1 + |Cs|) ^ 4 := by
    calc (1 : ℝ) + |Cs| = (1 + |Cs|) ^ 1 := (pow_one _).symm
      _ ≤ (1 + |Cs|) ^ 4 := pow_le_pow_right₀ hX1ge (by norm_num)
  have hp2 : α ^ 2 ≤ 1 := pow_le_one₀ hα.le hα1
  have hp3 : α ^ 3 ≤ 1 := pow_le_one₀ hα.le hα1
  -- the five pieces, in the final shape
  have hF1 : Work.Spaces.HkNorm α 3 S1 ≤ C1 * (1 + |Cs|) ^ 4 := by
    refine hmono1.trans (hbnd1.trans ?_)
    calc C1 * (1 + |Cs|) * α ^ 2 ≤ C1 * (1 + |Cs|) * 1 :=
          mul_le_mul_of_nonneg_left hp2 (by positivity)
      _ = C1 * (1 + |Cs|) := by ring
      _ ≤ C1 * (1 + |Cs|) ^ 4 := mul_le_mul_of_nonneg_left hX4 hC1pos.le
  have hF2 : Work.Spaces.HkNorm α 3 S2 ≤ C2 * (1 + |Cs|) ^ 4 := by
    refine hmono2.trans (hbnd2.trans ?_)
    calc C2 * (1 + |Cs|) * α ^ 2 ≤ C2 * (1 + |Cs|) * 1 :=
          mul_le_mul_of_nonneg_left hp2 (by positivity)
      _ = C2 * (1 + |Cs|) := by ring
      _ ≤ C2 * (1 + |Cs|) ^ 4 := mul_le_mul_of_nonneg_left hX4 hC2pos.le
  have hF3 : Work.Spaces.HkNorm α 3 S3 ≤ C3 * (1 + |Cs|) ^ 4 := by
    refine hmono3.trans (hbnd3.trans ?_)
    calc C3 * (1 + |Cs|) * α ^ 3 ≤ C3 * (1 + |Cs|) * 1 :=
          mul_le_mul_of_nonneg_left hp3 (by positivity)
      _ = C3 * (1 + |Cs|) := by ring
      _ ≤ C3 * (1 + |Cs|) ^ 4 := mul_le_mul_of_nonneg_left hX4 hC3pos.le
  have hF4 : Work.Spaces.HkNorm α 3 S4 ≤ C4 * (1 + |Cs|) ^ 4 := by
    refine hmono4.trans (hbnd4.trans ?_)
    calc C4 * α ^ 3 ≤ C4 * 1 := mul_le_mul_of_nonneg_left hp3 hC4pos.le
      _ = C4 * 1 := by ring
      _ ≤ C4 * (1 + |Cs|) ^ 4 := by
          refine mul_le_mul_of_nonneg_left ?_ hC4pos.le
          have h1 : (1 : ℝ) ≤ (1 + |Cs|) ^ 4 := one_le_pow₀ hX1ge
          linarith
  have hF5 : Work.Spaces.HkNorm α 3 S5 ≤ C5 * (1 + |Cs|) ^ 4 := by
    refine hmono5.trans (hbnd5.trans ?_)
    calc C5 * α ^ 2 ≤ C5 * 1 := mul_le_mul_of_nonneg_left hp2 hC5pos.le
      _ = C5 * 1 := by ring
      _ ≤ C5 * (1 + |Cs|) ^ 4 := by
          refine mul_le_mul_of_nonneg_left ?_ hC5pos.le
          have h1 : (1 : ℝ) ≤ (1 + |Cs|) ^ 4 := one_le_pow₀ hX1ge
          linarith
  -- the four triangle steps, with `√2 ≤ 2`
  have step1 : Work.Spaces.HkNorm α 3 Pall
      ≤ 2 * (Work.Spaces.HkNorm α 3 P1234 + Work.Spaces.HkNorm α 3 S5) := by
    refine htriPall.trans ?_
    exact mul_le_mul_of_nonneg_right hs2
      (by linarith [Work.Spaces.HkNorm_nonneg α 3 P1234, Work.Spaces.HkNorm_nonneg α 3 S5])
  have step2 : Work.Spaces.HkNorm α 3 P1234
      ≤ 2 * (Work.Spaces.HkNorm α 3 P123 + Work.Spaces.HkNorm α 3 S4) := by
    refine htri1234.trans ?_
    exact mul_le_mul_of_nonneg_right hs2
      (by linarith [Work.Spaces.HkNorm_nonneg α 3 P123, Work.Spaces.HkNorm_nonneg α 3 S4])
  have step3 : Work.Spaces.HkNorm α 3 P123
      ≤ 2 * (Work.Spaces.HkNorm α 3 P12 + Work.Spaces.HkNorm α 3 S3) := by
    refine htri123.trans ?_
    exact mul_le_mul_of_nonneg_right hs2
      (by linarith [Work.Spaces.HkNorm_nonneg α 3 P12, Work.Spaces.HkNorm_nonneg α 3 S3])
  have step4 : Work.Spaces.HkNorm α 3 P12
      ≤ 2 * (Work.Spaces.HkNorm α 3 S1 + Work.Spaces.HkNorm α 3 S2) := by
    refine htri12.trans ?_
    exact mul_le_mul_of_nonneg_right hs2
      (by linarith [Work.Spaces.HkNorm_nonneg α 3 S1, Work.Spaces.HkNorm_nonneg α 3 S2])
  have hchain : Work.Spaces.HkNorm α 3 Pall
      ≤ 16 * (Work.Spaces.HkNorm α 3 S1 + Work.Spaces.HkNorm α 3 S2
          + Work.Spaces.HkNorm α 3 S3 + Work.Spaces.HkNorm α 3 S4
          + Work.Spaces.HkNorm α 3 S5) := by
    linarith [step1, step2, step3, step4, Work.Spaces.HkNorm_nonneg α 3 S1,
      Work.Spaces.HkNorm_nonneg α 3 S2, Work.Spaces.HkNorm_nonneg α 3 S3,
      Work.Spaces.HkNorm_nonneg α 3 S4, Work.Spaces.HkNorm_nonneg α 3 S5]
  have hfin : Work.Spaces.HkNorm α 3 Pall
      ≤ 16 * (C1 + C2 + C3 + C4 + C5) * (1 + |Cs|) ^ 4 := by
    refine hchain.trans ?_
    have hsum5 : Work.Spaces.HkNorm α 3 S1 + Work.Spaces.HkNorm α 3 S2
        + Work.Spaces.HkNorm α 3 S3 + Work.Spaces.HkNorm α 3 S4
        + Work.Spaces.HkNorm α 3 S5
        ≤ C1 * (1 + |Cs|) ^ 4 + C2 * (1 + |Cs|) ^ 4 + C3 * (1 + |Cs|) ^ 4
          + C4 * (1 + |Cs|) ^ 4 + C5 * (1 + |Cs|) ^ 4 := by
      linarith [hF1, hF2, hF3, hF4, hF5]
    calc 16 * (Work.Spaces.HkNorm α 3 S1 + Work.Spaces.HkNorm α 3 S2
            + Work.Spaces.HkNorm α 3 S3 + Work.Spaces.HkNorm α 3 S4
            + Work.Spaces.HkNorm α 3 S5)
        ≤ 16 * (C1 * (1 + |Cs|) ^ 4 + C2 * (1 + |Cs|) ^ 4 + C3 * (1 + |Cs|) ^ 4
            + C4 * (1 + |Cs|) ^ 4 + C5 * (1 + |Cs|) ^ 4) := by linarith
      _ = 16 * (C1 + C2 + C3 + C4 + C5) * (1 + |Cs|) ^ 4 := by ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hsum]
    exact hSO_Pall.forall 3
  · rw [hsum]
    exact Work.FTS.OpenPkg.HkMem_mono_open hSO_Pall 3 (by norm_num) hmem4_Pall
  · rw [hsum]
    refine hfin.trans ?_
    rw [show (-(0 : ℝ)) = 0 by norm_num, Real.rpow_zero, mul_one]
    have hquad : (0 : ℝ) ≤ (1 + |Cs|) ^ 4 := by positivity
    nlinarith [hquad]

end Work.FTS.StrongPersist.L3Rhs
