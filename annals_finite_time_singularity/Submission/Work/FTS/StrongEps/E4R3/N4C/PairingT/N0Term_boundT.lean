/-
# `E4R3/N4C/PairingT/N0Term_boundT` — the honest `N₀`-block of the §8 assembly

This is the honest (`class-C` / open-quadrant) analogue of `Open2.N0Term_bound2`: from the
context `BlkCtxO` (the `N4ExtraH` interface, the honest per-piece table `RowInputsTO` and the
constant bookkeeping) the seven pieces of the `N₀`-block are summed with the per-piece bounds
`pieceBdO` / `pieceDirO`, giving

  `|IP α (N₀ α (F_*+g) g) g| ≤ 7·(K₀(C+1)·Pbd α (Xn α g))`.

The proof is the verbatim adaptation of `N0Block2.N0Term_bound2`; the only differences are that
the smoothness of the seven pieces comes from the honest table `RowInputsTO` itself (each row
carries its `GoodO α ·` conjunct) and that the linearity is the honest `IPO_add7`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.E4R3.N4C.PairingT.RowInputs
import Submission.Work.FTS.Nonlinear.Assembly
import Submission.Work.Construction.Apriori

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.N4C.PairingT

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin
open Work.FTS.VocabO (HQo)
open Work.FTS.StrongEps.E4R3.N4C

set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The `N₀` block** (seven pieces), honest version of `Open2.N0Term_bound2`:
`|IP α (N₀ α (F_*+g) g) g| ≤ 7·(K₀(C+1)·Pbd α X)`. -/
theorem N0Term_boundT {IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ}
    {α₂ Ct K₀ C C₀ α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn}
    (h : Work.FTS.StrongEps.E4R3.N4C.BlkCtxO IP α₂ Ct K₀ C C₀ α g Φs Φg) :
    |IP α (Work.Construction.N0 α (Work.Construction.Ftot α g) g) g|
      ≤ 7 * (K₀ * (C + 1) * Work.FTS.Nonlin.Pbd α (Work.FTS.Nonlin.Xn α g)) := by
  set N0v := Work.Construction.N0 α (Work.Construction.Ftot α g) g with hN0vdef
  set X := Work.FTS.Nonlin.Xn α g with hXdef
  have hE : N4ExtraH IP α₂ Ct := h.hE
  have hα : 0 < α := h.hα
  have hα1 : α ≤ 1 := h.hα1
  have hαIoc : α ∈ Set.Ioc 0 α₂ := h.hαIoc
  have hCt : 0 < Ct := h.hCt
  have hK₀Ct : Ct ≤ K₀ := h.hK₀Ct
  have hK₀one : 1 ≤ K₀ := h.hK₀one
  have hC : 0 < C := h.hC
  have hR : RowInputsTO IP α C g Φs Φg := h.hR
  have hg4 : HQo α 4 g := BlkCtxO.hg4 h
  have hX0 : 0 ≤ X := by rw [hXdef]; exact Work.Spaces.HkNorm_nonneg α 4 g
  have hPbd0 : 0 ≤ Pbd α X := Pbd_nonneg hα.le hX0
  have g1 : GoodO α (N0fix α) := hR.r1.1
  have g2 : GoodO α (N03g α g) := hR.r2.1
  have g3 : GoodO α (N04aF α g) := hR.r3.1
  have g4 : GoodO α (N04bF α g) := hR.r4.1
  have g5 : GoodO α (N05aF α g) := hR.r5.1
  have g6 : GoodO α (N05bF α g) := hR.r6.1
  have g7 : GoodO α (N06F α g) := hR.r7.1
  have g12' : GoodO α (N0fix α + N03g α g) := goodO_add g1 g2
  have g123' : GoodO α (N0fix α + N03g α g + N04aF α g) := goodO_add g12' g3
  have g1234' : GoodO α (N0fix α + N03g α g + N04aF α g + N04bF α g) := goodO_add g123' g4
  have g12345' : GoodO α (N0fix α + N03g α g + N04aF α g + N04bF α g + N05aF α g) :=
    goodO_add g1234' g5
  have g123456' : GoodO α (N0fix α + N03g α g + N04aF α g + N04bF α g + N05aF α g
      + N05bF α g) := goodO_add g12345' g6
  have gN0sum : GoodO α (N0fix α + N03g α g + N04aF α g + N04bF α g + N05aF α g + N05bF α g
      + N06F α g) := goodO_add g123456' g7
  have hcongr : IP α N0v g = IP α (N0fix α + N03g α g + N04aF α g + N04bF α g
      + N05aF α g + N05bF α g + N06F α g) g := by
    refine hE.congr α hαIoc N0v _ g hR.hkN0 gN0sum hg4 ?_
    intro z θ hzθ
    rw [hN0vdef, hR.hN0 z θ hzθ]
    simp only [Pi.add_apply]
    ring
  have hsum : IP α N0v g = IP α (N0fix α) g + IP α (N03g α g) g + IP α (N04aF α g) g
      + IP α (N04bF α g) g + IP α (N05aF α g) g + IP α (N05bF α g) g
      + IP α (N06F α g) g := by
    rw [hcongr]
    exact IPO_add7 hE hαIoc hg4 g1 g2 g3 g4 g5 g6 g7
      g12' g123' g1234' g12345' g123456'
  have h1 := pieceBdO hE hαIoc hg4 hCt hK₀Ct hX0 hPbd0 hC (N0fix α) (α ^ 2) hR.r1.2
    (alpha_sq_mul_le_Pbd hα hX0) hR.r1.1
  have h2 := pieceBdO hE hαIoc hg4 hCt hK₀Ct hX0 hPbd0 hC (N03g α g) (α ^ (-(1 : ℝ)) * X ^ 2)
    hR.r2.2 (by
      have he : α ^ (-(1 : ℝ)) * X ^ 2 * X = α ^ (-(1 : ℝ)) * X ^ 3 := by ring
      rw [he]; exact rpow_neg_one_mul_cube_le_Pbd hα hα1 hX0) hR.r2.1
  have h3 := pieceBdO hE hαIoc hg4 hCt hK₀Ct hX0 hPbd0 hC (N04aF α g) (Real.sqrt α * X) hR.r3.2
    (by
      have he : Real.sqrt α * X * X = Real.sqrt α * X ^ 2 := by ring
      rw [he]; exact sqrt_mul_sq_le_Pbd hα hX0) hR.r3.1
  have h4 := pieceDirO (N04bF α g) (α ^ (-(3 / 2 : ℝ)) * X ^ 3) hR.r4.2
    (rpow_neg_three_half_mul_cube_le_Pbd hα hX0) hPbd0 hC hK₀one
  have h5 := pieceBdO hE hαIoc hg4 hCt hK₀Ct hX0 hPbd0 hC (N05aF α g) (Real.sqrt α * X) hR.r5.2
    (by
      have he : Real.sqrt α * X * X = Real.sqrt α * X ^ 2 := by ring
      rw [he]; exact sqrt_mul_sq_le_Pbd hα hX0) hR.r5.1
  have h6 := pieceDirO (N05bF α g) (α ^ (-(1 / 2 : ℝ)) * X ^ 3) hR.r6.2
    (rpow_neg_half_mul_cube_le_Pbd hα hα1 hX0) hPbd0 hC hK₀one
  have h7 := pieceDirO (N06F α g) (Real.sqrt α * X ^ 2) hR.r7.2
    (sqrt_mul_sq_le_Pbd hα hX0) hPbd0 hC hK₀one
  have htri : |IP α (N0fix α) g + IP α (N03g α g) g + IP α (N04aF α g) g
      + IP α (N04bF α g) g + IP α (N05aF α g) g + IP α (N05bF α g) g
      + IP α (N06F α g) g|
      ≤ |IP α (N0fix α) g| + |IP α (N03g α g) g| + |IP α (N04aF α g) g|
      + |IP α (N04bF α g) g| + |IP α (N05aF α g) g| + |IP α (N05bF α g) g|
      + |IP α (N06F α g) g| := by
    have h8 := abs_add_le (IP α (N0fix α) g + IP α (N03g α g) g + IP α (N04aF α g) g
      + IP α (N04bF α g) g + IP α (N05aF α g) g + IP α (N05bF α g) g)
      (IP α (N06F α g) g)
    have h9 := Work.Construction.abs_sum_le_five (IP α (N0fix α) g) (IP α (N03g α g) g)
      (IP α (N04aF α g) g) (IP α (N04bF α g) g) (IP α (N05aF α g) g)
    have h10 := abs_add_le (IP α (N0fix α) g + IP α (N03g α g) g + IP α (N04aF α g) g
      + IP α (N04bF α g) g + IP α (N05aF α g) g) (IP α (N05bF α g) g)
    linarith [h8, h9, h10]
  rw [hsum]
  linarith [htri, h1, h2, h3, h4, h5, h6, h7,
    abs_nonneg (IP α (N0fix α) g), abs_nonneg (IP α (N03g α g) g),
    abs_nonneg (IP α (N04aF α g) g), abs_nonneg (IP α (N04bF α g) g),
    abs_nonneg (IP α (N05aF α g) g), abs_nonneg (IP α (N05bF α g) g),
    abs_nonneg (IP α (N06F α g) g)]

end Work.FTS.StrongEps.E4R3.N4C.PairingT
