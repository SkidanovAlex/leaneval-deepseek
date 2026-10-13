/-
# N4 — the row groups and the glue from the rows to `RowInputs`

This module splits the 26 per-piece estimates of design §3.4 (plus the `AK` bound `rak` and the
three zero-mode estimates `rl0`/`rl1`/`rl2` of §3.5) into three structures — `N0Rows` (rows
1--7), `NRows` (rows 8--26) and `AuxRows` (`rak`, `rl0`, `rl1`, `rl2`) — carrying a *single*
constant `K`, and proves the **glue** `rowInputs_of_parts`: from the three groups (with
constants `K₁`, `K₂`, `K₃`), the three exact splits of `N₀`, `N` and `N_*`, and the inequality
`max K₁ (max K₂ K₃) ≤ C`, the full `RowInputs IP α C g Φs Φg` of the assembly follows.

The row groups themselves are proved in

* `Submission/Work/FTS/Nonlinear/Pieces/rowsN0.lean` (rows 1--7),
* `Submission/Work/FTS/Nonlinear/Pieces/rowsN.lean` (rows 8--26),
* `Submission/Work/FTS/Nonlinear/Pieces/rowsAux.lean` (`rak`, `rl0`--`rl2`),

each as `∃ K > 0, ∀ {α g Φs Φg}, <context> → <rows with K>` with `K` **independent of
`α, g, Φs, Φg`** (it may depend on `IP, α₂, Ci, Ct, Ce, Cs`), which is what the a-priori
bootstrap of N5 needs: `pairing_bound` needs one constant `C₀` uniform in `α, g, Φs, Φg`.

The three splits are supplied by `Pieces/splitsDiff.splits_of_diff` (proved) from
`Pieces/L12FK_add_ge0.L12FK_add_ge0` (proved) and the differentiability field
`N4Norm.l12diff`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Nonlinear.Pieces.Ctx
import Submission.Work.FTS.Nonlinear.RowInputs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology

namespace Work.FTS.Nonlinear.Pieces

open Work.FTS.Galerkin (Fn Fam slice galFun galField coeffOf IsSolOn IsGalFam ConvLocUnif
  muDyn lamDyn dynLin dynRHS)
open Work.FTS.Nonlin

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **Rows 1--7** of design §3.4: the `N₀`-block, with a single constant `K`. -/
structure N0Rows (IP : ℝ → Fn → Fn → ℝ) (α K : ℝ) (g Φs Φg : Fn) : Prop where
  /-- row 1: `|N₀₁+N₀₂|_{ℋ⁴} ≤ Kα²` (tex 1398--1402) -/
  r1 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N0fix α) ≤ K * α ^ 2
  /-- row 2: `|N₀₃|_{ℋ⁴} ≤ Kα^{-1}X²` (tex 1404--1406) -/
  r2 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N03g α g)
    ≤ K * (α ^ (-(1 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2)
  /-- row 3: `|N₀₄ᵃ|_{ℋ⁴} ≤ K√α X` (tex 1410--1412) -/
  r3 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N04aF α g)
    ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g)
  /-- row 4: `|(N₀₄ᵇ, g)| ≤ Kα^{-3/2}X³` (tex 1414) -/
  r4 : |IP α (Work.FTS.Nonlin.N04bF α g) g|
    ≤ K * (α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3)
  /-- row 5: `|N₀₅ᵃ|_{ℋ⁴} ≤ K√α X` (tex 1416--1418) -/
  r5 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N05aF α g)
    ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g)
  /-- row 6: `|(N₀₅ᵇ, g)| ≤ Kα^{-1/2}X³` (tex 1419) -/
  r6 : |IP α (Work.FTS.Nonlin.N05bF α g) g|
    ≤ K * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3)
  /-- row 7: `|(N₀₆, g)| ≤ K√α X²` (tex 1421--1423) -/
  r7 : |IP α (Work.FTS.Nonlin.N06F α g) g|
    ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2)

/-- **Rows 8--26** of design §3.4: the `N`-block (the four-way split of `N₁, …, N₅`). -/
structure NRows (IP : ℝ → Fn → Fn → ℝ) (α K : ℝ) (g Φs Φg : Fn) : Prop where
  r8 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1gg α g Φg)
    ≤ K * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2)
  r9 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1gs α g Φg)
    ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g)
  r10 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1sg α Φs g)
    ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g)
  r11 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N1ss α Φs) ≤ K * α ^ 2
  r12 : |IP α (Work.FTS.Nonlin.N2gg α g Φg) g|
    ≤ K * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3)
  r13 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N2gs α g Φg)
    ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g)
  r14 : |IP α (Work.FTS.Nonlin.N2sg α Φs g) g|
    ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2)
  r15 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N2ss α Φs) ≤ K * α ^ 2
  r16 : |IP α (Work.FTS.Nonlin.N3gg α g Φg) g|
    ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 3)
  r17 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N3gs α g Φg)
    ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g)
  r18 : |IP α (Work.FTS.Nonlin.N3sg α Φs g) g|
    ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g ^ 2)
  r19 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N3ss α Φs) ≤ K * α ^ 3
  r20 : |IP α (Work.FTS.Nonlin.N4gg α g) g|
    ≤ K * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3)
  r21 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N4gs α g)
    ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g)
  r22 : |IP α (Work.FTS.Nonlin.N4sg α g) g|
    ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2)
  r23 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N4ss α) ≤ K * α ^ 3
  r24 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5gg g) ≤ K * Work.FTS.Nonlin.Xn α g ^ 2
  r25 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5gs α g)
      + Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5sg α g)
    ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g)
  r26 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5ss α) ≤ K * α ^ 2

/-- **The auxiliary rows**: the `ℋ⁴`-bound of `AK` (`rak`) and the three zero-mode estimates
`rl0`--`rl2` of design §3.5 (`L-N4.6`), with a single constant `K`. -/
structure AuxRows (IP : ℝ → Fn → Fn → ℝ) (α K : ℝ) (g Φs Φg : Fn) : Prop where
  /-- the `ℋ⁴`-bound of `AK` (design §3.2) -/
  rak : Work.FTS.Nonlin.Xn α (Work.Construction.AK α) ≤ K
  /-- `L-N4.6`: `|L₁₂(N₀)(0)| ≤ K(α² + √α X + α^{-3/2}X²)` -/
  rl0 : |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α g) g) 0|
    ≤ K * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
      + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2)
  /-- `L-N4.6`: `|L₁₂(N)(0)| ≤ K(α² + √α X + α^{-3/2}X²)` -/
  rl1 : |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + Φg z θ)) 0|
    ≤ K * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
      + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2)
  /-- `L-N4.6`: `|L₁₂(3D_θg/(1+z))(0)| ≤ K X` (tex 1517--1521) -/
  rl2 : |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0|
    ≤ K * Work.FTS.Nonlin.Xn α g

/-! ## The glue -/

/-- **From the three row groups and the three splits to `RowInputs`.**

`C` is the single constant of `RowInputs`; it is required to dominate the three group
constants.  All the bookkeeping is a direct reshuffling of the fields. -/
theorem rowInputs_of_parts {IP : ℝ → Fn → Fn → ℝ}
    {α₂ Ci Ct Ce Cs C K₁ K₂ K₃ α : ℝ} {g Φs Φg : Fn}
    (hctx : Work.FTS.Nonlin.RowCtx IP α₂ Ci Ct Ce Cs α g Φs Φg)
    (h1 : N0Rows IP α K₁ g Φs Φg) (h2 : NRows IP α K₂ g Φs Φg)
    (h3 : AuxRows IP α K₃ g Φs Φg)
    (hK1 : K₁ ≤ C) (hK2 : K₂ ≤ C) (hK3 : K₃ ≤ C)
    (hspl0 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.N0 α (Work.Construction.Ftot α g) g z θ
        = Work.FTS.Nonlin.N0fix α z θ + (Work.FTS.Nonlin.N03g α g z θ
            + Work.FTS.Nonlin.N04aF α g z θ + Work.FTS.Nonlin.N04bF α g z θ
            + Work.FTS.Nonlin.N05aF α g z θ + Work.FTS.Nonlin.N05bF α g z θ
            + Work.FTS.Nonlin.N06F α g z θ))
    (hspl : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.N α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) z θ
        = (Work.FTS.Nonlin.N1gg α g Φg z θ + Work.FTS.Nonlin.N1gs α g Φg z θ
            + Work.FTS.Nonlin.N1sg α Φs g z θ + Work.FTS.Nonlin.N1ss α Φs z θ)
          + (Work.FTS.Nonlin.N2gg α g Φg z θ + Work.FTS.Nonlin.N2gs α g Φg z θ
            + Work.FTS.Nonlin.N2sg α Φs g z θ + Work.FTS.Nonlin.N2ss α Φs z θ)
          + (Work.FTS.Nonlin.N3gg α g Φg z θ + Work.FTS.Nonlin.N3gs α g Φg z θ
            + Work.FTS.Nonlin.N3sg α Φs g z θ + Work.FTS.Nonlin.N3ss α Φs z θ)
          + (Work.FTS.Nonlin.N4gg α g z θ + Work.FTS.Nonlin.N4gs α g z θ
            + Work.FTS.Nonlin.N4sg α g z θ + Work.FTS.Nonlin.N4ss α z θ)
          + (Work.FTS.Nonlin.N5gg g z θ + Work.FTS.Nonlin.N5gs α g z θ
            + Work.FTS.Nonlin.N5sg α g z θ + Work.FTS.Nonlin.N5ss α z θ))
    (hNs : ∀ μ : ℝ, μ ≠ -1 → ∀ z θ,
      Work.Construction.Nstar μ (Work.Construction.lamfun μ) g z θ
        = Work.FTS.Nonlin.NstarLam μ g z θ) :
    Work.FTS.Nonlin.RowInputs IP α C g Φs Φg := by
  have hα0 : (0 : ℝ) ≤ α := hctx.hα.le
  have hX0 : (0 : ℝ) ≤ Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hsq : (0 : ℝ) ≤ Real.sqrt α := Real.sqrt_nonneg α
  have hX2 : (0 : ℝ) ≤ Xn α g ^ 2 := pow_nonneg hX0 2
  have hX3 : (0 : ℝ) ≤ Xn α g ^ 3 := pow_nonneg hX0 3
  have hr1 : (0 : ℝ) ≤ α ^ (-(1 : ℝ)) := Real.rpow_nonneg hα0 _
  have hr12 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα0 _
  have hr32 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hα0 _
  have h3h : (0 : ℝ) ≤ α ^ (3 / 2 : ℝ) := Real.rpow_nonneg hα0 _
  refine
    { reg4 := hctx.reg4
      r1 := le_trans h1.r1 (mul_le_mul_of_nonneg_right hK1 (pow_nonneg hα0 2))
      r2 := le_trans h1.r2 (mul_le_mul_of_nonneg_right hK1 (mul_nonneg hr1 hX2))
      r3 := le_trans h1.r3 (mul_le_mul_of_nonneg_right hK1 (mul_nonneg hsq hX0))
      r4 := le_trans h1.r4 (mul_le_mul_of_nonneg_right hK1 (mul_nonneg hr32 hX3))
      r5 := le_trans h1.r5 (mul_le_mul_of_nonneg_right hK1 (mul_nonneg hsq hX0))
      r6 := le_trans h1.r6 (mul_le_mul_of_nonneg_right hK1 (mul_nonneg hr12 hX3))
      r7 := le_trans h1.r7 (mul_le_mul_of_nonneg_right hK1 (mul_nonneg hsq hX2))
      r8 := le_trans h2.r8 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg hr12 hX2))
      r9 := le_trans h2.r9 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg hsq hX0))
      r10 := le_trans h2.r10 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg hsq hX0))
      r11 := le_trans h2.r11 (mul_le_mul_of_nonneg_right hK2 (pow_nonneg hα0 2))
      r12 := le_trans h2.r12 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg hr12 hX3))
      r13 := le_trans h2.r13 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg h3h hX0))
      r14 := le_trans h2.r14 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg hsq hX2))
      r15 := le_trans h2.r15 (mul_le_mul_of_nonneg_right hK2 (pow_nonneg hα0 2))
      r16 := le_trans h2.r16 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg hsq hX3))
      r17 := le_trans h2.r17 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg h3h hX0))
      r18 := le_trans h2.r18 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg h3h hX2))
      r19 := le_trans h2.r19 (mul_le_mul_of_nonneg_right hK2 (pow_nonneg hα0 3))
      r20 := le_trans h2.r20 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg hr12 hX3))
      r21 := le_trans h2.r21 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg h3h hX0))
      r22 := le_trans h2.r22 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg hsq hX2))
      r23 := le_trans h2.r23 (mul_le_mul_of_nonneg_right hK2 (pow_nonneg hα0 3))
      r24 := le_trans h2.r24 (mul_le_mul_of_nonneg_right hK2 hX2)
      r25 := le_trans h2.r25 (mul_le_mul_of_nonneg_right hK2 (mul_nonneg hsq hX0))
      r26 := le_trans h2.r26 (mul_le_mul_of_nonneg_right hK2 (pow_nonneg hα0 2))
      rak := le_trans h3.rak hK3
      rl0 := le_trans h3.rl0
        (mul_le_mul_of_nonneg_right hK3 (by positivity))
      rl1 := le_trans h3.rl1
        (mul_le_mul_of_nonneg_right hK3 (by positivity))
      rl2 := le_trans h3.rl2 (mul_le_mul_of_nonneg_right hK3 hX0)
      hN0 := hspl0
      hN := hspl
      hNs := hNs }

end Work.FTS.Nonlinear.Pieces
