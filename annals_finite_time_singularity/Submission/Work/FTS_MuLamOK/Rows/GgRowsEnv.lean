/-
# `GgRowsEnv` — the three `gg`-rows priced against `Env` in the honest (open) class

The `gg`-pieces `N₁^{gg}`, `N₂^{gg}`, `N₃^{gg}` of the `N`-split, priced against the standard
envelope `Env α f = α² + √α·|f|_{ℋ⁴} + α^{-3/2}·|f|²_{ℋ⁴}` of the `rl1` estimate, for the honest
open-quadrant class

  `SmoothOpen f` + `HkMem α 4 f` + `EllPkgGo α Ce f Ξg`.

The three rows themselves are the *proved* theorems
`RowMuAux.OpenRows.row1GGopen`, `row2GGopen`, `row3GGopen`; each of them takes, besides the honest
class, the angular Agmon bound of its coefficient `A` (`A = ℛ`, `𝒰/sin 2θ`, `𝒱`), which
`Work.FTS.NonlinRows.Rl1.angSup_le` (`= angSupHk`) supplies from `HQo α 4 A` — and `EllPkgGo`
supplies exactly `HQo α 4 A` (`hEll.R`, `hEll.U`, `hEll.V`), with `PhiTg = PhiTil` definitionally.

The row conclusion is

  `Fa (N_i^{gg}) ≤ ofReal (√(C_A/(γ-1)) · √(π/2) · c_i · max Ce 0 · |f|²_{ℋ⁴})`

with `c₁ = c₂ = 6`, `c₃ = 6α` and `C_A ≥ 0` the Agmon constant.  Since `γ - 1 = α/10`
(`Spaces.gam_sub_one`),

  `√(C_A/(γ-1)) = √(10·C_A)·α^{-1/2}`,

and `α^{-1/2}·c_i ≤ 2·α^{-3/2}` for `0 < α ≤ 1` (`c_i ≤ 2`), so the common constant

  `K = 6·√(π/2)·√(10·C_A)·max Ce 0 + 1`

works: it absorbs `2·α^{-3/2}|f|²_{ℋ⁴} ≤ 2·Env α f` and the leftover `+1` covers the degenerate
case `max Ce 0 = 0` (where the rows give the trivial constant `0`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.OpenRows.row1GGopen
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.OpenRows.row2GGopen
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.OpenRows.row3GGopen
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.SlotDataOpen
import Submission.Work.FTS.NonlinRows.Rl1.tools

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_MuLamOK.Rows

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlinear.Pieces (Fa)

/-! ## The arithmetic of the row constants -/

/-- `√(C_A/(γ-1)) = √(10·C_A)·α^{-1/2}` (`γ - 1 = α/10`). -/
private theorem sqrt_div_gam_gg {CA α : ℝ} (hCA : 0 ≤ CA) (hα : 0 < α) :
    Real.sqrt (CA / (Work.Spaces.gam α - 1)) = Real.sqrt (10 * CA) * α ^ (-(1 / 2 : ℝ)) := by
  have hγ : Work.Spaces.gam α - 1 = α / 10 := Work.Spaces.gam_sub_one α
  have h10 : (0 : ℝ) ≤ 10 * CA := by linarith
  have hsq : (Real.sqrt (10 * CA) * α ^ (-(1 / 2 : ℝ))) ^ 2 = CA / (Work.Spaces.gam α - 1) := by
    rw [mul_pow, Real.sq_sqrt h10, ← Real.rpow_two, ← Real.rpow_mul hα.le,
      show -(1 / 2 : ℝ) * 2 = -1 by norm_num, Real.rpow_neg_one, hγ]
    field_simp
  rw [← hsq, Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hα.le _))]

/-- **The row constant is dominated by `Env`.**  For `0 < α ≤ 1`, `C_A, B ≥ 0` and `0 ≤ c ≤ 2`,
the row expression `√(C_A/(γ-1))·3√(π/2)·c·B·|g|²_{ℋ⁴}` is at most
`(6·√(π/2)·√(10·C_A)·B + 1)·Env α g` (because `α^{-1/2}·c ≤ 2·α^{-3/2}` and
`α^{-3/2}·|g|²_{ℋ⁴} ≤ Env α g`). -/
private theorem rowConstLe_gg {α CA B c : ℝ} {g : Fn} (hCA : 0 ≤ CA) (hB : 0 ≤ B)
    (hc : 0 ≤ c) (hc2 : c ≤ 2) (hα : 0 < α) (hα1 : α ≤ 1) :
    Real.sqrt (CA / (Work.Spaces.gam α - 1)) * (3 * Real.sqrt (Real.pi / 2)) * c * B
        * (Work.FTS.Nonlin.Xn α g) ^ 2
      ≤ (6 * Real.sqrt (Real.pi / 2) * Real.sqrt (10 * CA) * B + 1)
        * Work.FTS.NonlinRows.Rl1.Env α g := by
  have hX : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hX2 : 0 ≤ (Work.FTS.Nonlin.Xn α g) ^ 2 := sq_nonneg _
  have hEnv : 0 ≤ Work.FTS.NonlinRows.Rl1.Env α g :=
    Work.FTS.NonlinRows.Rl1.Env_nonneg g hα.le
  have hp3 : 0 ≤ α ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  -- `α^{-1/2} ≤ α^{-3/2}`
  have hpow : α ^ (-(1 / 2 : ℝ)) ≤ α ^ (-(3 / 2 : ℝ)) := by
    have h1 : α ^ (-(3 / 2 : ℝ)) = α ^ (-(1 / 2 : ℝ)) * α ^ (-(1 : ℝ)) := by
      rw [← Real.rpow_add hα]
      congr 1
      norm_num
    rw [h1]
    have h2 : 1 ≤ α ^ (-(1 : ℝ)) := by
      rw [Real.rpow_neg_one]
      simpa only [one_div] using one_le_one_div hα hα1
    have h3 : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
    nlinarith
  have h0 : 0 ≤ 6 * Real.sqrt (Real.pi / 2) * Real.sqrt (10 * CA) * B :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)) hB
  have hpos : 0 ≤ Real.sqrt (10 * CA) * (3 * Real.sqrt (Real.pi / 2)) * B
      * (Work.FTS.Nonlin.Xn α g) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))) hB) hX2
  have hstep1 : α ^ (-(1 / 2 : ℝ)) * c ≤ 2 * α ^ (-(3 / 2 : ℝ)) := by
    have h := mul_le_mul hpow hc2 hc hp3
    linarith [h]
  -- `α^{-3/2}·|g|² ≤ Env`
  have hEnvge : α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α g) ^ 2
      ≤ Work.FTS.NonlinRows.Rl1.Env α g := by
    rw [Work.FTS.NonlinRows.Rl1.Env]
    have h1 : 0 ≤ α ^ 2 := sq_nonneg α
    have h2 : 0 ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α g :=
      mul_nonneg (Real.sqrt_nonneg α) hX
    linarith
  rw [sqrt_div_gam_gg hCA hα]
  have h1 : Real.sqrt (10 * CA) * α ^ (-(1 / 2 : ℝ)) * (3 * Real.sqrt (Real.pi / 2)) * c * B
        * (Work.FTS.Nonlin.Xn α g) ^ 2
      = (Real.sqrt (10 * CA) * (3 * Real.sqrt (Real.pi / 2)) * B
          * (Work.FTS.Nonlin.Xn α g) ^ 2) * (α ^ (-(1 / 2 : ℝ)) * c) := by ring
  rw [h1]
  have h2 : (Real.sqrt (10 * CA) * (3 * Real.sqrt (Real.pi / 2)) * B
        * (Work.FTS.Nonlin.Xn α g) ^ 2) * (α ^ (-(1 / 2 : ℝ)) * c)
      ≤ (Real.sqrt (10 * CA) * (3 * Real.sqrt (Real.pi / 2)) * B
        * (Work.FTS.Nonlin.Xn α g) ^ 2) * (2 * α ^ (-(3 / 2 : ℝ))) :=
    mul_le_mul_of_nonneg_left hstep1 hpos
  have h3 : (Real.sqrt (10 * CA) * (3 * Real.sqrt (Real.pi / 2)) * B
        * (Work.FTS.Nonlin.Xn α g) ^ 2) * (2 * α ^ (-(3 / 2 : ℝ)))
      = 6 * Real.sqrt (Real.pi / 2) * Real.sqrt (10 * CA) * B
        * (α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α g) ^ 2) := by ring
  have h4 : 6 * Real.sqrt (Real.pi / 2) * Real.sqrt (10 * CA) * B
        * (α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α g) ^ 2)
      ≤ 6 * Real.sqrt (Real.pi / 2) * Real.sqrt (10 * CA) * B
        * Work.FTS.NonlinRows.Rl1.Env α g :=
    mul_le_mul_of_nonneg_left hEnvge h0
  have h5 : 6 * Real.sqrt (Real.pi / 2) * Real.sqrt (10 * CA) * B
        * Work.FTS.NonlinRows.Rl1.Env α g
      ≤ (6 * Real.sqrt (Real.pi / 2) * Real.sqrt (10 * CA) * B + 1)
        * Work.FTS.NonlinRows.Rl1.Env α g := by
    nlinarith [hEnv]
  exact le_trans h2 (le_trans (le_of_eq h3) (le_trans h4 h5))

/-! ## The three rows against `Env` -/

theorem GgRowsEnv (Ce : ℝ) : ∃ K : ℝ, 0 < K ∧
    ∀ {α : ℝ} {f Ξg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
      Work.FTS.VocabO.EllPkgGo α Ce f Ξg →
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N1gg α f Ξg)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α f) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N2gg α f Ξg)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α f) ∧
      Work.FTS.Nonlinear.Pieces.Fa (Work.FTS.Nonlin.N3gg α f Ξg)
        ≤ ENNReal.ofReal (K * Work.FTS.NonlinRows.Rl1.Env α f) := by
  obtain ⟨CA, hCA, hang⟩ := Work.FTS.NonlinRows.Rl1.angSup_le
  refine ⟨6 * Real.sqrt (Real.pi / 2) * Real.sqrt (10 * CA) * max Ce 0 + 1, ?_, ?_⟩
  · have h : 0 ≤ 6 * Real.sqrt (Real.pi / 2) * Real.sqrt (10 * CA) * max Ce 0 :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)) (le_max_right Ce 0)
    linarith
  intro α f Ξg hα hα1 hso hmem hEll
  have hB0 : 0 ≤ max Ce 0 := le_max_right Ce 0
  -- the two row constants, dominated by `Env`
  have hrc12 := rowConstLe_gg (α := α) (CA := CA) (B := max Ce 0) (c := 2) (g := f)
    hCA.le hB0 (by norm_num) (by norm_num) hα hα1
  have hrc3 := rowConstLe_gg (α := α) (CA := CA) (B := max Ce 0) (c := 2 * α) (g := f)
    hCA.le hB0 (by positivity) (by linarith) hα hα1
  refine ⟨?_, ?_, ?_⟩
  · have h1 := Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.OpenRows.row1GGopen (CA := CA) hCA
      (α := α) (Ce := Ce) hα hso hmem hEll
      (fun z θ hz hθ0 hθ1 =>
        hang α (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α f Ξg)) hα hα1
          hEll.R.1.1 hEll.R.1.2 z θ hz hθ0 hθ1)
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have heq : Real.sqrt (CA / (Work.Spaces.gam α - 1)) * (3 * Real.sqrt (Real.pi / 2)) * 2
          * max Ce 0 * (Work.FTS.Nonlin.Xn α f) ^ 2
        = Real.sqrt (CA / (Work.Spaces.gam α - 1)) * Real.sqrt (Real.pi / 2) * 6
          * max Ce 0 * (Work.FTS.Nonlin.Xn α f) ^ 2 := by ring
    rw [← heq]
    exact hrc12
  · have h2 := Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.OpenRows.row2GGopen (CA := CA) hCA
      (α := α) (Ce := Ce) hα hso hmem hEll
      (fun z θ hz hθ0 hθ1 =>
        hang α (fun z θ => Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α f Ξg) z θ
            / Work.Construction.s2 θ) hα hα1 hEll.U.1.1 hEll.U.1.2 z θ hz hθ0 hθ1)
    refine h2.trans (ENNReal.ofReal_le_ofReal ?_)
    have heq : Real.sqrt (CA / (Work.Spaces.gam α - 1)) * (3 * Real.sqrt (Real.pi / 2)) * 2
          * max Ce 0 * (Work.FTS.Nonlin.Xn α f) ^ 2
        = Real.sqrt (CA / (Work.Spaces.gam α - 1)) * Real.sqrt (Real.pi / 2) * 6
          * max Ce 0 * (Work.FTS.Nonlin.Xn α f) ^ 2 := by ring
    rw [← heq]
    exact hrc12
  · have h3 := Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.OpenRows.row3GGopen (CA := CA) hCA
      (α := α) (Ce := Ce) hα hso hmem hEll
      (fun z θ hz hθ0 hθ1 =>
        hang α (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α f Ξg)) hα hα1
          hEll.V.1.1 hEll.V.1.2 z θ hz hθ0 hθ1)
    refine h3.trans (ENNReal.ofReal_le_ofReal ?_)
    have heq : Real.sqrt (CA / (Work.Spaces.gam α - 1)) * (3 * Real.sqrt (Real.pi / 2)) * (2 * α)
          * max Ce 0 * (Work.FTS.Nonlin.Xn α f) ^ 2
        = Real.sqrt (CA / (Work.Spaces.gam α - 1)) * Real.sqrt (Real.pi / 2) * (6 * α)
          * max Ce 0 * (Work.FTS.Nonlin.Xn α f) ^ 2 := by ring
    rw [← heq]
    exact hrc3

end

end Work.FTS_MuLamOK.Rows
