import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnN0Aux
import Submission.Work.FTS.OpenPkg.wprod_field_winf
import Submission.Work.FTS.OpenPkg.angmul_field
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.GalFields.RHS.sharpN0_defs
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.LocData.HkMem_const_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.ClassCRHS

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-- Negation as a lambda (for rewriting under `Xn`/`HkMem`). -/
private theorem neg_apply_eq (f : ℝ → ℝ → ℝ) : (fun z θ => -f z θ) = -f := rfl

private theorem mem_neg_apply {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (h : Work.Spaces.HkMem α k f) : Work.Spaces.HkMem α k (fun z θ => -f z θ) := by
  rw [neg_apply_eq f]
  exact mem_neg h

private theorem Xn_neg_apply {α : ℝ} (f : ℝ → ℝ → ℝ) :
    Work.FTS.Nonlin.Xn α (fun z θ => -f z θ) = Work.FTS.Nonlin.Xn α f := by
  rw [neg_apply_eq f]
  exact Xn_neg f

/-- The standard nonnegativity of `3/(2α)`. -/
private theorem three_div_two_pos {α : ℝ} (hα : 0 < α) : (0 : ℝ) < 3 / (2 * α) := by positivity

/-! ## The six product rows of the `N₀`-block

Each lemma below proves the `ℋ⁴`-honesty, smoothness and `ℋ⁴`-size of one product piece
`N03g`, `N04aF`, `N04bF`, `N05aF`, `N05bF`, `N06F` of the split, in terms of the universal
product rules (`prod_field`, `wprod_field_winf`) supplied as hypotheses, and of the size bounds
of the factors. -/

/-- **Row 2 of the `N₀`-table**: `N₀₃ᵍ = (1/α)·L₁₂(w)·w`. -/
theorem row_N03g {α Cp C1 : ℝ} {w : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hsmw : Work.FTS.EllipticEst.SmoothOpen w) (hmem4 : Work.Spaces.HkMem α 4 w)
    (hL12sm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.L12 w z))
    (hL12mem : Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 w z))
    (hCp : 0 < Cp) (hC1 : 0 < C1)
    (hL12le : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 w z)
      ≤ C1 * Work.FTS.Nonlin.Xn α w)
    (hprod : ∀ f g : Work.FTS.Galerkin.Fn, Work.FTS.VocabO.HQo α 4 f →
      Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Cp * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N03g α w) ∧
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N03g α w) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N03g α w)
        ≤ (1 / α) * (((Cp * α ^ (-(1 / 2 : ℝ))) * (C1 * Work.FTS.Nonlin.Xn α w))
            * Work.FTS.Nonlin.Xn α w) := by
  have h1α : (0 : ℝ) < 1 / α := by positivity
  have hpα : 0 ≤ Cp * α ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hCp.le (Real.rpow_nonneg hα.le _)
  have hXw0 : 0 ≤ Work.FTS.Nonlin.Xn α w := Work.Spaces.HkNorm_nonneg α 4 w
  have h1eq : Work.FTS.Nonlin.N03g α w
      = fun z θ => (1 / α) * (Work.Construction.L12 w z * w z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N03g, Work.Construction.N03]
    ring
  have hrow := hprod
    (fun z θ => Work.Construction.L12 w z) w ⟨hL12sm, hL12mem⟩ ⟨hsmw, hmem4⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [h1eq]
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (1 / α)
      (Work.FTS.NonlinRows.smoothOpen_mul hL12sm hsmw)
  · rw [h1eq]
    exact Work.FTS.LocData.HkMem_const_mul α 4 (1 / α) hrow.1
  · rw [h1eq, Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul, abs_of_nonneg h1α.le]
    refine mul_le_mul_of_nonneg_left ?_ h1α.le
    exact le_trans hrow.2
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL12le hpα) hXw0)

/-- **Row 3 of the `N₀`-table**: `N₀₄ᵃ = D_θF_* · ((3/(2α))·L₁₂(w))`. -/
theorem row_N04aF {α Cw C1 CF : ℝ} {w : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hL12sm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.L12 w z))
    (hL12mem : Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 w z))
    (hCw : 0 < Cw) (hC1 : 0 < C1) (hCF : 0 < CF)
    (hL12le : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 w z)
      ≤ C1 * Work.FTS.Nonlin.Xn α w)
    (hDthFWmem : Work.Spaces.WlInfMem α 4 (Work.Spaces.Dth (Work.Construction.Fstar α)))
    (hDthFWle : Work.Spaces.WlInf α 4 (Work.Spaces.Dth (Work.Construction.Fstar α))
      ≤ CF * α ^ 2)
    (hWprod : ∀ f g : Work.FTS.Galerkin.Fn, Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.WlInfMem α 4 f → Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Cw * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N04aF α w) ∧
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N04aF α w) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N04aF α w)
        ≤ ((Cw * α ^ (-(1 / 2 : ℝ))) * (CF * α ^ 2))
          * ((3 / (2 * α)) * (C1 * Work.FTS.Nonlin.Xn α w)) := by
  have h32 : (0 : ℝ) < 3 / (2 * α) := three_div_two_pos hα
  have hα2nn : 0 ≤ α ^ 2 := sq_nonneg α
  have hwα : 0 ≤ Cw * α ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hCw.le (Real.rpow_nonneg hα.le _)
  have hDthFsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth (Work.Construction.Fstar α)) :=
    (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α).Dth
  have hAsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (3 / (2 * α)) * Work.Construction.L12 w z) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul (3 / (2 * α)) hL12sm
  have hAmem : Work.Spaces.HkMem α 4 (fun z θ => (3 / (2 * α)) * Work.Construction.L12 w z) :=
    Work.FTS.LocData.HkMem_const_mul α 4 (3 / (2 * α)) hL12mem
  have hAle : Work.FTS.Nonlin.Xn α (fun z θ => (3 / (2 * α)) * Work.Construction.L12 w z)
      ≤ (3 / (2 * α)) * (C1 * Work.FTS.Nonlin.Xn α w) := by
    rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul, abs_of_nonneg h32.le]
    exact mul_le_mul_of_nonneg_left hL12le h32.le
  have h3eq : Work.FTS.Nonlin.N04aF α w
      = fun z θ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ
          * ((3 / (2 * α)) * Work.Construction.L12 w z) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N04aF, Work.Construction.N04a, Work.Construction.s2,
      Work.Spaces.Dth]
    ring
  have hrow := hWprod (Work.Spaces.Dth (Work.Construction.Fstar α))
    (fun z θ => (3 / (2 * α)) * Work.Construction.L12 w z) hDthFsm hDthFWmem ⟨hAsm, hAmem⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [h3eq]
    exact Work.FTS.NonlinRows.smoothOpen_mul hDthFsm hAsm
  · rw [h3eq]; exact hrow.1
  · rw [h3eq]
    refine le_trans hrow.2 ?_
    have hpos : 0 ≤ (Cw * α ^ (-(1 / 2 : ℝ))) * (CF * α ^ 2) :=
      mul_nonneg hwα (mul_nonneg hCF.le hα2nn)
    calc ((Cw * α ^ (-(1 / 2 : ℝ)))
            * Work.Spaces.WlInf α 4 (Work.Spaces.Dth (Work.Construction.Fstar α)))
          * Work.FTS.Nonlin.Xn α (fun z θ => (3 / (2 * α)) * Work.Construction.L12 w z)
        ≤ ((Cw * α ^ (-(1 / 2 : ℝ))) * (CF * α ^ 2))
            * Work.FTS.Nonlin.Xn α
              (fun z θ => (3 / (2 * α)) * Work.Construction.L12 w z) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDthFWle hwα)
            (Work.Spaces.HkNorm_nonneg α 4 _)
      _ ≤ ((Cw * α ^ (-(1 / 2 : ℝ))) * (CF * α ^ 2))
            * ((3 / (2 * α)) * (C1 * Work.FTS.Nonlin.Xn α w)) :=
          mul_le_mul_of_nonneg_left hAle hpos

/-- **Row 4 of the `N₀`-table**: `N₀₄ᵇ = D_θw · ((3/(2α))·L₁₂(w))`. -/
theorem row_N04bF {α Cp C1 Bd : ℝ} {w : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hsmw : Work.FTS.EllipticEst.SmoothOpen w)
    (hL12sm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.L12 w z))
    (hL12mem : Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 w z))
    (hCp : 0 < Cp) (hC1 : 0 < C1)
    (hL12le : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 w z)
      ≤ C1 * Work.FTS.Nonlin.Xn α w)
    (hDthw_mem : Work.Spaces.HkMem α 4 (Work.Spaces.Dth w))
    (hDthw_le : Work.FTS.Nonlin.Xn α (Work.Spaces.Dth w) ≤ Bd) (hBd : 0 ≤ Bd)
    (hprod : ∀ f g : Work.FTS.Galerkin.Fn, Work.FTS.VocabO.HQo α 4 f →
      Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Cp * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N04bF α w) ∧
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N04bF α w) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N04bF α w)
        ≤ ((Cp * α ^ (-(1 / 2 : ℝ))) * Bd)
          * ((3 / (2 * α)) * (C1 * Work.FTS.Nonlin.Xn α w)) := by
  have h32 : (0 : ℝ) < 3 / (2 * α) := three_div_two_pos hα
  have hpα : 0 ≤ Cp * α ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hCp.le (Real.rpow_nonneg hα.le _)
  have hAsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (3 / (2 * α)) * Work.Construction.L12 w z) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul (3 / (2 * α)) hL12sm
  have hAmem : Work.Spaces.HkMem α 4 (fun z θ => (3 / (2 * α)) * Work.Construction.L12 w z) :=
    Work.FTS.LocData.HkMem_const_mul α 4 (3 / (2 * α)) hL12mem
  have hAle : Work.FTS.Nonlin.Xn α (fun z θ => (3 / (2 * α)) * Work.Construction.L12 w z)
      ≤ (3 / (2 * α)) * (C1 * Work.FTS.Nonlin.Xn α w) := by
    rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul, abs_of_nonneg h32.le]
    exact mul_le_mul_of_nonneg_left hL12le h32.le
  have h4eq : Work.FTS.Nonlin.N04bF α w
      = fun z θ => Work.Spaces.Dth w z θ * ((3 / (2 * α)) * Work.Construction.L12 w z) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N04bF, Work.Construction.N04b, Work.Construction.s2,
      Work.Spaces.Dth]
    ring
  have hrow := hprod (Work.Spaces.Dth w) (fun z θ => (3 / (2 * α)) * Work.Construction.L12 w z)
    ⟨hsmw.Dth, hDthw_mem⟩ ⟨hAsm, hAmem⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [h4eq]
    exact Work.FTS.NonlinRows.smoothOpen_mul hsmw.Dth hAsm
  · rw [h4eq]; exact hrow.1
  · rw [h4eq]
    refine le_trans hrow.2 ?_
    have hpos : 0 ≤ (Cp * α ^ (-(1 / 2 : ℝ))) * Bd := mul_nonneg hpα hBd
    calc ((Cp * α ^ (-(1 / 2 : ℝ))) * Work.FTS.Nonlin.Xn α (Work.Spaces.Dth w))
          * Work.FTS.Nonlin.Xn α (fun z θ => (3 / (2 * α)) * Work.Construction.L12 w z)
        ≤ ((Cp * α ^ (-(1 / 2 : ℝ))) * Bd)
            * Work.FTS.Nonlin.Xn α
              (fun z θ => (3 / (2 * α)) * Work.Construction.L12 w z) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDthw_le hpα)
            (Work.Spaces.HkNorm_nonneg α 4 _)
      _ ≤ ((Cp * α ^ (-(1 / 2 : ℝ))) * Bd)
            * ((3 / (2 * α)) * (C1 * Work.FTS.Nonlin.Xn α w)) :=
          mul_le_mul_of_nonneg_left hAle hpos

/-- **Row 5 of the `N₀`-table**: `N₀₅ᵃ = D_zF_* · (-(c2m·L₁₂(w)))`. -/
theorem row_N05aF {α Cw Cdz CB : ℝ} {w : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hBsmt : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z))
    (hBmem : Work.Spaces.HkMem α 4
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z))
    (hBle : Work.FTS.Nonlin.Xn α
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z) ≤ CB) (hCB : 0 ≤ CB)
    (hCw : 0 < Cw) (hCdz : 0 < Cdz)
    (hDzFWmem : Work.Spaces.WlInfMem α 4 (Work.Spaces.Dz (Work.Construction.Fstar α)))
    (hDzFWle : Work.Spaces.WlInf α 4 (Work.Spaces.Dz (Work.Construction.Fstar α))
      ≤ Cdz * α)
    (hWprod : ∀ f g : Work.FTS.Galerkin.Fn, Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.WlInfMem α 4 f → Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Cw * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N05aF α w) ∧
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N05aF α w) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N05aF α w)
        ≤ ((Cw * α ^ (-(1 / 2 : ℝ))) * (Cdz * α)) * CB := by
  have hαnn : 0 ≤ α := hα.le
  have hwα : 0 ≤ Cw * α ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hCw.le (Real.rpow_nonneg hα.le _)
  have hDzFsm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz (Work.Construction.Fstar α)) :=
    (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α).Dz
  have h5sm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => -(Work.Construction.c2m θ * Work.Construction.L12 w z)) := by
    refine (Work.FTS.NonlinRows.smoothOpen_const_mul (-1) hBsmt).congr ?_
    intro z θ _ _ _
    ring
  have h5memg : Work.Spaces.HkMem α 4
      (fun z θ => -(Work.Construction.c2m θ * Work.Construction.L12 w z)) :=
    mem_neg_apply hBmem
  have h5leg : Work.FTS.Nonlin.Xn α
      (fun z θ => -(Work.Construction.c2m θ * Work.Construction.L12 w z)) ≤ CB := by
    rw [Xn_neg_apply]
    exact hBle
  have h5eq : Work.FTS.Nonlin.N05aF α w
      = fun z θ => Work.Spaces.Dz (Work.Construction.Fstar α) z θ
          * (-(Work.Construction.c2m θ * Work.Construction.L12 w z)) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N05aF, Work.Construction.N05a]
    ring
  have hrow := hWprod (Work.Spaces.Dz (Work.Construction.Fstar α))
    (fun z θ => -(Work.Construction.c2m θ * Work.Construction.L12 w z))
    hDzFsm hDzFWmem ⟨h5sm, h5memg⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [h5eq]
    exact Work.FTS.NonlinRows.smoothOpen_mul hDzFsm h5sm
  · rw [h5eq]; exact hrow.1
  · rw [h5eq]
    refine le_trans hrow.2 ?_
    have hpos : 0 ≤ (Cw * α ^ (-(1 / 2 : ℝ))) * (Cdz * α) :=
      mul_nonneg hwα (mul_nonneg hCdz.le hαnn)
    calc ((Cw * α ^ (-(1 / 2 : ℝ)))
            * Work.Spaces.WlInf α 4 (Work.Spaces.Dz (Work.Construction.Fstar α)))
          * Work.FTS.Nonlin.Xn α
            (fun z θ => -(Work.Construction.c2m θ * Work.Construction.L12 w z))
        ≤ ((Cw * α ^ (-(1 / 2 : ℝ))) * (Cdz * α))
            * Work.FTS.Nonlin.Xn α
              (fun z θ => -(Work.Construction.c2m θ * Work.Construction.L12 w z)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDzFWle hwα)
            (Work.Spaces.HkNorm_nonneg α 4 _)
      _ ≤ ((Cw * α ^ (-(1 / 2 : ℝ))) * (Cdz * α)) * CB :=
          mul_le_mul_of_nonneg_left h5leg hpos

/-- **Row 6 of the `N₀`-table**: `N₀₅ᵇ = -((c2m·L₁₂(w)) · D_zw)`. -/
theorem row_N05bF {α Cp CB Bd : ℝ} {w : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hsmw : Work.FTS.EllipticEst.SmoothOpen w)
    (hBsmt : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z))
    (hBmem : Work.Spaces.HkMem α 4
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z))
    (hBle : Work.FTS.Nonlin.Xn α
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z) ≤ CB)
    (hCB : 0 ≤ CB) (hCp : 0 < Cp)
    (hDzw_mem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz w))
    (hDzw_le : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz w) ≤ Bd) (hBd : 0 ≤ Bd)
    (hprod : ∀ f g : Work.FTS.Galerkin.Fn, Work.FTS.VocabO.HQo α 4 f →
      Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Cp * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N05bF α w) ∧
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N05bF α w) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N05bF α w)
        ≤ ((Cp * α ^ (-(1 / 2 : ℝ))) * CB) * Bd := by
  have hpα : 0 ≤ Cp * α ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hCp.le (Real.rpow_nonneg hα.le _)
  have h6eq : Work.FTS.Nonlin.N05bF α w
      = fun z θ => -((Work.Construction.c2m θ * Work.Construction.L12 w z)
          * Work.Spaces.Dz w z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N05bF, Work.Construction.N05b]
    ring
  have h6eq' : Work.FTS.Nonlin.N05bF α w
      = fun z θ => (-(Work.Construction.c2m θ * Work.Construction.L12 w z))
          * Work.Spaces.Dz w z θ := by
    funext z θ
    simp only [Work.FTS.Nonlin.N05bF, Work.Construction.N05b]
    ring
  have hrow := hprod (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z)
    (Work.Spaces.Dz w) ⟨hBsmt, hBmem⟩ ⟨hsmw.Dz, hDzw_mem⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [h6eq']
    exact Work.FTS.NonlinRows.smoothOpen_mul
      ((Work.FTS.NonlinRows.smoothOpen_const_mul (-1) hBsmt).congr (by
        intro z θ _ _ _; ring)) hsmw.Dz
  · rw [h6eq]
    exact mem_neg_apply hrow.1
  · rw [h6eq, Xn_neg_apply]
    refine le_trans hrow.2 ?_
    have hpos : 0 ≤ (Cp * α ^ (-(1 / 2 : ℝ))) * CB := mul_nonneg hpα hCB
    calc ((Cp * α ^ (-(1 / 2 : ℝ))) * Work.FTS.Nonlin.Xn α
            (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z))
          * Work.FTS.Nonlin.Xn α (Work.Spaces.Dz w)
        ≤ ((Cp * α ^ (-(1 / 2 : ℝ))) * CB) * Work.FTS.Nonlin.Xn α (Work.Spaces.Dz w) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBle hpα)
            (Work.Spaces.HkNorm_nonneg α 4 _)
      _ ≤ ((Cp * α ^ (-(1 / 2 : ℝ))) * CB) * Bd :=
          mul_le_mul_of_nonneg_left hDzw_le hpos

/-- **Row 7 of the `N₀`-table**: `N₀₆ = -((c2m·L₁₂(F_*)) · D_zw)`. -/
theorem row_N06F {α Cw Cw0 Bd : ℝ} {w : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hsmw : Work.FTS.EllipticEst.SmoothOpen w)
    (hDzw_mem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz w))
    (hDzw_le : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz w) ≤ Bd) (hBd : 0 ≤ Bd)
    (hc2mL12Fsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z))
    (hc2mL12FWmem : Work.Spaces.WlInfMem α 4
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z))
    (hc2mL12FWle : Work.Spaces.WlInf α 4
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z)
      ≤ Cw0 * α)
    (hCw : 0 < Cw) (hCw0 : 0 < Cw0)
    (hWprod : ∀ f g : Work.FTS.Galerkin.Fn, Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.WlInfMem α 4 f → Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Cw * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N06F α w) ∧
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N06F α w) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N06F α w)
        ≤ ((Cw * α ^ (-(1 / 2 : ℝ))) * (Cw0 * α)) * Bd := by
  have hαnn : 0 ≤ α := hα.le
  have hwα : 0 ≤ Cw * α ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hCw.le (Real.rpow_nonneg hα.le _)
  have h7eq : Work.FTS.Nonlin.N06F α w
      = fun z θ => -((Work.Construction.c2m θ
          * Work.Construction.L12 (Work.Construction.Fstar α) z)
          * Work.Spaces.Dz w z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N06F, Work.Construction.N06]
    ring
  have h7eq' : Work.FTS.Nonlin.N06F α w
      = fun z θ => (-(Work.Construction.c2m θ
          * Work.Construction.L12 (Work.Construction.Fstar α) z))
          * Work.Spaces.Dz w z θ := by
    funext z θ
    simp only [Work.FTS.Nonlin.N06F, Work.Construction.N06]
    ring
  have hrow := hWprod
    (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z)
    (Work.Spaces.Dz w) hc2mL12Fsm hc2mL12FWmem ⟨hsmw.Dz, hDzw_mem⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [h7eq']
    exact Work.FTS.NonlinRows.smoothOpen_mul
      ((Work.FTS.NonlinRows.smoothOpen_const_mul (-1) hc2mL12Fsm).congr (by
        intro z θ _ _ _; ring)) hsmw.Dz
  · rw [h7eq]
    exact mem_neg_apply hrow.1
  · rw [h7eq, Xn_neg_apply]
    refine le_trans hrow.2 ?_
    have hpos : 0 ≤ (Cw * α ^ (-(1 / 2 : ℝ))) * (Cw0 * α) :=
      mul_nonneg hwα (mul_nonneg hCw0.le hαnn)
    calc ((Cw * α ^ (-(1 / 2 : ℝ))) * Work.Spaces.WlInf α 4
            (fun z θ => Work.Construction.c2m θ
              * Work.Construction.L12 (Work.Construction.Fstar α) z))
          * Work.FTS.Nonlin.Xn α (Work.Spaces.Dz w)
        ≤ ((Cw * α ^ (-(1 / 2 : ℝ))) * (Cw0 * α)) * Work.FTS.Nonlin.Xn α (Work.Spaces.Dz w) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc2mL12FWle hwα)
            (Work.Spaces.HkNorm_nonneg α 4 _)
      _ ≤ ((Cw * α ^ (-(1 / 2 : ℝ))) * (Cw0 * α)) * Bd :=
          mul_le_mul_of_nonneg_left hDzw_le hpos

end Work.FTS.StrongEps.ClassCRHS
