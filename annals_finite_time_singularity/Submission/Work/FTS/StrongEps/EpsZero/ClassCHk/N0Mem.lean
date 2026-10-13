/-
# `N0Mem` — the `ℋ⁴`-honesty of the `N₀`-block of the `g`-equation for class-`C` data

This module proves

  `Work.Spaces.HkMem α 4 (Construction.N0 α (Construction.Ftot α w) w)`

from the linear class `ClassC α w` alone.  (`N₀` does not involve the stream function `Φ`, so
the elliptic package hypothesis `EllPkgGo α Ce w Φg` is not used.)

The route is the seven-row split of `N₀` on the open quadrant
(`StrongEps.ClassCRHS.N0_split_open`):

  `N₀ α (F_*+w) w = N0fix α + (N03g α w + (N04aF α w + (N04bF α w
      + (N05aF α w + (N05bF α w + N06F α w)))))`,

each row being a product of two `ℋ⁴`-honest factors:

* `N0fix` is the `F_*`-only block (`NonlinRows.HkMem_N0fix`);
* `N03g  α w = (1/α)·(L₁₂(w)·w)`: both factors are `HQo α 4` (`l12H_field`, `ClassC.mem`),
  multiplied by `OpenPkg.prod_field`;
* `N04aF α w = D_θF_* · (3/(2α))L₁₂(w)`: `D_θF_*` is `𝒲^{4,∞}` (`FstarPkg.DthFstar_W`) and
  the second factor is `HQo α 4`, so `OpenPkg.wprod_field_winf` applies;
* `N04bF α w = D_θw · (3/(2α))L₁₂(w)`: `prod_field` again (`D_θw ∈ ℋ⁴` by
  `hkMem_Dth_of_smoothOpen`);
* `N05aF α w = D_zF_* · (-(c2m·L₁₂(w)))`, `N05bF α w = -(c2m·L₁₂(w)·D_zw)`: `c2m·L₁₂(w) ∈ ℋ⁴`
  by the angular multiplication rule `OpenPkg.angmul_field`;
* `N06F  α w = -(c2m·L₁₂(F_*)·D_zw)`: `c2m·L₁₂(F_*) ∈ 𝒲^{4,∞}` (`FstarPkg.c2m_L12Fstar_W`).

The rows are glued with `OpenPkg.HkMem_add_of_contDiffOn_four` and transferred from the open
quadrant to the closed domain with `EllipticEst.Cert.GbarSin.HkMem_congr_Q0`.

All the ingredients are used only through their *membership* conjuncts; no smallness or size
bound on `w` (such as `Xn α w ≤ C₀α²`) is needed.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.StrongEps.ClassCRHS.N0_split_open
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnN0Aux
import Submission.Work.FTS.OpenPkg.prod_field
import Submission.Work.FTS.OpenPkg.wprod_field_winf
import Submission.Work.FTS.OpenPkg.angmul_field
import Submission.Work.FTS.OpenPkg.l12H_field
import Submission.Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.EllipticEst.UopHk.hkMemDzPth_of_shifted
import Submission.Work.FTS.NonlinRows.NRow1
import Submission.Work.FTS.NonlinRows.NRow1_7Aux
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Pieces.Basic
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsN0FixBlock
import Submission.Work.FTS.GalFields.RHS.sharpN0_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsZero.ClassCHk

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

theorem N0Mem {α Ce : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {w Φg : Work.FTS.Galerkin.Fn} (hw : Work.FTS.ClassC.ClassC α w)
    (hell : Work.FTS.VocabO.EllPkgGo α Ce w Φg) :
    Work.Spaces.HkMem α 4 (Work.Construction.N0 α (Work.Construction.Ftot α w) w) := by
  -- `N₀` only involves `w` and `F_*`; the elliptic package `hell` is not needed.
  have _hell := hell
  -- ## the universal constants of the product rules
  obtain ⟨Cp, _hCppos, hprod⟩ := Work.FTS.OpenPkg.prod_field
  obtain ⟨Cw, _hCwpos, hwprod⟩ := Work.FTS.OpenPkg.wprod_field_winf
  obtain ⟨Cang, _hCangpos, hang⟩ := Work.FTS.OpenPkg.angmul_field
  obtain ⟨C1, _hC1pos, hl12⟩ := Work.FTS.OpenPkg.l12H_field
  obtain ⟨_CF, _hCFpos, hFstarW⟩ := Work.FTS.Nonlinear.FstarPkg.DthFstar_W
  obtain ⟨_Cdz, _hCdzpos, hDzFstarW⟩ := Work.FTS.Nonlinear.FstarPkg.DzFstar_W
  obtain ⟨_Cw0, _hCw0pos, hc2mL12FstarW⟩ := Work.FTS.Nonlinear.FstarPkg.c2m_L12Fstar_W
  -- ## the class-`C` data
  have hsmw : Work.FTS.EllipticEst.SmoothOpen w := hw.reg
  have hm7 : Work.Spaces.HkMem α 7 w := hw.mem
  have hm4 : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open (α := α) (k := 7) (f := w) hsmw 4 (by norm_num) hm7
  have hm5 : Work.Spaces.HkMem α 5 w :=
    Work.FTS.OpenPkg.HkMem_mono_open (α := α) (k := 7) (f := w) hsmw 5 (by norm_num) hm7
  have hQw : Work.FTS.VocabO.HQo α 4 w := ⟨hsmw, hm4⟩
  -- ## `L₁₂(w)`
  have hL12 := hl12 α hα hα1 w hQw hw.l12
  have hL12mem : Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 w z) := hL12.1
  have hL12sm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.L12 w z) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_aux hα hw
  -- ## `D_z w`, `D_θ w`
  have hDzw_mem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz w) :=
    Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 4 hsmw hm5
  have hDthw_mem : Work.Spaces.HkMem α 4 (Work.Spaces.Dth w) :=
    Work.FTS.StrongEps.ClassCRHS.hkMem_Dth_of_smoothOpen hα 4 hsmw hm5
  -- ## the factor `A = (3/(2α))·L₁₂(w)`
  have hAsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (3 / (2 * α)) * Work.Construction.L12 w z) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul (3 / (2 * α)) hL12sm
  have hAmem : Work.Spaces.HkMem α 4
      (fun z θ => (3 / (2 * α)) * Work.Construction.L12 w z) :=
    Work.FTS.LocData.HkMem_const_mul α 4 (3 / (2 * α)) hL12mem
  -- ## the factor `B = c2m·L₁₂(w)` (via the angular multiplication rule)
  have hc2msm : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Work.Construction.c2m θ) :=
    Work.FTS.GalFields.RHS.smoothOpen_c2m_ang
  have hc2mb : ∀ θ ∈ Work.Spaces.Iθ, |Work.Construction.c2m θ| ≤ 1000 := by
    intro θ hθ
    have h := Work.FTS.Nonlinear.Pieces.abs_c2m_le_two hθ
    linarith
  have hc2mIt : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Work.Construction.c2m θ') 0 θ|
        ≤ 1000 * Real.sin (2 * θ) := by
    intro i hi hi4 θ hθ
    have h := Work.FTS.Nonlinear.Pieces.DthIter_c2m_le i hi hi4 θ
    rw [show (Real.sin (2 * θ)) ^ (2 : ℝ) = (Real.sin (2 * θ)) ^ (2 : ℕ) from
      Real.rpow_natCast _ 2] at h
    have h0 : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have h1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hsq : Real.sin (2 * θ) ^ 2 ≤ Real.sin (2 * θ) := by nlinarith
    linarith
  have hBmem : Work.Spaces.HkMem α 4
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z) :=
    (hang α hα hα1 (fun θ => Work.Construction.c2m θ)
      (fun z θ => Work.Construction.L12 w z) 1000 hc2msm hc2mb hc2mIt hL12sm hL12mem).1
  have hBsmt : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z) :=
    Work.FTS.NonlinRows.smoothOpen_mul hc2msm hL12sm
  have hnegBmem : Work.Spaces.HkMem α 4
      (fun z θ => (-1) * (Work.Construction.c2m θ * Work.Construction.L12 w z)) :=
    Work.FTS.LocData.HkMem_const_mul α 4 (-1) hBmem
  have hnegBsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (-1) * (Work.Construction.c2m θ * Work.Construction.L12 w z)) :=
    Work.FTS.NonlinRows.smoothOpen_const_mul (-1) hBsmt
  -- ## the fixed profile atoms
  have hFstarsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Fstar α) :=
    Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α
  have hDthFsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dth (Work.Construction.Fstar α)) := hFstarsm.Dth
  have hDzFsm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dz (Work.Construction.Fstar α)) := hFstarsm.Dz
  have hc2mL12Fsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.c2m θ
        * Work.Construction.L12 (Work.Construction.Fstar α) z) :=
    Work.FTS.NonlinRows.smoothOpen_mul hc2msm
      (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_L12_Fstar α)
  -- ## row 0: the fixed block
  have hp0 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N0fix α) :=
    Work.FTS.NonlinRows.HkMem_N0fix α hα hα1
  have hp0sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N0fix α) :=
    Work.FTS.StrongPersist.L3Rhs.smoothOpen_N0fix α hα hα1
  -- ## row 1: `N₀₃ᵍ = (1/α)·L₁₂(w)·w`
  have h1eq : Work.FTS.Nonlin.N03g α w
      = fun z θ => (1 / α) * (Work.Construction.L12 w z * w z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N03g, Work.Construction.N03]
    ring
  have hp1 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N03g α w) := by
    rw [h1eq]
    exact Work.FTS.LocData.HkMem_const_mul α 4 (1 / α)
      (hprod α hα hα1 (fun z θ => Work.Construction.L12 w z) w
        ⟨hL12sm, hL12mem⟩ ⟨hsmw, hm4⟩).1
  have hp1sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N03g α w) := by
    rw [h1eq]
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (1 / α)
      (Work.FTS.NonlinRows.smoothOpen_mul hL12sm hsmw)
  -- ## row 2: `N₀₄ᵃ = D_θF_* · A`
  have h2eq : Work.FTS.Nonlin.N04aF α w
      = fun z θ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ
          * ((3 / (2 * α)) * Work.Construction.L12 w z) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N04aF, Work.Construction.N04a, Work.Construction.s2,
      Work.Spaces.Dth]
    ring
  have hp2 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N04aF α w) := by
    rw [h2eq]
    exact (hwprod α hα hα1 (Work.Spaces.Dth (Work.Construction.Fstar α))
      (fun z θ => (3 / (2 * α)) * Work.Construction.L12 w z)
      hDthFsm (hFstarW α hα hα1).1 ⟨hAsm, hAmem⟩).1
  have hp2sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N04aF α w) := by
    rw [h2eq]
    exact Work.FTS.NonlinRows.smoothOpen_mul hDthFsm hAsm
  -- ## row 3: `N₀₄ᵇ = D_θw · A`
  have h3eq : Work.FTS.Nonlin.N04bF α w
      = fun z θ => Work.Spaces.Dth w z θ
          * ((3 / (2 * α)) * Work.Construction.L12 w z) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N04bF, Work.Construction.N04b, Work.Construction.s2,
      Work.Spaces.Dth]
    ring
  have hp3 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N04bF α w) := by
    rw [h3eq]
    exact (hprod α hα hα1 (Work.Spaces.Dth w)
      (fun z θ => (3 / (2 * α)) * Work.Construction.L12 w z)
      ⟨hsmw.Dth, hDthw_mem⟩ ⟨hAsm, hAmem⟩).1
  have hp3sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N04bF α w) := by
    rw [h3eq]
    exact Work.FTS.NonlinRows.smoothOpen_mul hsmw.Dth hAsm
  -- ## row 4: `N₀₅ᵃ = D_zF_* · (-B)`
  have h4eq : Work.FTS.Nonlin.N05aF α w
      = fun z θ => Work.Spaces.Dz (Work.Construction.Fstar α) z θ
          * ((-1) * (Work.Construction.c2m θ * Work.Construction.L12 w z)) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N05aF, Work.Construction.N05a]
    ring
  have hp4 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N05aF α w) := by
    rw [h4eq]
    exact (hwprod α hα hα1 (Work.Spaces.Dz (Work.Construction.Fstar α))
      (fun z θ => (-1) * (Work.Construction.c2m θ * Work.Construction.L12 w z))
      hDzFsm (hDzFstarW α hα hα1).1 ⟨hnegBsm, hnegBmem⟩).1
  have hp4sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N05aF α w) := by
    rw [h4eq]
    exact Work.FTS.NonlinRows.smoothOpen_mul hDzFsm hnegBsm
  -- ## row 5: `N₀₅ᵇ = -B·D_zw`
  have h5eq : Work.FTS.Nonlin.N05bF α w
      = fun z θ => (-1) * ((Work.Construction.c2m θ * Work.Construction.L12 w z)
          * Work.Spaces.Dz w z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N05bF, Work.Construction.N05b]
    ring
  have hp5 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N05bF α w) := by
    rw [h5eq]
    exact Work.FTS.LocData.HkMem_const_mul α 4 (-1)
      (hprod α hα hα1
        (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z)
        (Work.Spaces.Dz w) ⟨hBsmt, hBmem⟩ ⟨hsmw.Dz, hDzw_mem⟩).1
  have hp5sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N05bF α w) := by
    rw [h5eq]
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (-1)
      (Work.FTS.NonlinRows.smoothOpen_mul hBsmt hsmw.Dz)
  -- ## row 6: `N₀₆ = -c2m·L₁₂(F_*)·D_zw`
  have h6eq : Work.FTS.Nonlin.N06F α w
      = fun z θ => (-1) * ((Work.Construction.c2m θ
          * Work.Construction.L12 (Work.Construction.Fstar α) z)
          * Work.Spaces.Dz w z θ) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N06F, Work.Construction.N06]
    ring
  have hp6 : Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N06F α w) := by
    rw [h6eq]
    exact Work.FTS.LocData.HkMem_const_mul α 4 (-1)
      (hwprod α hα hα1
        (fun z θ => Work.Construction.c2m θ
          * Work.Construction.L12 (Work.Construction.Fstar α) z)
        (Work.Spaces.Dz w) hc2mL12Fsm (hc2mL12FstarW α hα hα1).1
        ⟨hsmw.Dz, hDzw_mem⟩).1
  have hp6sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N06F α w) := by
    rw [h6eq]
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (-1)
      (Work.FTS.NonlinRows.smoothOpen_mul hc2mL12Fsm hsmw.Dz)
  -- ## the additive closure of `ℋ⁴`-honesty
  have hadd : ∀ (u v : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen u →
      Work.FTS.EllipticEst.SmoothOpen v → Work.Spaces.HkMem α 4 u →
      Work.Spaces.HkMem α 4 v → Work.Spaces.HkMem α 4 (fun z θ => u z θ + v z θ) := by
    intro u v hu hv hum hvm
    exact Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four (hu.forall 4) (hv.forall 4) hum hvm
  have haddsm : ∀ (u v : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.SmoothOpen u →
      Work.FTS.EllipticEst.SmoothOpen v →
      Work.FTS.EllipticEst.SmoothOpen (fun z θ => u z θ + v z θ) := by
    intro u v hu hv
    exact Work.FTS.NonlinRows.smoothOpen_add hu hv
  -- ## the nested assembly
  have h56 : Work.Spaces.HkMem α 4 (fun z θ => Work.FTS.Nonlin.N05bF α w z θ
      + Work.FTS.Nonlin.N06F α w z θ) :=
    hadd (Work.FTS.Nonlin.N05bF α w) (Work.FTS.Nonlin.N06F α w) hp5sm hp6sm hp5 hp6
  have h56sm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.FTS.Nonlin.N05bF α w z θ
      + Work.FTS.Nonlin.N06F α w z θ) :=
    haddsm (Work.FTS.Nonlin.N05bF α w) (Work.FTS.Nonlin.N06F α w) hp5sm hp6sm
  have h456 : Work.Spaces.HkMem α 4 (fun z θ => Work.FTS.Nonlin.N05aF α w z θ
      + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)) :=
    hadd (Work.FTS.Nonlin.N05aF α w)
      (fun z θ => Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)
      hp4sm h56sm hp4 h56
  have h456sm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.FTS.Nonlin.N05aF α w z θ
      + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)) :=
    haddsm (Work.FTS.Nonlin.N05aF α w)
      (fun z θ => Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)
      hp4sm h56sm
  have h3456 : Work.Spaces.HkMem α 4 (fun z θ => Work.FTS.Nonlin.N04bF α w z θ
      + (Work.FTS.Nonlin.N05aF α w z θ
        + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ))) :=
    hadd (Work.FTS.Nonlin.N04bF α w)
      (fun z θ => Work.FTS.Nonlin.N05aF α w z θ
        + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ))
      hp3sm h456sm hp3 h456
  have h3456sm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.Nonlin.N04bF α w z θ
        + (Work.FTS.Nonlin.N05aF α w z θ
          + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ))) :=
    haddsm (Work.FTS.Nonlin.N04bF α w)
      (fun z θ => Work.FTS.Nonlin.N05aF α w z θ
        + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ))
      hp3sm h456sm
  have h23456 : Work.Spaces.HkMem α 4 (fun z θ => Work.FTS.Nonlin.N04aF α w z θ
      + (Work.FTS.Nonlin.N04bF α w z θ
        + (Work.FTS.Nonlin.N05aF α w z θ
          + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)))) :=
    hadd (Work.FTS.Nonlin.N04aF α w)
      (fun z θ => Work.FTS.Nonlin.N04bF α w z θ
        + (Work.FTS.Nonlin.N05aF α w z θ
          + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)))
      hp2sm h3456sm hp2 h3456
  have h23456sm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.Nonlin.N04aF α w z θ
        + (Work.FTS.Nonlin.N04bF α w z θ
          + (Work.FTS.Nonlin.N05aF α w z θ
            + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)))) :=
    haddsm (Work.FTS.Nonlin.N04aF α w)
      (fun z θ => Work.FTS.Nonlin.N04bF α w z θ
        + (Work.FTS.Nonlin.N05aF α w z θ
          + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)))
      hp2sm h3456sm
  have h123456 : Work.Spaces.HkMem α 4 (fun z θ => Work.FTS.Nonlin.N03g α w z θ
      + (Work.FTS.Nonlin.N04aF α w z θ
        + (Work.FTS.Nonlin.N04bF α w z θ
          + (Work.FTS.Nonlin.N05aF α w z θ
            + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ))))) :=
    hadd (Work.FTS.Nonlin.N03g α w)
      (fun z θ => Work.FTS.Nonlin.N04aF α w z θ
        + (Work.FTS.Nonlin.N04bF α w z θ
          + (Work.FTS.Nonlin.N05aF α w z θ
            + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ))))
      hp1sm h23456sm hp1 h23456
  have hsum : Work.Spaces.HkMem α 4 (fun z θ => Work.FTS.Nonlin.N0fix α z θ
      + (Work.FTS.Nonlin.N03g α w z θ
        + (Work.FTS.Nonlin.N04aF α w z θ
          + (Work.FTS.Nonlin.N04bF α w z θ
            + (Work.FTS.Nonlin.N05aF α w z θ
              + (Work.FTS.Nonlin.N05bF α w z θ
                + Work.FTS.Nonlin.N06F α w z θ)))))) :=
    hadd (Work.FTS.Nonlin.N0fix α)
      (fun z θ => Work.FTS.Nonlin.N03g α w z θ
        + (Work.FTS.Nonlin.N04aF α w z θ
          + (Work.FTS.Nonlin.N04bF α w z θ
            + (Work.FTS.Nonlin.N05aF α w z θ
              + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)))))
      hp0sm
      (haddsm (Work.FTS.Nonlin.N03g α w)
        (fun z θ => Work.FTS.Nonlin.N04aF α w z θ
          + (Work.FTS.Nonlin.N04bF α w z θ
            + (Work.FTS.Nonlin.N05aF α w z θ
              + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ))))
        hp1sm h23456sm)
      hp0 h123456
  -- ## transfer from the open quadrant to the domain
  refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hsum ?_
  intro z hz θ hθ
  exact (Work.FTS.StrongEps.ClassCRHS.N0_split_open hα hsmw z θ ⟨hz, hθ⟩).symm

end Work.FTS.StrongEps.EpsZero.ClassCHk
