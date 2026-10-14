import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.GalFields.RHS.HkSum
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.LocData.zero_slice_locG
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.OpenPkg.prod_field
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsNstarBlock
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBound
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundE
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundR
import Submission.Work.FTS.StrongPersist.N6Trans.slotT2Six
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand

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

/-- **The `N₀`-block of the scheme's right-hand side is `ℋ⁴`-honest and bounded, for `ClassC`
data of small `ℋ⁴`-size and bounded `ℋ⁶`-size.**

`N0 α (Ftot α w) w` is the sum of seven products (`Construction.N0`):
`(3/(2α))·s2·L₁₂(F_*+w)·pth (F_*+w)`, `-c2m·L₁₂(F_*+w)·Dz (F_*+w)`, `(1/α)·L₁₂(w)·w`,
`(3/(2α))·s2·L₁₂(w)·pth (F_*+w)`, `-c2m·L₁₂(w)·Dz(F_*+w)`, `-c2m·L₁₂(F_*)·Dz(w)`.

Route hints (do not re-derive the analysis):

* all products go through `Work.FTS.OpenPkg.prod_field` (ℋ⁴×ℋ⁴ → ℋ⁴, loss `α^{-1/2}`,
  threshold-free: `∀ α, 0 < α → α ≤ 1 → ...`), `Work.FTS.OpenPkg.wprod_field_winf`
  (`𝒲^{4,∞} × ℋ⁴ → ℋ⁴`) for the `F_*`/`Γ`/`c2m` coefficients, and
  `Work.FTS.GalFields.RHS.HkNorm_add_le_open` (+ `HkNorm_finset_sum_le`) for the sums;
* `L₁₂(w)` and `FK(w)`: `Work.FTS.OpenPkg.l12H_field` / `fkH_field` (input `HQo α 4 w` and
  `L12 w 0 = 0`, both from `hw`), giving `Xn ≤ Ci·Xn α w ≤ Ci·C₀α²`;
* `s2 θ * pth (F_*+w) = Dth (F_*+w)` **everywhere** (definitional) — always rewrite to `Dth`
  before applying a product rule (`pth` alone is not `ℋ⁴`-honest);
* `Dz w`, `Dth w` in `ℋ⁴`: `Work.FTS.GalFields.Xn_Dz_le_Xn5` / `Xn_Dth_le_Xn5` (needs only
  `SmoothOpen w` and `HkMem α 5 w`, which follow from `hw`), bounded by `Xn5 α w ≤ Xn6 α w ≤ B`;
* `Dz (F_*+w) = Dz F_* + Dz w`, `Dth (F_*+w) = Dth F_* + Dth w` (additivity of `Dz`/`Dth`);
* the *fixed* `F_*`-profile atoms (`F_*`, `Dth F_*`, `Dz F_*`, `L₁₂(F_*)`):
  `Work.FTS.Nonlinear.FstarPkg.{Fstar_W, DthFstar_W, DzFstar_W}` give `WlInfMem`/`WlInf`-bounds,
  and `Work.FTS.NonlinRows.wtoHQ_of_pointwise_open` (or `...prod_field`-style combinations)
  turn them into `HkMem α 4` plus a norm bound; `Construction.L12_Fstar_eq` identifies
  `L₁₂(F_*) z = 2α/(1+z)`.

The constant `K` may depend on `α, C₀, B` (and on the fixed data), but **not** on `w`. -/
theorem HkMemXnN0 : ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {C₀ B : ℝ},
    ∃ K : ℝ, 0 < K ∧ ∀ {w : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
      Work.Spaces.HkNorm α 6 w ≤ B →
      Work.Spaces.HkMem α 4 (Work.Construction.N0 α (Work.Construction.Ftot α w) w) ∧
      Work.FTS.Nonlin.Xn α (Work.Construction.N0 α (Work.Construction.Ftot α w) w) ≤ K := by
  intro α hαIoc C₀ B
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  -- ## the universal constants of the library
  obtain ⟨Cp, hCp, hprod⟩ := Work.FTS.OpenPkg.prod_field
  obtain ⟨Cw, hCw, hwprod⟩ := Work.FTS.OpenPkg.wprod_field_winf
  obtain ⟨Cang, hCang, hang⟩ := Work.FTS.OpenPkg.angmul_field
  obtain ⟨C1, hC1, hl12⟩ := Work.FTS.OpenPkg.l12H_field
  obtain ⟨CF, hCF, hFstarW⟩ := Work.FTS.Nonlinear.FstarPkg.DthFstar_W
  obtain ⟨Cdz, hCdz, hDzFW⟩ := Work.FTS.Nonlinear.FstarPkg.DzFstar_W
  obtain ⟨Cw0, hCw0, hc2mL12W⟩ := Work.FTS.Nonlinear.FstarPkg.c2m_L12Fstar_W
  obtain ⟨K1, hK1, hN0fixbd⟩ := Work.FTS.Nonlinear.Pieces.RowsN0Aux.N0fix_bound
  -- ## the two size constants
  set Cx : ℝ := max C₀ 1 with hCxdef
  set Cb : ℝ := max B 1 with hCbdef
  have hCx1 : (1 : ℝ) ≤ Cx := le_max_right _ _
  have hCb1 : (1 : ℝ) ≤ Cb := le_max_right _ _
  have hCx0 : 0 < Cx := lt_of_lt_of_le zero_lt_one hCx1
  have hCb0 : 0 < Cb := lt_of_lt_of_le zero_lt_one hCb1
  -- ## the seven piece bounds
  set b0 : ℝ := K1 * α ^ 2 with hb0
  set b1 : ℝ := (1 / α) * (((Cp * α ^ (-(1 / 2 : ℝ))) * (C1 * (Cx * α ^ 2)))
    * (Cx * α ^ 2)) with hb1
  set b2 : ℝ := ((Cw * α ^ (-(1 / 2 : ℝ))) * (CF * α ^ 2))
    * ((3 / (2 * α)) * (C1 * (Cx * α ^ 2))) with hb2
  set b3 : ℝ := ((Cp * α ^ (-(1 / 2 : ℝ))) * Cb)
    * ((3 / (2 * α)) * (C1 * (Cx * α ^ 2))) with hb3
  set b4 : ℝ := ((Cw * α ^ (-(1 / 2 : ℝ))) * (Cdz * α))
    * (Cang * 1000 * (C1 * (Cx * α ^ 2))) with hb4
  set b5 : ℝ := ((Cp * α ^ (-(1 / 2 : ℝ))) * (Cang * 1000 * (C1 * (Cx * α ^ 2))))
    * Cb with hb5
  set b6 : ℝ := ((Cw * α ^ (-(1 / 2 : ℝ))) * (Cw0 * α)) * Cb with hb6
  -- ## the cumulative bounds
  set c6 : ℝ := 2 * (b5 + b6) with hc6
  set c5 : ℝ := 2 * (b4 + c6) with hc5
  set c4 : ℝ := 2 * (b3 + c5) with hc4
  set c3 : ℝ := 2 * (b2 + c4) with hc3
  set c2 : ℝ := 2 * (b1 + c3) with hc2
  set c1 : ℝ := 2 * (b0 + c2) with hc1
  -- ## nonnegativity of the constants
  have hαnn : 0 ≤ α := hα.le
  have hα2nn : 0 ≤ α ^ 2 := sq_nonneg α
  have hb0nn : 0 ≤ b0 := by rw [hb0]; exact mul_nonneg hK1.le hα2nn
  have hb1nn : 0 ≤ b1 := by rw [hb1]; positivity
  have hb2nn : 0 ≤ b2 := by rw [hb2]; positivity
  have hb3nn : 0 ≤ b3 := by rw [hb3]; positivity
  have hb4nn : 0 ≤ b4 := by rw [hb4]; positivity
  have hb5nn : 0 ≤ b5 := by rw [hb5]; positivity
  have hb6nn : 0 ≤ b6 := by rw [hb6]; positivity
  have hc6nn : 0 ≤ c6 := by rw [hc6]; linarith
  have hc5nn : 0 ≤ c5 := by rw [hc5]; linarith
  have hc4nn : 0 ≤ c4 := by rw [hc4]; linarith
  have hc3nn : 0 ≤ c3 := by rw [hc3]; linarith
  have hc2nn : 0 ≤ c2 := by rw [hc2]; linarith
  have hc1nn : 0 ≤ c1 := by rw [hc1]; linarith
  refine ⟨c1 + 1, by linarith, ?_⟩
  -- ## the data
  intro w hw hXnw hX6
  have hsmw : Work.FTS.EllipticEst.SmoothOpen w := hw.reg
  have hm7 : Work.Spaces.HkMem α 7 w := hw.mem
  have hm6 : Work.Spaces.HkMem α 6 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmw 6 (by norm_num) hm7
  have hm5 : Work.Spaces.HkMem α 5 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmw 5 (by norm_num) hm7
  have hm4 : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmw 4 (by norm_num) hm7
  have hXw0 : 0 ≤ Work.FTS.Nonlin.Xn α w := Work.Spaces.HkNorm_nonneg α 4 w
  have hC0nn : 0 ≤ C₀ := by
    have h2 : (0 : ℝ) < α ^ 2 := pow_pos hα 2
    nlinarith [hXnw, hXw0, h2]
  have hBnn : 0 ≤ B := le_trans (Work.Spaces.HkNorm_nonneg α 6 w) hX6
  have hXw : Work.FTS.Nonlin.Xn α w ≤ Cx * α ^ 2 :=
    le_trans hXnw (mul_le_mul_of_nonneg_right (le_max_left C₀ 1) hα2nn)
  -- ## the derivatives of `w`
  have hDzw_mem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz w) :=
    Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 4 hsmw hm5
  have hX5 : Work.FTS.GalFields.Xn5 α w ≤ B :=
    le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (α := α) (k := 6) (k' := 5)
      (by norm_num) hm6) hX6
  have hDzw_le : Work.FTS.Nonlin.Xn α (Work.Spaces.Dz w) ≤ Cb :=
    le_trans (le_trans (Work.FTS.GalFields.Xn_Dz_le_Xn5 hα hsmw hm5) hX5) (le_max_left B 1)
  have hDthw_mem : Work.Spaces.HkMem α 4 (Work.Spaces.Dth w) :=
    hkMem_Dth_of_smoothOpen hα 4 hsmw hm5
  have hDthw_le : Work.FTS.Nonlin.Xn α (Work.Spaces.Dth w) ≤ Cb :=
    le_trans (le_trans (Work.FTS.GalFields.Xn_Dth_le_Xn5 hα hm5) hX5) (le_max_left B 1)
  -- ## `L₁₂(w)`
  have hL12p : Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 w z) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 w z)
        ≤ C1 * Work.FTS.Nonlin.Xn α w :=
    hl12 α hα hα1 w ⟨hsmw, hm4⟩ hw.l12
  have hL12mem : Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 w z) := hL12p.1
  have hL12sm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Construction.L12 w z) :=
    smoothOpen_L12_radial_aux hα hw
  have hL12le : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 w z)
      ≤ C1 * Work.FTS.Nonlin.Xn α w := hL12p.2
  have hL12le' : Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 w z)
      ≤ C1 * (Cx * α ^ 2) :=
    le_trans hL12le (mul_le_mul_of_nonneg_left hXw hC1.le)
  -- ## the angular factor `c2m`
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
  -- ## the factor `B = c2m·L₁₂(w)` and its bound `CB`
  set CB : ℝ := Cang * 1000 * (C1 * (Cx * α ^ 2)) with hCB
  have hBsmt : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z) :=
    Work.FTS.NonlinRows.smoothOpen_mul hc2msm hL12sm
  have hBp := hang α hα hα1 (fun θ => Work.Construction.c2m θ)
    (fun z θ => Work.Construction.L12 w z) 1000 hc2msm hc2mb hc2mIt hL12sm hL12mem
  have hBmem : Work.Spaces.HkMem α 4
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z) := hBp.1
  have hBle : Work.FTS.Nonlin.Xn α
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 w z) ≤ CB := by
    rw [hCB]
    exact le_trans hBp.2 (mul_le_mul_of_nonneg_left hL12le' (by positivity))
  have hCBnn : 0 ≤ CB := by rw [hCB]; positivity
  -- ## the fixed profile atom `c2m·L₁₂(F_*)`
  have hc2mL12Fsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.c2m θ * Work.Construction.L12 (Work.Construction.Fstar α) z) :=
    Work.FTS.NonlinRows.smoothOpen_mul hc2msm
      (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_L12_Fstar α)
  -- ## the six product rows
  have h0r : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N0fix α) ∧
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N0fix α) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N0fix α) ≤ b0 := by
    refine ⟨Work.FTS.StrongPersist.L3Rhs.smoothOpen_N0fix α hα hα1,
      Work.FTS.NonlinRows.HkMem_N0fix α hα hα1, ?_⟩
    rw [hb0]; exact hN0fixbd α hα hα1
  have h1r := row_N03g (α := α) (Cp := Cp) (C1 := C1) hα hα1 hsmw hm4 hL12sm hL12mem
    hCp hC1 hL12le (hprod α hα hα1)
  have h3r := row_N04aF (α := α) (Cw := Cw) (C1 := C1) (CF := CF) hα hα1 hL12sm hL12mem
    hCw hC1 hCF hL12le (hFstarW α hα hα1).1 (hFstarW α hα hα1).2 (hwprod α hα hα1)
  have h4r := row_N04bF (α := α) (Cp := Cp) (C1 := C1) (Bd := Cb) hα hα1 hsmw hL12sm hL12mem
    hCp hC1 hL12le hDthw_mem hDthw_le hCb0.le (hprod α hα hα1)
  have h5r := row_N05aF (α := α) (Cw := Cw) (Cdz := Cdz) (CB := CB) hα hα1 hBsmt hBmem
    hBle hCBnn hCw hCdz (hDzFW α hα hα1).1 (hDzFW α hα hα1).2 (hwprod α hα hα1)
  have h6r := row_N05bF (α := α) (Cp := Cp) (CB := CB) (Bd := Cb) hα hα1 hsmw hBsmt hBmem
    hBle hCBnn hCp hDzw_mem hDzw_le hCb0.le (hprod α hα hα1)
  have h7r := row_N06F (α := α) (Cw := Cw) (Cw0 := Cw0) (Bd := Cb) hα hα1 hsmw hDzw_mem
    hDzw_le hCb0.le hc2mL12Fsm (hc2mL12W α hα hα1).1 (hc2mL12W α hα hα1).2 hCw hCw0
    (hwprod α hα hα1)
  -- ## the bounds, weakened to the canonical `b`-form
  have hpα : 0 ≤ Cp * α ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hCp.le (Real.rpow_nonneg hα.le _)
  have hwα : 0 ≤ Cw * α ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hCw.le (Real.rpow_nonneg hα.le _)
  have hCxα : 0 ≤ Cx * α ^ 2 := mul_nonneg hCx0.le hα2nn
  have h1α : 0 ≤ 1 / α := by positivity
  have h32 : 0 ≤ 3 / (2 * α) := by positivity
  have h1le : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N03g α w) ≤ b1 := by
    refine le_trans h1r.2.2 ?_
    rw [hb1]
    refine mul_le_mul_of_nonneg_left ?_ h1α
    have hA : (Cp * α ^ (-(1 / 2 : ℝ))) * (C1 * Work.FTS.Nonlin.Xn α w)
        ≤ (Cp * α ^ (-(1 / 2 : ℝ))) * (C1 * (Cx * α ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hXw hC1.le) hpα
    have hA0 : 0 ≤ (Cp * α ^ (-(1 / 2 : ℝ))) * (C1 * (Cx * α ^ 2)) :=
      mul_nonneg hpα (mul_nonneg hC1.le hCxα)
    calc ((Cp * α ^ (-(1 / 2 : ℝ))) * (C1 * Work.FTS.Nonlin.Xn α w))
          * Work.FTS.Nonlin.Xn α w
        ≤ ((Cp * α ^ (-(1 / 2 : ℝ))) * (C1 * (Cx * α ^ 2)))
            * Work.FTS.Nonlin.Xn α w := mul_le_mul_of_nonneg_right hA hXw0
      _ ≤ ((Cp * α ^ (-(1 / 2 : ℝ))) * (C1 * (Cx * α ^ 2))) * (Cx * α ^ 2) :=
          mul_le_mul_of_nonneg_left hXw hA0
  have h2le : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N04aF α w) ≤ b2 := by
    refine le_trans h3r.2.2 ?_
    rw [hb2]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hwα (mul_nonneg hCF.le hα2nn))
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hXw hC1.le) h32
  have h3le : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N04bF α w) ≤ b3 := by
    refine le_trans h4r.2.2 ?_
    rw [hb3]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hpα hCb0.le)
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hXw hC1.le) h32
  have h4le : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N05aF α w) ≤ b4 := by
    rw [hb4]; exact h5r.2.2
  have h5le : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N05bF α w) ≤ b5 := by
    rw [hb5]; exact h6r.2.2
  have h6le : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N06F α w) ≤ b6 := by
    rw [hb6]; exact h7r.2.2
  -- ## the nested assembly
  have ht6 := add2 (u := Work.FTS.Nonlin.N05bF α w) (v := Work.FTS.Nonlin.N06F α w) hα
    h6r.1 h7r.1 h6r.2.1 h7r.2.1 h5le h6le hb5nn hb6nn
  have ht6' : Work.FTS.Nonlin.Xn α
      (fun z θ => Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ) ≤ c6 := by
    rw [hc6]; exact ht6.2
  have hsm6' : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ) :=
    Work.FTS.NonlinRows.smoothOpen_add h6r.1 h7r.1
  have ht5 := add2 (u := Work.FTS.Nonlin.N05aF α w)
    (v := fun z θ => Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ) hα
    h5r.1 hsm6' h5r.2.1 ht6.1 h4le ht6' hb4nn hc6nn
  have ht5' : Work.FTS.Nonlin.Xn α
      (fun z θ => Work.FTS.Nonlin.N05aF α w z θ
        + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)) ≤ c5 := by
    rw [hc5]; exact ht5.2
  have hsm5' : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.Nonlin.N05aF α w z θ
        + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)) :=
    Work.FTS.NonlinRows.smoothOpen_add h5r.1 hsm6'
  have ht4 := add2 (u := Work.FTS.Nonlin.N04bF α w)
    (v := fun z θ => Work.FTS.Nonlin.N05aF α w z θ
      + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)) hα
    h4r.1 hsm5' h4r.2.1 ht5.1 h3le ht5' hb3nn hc5nn
  have ht4' : Work.FTS.Nonlin.Xn α
      (fun z θ => Work.FTS.Nonlin.N04bF α w z θ
        + (Work.FTS.Nonlin.N05aF α w z θ
          + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ))) ≤ c4 := by
    rw [hc4]; exact ht4.2
  have hsm4' : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.Nonlin.N04bF α w z θ
        + (Work.FTS.Nonlin.N05aF α w z θ
          + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ))) :=
    Work.FTS.NonlinRows.smoothOpen_add h4r.1 hsm5'
  have ht3 := add2 (u := Work.FTS.Nonlin.N04aF α w)
    (v := fun z θ => Work.FTS.Nonlin.N04bF α w z θ
      + (Work.FTS.Nonlin.N05aF α w z θ
        + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ))) hα
    h3r.1 hsm4' h3r.2.1 ht4.1 h2le ht4' hb2nn hc4nn
  have ht3' : Work.FTS.Nonlin.Xn α
      (fun z θ => Work.FTS.Nonlin.N04aF α w z θ
        + (Work.FTS.Nonlin.N04bF α w z θ
          + (Work.FTS.Nonlin.N05aF α w z θ
            + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)))) ≤ c3 := by
    rw [hc3]; exact ht3.2
  have hsm3' : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.Nonlin.N04aF α w z θ
        + (Work.FTS.Nonlin.N04bF α w z θ
          + (Work.FTS.Nonlin.N05aF α w z θ
            + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)))) :=
    Work.FTS.NonlinRows.smoothOpen_add h3r.1 hsm4'
  have ht2 := add2 (u := Work.FTS.Nonlin.N03g α w)
    (v := fun z θ => Work.FTS.Nonlin.N04aF α w z θ
      + (Work.FTS.Nonlin.N04bF α w z θ
        + (Work.FTS.Nonlin.N05aF α w z θ
          + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)))) hα
    h1r.1 hsm3' h1r.2.1 ht3.1 h1le ht3' hb1nn hc3nn
  have ht2' : Work.FTS.Nonlin.Xn α
      (fun z θ => Work.FTS.Nonlin.N03g α w z θ
        + (Work.FTS.Nonlin.N04aF α w z θ
          + (Work.FTS.Nonlin.N04bF α w z θ
            + (Work.FTS.Nonlin.N05aF α w z θ
              + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ))))) ≤ c2 := by
    rw [hc2]; exact ht2.2
  have hsm2' : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.FTS.Nonlin.N03g α w z θ
        + (Work.FTS.Nonlin.N04aF α w z θ
          + (Work.FTS.Nonlin.N04bF α w z θ
            + (Work.FTS.Nonlin.N05aF α w z θ
              + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ))))) :=
    Work.FTS.NonlinRows.smoothOpen_add h1r.1 hsm3'
  have ht1 := add2 (u := Work.FTS.Nonlin.N0fix α)
    (v := fun z θ => Work.FTS.Nonlin.N03g α w z θ
      + (Work.FTS.Nonlin.N04aF α w z θ
        + (Work.FTS.Nonlin.N04bF α w z θ
          + (Work.FTS.Nonlin.N05aF α w z θ
            + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ))))) hα
    h0r.1 hsm2' h0r.2.1 ht2.1 h0r.2.2 ht2' hb0nn hc2nn
  have hSum_le : Work.FTS.Nonlin.Xn α
      (fun z θ => Work.FTS.Nonlin.N0fix α z θ
        + (Work.FTS.Nonlin.N03g α w z θ
          + (Work.FTS.Nonlin.N04aF α w z θ
            + (Work.FTS.Nonlin.N04bF α w z θ
              + (Work.FTS.Nonlin.N05aF α w z θ
                + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)))))) ≤ c1 := by
    rw [hc1]; exact ht1.2
  -- ## the transfer to `N₀`
  have hsplit := fun z θ (h : (z, θ) ∈ Work.Construction.Qd) =>
    N0_split_open_aux hα hsmw z θ h
  have hmem : Work.Spaces.HkMem α 4 (Work.Construction.N0 α (Work.Construction.Ftot α w) w) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 ht1.1
      (fun z hz θ hθ => (hsplit z θ ⟨hz, hθ.1, hθ.2⟩).symm)
  have hksq : Work.Spaces.HkSq α 4 (Work.Construction.N0 α (Work.Construction.Ftot α w) w)
      = Work.Spaces.HkSq α 4
        (fun z θ => Work.FTS.Nonlin.N0fix α z θ
          + (Work.FTS.Nonlin.N03g α w z θ
            + (Work.FTS.Nonlin.N04aF α w z θ
              + (Work.FTS.Nonlin.N04bF α w z θ
                + (Work.FTS.Nonlin.N05aF α w z θ
                  + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)))))) :=
    Work.FTS.EllipticEst.HkSq_congr_open α 4
      (fun z θ hz hθ0 hθ1 => hsplit z θ ⟨hz, hθ0, hθ1⟩)
  have hXn : Work.FTS.Nonlin.Xn α
      (Work.Construction.N0 α (Work.Construction.Ftot α w) w) ≤ c1 := by
    have h : Work.FTS.Nonlin.Xn α (Work.Construction.N0 α (Work.Construction.Ftot α w) w)
        = Work.FTS.Nonlin.Xn α
          (fun z θ => Work.FTS.Nonlin.N0fix α z θ
            + (Work.FTS.Nonlin.N03g α w z θ
              + (Work.FTS.Nonlin.N04aF α w z θ
                + (Work.FTS.Nonlin.N04bF α w z θ
                  + (Work.FTS.Nonlin.N05aF α w z θ
                    + (Work.FTS.Nonlin.N05bF α w z θ + Work.FTS.Nonlin.N06F α w z θ)))))) := by
      simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm, hksq]
    rw [h]
    exact hSum_le
  exact ⟨hmem, le_trans hXn (by linarith)⟩

end Work.FTS.StrongEps.ClassCRHS
