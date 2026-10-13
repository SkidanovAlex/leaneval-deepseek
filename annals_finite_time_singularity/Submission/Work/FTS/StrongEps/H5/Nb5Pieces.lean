/-
# `H5/Nb5Pieces` — the twenty level-`5` `NBlk` pieces, priced by the atomic packages

The level-`5` transcription of the bookkeeping half of `ClassCRHS.nb_data`: from the four atomic
packages (`HAtoms5Pkg`, `WStar5Pkg`, `WFixed5Pkg`, `HFixed5Pkg`) and the order-`5` `sin²θ`-slot
bound, every one of the twenty pieces `NBlk α w Φs Φg k` is `ℋ⁵`-honest with a *common*
level-`5` norm bound `Kbig`, independent of `w`, `Φg`.

The two product rules are `H5.prodHH5` (`ℋ⁵` × `ℋ⁵`, i.e. the level shift plus the level-four
`OpenPkg.prod_field`) and `H5.prodWH5` (`𝒲^{5,∞}` × `ℋ⁵`, i.e. `H5.wprod_field_winf5`); the four
`sin²θ`-pieces go through `L3Rhs.ang_mul_HkSq_le 5`.  The transfer from the sum of the pieces to
`N` itself is in `H5.Nb5Core`.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.StrongEps.H5.Nb5Pkgs
import Submission.Work.FTS.StrongEps.H5.ProdWrappers5
import Submission.Work.FTS.StrongEps.H5.HkSum5
import Submission.Work.FTS.StrongEps.H5.L5of
import Submission.Work.FTS.StrongEps.H5.wprod_field_winf5
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnNDefs
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnNAux
import Submission.Work.FTS.Nonlinear.Pieces.RNP.RNP24.angProfile_sinSq
import Submission.Work.FTS.StrongPersist.L3Rhs.c2m_mul_HkSq_le
import Submission.Work.FTS.Nonlinear.Open.Row25Aux
import Submission.Work.FTS.OpenPkg.prod_field

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.H5

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-- **The twenty level-`5` `NBlk` pieces, priced.** -/
theorem Nb5_pieces (hH : HAtoms5Pkg) (hWs : WStar5Pkg) (hWf : WFixed5Pkg) (hHf : HFixed5Pkg)
    (hsin5 : SinSqSlot5Pkg) :
    ∀ {α : ℝ}, α ∈ Set.Ioc 0 1 → ∀ {C₀ B Ce Cs6 : ℝ} {Φs : Fn},
      ∃ Kbig : ℝ, 0 < Kbig ∧ ∀ {w Φg : Fn},
        Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
        Work.Spaces.HkNorm α 6 w ≤ B →
        Work.FTS.ClassC.EllPkgK α 6 Ce w Φg →
        Work.FTS.StrongPersist.StarPkg6 α Cs6 Φs →
        ∀ k ∈ Finset.range 20,
          Work.Spaces.HkMem α 5 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k) ∧
          Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k) ≤ Kbig := by
  intro α hαI C₀ B Ce Cs6 Φs
  have hα0 : 0 < α := hαI.1
  have hα1 : α ≤ 1 := hαI.2
  -- ## the universal rules
  obtain ⟨Cprod, hCprod, hPRf⟩ := Work.FTS.OpenPkg.prod_field
  obtain ⟨Cw, hCw, hWRf⟩ := wprod_field_winf5
  obtain ⟨Cang, hCang, hangfield⟩ := Work.FTS.StrongPersist.L3Rhs.ang_mul_HkSq_le 5
  obtain ⟨Bsin, hBsin, hSinInt, hSinB, hSinIt⟩ :=
    Work.FTS.Nonlinear.Pieces.RNP.RNP24.angProfile_sinSq
  obtain ⟨Bsin5, hBsin5, hSin5⟩ := hsin5
  have hPR : ∀ f g : Fn, Work.FTS.VocabO.HQo α 4 f → Work.FTS.VocabO.HQo α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ Cprod * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g :=
    hPRf α hα0 hα1
  have hWR : ∀ f g : Fn, Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.WlInfMem α 5 f →
      Work.FTS.VocabO.HQo α 5 g →
      Work.Spaces.HkMem α 5 (fun z θ => f z θ * g z θ) ∧
      Work.Spaces.HkNorm α 5 (fun z θ => f z θ * g z θ)
        ≤ Cw * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 5 f * Work.Spaces.HkNorm α 5 g :=
    hWRf α hα0 hα1
  -- ## the atomic constants
  obtain ⟨aH, haH, hHA⟩ := hH hαI
  obtain ⟨aWs, haWs, hWA⟩ := hWs hαI (Cs6 := Cs6)
  obtain ⟨aWf, haWf, hWfA⟩ := hWf hαI
  obtain ⟨aHf, haHf, hHfA⟩ := hHf hαI
  set A : ℝ := max (max aH aWs) (max aWf aHf) with hAdef
  have hA1 : aH ≤ A := le_trans (le_max_left _ _) (le_max_left _ _)
  have hA2 : aWs ≤ A := le_trans (le_max_right _ _) (le_max_left _ _)
  have hA3 : aWf ≤ A := le_trans (le_max_left _ _) (le_max_right _ _)
  have hA4 : aHf ≤ A := le_trans (le_max_right _ _) (le_max_right _ _)
  have hAnn : 0 ≤ A := le_trans haH.le hA1
  -- ## the two coefficient levels and the angular coefficient
  set P1 : ℝ := 3 * (Cprod * α ^ (-(1 / 2 : ℝ)) * A * A) with hP1def
  set P2 : ℝ := Cw * α ^ (-(1 / 2 : ℝ)) * A * A with hP2def
  have hP1nn : 0 ≤ P1 := by
    rw [hP1def]
    exact mul_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg (mul_nonneg hCprod.le (Real.rpow_nonneg hα0.le _)) hAnn) hAnn)
  have hP2nn : 0 ≤ P2 := by
    rw [hP2def]
    exact mul_nonneg (mul_nonneg (mul_nonneg hCw.le (Real.rpow_nonneg hα0.le _)) hAnn) hAnn
  set Bmax : ℝ := max Bsin Bsin5 with hBmaxdef
  have hBmaxpos : 0 < Bmax := lt_of_lt_of_le hBsin (le_max_left _ _)
  have hSinSlots : ∀ i : ℕ, 1 ≤ i → i ≤ 5 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => -(Real.sin θ') ^ 2) 0 θ|
        ≤ Bmax * Real.sin (2 * θ) := by
    intro i hi1 hi5 θ hθ
    have hsin0 : 0 ≤ Real.sin (2 * θ) :=
      Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
    rcases eq_or_lt_of_le hi5 with h5 | h5
    · rw [h5]
      exact le_trans (hSin5 θ hθ) (mul_le_mul_of_nonneg_right (le_max_right _ _) hsin0)
    · exact le_trans (hSinIt i hi1 (by omega) θ hθ)
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hsin0)
  have hSinBnd : ∀ θ ∈ Work.Spaces.Iθ, |-(Real.sin θ) ^ 2| ≤ Bmax :=
    fun θ hθ => le_trans (hSinB θ hθ) (le_max_left _ _)
  set Sang : ℝ := Real.sqrt (Cang * Bmax ^ 2) with hSangdef
  have hSangnn : 0 ≤ Sang := Real.sqrt_nonneg _
  -- ## the table of the twenty bounds
  set T : ℕ → ℝ := fun k => match k with
    | 0 => |(2 : ℝ)| * P1
    | 1 => |(2 : ℝ)| * P2
    | 2 => |(2 : ℝ)| * P2
    | 3 => |(2 : ℝ)| * P2
    | 4 => |(-2 : ℝ)| * P1
    | 5 => |(-2 : ℝ)| * P2
    | 6 => |(-2 : ℝ)| * P2
    | 7 => |(-2 : ℝ)| * P2
    | 8 => |(-(2 * α))| * P1
    | 9 => |(-(2 * α))| * P2
    | 10 => |(-(2 * α))| * P2
    | 11 => |(-(2 * α))| * P2
    | 12 => |(-(1 / 2))| * P1
    | 13 => |(-(1 / 2))| * P2
    | 14 => |(1 / 2)| * P2
    | 15 => A
    | 16 => Sang * P1
    | 17 => Sang * P2
    | 18 => Sang * P2
    | _ => Sang * A with hTdef
  have hTnn : ∀ k ∈ Finset.range 20, 0 ≤ T k := by
    intro k hk
    have hk20 : k < 20 := Finset.mem_range.mp hk
    interval_cases k <;> simp only [hTdef] <;> first | positivity | exact hAnn
  set Kbig : ℝ := 1 + ∑ k ∈ Finset.range 20, T k with hKbigdef
  have hKbigpos : 0 < Kbig := by
    rw [hKbigdef]
    linarith [Finset.sum_nonneg hTnn]
  have hbE : ∀ k ∈ Finset.range 20, T k ≤ Kbig := by
    intro k hk
    rw [hKbigdef]
    linarith [Finset.single_le_sum hTnn hk]
  refine ⟨Kbig, hKbigpos, ?_⟩
  intro w Φg hw hXw hX6 hell hstar
  -- ## the atoms, for the actual `w`, `Φg`
  obtain ⟨hRp, hUp, hVp, hwp, hDthp, hDzp, hFKp, hφwp, hφDthp, hφDzp⟩ := hHA hw hXw hX6 hell
  have hqoR := hRp.1
  have hRbd' : Work.Spaces.HkNorm α 5
      (Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α w Φg)) ≤ A := le_trans hRp.2 hA1
  have hqoU := hUp.1
  have hUbd' : Work.Spaces.HkNorm α 5 (fun z θ => Work.Construction.Uop α
      (Work.FTS.Nonlin.PhiTg α w Φg) z θ / Work.Construction.s2 θ) ≤ A := le_trans hUp.2 hA1
  have hqoV := hVp.1
  have hVbd' : Work.Spaces.HkNorm α 5
      (Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α w Φg)) ≤ A := le_trans hVp.2 hA1
  have hqow := hwp.1
  have hwbd' : Work.Spaces.HkNorm α 5 w ≤ A := le_trans hwp.2 hA1
  have hqoDthw := hDthp.1
  have hDthwbd' : Work.Spaces.HkNorm α 5 (Work.Spaces.Dth w) ≤ A := le_trans hDthp.2 hA1
  have hqoDzw := hDzp.1
  have hDzwbd' : Work.Spaces.HkNorm α 5 (Work.Spaces.Dz w) ≤ A := le_trans hDzp.2 hA1
  have hqoFKw := hFKp.1
  have hFKwbd' : Work.Spaces.HkNorm α 5 (fun z _ => Work.Construction.FK w z) ≤ A :=
    le_trans hFKp.2 hA1
  have hqoφw := hφwp.1
  have hφwbd' : Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z) * w z θ) ≤ A :=
    le_trans hφwp.2 hA1
  have hqoφDthw := hφDthp.1
  have hφDthwbd' : Work.Spaces.HkNorm α 5
      (fun z θ => z / (1 + z) * Work.Spaces.Dth w z θ) ≤ A := le_trans hφDthp.2 hA1
  have hqoφDzw := hφDzp.1
  have hφDzwbd' : Work.Spaces.HkNorm α 5
      (fun z θ => z / (1 + z) * Work.Spaces.Dz w z θ) ≤ A := le_trans hφDzp.2 hA1
  obtain ⟨hRsp, hUsp, hVsp⟩ := hWA hstar
  have hRsm := hRsp.1
  have hRwm := hRsp.2.1
  have hRwb' : Work.Spaces.WlInf α 5 (fun z θ => (z + 1) / z
      * Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ) ≤ A :=
    le_trans hRsp.2.2 hA2
  have hUsm := hUsp.1
  have hUwm := hUsp.2.1
  have hUwb' : Work.Spaces.WlInf α 5 (fun z θ => (z + 1) / z
      * (Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
        / Work.Construction.s2 θ)) ≤ A := le_trans hUsp.2.2 hA2
  have hVsm := hVsp.1
  have hVwm := hVsp.2.1
  have hVwb' : Work.Spaces.WlInf α 5 (fun z θ => (z + 1) / z
      * Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ) ≤ A :=
    le_trans hVsp.2.2 hA2
  obtain ⟨hFp, hDthFp, hDzFp, hKerp⟩ := hWfA
  have hFsm := hFp.1
  have hFwm := hFp.2.1
  have hFwb' : Work.Spaces.WlInf α 5 (Work.Construction.Fstar α) ≤ A :=
    le_trans hFp.2.2 hA3
  have hDthFsm := hDthFp.1
  have hDthFwm := hDthFp.2.1
  have hDthFwb' : Work.Spaces.WlInf α 5 (Work.Spaces.Dth (Work.Construction.Fstar α)) ≤ A :=
    le_trans hDthFp.2.2 hA3
  have hDzFsm := hDzFp.1
  have hDzFwm := hDzFp.2.1
  have hDzFwb' : Work.Spaces.WlInf α 5 (Work.Spaces.Dz (Work.Construction.Fstar α)) ≤ A :=
    le_trans hDzFp.2.2 hA3
  have hKersm := hKerp.1
  have hKerwm := hKerp.2.1
  have hKerwb' : Work.Spaces.WlInf α 5 (fun z _ => (-(2 * α)) * Work.Spaces.hKer z) ≤ A :=
    le_trans hKerp.2.2 hA3
  obtain ⟨hφFp, hφDthFp, hφDzFp, hFKthFp, hFKFp⟩ := hHfA
  have hφF := hφFp.1
  have hφFbd' : Work.Spaces.HkNorm α 5
      (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ) ≤ A :=
    le_trans hφFp.2 hA4
  have hφDthF := hφDthFp.1
  have hφDthFbd' : Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z)
      * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ≤ A := le_trans hφDthFp.2 hA4
  have hφDzF := hφDzFp.1
  have hφDzFbd' : Work.Spaces.HkNorm α 5 (fun z θ => z / (1 + z)
      * Work.Spaces.Dz (Work.Construction.Fstar α) z θ) ≤ A := le_trans hφDzFp.2 hA4
  have hFKthF := hFKthFp.1
  have hFKthFbd' : Work.Spaces.HkNorm α 5 (fun z θ =>
      Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ≤ A := le_trans hFKthFp.2 hA4
  have hFKF := hFKFp.1
  have hFKFbd' : Work.Spaces.HkNorm α 5 (fun z θ =>
      Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Construction.Fstar α z θ) ≤ A := le_trans hFKFp.2 hA4
  -- ## the fourteen `ℋ × ℋ` / `𝒲 × ℋ` pieces
  have hp0 := prodHH5 (α := α) (Cprod := Cprod) (c := 2) (a := A) (b := A) hα0 hα1 hCprod
    hPR hAnn hAnn hqoR hRbd' hqow hwbd'
  have hp1 := prodWH5 (α := α) (Cw := Cw) (c := 2) (a := A) (b := A) hα0 hCw hWR hAnn hAnn
    hFsm hFwm hFwb' hqoR hRbd'
  have hp2 := prodWH5 (α := α) (Cw := Cw) (c := 2) (a := A) (b := A) hα0 hCw hWR hAnn hAnn
    hRsm hRwm hRwb' hqoφw hφwbd'
  have hp3 := prodWH5 (α := α) (Cw := Cw) (c := 2) (a := A) (b := A) hα0 hCw hWR hAnn hAnn
    hRsm hRwm hRwb' hφF hφFbd'
  have hp4 := prodHH5 (α := α) (Cprod := Cprod) (c := -2) (a := A) (b := A) hα0 hα1 hCprod
    hPR hAnn hAnn hqoU hUbd' hqoDthw hDthwbd'
  have hp5 := prodWH5 (α := α) (Cw := Cw) (c := -2) (a := A) (b := A) hα0 hCw hWR hAnn hAnn
    hDthFsm hDthFwm hDthFwb' hqoU hUbd'
  have hp6 := prodWH5 (α := α) (Cw := Cw) (c := -2) (a := A) (b := A) hα0 hCw hWR hAnn hAnn
    hUsm hUwm hUwb' hqoφDthw hφDthwbd'
  have hp7 := prodWH5 (α := α) (Cw := Cw) (c := -2) (a := A) (b := A) hα0 hCw hWR hAnn hAnn
    hUsm hUwm hUwb' hφDthF hφDthFbd'
  have hp8 := prodHH5 (α := α) (Cprod := Cprod) (c := -(2 * α)) (a := A) (b := A) hα0 hα1
    hCprod hPR hAnn hAnn hqoV hVbd' hqoDzw hDzwbd'
  have hp9 := prodWH5 (α := α) (Cw := Cw) (c := -(2 * α)) (a := A) (b := A) hα0 hCw hWR
    hAnn hAnn hDzFsm hDzFwm hDzFwb' hqoV hVbd'
  have hp10 := prodWH5 (α := α) (Cw := Cw) (c := -(2 * α)) (a := A) (b := A) hα0 hCw hWR
    hAnn hAnn hVsm hVwm hVwb' hqoφDzw hφDzwbd'
  have hp11 := prodWH5 (α := α) (Cw := Cw) (c := -(2 * α)) (a := A) (b := A) hα0 hCw hWR
    hAnn hAnn hVsm hVwm hVwb' hφDzF hφDzFbd'
  have hp12 := prodHH5 (α := α) (Cprod := Cprod) (c := -(1 / 2)) (a := A) (b := A) hα0 hα1
    hCprod hPR hAnn hAnn hqoFKw hFKwbd' hqoDthw hDthwbd'
  have hp13 := prodWH5 (α := α) (Cw := Cw) (c := -(1 / 2)) (a := A) (b := A) hα0 hCw hWR
    hAnn hAnn hDthFsm hDthFwm hDthFwb' hqoFKw hFKwbd'
  have hp14 := prodWH5 (α := α) (Cw := Cw) (c := (1 / 2)) (a := A) (b := A) hα0 hCw hWR
    hAnn hAnn hKersm hKerwm hKerwb' hqoDthw hDthwbd'
  -- ## the four `sin²θ`-pieces
  have hSinMul : ∀ G : Fn, Work.FTS.EllipticEst.SmoothOpen G → Work.Spaces.HkMem α 5 G →
      Work.Spaces.HkMem α 5 (fun z θ => -(Real.sin θ) ^ 2 * G z θ) ∧
      Work.Spaces.HkSq α 5 (fun z θ => -(Real.sin θ) ^ 2 * G z θ)
        ≤ Cang * Bmax ^ 2 * Work.Spaces.HkSq α 5 G := by
    intro G hGsm hGm
    exact hangfield α hα0 hα1 (fun θ => -(Real.sin θ) ^ 2) Bmax hBmaxpos
      Work.FTS.Nonlinear.Open.row25_smoothOpen_neg_sinSq hSinBnd hSinSlots G hGsm hGm
  have hSinNorm : ∀ {G : Fn}, Work.FTS.EllipticEst.SmoothOpen G → Work.Spaces.HkMem α 5 G →
      Work.Spaces.HkNorm α 5 (fun z θ => -(Real.sin θ) ^ 2 * G z θ)
        ≤ Sang * Work.Spaces.HkNorm α 5 G := by
    intro G hGsm hGm
    have h1 := (hSinMul G hGsm hGm).2
    calc Work.Spaces.HkNorm α 5 (fun z θ => -(Real.sin θ) ^ 2 * G z θ)
        = Real.sqrt (Work.Spaces.HkSq α 5 (fun z θ => -(Real.sin θ) ^ 2 * G z θ)) := rfl
      _ ≤ Real.sqrt (Cang * Bmax ^ 2 * Work.Spaces.HkSq α 5 G) := Real.sqrt_le_sqrt h1
      _ = Sang * Work.Spaces.HkNorm α 5 G := by
          rw [Real.sqrt_mul (by positivity), hSangdef]
          rfl
  have hFKwsmo : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.FK w z) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_FKw_of_classC hw
  have hFKesmo : Work.FTS.EllipticEst.SmoothOpen
      (fun z _ => Work.Construction.FK (Work.Construction.Fstar α) z) :=
    Work.FTS.GalFields.RHS.smoothOpen_FK_Fstar_rad α hα0 hα1
  have hp16i := prodHH5 (α := α) (Cprod := Cprod) (c := 1) (a := A) (b := A) hα0 hα1 hCprod
    hPR hAnn hAnn hqoFKw hFKwbd' hqow hwbd'
  have hp17i := prodWH5 (α := α) (Cw := Cw) (c := 1) (a := A) (b := A) hα0 hCw hWR hAnn hAnn
    hFsm hFwm hFwb' hqoFKw hFKwbd'
  have hp18i := prodWH5 (α := α) (Cw := Cw) (c := 1) (a := A) (b := A) hα0 hCw hWR hAnn hAnn
    hKersm hKerwm hKerwb' hqow hwbd'
  have hp16m : Work.Spaces.HkMem α 5 (fun z θ => -(Real.sin θ) ^ 2
      * (Work.Construction.FK w z * w z θ)) :=
    (hSinMul _ (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hFKwsmo hw.reg)
      (by simpa only [one_mul] using hp16i.1)).1
  have hp16b : Work.Spaces.HkNorm α 5 (fun z θ => -(Real.sin θ) ^ 2
      * (Work.Construction.FK w z * w z θ)) ≤ Sang * P1 := by
    refine le_trans (hSinNorm (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hFKwsmo hw.reg)
      (by simpa only [one_mul] using hp16i.1)) ?_
    exact mul_le_mul_of_nonneg_left (by simpa only [one_mul, abs_one] using hp16i.2) hSangnn
  have hp17m : Work.Spaces.HkMem α 5 (fun z θ => -(Real.sin θ) ^ 2
      * (Work.Construction.Fstar α z θ * Work.Construction.FK w z)) :=
    (hSinMul _ (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hFsm hFKwsmo)
      (by simpa only [one_mul] using hp17i.1)).1
  have hp17b : Work.Spaces.HkNorm α 5 (fun z θ => -(Real.sin θ) ^ 2
      * (Work.Construction.Fstar α z θ * Work.Construction.FK w z))
      ≤ Sang * P2 := by
    refine le_trans (hSinNorm (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hFsm hFKwsmo)
      (by simpa only [one_mul] using hp17i.1)) ?_
    exact mul_le_mul_of_nonneg_left (by simpa only [one_mul, abs_one] using hp17i.2) hSangnn
  have hp18m : Work.Spaces.HkMem α 5 (fun z θ => -(Real.sin θ) ^ 2
      * ((-(2 * α)) * Work.Spaces.hKer z * w z θ)) :=
    (hSinMul _ (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hKersm hw.reg)
      (by simpa only [one_mul] using hp18i.1)).1
  have hp18b : Work.Spaces.HkNorm α 5 (fun z θ => -(Real.sin θ) ^ 2
      * ((-(2 * α)) * Work.Spaces.hKer z * w z θ)) ≤ Sang * P2 := by
    refine le_trans (hSinNorm (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hKersm hw.reg)
      (by simpa only [one_mul] using hp18i.1)) ?_
    exact mul_le_mul_of_nonneg_left (by simpa only [one_mul, abs_one] using hp18i.2) hSangnn
  have hYeq : (fun z θ => (-1) * (-(Real.sin θ) ^ 2
        * ((-(2 * α)) * Work.Spaces.hKer z * w z θ)))
      = Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 18 := by
    funext z θ
    simp only [Work.FTS.StrongEps.ClassCRHS.NBlk]
    rw [Work.FTS.Nonlin.FK_Fstar hα0 hα1, Work.Spaces.hKer_apply]
    ring
  have hp18mN : Work.Spaces.HkMem α 5 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 18) :=
    hYeq ▸ (Work.FTS.LocData.HkMem_const_mul α 5 (-1) hp18m)
  have hp18bN : Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg 18)
      ≤ T 18 := by
    have hb : Work.Spaces.HkNorm α 5 (fun z θ => -(Real.sin θ) ^ 2
        * ((-(2 * α)) * Work.Spaces.hKer z * w z θ)) ≤ Sang * P2 := hp18b
    rw [← hYeq, HkNorm_const_mul5, hTdef]
    simpa only [abs_neg, abs_one, one_mul] using hb
  -- ## pieces 15 and 19: the two fixed `ℋ`-atoms
  have hp15m : Work.Spaces.HkMem α 5 (fun z θ => (-(1 / 2))
      * (Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)) :=
    Work.FTS.LocData.HkMem_const_mul α 5 (-(1 / 2)) hFKthF.2
  have hp15b : Work.Spaces.HkNorm α 5 (fun z θ => (-(1 / 2))
      * (Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)) ≤ A := by
    rw [HkNorm_const_mul5]
    calc |(-(1 / 2))| * Work.Spaces.HkNorm α 5 (fun z θ =>
          Work.Construction.FK (Work.Construction.Fstar α) z
            * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)
        = (1 / 2) * Work.Spaces.HkNorm α 5 (fun z θ =>
            Work.Construction.FK (Work.Construction.Fstar α) z
              * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) := by norm_num
      _ ≤ (1 / 2) * A := mul_le_mul_of_nonneg_left hFKthFbd' (by norm_num)
      _ ≤ A := by linarith [hAnn]
  have hp19m : Work.Spaces.HkMem α 5 (fun z θ => -(Real.sin θ) ^ 2
      * (Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Construction.Fstar α z θ)) :=
    (hSinMul _ (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hFKesmo hFsm) hFKF.2).1
  have hp19b : Work.Spaces.HkNorm α 5 (fun z θ => -(Real.sin θ) ^ 2
      * (Work.Construction.FK (Work.Construction.Fstar α) z
        * Work.Construction.Fstar α z θ)) ≤ Sang * A := by
    refine le_trans (hSinNorm (Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl hFKesmo hFsm)
      hFKF.2) ?_
    exact mul_le_mul_of_nonneg_left hFKFbd' hSangnn
  -- ## the twenty pieces
  have hpiece : ∀ k ∈ Finset.range 20,
      Work.Spaces.HkMem α 5 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k) ∧
      Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.ClassCRHS.NBlk α w Φs Φg k) ≤ T k := by
    intro k hk
    have hk20 : k < 20 := Finset.mem_range.mp hk
    interval_cases k
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp0.1,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp0.2⟩
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp1.1,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp1.2⟩
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp2.1,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp2.2⟩
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp3.1,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp3.2⟩
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp4.1,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp4.2⟩
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp5.1,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp5.2⟩
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp6.1,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp6.2⟩
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp7.1,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp7.2⟩
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp8.1,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp8.2⟩
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp9.1,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp9.2⟩
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp10.1,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp10.2⟩
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp11.1,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp11.2⟩
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp12.1,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp12.2⟩
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp13.1,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp13.2⟩
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp14.1,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp14.2⟩
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp15m,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp15b⟩
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp16m,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp16b⟩
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp17m,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp17b⟩
    · exact ⟨hp18mN, hp18bN⟩
    · exact ⟨by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs] using hp19m,
        by simpa only [Work.FTS.StrongEps.ClassCRHS.NBlk, Work.FTS.Nonlin.PhiTs, hTdef] using hp19b⟩
  intro k hk
  exact ⟨(hpiece k hk).1, le_trans (hpiece k hk).2 (hbE k hk)⟩

end Work.FTS.StrongEps.H5
