import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsMemOfClassCJeps
import Submission.Work.FTS.StrongEps.EpsLocalPStar.SqWeakAux
import Submission.Work.FTS.StrongEps.EpsLocalPStar.profRHS_sub_sup_le
import Submission.Work.FTS.StrongEps.IsEpsSolPQ.EpsSq_intervalIntegral_le_sqrt
import Submission.Work.FTS.StrongEps.IsEpsSolPQ.epsSolP_volterra
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.zeroTermDth
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.radialSupMul_cd6
import Submission.Work.FTS.StrongPersist.SP6.EH6
import Submission.Work.FTS_RegExport.RXB.l12_aux
import Submission.Work.FTS_RegExport.RXR5.R5PiecesF
import Submission.Work.FTS_RegExport.RXR5L.EllProd_C1JetFull
import Submission.Work.FTS_RegExport.RXR5L.mubarData
import Submission.Work.FTS_RegExport.RXT.C2Radial
import Submission.Work.FTS_RegExport.RXT.Sys.FBZhat
import Submission.Work.FTS_RegExport.RXT.Sys.slice_contDiffOn_four
import Submission.Work.FTS_RegExport.RXT.SysAux.FK_jet_pkg_uniform
import Submission.Work.FTS_RegExport.RXT.SysAux.L12_jet_pkg_uniform
import Submission.Work.FTS_RegExport.RegExportProved
import Submission.Work.FTS_RegExport.Supp
import Submission.Work.FTS_RegExport.THL.L.DzDthSG_C1Jet_of_inputs
import Submission.Work.FTS_StreamBdry.Inputs.ftau_Dz_cont
import Submission.Work.FTS_StreamBdry.Inputs.ftau_cont
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_majorant
import Submission.Work.FTS_StreamBdry.SB4.l12_zero_plainE
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Stability.mul_rpow_le
-- ===== merged: Submission.Work.FTS.EpsEngine.SmoothOpenFeps =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

open Work.FTS.StrongEps

set_option autoImplicit false

/-- **The projection `Pz` preserves `SmoothOpen`** (`Pz f = f − c•bump` with `c` a number and
`bump` smooth). -/
theorem smoothOpen_Pz_of_smoothOpen {f : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (Pz f) := by
  have h2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (Work.Construction.L12 f 0 / pzNorm) * bump z θ) :=
    Work.FTS.EllipticEst.SmoothOpen.const_mul' _ Work.FTS.StrongEps.smoothOpen_bump
  have h3 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => f z θ - (Work.Construction.L12 f 0 / pzNorm) * bump z θ) :=
    Work.FTS.EllipticEst.smoothOpen_sub hf h2
  refine Work.FTS.EllipticEst.SmoothOpen.congr h3 (fun z θ _ _ _ => ?_)
  rw [Pz_apply]


end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.profRHS_sub_sup_le_Sq =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000


theorem profRHS_sub_sup_le_Sq {α C₀ Ce Cs R : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {ε : ℝ}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ {u v : Work.FTS.Galerkin.Fn},
      Work.FTS.EllipticEst.SmoothOpen u → Work.FTS.EllipticEst.SmoothOpen v →
      Work.FTS.StrongEps.EpsMem α u → Work.FTS.StrongEps.EpsSq α u ≤ R →
      Work.FTS.StrongEps.EpsMem α v → Work.FTS.StrongEps.EpsSq α v ≤ R →
      Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) →
      Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) →
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) ≤ C₀ * α ^ 2 →
      Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) ≤ C₀ * α ^ 2 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 u z θ
          - Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 v z θ|
          ≤ C * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)) := by
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hγ : 0 < Work.Spaces.gam α - 1 := by
    have := Work.Spaces.one_lt_gam hα0
    linarith
  -- ## the constants of the library
  obtain ⟨K₁, hK₁pos, hK₁⟩ :=
    Work.FTS.StrongEps.EpsRLX.DeltaXnBound (α := α) (C₀ := C₀) (Ce := Ce) (Cs := Cs)
      (Φs := Φs) (E := E) hα hEll hstar hml
  obtain ⟨CT, hCTpos, hCT⟩ := TraceToEpsMem
  obtain ⟨CH, hCHpos, hCH⟩ := Work.FTS.StrongEps.EpsSqTools.HkSq_JepsPz_le ρ hρ
  obtain ⟨CD, hCDpos, hCD⟩ := HkSq_Wp_sub_le_weak (α := α) hρ hα hε hε1
  obtain ⟨Cpt, hCpt0, hCpt⟩ := pointwise_le_HkNorm (α := α) hα0 hα1
  -- ## the `R`-dependent universe of the `ℋ⁶`-sizes of the two profiles
  set BS : ℝ := Real.sqrt (CH * (CH / ε) ^ 10 * R) + Real.sqrt (CH * (CH / ε) ^ 12 * R) + 1
    with hBSdef
  have hBS0 : 0 ≤ BS := by
    rw [hBSdef]
    have h1 := Real.sqrt_nonneg (CH * (CH / ε) ^ 10 * R)
    have h2 := Real.sqrt_nonneg (CH * (CH / ε) ^ 12 * R)
    linarith
  have hWp6 : ∀ {w : Fn}, Work.FTS.EllipticEst.SmoothOpen w → Work.FTS.StrongEps.EpsMem α w →
      Work.FTS.StrongEps.EpsSq α w ≤ R →
      Work.Spaces.HkNorm α 6 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε w) ≤ BS := by
    intro w hsw hmw hrw
    have hfac : 0 ≤ CH * (CH / ε) ^ 12 := by positivity
    have hle : Work.Spaces.HkSq α 6 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε w)
        ≤ CH * (CH / ε) ^ 12 * R :=
      le_trans (hCH α hα ε hε hε1 6 (by norm_num) w hsw hmw)
        (mul_le_mul_of_nonneg_left hrw hfac)
    rw [Work.Spaces.HkNorm]
    refine le_trans (Real.sqrt_le_sqrt hle) ?_
    rw [hBSdef]
    linarith [Real.sqrt_nonneg (CH * (CH / ε) ^ 10 * R),
      Real.sqrt_nonneg (CH * (CH / ε) ^ 12 * R)]
  have hWp5 : ∀ {w : Fn}, Work.FTS.EllipticEst.SmoothOpen w → Work.FTS.StrongEps.EpsMem α w →
      Work.FTS.StrongEps.EpsSq α w ≤ R →
      Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε w) ≤ BS := by
    intro w hsw hmw hrw
    have hfac : 0 ≤ CH * (CH / ε) ^ 10 := by positivity
    have hle : Work.Spaces.HkSq α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε w)
        ≤ CH * (CH / ε) ^ 10 * R :=
      le_trans (hCH α hα ε hε hε1 5 (by norm_num) w hsw hmw)
        (mul_le_mul_of_nonneg_left hrw hfac)
    rw [Work.Spaces.HkNorm]
    refine le_trans (Real.sqrt_le_sqrt hle) ?_
    rw [hBSdef]
    linarith [Real.sqrt_nonneg (CH * (CH / ε) ^ 10 * R),
      Real.sqrt_nonneg (CH * (CH / ε) ^ 12 * R)]
  -- ## the elliptic data of the profiles
  obtain ⟨RX, hRXpos, hRX⟩ :=
    Work.FTS.StrongEps.EpsRLX.XDataClean (α := α) (Ce := Ce) (Cs := Cs) (C₀ := C₀) (B := BS)
      hα hEll hstar hml hBS0
  -- ## the final constants
  set Q : ℝ := Real.sqrt CD with hQdef
  have hQ0 : 0 ≤ Q := Real.sqrt_nonneg _
  set M₀ : ℝ := 1 + 2 * BS with hM₀def
  have hM₀1 : 1 ≤ M₀ := by rw [hM₀def]; linarith
  have hM₀0 : 0 ≤ M₀ := le_trans zero_le_one hM₀1
  set T : ℝ := Real.sqrt (CH * (CH / ε) ^ 8 * (CT / (Work.Spaces.gam α - 1) ^ 2)) with hTdef
  have hT0 : 0 ≤ T := Real.sqrt_nonneg _
  refine ⟨max 1 (Cpt * T * K₁ * M₀ ^ 2 * Q), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro u v hsu hsv hmu hru hmv hrv hclu hclv hxnu hxnv
  -- ## the abbreviations
  set Φu : Fn := profRHS α Φs E (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) with hΦudef
  set Φv : Fn := profRHS α Φs E (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) with hΦvdef
  set Δ : Fn := fun z θ => Φu z θ - Φv z θ with hΔdef
  set d : Fn := fun z θ => Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ
      - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v z θ with hddef
  -- ## the `ℋ⁴`-data of `Δ`
  obtain ⟨hΔsm₀, hΔmem₀, hΔxn₀⟩ := hK₁
    (W₁ := Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)
    (W₂ := Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) hclu hclv hxnu hxnv
  have hΔsm : Work.FTS.EllipticEst.SmoothOpen Δ := by
    rw [hΔdef]
    simpa only [hΦudef, hΦvdef] using hΔsm₀
  have hΔmem4 : Work.Spaces.HkMem α 4 Δ := by
    rw [hΔdef]
    simpa only [hΦudef, hΦvdef] using hΔmem₀
  have hΔmem1 : Work.Spaces.HkMem α 1 Δ :=
    Work.FTS.OpenPkg.HkMem_mono_open hΔsm 1 (by norm_num) hΔmem4
  have hΔxn : Work.FTS.Nonlin.Xn α Δ
      ≤ K₁ * (1 + Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)
          + Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v)) ^ 2
        * Work.Spaces.HkNorm α 5 d := by
    rw [hΔdef, hddef]
    simpa only [hΦudef, hΦvdef] using hΔxn₀
  -- ## `EpsMem`/`EpsSq` of `Δ` via the vanishing angular traces
  obtain ⟨ht1, ht2⟩ := Work.FTS.StrongEps.EpsRLX.DiffTraces (α := α) (Ce := Ce) (Cs := Cs)
    (Φs := Φs) (W₁ := Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)
    (W₂ := Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) (E := E) hα hclu hclv
    ((hEll (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) hclu).1)
    ((hEll (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) hclv).1) hstar
  obtain ⟨hΔepsMem, hΔepsSq⟩ := hCT α hα Δ hΔsm hΔmem1
    (fun z hz => by simpa only [hΦudef, hΦvdef] using ht1 z hz)
    (fun z hz => by simpa only [hΦudef, hΦvdef] using ht2 z hz)
  have hΔHk : Work.Spaces.HkSq α 1 Δ ≤ (Work.FTS.Nonlin.Xn α Δ) ^ 2 := by
    refine le_trans (Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num) hΔmem4) ?_
    rw [show Work.FTS.Nonlin.Xn α Δ = Work.Spaces.HkNorm α 4 Δ from rfl, Work.Spaces.HkNorm,
      Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 Δ)]
  -- ## the per-profile regularity of the two right-hand sides
  have hXu := hRX (W := Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) hclu hxnu (hWp6 hsu hmu hru)
  have hXv := hRX (W := Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) hclv hxnv (hWp6 hsv hmv hrv)
  have hsmΦu : Work.FTS.EllipticEst.SmoothOpen Φu := by rw [hΦudef]; exact hXu.1
  have hmem4Φu : Work.Spaces.HkMem α 4 Φu := by rw [hΦudef]; exact hXu.2.1
  have hsmΦv : Work.FTS.EllipticEst.SmoothOpen Φv := by rw [hΦvdef]; exact hXv.1
  have hmem4Φv : Work.Spaces.HkMem α 4 Φv := by rw [hΦvdef]; exact hXv.2.1
  -- ## the size bounds
  have hDd : Work.Spaces.HkSq α 5 d
      ≤ CD * Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ) := by
    rw [hddef]
    exact hCD hsu hsv hmu hmv hclu hclv
  have hQbd : Work.Spaces.HkNorm α 5 d
      ≤ Q * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)) := by
    rw [Work.Spaces.HkNorm, hQdef]
    calc Real.sqrt (Work.Spaces.HkSq α 5 d)
        ≤ Real.sqrt (CD * Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)) :=
          Real.sqrt_le_sqrt hDd
      _ = Real.sqrt CD * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)) :=
          Real.sqrt_mul hCDpos.le _
  have hWu : Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) ≤ BS :=
    hWp5 hsu hmu hru
  have hWv : Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) ≤ BS :=
    hWp5 hsv hmv hrv
  have hMle : 1 + Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)
      + Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) ≤ M₀ := by
    rw [hM₀def]
    linarith
  have hM0 : 0 ≤ 1 + Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)
      + Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) := by
    have h1 : 0 ≤ Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u) :=
      Work.Spaces.HkNorm_nonneg α 5 _
    have h2 : 0 ≤ Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v) :=
      Work.Spaces.HkNorm_nonneg α 5 _
    linarith
  have hXnΔ : Work.FTS.Nonlin.Xn α Δ ≤ K₁ * M₀ ^ 2 * Work.Spaces.HkNorm α 5 d := by
    refine le_trans hΔxn ?_
    have hM2 : (1 + Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε u)
        + Work.Spaces.HkNorm α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε v)) ^ 2 ≤ M₀ ^ 2 :=
      pow_le_pow_left₀ hM0 hMle 2
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM2 hK₁pos.le)
      (Work.Spaces.HkNorm_nonneg α 5 d)
  have hKM : 0 ≤ K₁ * M₀ ^ 2 := mul_nonneg hK₁pos.le (pow_nonneg hM₀0 2)
  -- ## the mollified difference
  have hsmJΔ : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε Δ) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall Δ).mp hΔsm)
  have hsmWpΔ : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.EpsRLX.Wp ρ ε Δ) :=
    smoothOpen_Pz hsmJΔ
  have hmemWpΔ : Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε Δ) :=
    hkMem_Pz hsmJΔ (Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε
      ((Work.FTS.EllipticEst.smoothOpen_iff_forall Δ).mp hΔsm) hΔmem4)
  have hWpSq : Work.Spaces.HkSq α 4 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε Δ)
      ≤ CH * (CH / ε) ^ 8 * Work.FTS.StrongEps.EpsSq α Δ :=
    hCH α hα ε hε hε1 4 (by norm_num) Δ hΔsm hΔepsMem
  have hTbd : Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε Δ)
      ≤ T * Work.Spaces.HkNorm α 4 Δ := by
    have hx0 : 0 ≤ Work.Spaces.HkNorm α 4 Δ := Work.Spaces.HkNorm_nonneg α 4 Δ
    have hc1 : 0 ≤ CH * (CH / ε) ^ 8 := by positivity
    have hc2 : 0 ≤ CT / (Work.Spaces.gam α - 1) ^ 2 := div_nonneg hCTpos.le (sq_nonneg _)
    have hprod0 : 0 ≤ CH * (CH / ε) ^ 8 * (CT / (Work.Spaces.gam α - 1) ^ 2) :=
      mul_nonneg hc1 hc2
    have hA2 : Work.Spaces.HkSq α 4 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε Δ)
        ≤ T ^ 2 * (Work.Spaces.HkNorm α 4 Δ) ^ 2 := by
      refine le_trans hWpSq ?_
      calc CH * (CH / ε) ^ 8 * Work.FTS.StrongEps.EpsSq α Δ
          ≤ CH * (CH / ε) ^ 8
              * (CT / (Work.Spaces.gam α - 1) ^ 2 * Work.Spaces.HkSq α 1 Δ) :=
            mul_le_mul_of_nonneg_left hΔepsSq hc1
        _ ≤ CH * (CH / ε) ^ 8 * (CT / (Work.Spaces.gam α - 1) ^ 2
              * (Work.Spaces.HkNorm α 4 Δ) ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hΔHk hc2) hc1
        _ = T ^ 2 * (Work.Spaces.HkNorm α 4 Δ) ^ 2 := by
            rw [hTdef, Real.sq_sqrt hprod0]; ring
    rw [Work.Spaces.HkNorm]
    calc Real.sqrt (Work.Spaces.HkSq α 4 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε Δ))
        ≤ Real.sqrt (T ^ 2 * (Work.Spaces.HkNorm α 4 Δ) ^ 2) := Real.sqrt_le_sqrt hA2
      _ = T * Work.Spaces.HkNorm α 4 Δ := by
          rw [Real.sqrt_mul (sq_nonneg T), Real.sqrt_sq hT0, Real.sqrt_sq hx0]
  -- ## the second conjunct: the slice difference is the mollified profile of `Δ`
  have hIdent : Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 u
        - Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 v
      = Work.FTS.StrongEps.EpsRLX.Wp ρ ε Δ := by
    have h1 : Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 u
          - Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 v
        = Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε Φu)
          - Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε Φv) := by
      rw [Work.FTS.StrongEps.EpsLocalPStar.epsRHPSlice_eq_profRHS α ρ ε Φs E 0 u,
        Work.FTS.StrongEps.EpsLocalPStar.epsRHPSlice_eq_profRHS α ρ ε Φs E 0 v,
        hΦudef, hΦvdef]
      rfl
    rw [h1, hΔdef]
    exact Wp_sub_eq_mem hα hρ hε hsmΦu hsmΦv hmem4Φu hmem4Φv
  intro z θ hz hθ0 hθ1
  have hpt1 : Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 u z θ
        - Work.FTS.StrongEps.epsRHPSlice α ρ ε Φs E 0 v z θ
      = Work.FTS.StrongEps.EpsRLX.Wp ρ ε Δ z θ := by
    have := congrFun (congrFun hIdent z) θ
    simpa only [Pi.sub_apply] using this
  rw [hpt1]
  have hfinal : |Work.FTS.StrongEps.EpsRLX.Wp ρ ε Δ z θ|
      ≤ (Cpt * T * K₁ * M₀ ^ 2 * Q)
        * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)) := by
    calc |Work.FTS.StrongEps.EpsRLX.Wp ρ ε Δ z θ|
        ≤ Cpt * Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε Δ) :=
          hCpt hsmWpΔ hmemWpΔ hz hθ0 hθ1
      _ ≤ Cpt * (T * Work.Spaces.HkNorm α 4 Δ) :=
          mul_le_mul_of_nonneg_left hTbd hCpt0
      _ ≤ Cpt * (T * (K₁ * M₀ ^ 2 * Work.Spaces.HkNorm α 5 d)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hXnΔ hT0) hCpt0
      _ ≤ Cpt * (T * (K₁ * M₀ ^ 2
            * (Q * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ))))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQbd hKM) hT0) hCpt0
      _ = (Cpt * T * K₁ * M₀ ^ 2 * Q)
            * Real.sqrt (Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ)) := by ring
  exact le_trans hfinal (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _))

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.IsEpsSolP_eq_of_epsClass_proof =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.StrongEps.IsEpsSolPQ

set_option autoImplicit false

/-! ## Elementary honesty facts -/

/-- `EpsSq` is the integral of the weighted square over the domain measure `DomM`, for honest
members of the weighted space. -/
theorem EpsSq_eq_integral_DomM {α : ℝ} {f : Fn} (hf : EpsMem α f) :
    (∫ p : ℝ × ℝ, (f p.1 p.2 * epsW α p.1 p.2) ^ 2 ∂EpsLocalPStar.DomM) = EpsSq α f := by
  have hg : Integrable (fun p : ℝ × ℝ => (f p.1 p.2 * epsW α p.1 p.2) ^ 2)
      EpsLocalPStar.DomM := (EpsLocalPStar.EpsMem_iff_integrable2).mp hf
  rw [EpsSq, EpsLocalPStar.DomM]
  exact MeasureTheory.integral_prod _ hg

/-- A member of the engine's class `EpsClass` is an honest member of the weighted space: this is
`EpsMemOfClassCJeps`, whose hypothesis is exactly the `ClassC` clause of `EpsClass` (a statement
about the *projected mollified* slice). -/
theorem EpsMem_of_EpsClass {α C₁ B ε : ℝ} {ρ : ℝ × ℝ → ℝ} {u : Fn}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hu : Work.FTS.EpsEngine.EpsClass α ρ ε C₁ B u) : EpsMem α u := by
  obtain ⟨C, hC, h⟩ := Work.FTS.StrongEps.EpsLocalPStar.EpsMemOfClassCJeps ρ hρ
  exact (h α hα ε hε hε1 u hu.smoothOpen hu.hkMem hu.classC).1


/-- A `SmoothOpen` profile is a.e. strongly measurable in the weighted sense. -/
theorem AK2_of_SmoothOpen {α : ℝ} {u : Fn} (hu : Work.FTS.EllipticEst.SmoothOpen u) :
    EpsLocalPStar.AK2 α u := by
  rw [EpsLocalPStar.AK2]
  have hc : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (hu.forall 0).continuousOn
  have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => u p.1 p.2)
      EpsLocalPStar.DomM := by
    simpa only [EpsLocalPStar.DomM] using Work.Spaces.aesm_of_continuousOn_Qd _ hc
  have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => epsW α p.1 p.2) EpsLocalPStar.DomM :=
    (EpsLocalPStar.measurable_epsW α).aestronglyMeasurable
  refine (h1.mul h2).congr ?_
  filter_upwards with p
  simp only [Pi.mul_apply]

/-- The difference of two admissible slices is an honest member of the weighted space. -/
theorem EpsMem_sub_of_EpsClass {α C₁ B ε : ℝ} {ρ : ℝ × ℝ → ℝ} {u v : Fn}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hu : Work.FTS.EpsEngine.EpsClass α ρ ε C₁ B u)
    (hv : Work.FTS.EpsEngine.EpsClass α ρ ε C₁ B v) :
    EpsMem α (fun z θ => u z θ - v z θ) :=
  EpsLocalPStar.EpsMem_sub2 (AK2_of_SmoothOpen hu.smoothOpen) (AK2_of_SmoothOpen hv.smoothOpen)
    (EpsMem_of_EpsClass hα hρ hε hε1 hu) (EpsMem_of_EpsClass hα hρ hε hε1 hv)

/-- Pointwise domination of the weighted square of a difference (used to transfer integrability
and to bound `EpsSq` of a difference in terms of the two `EpsSq`'s). -/
theorem sq_sub_mul_le {a b c : ℝ} :
    ((a - b) * c) ^ 2 ≤ 2 * (a * c) ^ 2 + 2 * (b * c) ^ 2 := by
  nlinarith [sq_nonneg (a * c), sq_nonneg (b * c), sq_nonneg (a * c + b * c),
    sq_nonneg (a * c - b * c)]

/-- `EpsSq` of a difference is controlled by the two `EpsSq`'s, for honest summands. -/
theorem EpsSq_sub_le {α : ℝ} {u v : Fn} (hu : EpsMem α u) (hv : EpsMem α v)
    (huv : EpsMem α (fun z θ => u z θ - v z θ)) :
    EpsSq α (fun z θ => u z θ - v z θ) ≤ 2 * EpsSq α u + 2 * EpsSq α v := by
  have hX : Integrable (fun p : ℝ × ℝ => (u p.1 p.2 * epsW α p.1 p.2) ^ 2)
      EpsLocalPStar.DomM := (EpsLocalPStar.EpsMem_iff_integrable2).mp hu
  have hY : Integrable (fun p : ℝ × ℝ => (v p.1 p.2 * epsW α p.1 p.2) ^ 2)
      EpsLocalPStar.DomM := (EpsLocalPStar.EpsMem_iff_integrable2).mp hv
  have hD : Integrable
      (fun p : ℝ × ℝ => ((u p.1 p.2 - v p.1 p.2) * epsW α p.1 p.2) ^ 2)
      EpsLocalPStar.DomM := (EpsLocalPStar.EpsMem_iff_integrable2).mp huv
  rw [← EpsSq_eq_integral_DomM huv, ← EpsSq_eq_integral_DomM hu, ← EpsSq_eq_integral_DomM hv]
  refine le_trans (MeasureTheory.integral_mono hD (hX.const_mul 2 |>.add (hY.const_mul 2))
    (fun p => sq_sub_mul_le)) ?_
  simp only [Pi.add_apply]
  rw [MeasureTheory.integral_add (hX.const_mul 2) (hY.const_mul 2),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

/-- **Measurability of the `√EpsSq` of a jointly measurable, a.e. honest curve of profiles.**
Together with an a.e. bound this is the integrability input of the Minkowski/Grönwall step. -/
theorem aesm_sqrt_EpsSq {α τ : ℝ} {Φ : ℝ → Fn}
    (hmeas : AEStronglyMeasurable
      (fun q : ℝ × (ℝ × ℝ) => Φ q.1 q.2.1 q.2.2 * epsW α q.2.1 q.2.2)
      ((MeasureTheory.volume.restrict (Set.uIoc 0 τ)).prod EpsLocalPStar.DomM))
    (hmem : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)), EpsMem α (Φ s)) :
    AEStronglyMeasurable (fun s : ℝ => Real.sqrt (EpsSq α (Φ s)))
      (MeasureTheory.volume.restrict (Set.uIoc 0 τ)) := by
  have h1 : AEStronglyMeasurable
      (fun s : ℝ => ∫ p : ℝ × ℝ,
        (Φ s p.1 p.2 * epsW α p.1 p.2) ^ 2 ∂EpsLocalPStar.DomM)
      (MeasureTheory.volume.restrict (Set.uIoc 0 τ)) :=
    (hmeas.pow 2).integral_prod_right'
  refine (Real.continuous_sqrt.comp_aestronglyMeasurable h1).congr ?_
  filter_upwards [hmem] with s hs
  rw [EpsSq_eq_integral_DomM hs]

end Work.FTS.StrongEps.IsEpsSolPQ

namespace Work.FTS.StrongEps

set_option autoImplicit false

theorem IsEpsSolP_eq_of_epsClass_proof {α C₁ Ce Cs B T ε : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g₀ : Work.FTS.Galerkin.Fn} {g g' : Work.FTS.Galerkin.Fam}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hT : 0 < T)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) (hml : Work.FTS.StrongEps.MuLamOK α C₁ Φs E)
    (hB : 0 ≤ B)
    (hsol : Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g)
    (hsol' : Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g')
    (hcl : ∀ τ ∈ Set.Icc 0 T, Work.FTS.EpsEngine.EpsClass α ρ ε C₁ B
      (Work.FTS.Galerkin.slice g τ))
    (hcl' : ∀ τ ∈ Set.Icc 0 T, Work.FTS.EpsEngine.EpsClass α ρ ε C₁ B
      (Work.FTS.Galerkin.slice g' τ))
    (hc1 : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T))
    (hc1' : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g' p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T)) :
    ∀ τ ∈ Set.Icc 0 T, ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → g z θ τ = g' z θ τ := by
  -- ## abbreviations of the argument
  set F : Fn → Fn := Work.FTS.EpsEngine.Feps α ρ ε Φs E with hFdef
  set W : ℝ → Fn := fun s z θ =>
    Work.FTS.Galerkin.slice g s z θ - Work.FTS.Galerkin.slice g' s z θ with hWdef
  set Gc : ℝ → Fn := fun s z θ =>
    F (Work.FTS.Galerkin.slice g s) z θ - F (Work.FTS.Galerkin.slice g' s) z θ with hGcdef
  have hT0 : 0 ≤ T := hT.le
  -- ## the Lipschitz gate of the engine at the radius of the class
  obtain ⟨L, hLpos, hbd, hlip⟩ := Work.FTS.EpsEngine.BddLip_of_epsClass
    (α := α) (C₁ := C₁) (Ce := Ce) (Cs := Cs) (B := B) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε)
    hα hρ hε hε1 hEll hstar hml hB
  have hL0 : 0 ≤ L := hLpos.le
  -- ## the Volterra identity, together with the joint measurability of the two curves
  obtain ⟨hvol, hmeasG, hmeasW⟩ := Work.FTS.StrongEps.IsEpsSolPQ.epsSolP_volterra
    (α := α) (C₁ := C₁) (Ce := Ce) (Cs := Cs) (B := B) (T := T) (ε := ε) (ρ := ρ) (Φs := Φs)
    (E := E) (g₀ := g₀) (g := g) (g' := g') hα hρ hε hε1 hT hEll hstar hml hB hsol hsol' hc1 hc1'
  -- ## honesty of the slices and of their difference
  have hmem_slice : ∀ τ ∈ Set.Icc 0 T, EpsMem α (Work.FTS.Galerkin.slice g τ) := fun τ hτ =>
    Work.FTS.StrongEps.IsEpsSolPQ.EpsMem_of_EpsClass hα hρ hε hε1 (hcl τ hτ)
  have hmem_slice' : ∀ τ ∈ Set.Icc 0 T, EpsMem α (Work.FTS.Galerkin.slice g' τ) := fun τ hτ =>
    Work.FTS.StrongEps.IsEpsSolPQ.EpsMem_of_EpsClass hα hρ hε hε1 (hcl' τ hτ)
  have hmemW : ∀ τ ∈ Set.Icc 0 T, EpsMem α (W τ) := fun τ hτ =>
    Work.FTS.StrongEps.IsEpsSolPQ.EpsMem_sub_of_EpsClass hα hρ hε hε1 (hcl τ hτ) (hcl' τ hτ)
  -- ## the two halves of the right-hand side are honest and bounded
  have hmemF : ∀ τ ∈ Set.Icc 0 T, EpsMem α (F (Work.FTS.Galerkin.slice g τ)) := fun τ hτ =>
    (hbd _ (hcl τ hτ)).1
  have hmemF' : ∀ τ ∈ Set.Icc 0 T, EpsMem α (F (Work.FTS.Galerkin.slice g' τ)) := fun τ hτ =>
    (hbd _ (hcl' τ hτ)).1
  have hbdF : ∀ τ ∈ Set.Icc 0 T, EpsSq α (F (Work.FTS.Galerkin.slice g τ)) ≤ L := fun τ hτ =>
    (hbd _ (hcl τ hτ)).2
  have hbdF' : ∀ τ ∈ Set.Icc 0 T, EpsSq α (F (Work.FTS.Galerkin.slice g' τ)) ≤ L := fun τ hτ =>
    (hbd _ (hcl' τ hτ)).2
  -- ## a.e. honesty and a.e. boundedness of the right-hand side curve
  have hsae : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc 0 T)), s ∈ Set.Icc 0 T := by
    have h1 : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc 0 T)), s ∈ Set.Ioc 0 T := by
      rw [Set.uIoc_of_le hT0]
      exact MeasureTheory.ae_restrict_mem measurableSet_Ioc
    filter_upwards [h1] with s hs using ⟨hs.1.le, hs.2⟩
  have hAKG : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc 0 T)),
      Work.FTS.StrongEps.EpsLocalPStar.AK2 α (Gc s) := by
    have h1 := (hmeasG T ⟨hT0, le_refl T⟩).prodMk_left
    filter_upwards [h1] with s hs using hs
  have hmemG : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc 0 T)), EpsMem α (Gc s) := by
    filter_upwards [hAKG, hsae] with s hsAK hsI
    rw [Work.FTS.StrongEps.EpsLocalPStar.EpsMem_iff_integrable2]
    have hmeas : AEStronglyMeasurable
        (fun p : ℝ × ℝ => (Gc s p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
        Work.FTS.StrongEps.EpsLocalPStar.DomM := hsAK.pow 2
    have hXu : Integrable (fun p : ℝ × ℝ => (F (Work.FTS.Galerkin.slice g s) p.1 p.2
        * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2) Work.FTS.StrongEps.EpsLocalPStar.DomM :=
      (Work.FTS.StrongEps.EpsLocalPStar.EpsMem_iff_integrable2).mp (hmemF s hsI)
    have hXv : Integrable (fun p : ℝ × ℝ => (F (Work.FTS.Galerkin.slice g' s) p.1 p.2
        * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2) Work.FTS.StrongEps.EpsLocalPStar.DomM :=
      (Work.FTS.StrongEps.EpsLocalPStar.EpsMem_iff_integrable2).mp (hmemF' s hsI)
    have hdom : Integrable (fun p : ℝ × ℝ => 2 * (F (Work.FTS.Galerkin.slice g s) p.1 p.2
          * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2
        + 2 * (F (Work.FTS.Galerkin.slice g' s) p.1 p.2
          * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2) Work.FTS.StrongEps.EpsLocalPStar.DomM :=
      (hXu.const_mul 2).add (hXv.const_mul 2)
    refine Integrable.mono' hdom hmeas ?_
    filter_upwards with p
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h := Work.FTS.StrongEps.IsEpsSolPQ.sq_sub_mul_le
      (a := F (Work.FTS.Galerkin.slice g s) p.1 p.2)
      (b := F (Work.FTS.Galerkin.slice g' s) p.1 p.2)
      (c := Work.FTS.StrongEps.epsW α p.1 p.2)
    simpa only [hGcdef] using h
  have hbndG : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc 0 T)), EpsSq α (Gc s) ≤ 4 * L := by
    filter_upwards [hmemG, hsae] with s hmem hsI
    have hsub := Work.FTS.StrongEps.IsEpsSolPQ.EpsSq_sub_le (hmemF s hsI) (hmemF' s hsI) hmem
    have h1 := hbdF s hsI
    have h2 := hbdF' s hsI
    have hsub' : EpsSq α (Gc s) ≤ 2 * EpsSq α (F (Work.FTS.Galerkin.slice g s))
        + 2 * EpsSq α (F (Work.FTS.Galerkin.slice g' s)) := by
      simpa only [hGcdef] using hsub
    linarith
  -- ## the Lipschitz bound in the strong weight
  have hlipW : ∀ τ ∈ Set.Icc 0 T, EpsSq α (Gc τ) ≤ L * EpsSq α (W τ) := by
    intro τ hτ
    have h := hlip (Work.FTS.Galerkin.slice g τ) (Work.FTS.Galerkin.slice g' τ)
      (hcl τ hτ) (hcl' τ hτ)
    simpa only [hGcdef, hWdef, hFdef] using h
  -- ## the `L²`-Minkowski estimate, for every horizon
  have hMink : ∀ τ ∈ Set.Icc 0 T,
      EpsSq α (W τ) ≤ (∫ s in (0 : ℝ)..τ, Real.sqrt (EpsSq α (Gc s))) ^ 2 := by
    intro τ hτ
    have hsubu : Set.uIoc 0 τ ⊆ Set.uIoc 0 T := by
      rw [Set.uIoc_of_le hτ.1, Set.uIoc_of_le hT0]
      exact Set.Ioc_subset_Ioc_right hτ.2
    have hle : MeasureTheory.volume.restrict (Set.uIoc 0 τ)
        ≤ MeasureTheory.volume.restrict (Set.uIoc 0 T) :=
      MeasureTheory.Measure.restrict_mono hsubu (le_refl _)
    have hGmem' : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)), EpsMem α (Gc s) :=
      Filter.Eventually.filter_mono (MeasureTheory.ae_mono hle) hmemG
    have hbnd' : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)), EpsSq α (Gc s) ≤ 4 * L :=
      Filter.Eventually.filter_mono (MeasureTheory.ae_mono hle) hbndG
    have hw : ∀ᵐ p ∂Work.FTS.StrongEps.EpsLocalPStar.DomM,
        W τ p.1 p.2 = ∫ s in (0 : ℝ)..τ, Gc s p.1 p.2 := by
      filter_upwards [Work.FTS.StrongEps.EpsLocalPStar.ae_open_DomM] with p hp
      have h := hvol p.1 p.2 τ hp.1 ⟨hp.2.1, hp.2.2⟩ hτ
      simpa only [hWdef, hGcdef, hFdef, Work.FTS.Galerkin.slice] using h
    exact Work.FTS.StrongEps.IsEpsSolPQ.EpsSq_intervalIntegral_le_sqrt hτ.1 (by linarith)
      (hmeasG τ hτ) hGmem' hbnd' (hmemW τ hτ) hw
  -- ## the uniform bound on `φ = √(EpsSq α (W ·))`
  obtain ⟨CB, hCBpos, hCB⟩ := Work.FTS.StrongEps.EpsLocalPStar.EpsMemOfClassCJeps ρ hρ
  set M : ℝ := Real.sqrt (4 * (CB / (Work.Spaces.gam α - 1) ^ 2 * B ^ 2)) with hMdef
  have hM0 : 0 ≤ M := Real.sqrt_nonneg _
  have hEpsSq_slice : ∀ τ ∈ Set.Icc 0 T,
      EpsSq α (Work.FTS.Galerkin.slice g τ) ≤ CB / (Work.Spaces.gam α - 1) ^ 2 * B ^ 2 := by
    intro τ hτ
    have hb := (hCB α hα ε hε hε1 (Work.FTS.Galerkin.slice g τ) (hcl τ hτ).smoothOpen
      (hcl τ hτ).hkMem (hcl τ hτ).classC).2
    have hmono := Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (k := 1) (l := 6) (by norm_num)
      (hcl τ hτ).hkMem
    have hB2 : Work.Spaces.HkSq α 1 (Work.FTS.Galerkin.slice g τ) ≤ B ^ 2 := by
      refine le_trans hmono ?_
      rw [show Work.Spaces.HkSq α 6 (Work.FTS.Galerkin.slice g τ)
        = (Work.Spaces.HkNorm α 6 (Work.FTS.Galerkin.slice g τ)) ^ 2 from
          (Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 _)).symm]
      exact pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 6 _) (hcl τ hτ).hkNorm 2
    exact le_trans hb (mul_le_mul_of_nonneg_left hB2 (div_nonneg hCBpos.le (sq_nonneg _)))
  have hEpsSq_slice' : ∀ τ ∈ Set.Icc 0 T,
      EpsSq α (Work.FTS.Galerkin.slice g' τ) ≤ CB / (Work.Spaces.gam α - 1) ^ 2 * B ^ 2 := by
    intro τ hτ
    have hb := (hCB α hα ε hε hε1 (Work.FTS.Galerkin.slice g' τ) (hcl' τ hτ).smoothOpen
      (hcl' τ hτ).hkMem (hcl' τ hτ).classC).2
    have hmono := Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (k := 1) (l := 6) (by norm_num)
      (hcl' τ hτ).hkMem
    have hB2 : Work.Spaces.HkSq α 1 (Work.FTS.Galerkin.slice g' τ) ≤ B ^ 2 := by
      refine le_trans hmono ?_
      rw [show Work.Spaces.HkSq α 6 (Work.FTS.Galerkin.slice g' τ)
        = (Work.Spaces.HkNorm α 6 (Work.FTS.Galerkin.slice g' τ)) ^ 2 from
          (Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 _)).symm]
      exact pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 6 _) (hcl' τ hτ).hkNorm 2
    exact le_trans hb (mul_le_mul_of_nonneg_left hB2 (div_nonneg hCBpos.le (sq_nonneg _)))
  have hWbd : ∀ τ ∈ Set.Icc 0 T, EpsSq α (W τ) ≤ M ^ 2 := by
    intro τ hτ
    have hsub := Work.FTS.StrongEps.IsEpsSolPQ.EpsSq_sub_le (hmem_slice τ hτ) (hmem_slice' τ hτ)
      (hmemW τ hτ)
    have hsub' : EpsSq α (W τ) ≤ 2 * EpsSq α (Work.FTS.Galerkin.slice g τ)
        + 2 * EpsSq α (Work.FTS.Galerkin.slice g' τ) := by
      simpa only [hWdef] using hsub
    have h1 := hEpsSq_slice τ hτ
    have h2 := hEpsSq_slice' τ hτ
    rw [hMdef, Real.sq_sqrt (by positivity)]
    linarith
  -- ## the Grönwall inequality
  have hmeasW2 : MeasureTheory.AEStronglyMeasurable (fun s : ℝ => EpsSq α (W s))
      (MeasureTheory.volume.restrict (Set.uIoc 0 T)) := by
    have h1 : MeasureTheory.AEStronglyMeasurable
        (fun s : ℝ => ∫ p : ℝ × ℝ,
          (W s p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2
          ∂Work.FTS.StrongEps.EpsLocalPStar.DomM)
        (MeasureTheory.volume.restrict (Set.uIoc 0 T)) :=
      ((hmeasW T ⟨hT0, le_refl T⟩).pow 2).integral_prod_right'
    refine h1.congr ?_
    filter_upwards [hsae] with s hsI
    exact Work.FTS.StrongEps.IsEpsSolPQ.EpsSq_eq_integral_DomM (hmemW s hsI)
  have hφaeT : MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Real.sqrt (EpsSq α (W s)))
      (MeasureTheory.volume.restrict (Set.uIoc 0 T)) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hmeasW2
  have hbdaT : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc 0 T)),
      ‖Real.sqrt (EpsSq α (W s))‖ ≤ M := by
    filter_upwards [hsae] with s hsI
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    calc Real.sqrt (EpsSq α (W s)) ≤ Real.sqrt (M ^ 2) := Real.sqrt_le_sqrt (hWbd s hsI)
      _ = M := Real.sqrt_sq hM0
  haveI hfinT : IsFiniteMeasure (MeasureTheory.volume.restrict (Set.uIoc 0 T)) := ⟨by
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Real.volume_uIoc, sub_zero, abs_of_nonneg hT0]
    exact ENNReal.ofReal_lt_top⟩
  have hintφ : MeasureTheory.IntegrableOn (fun s : ℝ => Real.sqrt (EpsSq α (W s)))
      (Set.Icc 0 T) := by
    have hInt := MeasureTheory.Integrable.of_bound hφaeT M hbdaT
    show Integrable (fun s : ℝ => Real.sqrt (EpsSq α (W s)))
      (MeasureTheory.volume.restrict (Set.Icc 0 T))
    rw [← MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioc_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0) (b := T)),
      ← Set.uIoc_of_le hT0]
    exact hInt
  have hgron : ∀ τ ∈ Set.Icc 0 T, Real.sqrt (EpsSq α (W τ)) = 0 := by
    refine Work.FTS.StrongEps.IsEpsSolPQ.eq_zero_of_le_mul_intervalIntegral
      (Real.sqrt_nonneg L) hT0 hM0 hintφ (fun τ hτ => Real.sqrt_nonneg _)
      (fun τ hτ => ?_) (fun τ hτ => ?_)
    · calc Real.sqrt (EpsSq α (W τ)) ≤ Real.sqrt (M ^ 2) := Real.sqrt_le_sqrt (hWbd τ hτ)
        _ = M := Real.sqrt_sq hM0
    · have hsubu : Set.uIoc 0 τ ⊆ Set.uIoc 0 T := by
        rw [Set.uIoc_of_le hτ.1, Set.uIoc_of_le hT0]
        exact Set.Ioc_subset_Ioc_right hτ.2
      have hle : MeasureTheory.volume.restrict (Set.uIoc 0 τ)
          ≤ MeasureTheory.volume.restrict (Set.uIoc 0 T) :=
        MeasureTheory.Measure.restrict_mono hsubu (le_refl _)
      -- interval integrability of the three curves
      have hφint : IntervalIntegrable (fun s : ℝ => Real.sqrt (EpsSq α (W s)))
          MeasureTheory.volume 0 τ := by
        have hφae : MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Real.sqrt (EpsSq α (W s)))
            (MeasureTheory.volume.restrict (Set.uIoc 0 τ)) :=
          Real.continuous_sqrt.comp_aestronglyMeasurable (hmeasW2.mono_measure hle)
        have hbd : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)),
            ‖Real.sqrt (EpsSq α (W s))‖ ≤ M :=
          Filter.Eventually.filter_mono (MeasureTheory.ae_mono hle) hbdaT
        exact IntervalIntegrable.mono_fun'
          (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => M) MeasureTheory.volume 0 τ)
          hφae hbd
      have hLint : IntervalIntegrable (fun s : ℝ => Real.sqrt L * Real.sqrt (EpsSq α (W s)))
          MeasureTheory.volume 0 τ := hφint.const_mul (Real.sqrt L)
      have hGae : MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Real.sqrt (EpsSq α (Gc s)))
          (MeasureTheory.volume.restrict (Set.uIoc 0 τ)) :=
        Work.FTS.StrongEps.IsEpsSolPQ.aesm_sqrt_EpsSq (hmeasG τ hτ)
          (Filter.Eventually.filter_mono (MeasureTheory.ae_mono hle) hmemG)
      have hGbd : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.uIoc 0 τ)),
          ‖Real.sqrt (EpsSq α (Gc s))‖ ≤ 2 * Real.sqrt L := by
        filter_upwards [Filter.Eventually.filter_mono (MeasureTheory.ae_mono hle) hbndG]
          with s hs
        rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
        calc Real.sqrt (EpsSq α (Gc s)) ≤ Real.sqrt (4 * L) := Real.sqrt_le_sqrt hs
          _ = 2 * Real.sqrt L := by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
                Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 ^ 2),
                Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
      have hGint : IntervalIntegrable (fun s : ℝ => Real.sqrt (EpsSq α (Gc s)))
          MeasureTheory.volume 0 τ :=
        IntervalIntegrable.mono_fun'
          (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => 2 * Real.sqrt L)
            MeasureTheory.volume 0 τ) hGae hGbd
      calc Real.sqrt (EpsSq α (W τ))
          ≤ ∫ s in (0 : ℝ)..τ, Real.sqrt (EpsSq α (Gc s)) := by
            calc Real.sqrt (EpsSq α (W τ))
                ≤ Real.sqrt ((∫ s in (0 : ℝ)..τ, Real.sqrt (EpsSq α (Gc s))) ^ 2) :=
                  Real.sqrt_le_sqrt (hMink τ hτ)
              _ = |∫ s in (0 : ℝ)..τ, Real.sqrt (EpsSq α (Gc s))| := Real.sqrt_sq_eq_abs _
              _ = ∫ s in (0 : ℝ)..τ, Real.sqrt (EpsSq α (Gc s)) :=
                  abs_of_nonneg (intervalIntegral.integral_nonneg hτ.1
                    (fun u _ => Real.sqrt_nonneg _))
        _ ≤ ∫ s in (0 : ℝ)..τ, Real.sqrt L * Real.sqrt (EpsSq α (W s)) :=
            intervalIntegral.integral_mono_on hτ.1 hGint hLint (fun s hs => by
              have hsI : s ∈ Set.Icc 0 T := ⟨hs.1, le_trans hs.2 hτ.2⟩
              calc Real.sqrt (EpsSq α (Gc s)) ≤ Real.sqrt (L * EpsSq α (W s)) :=
                    Real.sqrt_le_sqrt (hlipW s hsI)
                _ = Real.sqrt L * Real.sqrt (EpsSq α (W s)) := Real.sqrt_mul hL0 _)
        _ = Real.sqrt L * ∫ s in (0 : ℝ)..τ, Real.sqrt (EpsSq α (W s)) :=
            intervalIntegral.integral_const_mul _ _
  -- ## the endgame: the weighted energy vanishes, hence the profile does
  intro τ hτ z θ hz hθ
  have hWsq : EpsSq α (W τ) = 0 :=
    le_antisymm (Real.sqrt_eq_zero'.mp (hgron τ hτ)) (EpsSq_nonneg α (W τ))
  have hmemw := hmemW τ hτ
  have hint : Integrable (fun p : ℝ × ℝ => (W τ p.1 p.2 * epsW α p.1 p.2) ^ 2)
      Work.FTS.StrongEps.EpsLocalPStar.DomM :=
    (Work.FTS.StrongEps.EpsLocalPStar.EpsMem_iff_integrable2).mp hmemw
  have hz0 : (∫ p : ℝ × ℝ, (W τ p.1 p.2 * epsW α p.1 p.2) ^ 2
      ∂Work.FTS.StrongEps.EpsLocalPStar.DomM) = 0 := by
    rw [Work.FTS.StrongEps.IsEpsSolPQ.EpsSq_eq_integral_DomM hmemw]
    exact hWsq
  have hae : ∀ᵐ p ∂Work.FTS.StrongEps.EpsLocalPStar.DomM, W τ p.1 p.2 * epsW α p.1 p.2 = 0 := by
    have h := (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun p => sq_nonneg _) hint).mp hz0
    filter_upwards [h] with p hp
    exact sq_eq_zero_iff.mp hp
  have haeQ : ∀ᵐ p ∂(MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)),
      W τ p.1 p.2 = 0 := by
    rw [← Work.FTS.StrongEps.EpsLocalPStar.DomM_eq]
    filter_upwards [hae, Work.FTS.StrongEps.EpsLocalPStar.ae_open_DomM] with p hp hpq
    exact (mul_eq_zero.mp hp).resolve_right
      (Work.FTS.StrongEps.EpsSqTools.epsW_ne_zero hpq.1 ⟨hpq.2.1, hpq.2.2⟩)
  have haeQ0 : (fun p : ℝ × ℝ => W τ p.1 p.2)
      =ᵐ[MeasureTheory.volume.restrict Work.FTS.EllipticEst.Q0] 0 := by
    refine MeasureTheory.ae_restrict_of_ae_restrict_of_subset ?_ haeQ
    intro p hp
    exact ⟨(Set.mem_Ioi.mp hp.1).le, hp.2.1.le, hp.2.2.le⟩
  have hcont : ContinuousOn (fun p : ℝ × ℝ => W τ p.1 p.2) Work.FTS.EllipticEst.Q0 := by
    have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.Galerkin.slice g τ p.1 p.2)
        Work.FTS.EllipticEst.Q0 := ((hcl τ hτ).smoothOpen.forall 0).continuousOn
    have h2 : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.Galerkin.slice g' τ p.1 p.2)
        Work.FTS.EllipticEst.Q0 := ((hcl' τ hτ).smoothOpen.forall 0).continuousOn
    exact (h1.sub h2).congr (fun p _ => by simp only [hWdef, Pi.sub_apply])
  have heq := MeasureTheory.Measure.eqOn_open_of_ae_eq haeQ0 Work.FTS.EllipticEst.isOpen_Q0 hcont
    continuousOn_const
  have hzθ := heq (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)
  simp only [hWdef, Work.FTS.Galerkin.slice] at hzθ
  exact sub_eq_zero.mp hzθ

end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR5.r5Parts_hVP =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR5

open scoped Real Topology
open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Regularity (pExp Jet gSlice)

set_option linter.unusedVariables false

/-! ## The two remaining inputs of the assembly

The `C1Jet`-data of the class slots (`SG_C1Jet`, `DzDthSG_C1Jet_of_inputs`, `Ftau_C1Jet`,
`DthFtau_C1Jet`, `DzFtau_C1Jet`), the elliptic product slots (`EllProd_C1JetFull`), the `FK`-slot
(`FK_C1Jet`), the `N_*`-slot (`NsData_C1Jet`), the `mubar`-data (`mubarData`), the static-profile
slots (`Fstar_C1Jet`) and the three boundary values (`R0vals`) are all proved.  The two inputs
that are *derived* here are

* `profFull_SG_support`: the compact `z`-support of the sanitised full profile
  `profFull α (gS α (tauExt g))` (the `hsupp` of `L12f_C1Jet_profFull`), from `r7Block_proved`
  (= `suppExport`) — note that the profile's own exponent is `α` here (the satisfiable form);
* `muDyn_data_SG`: the bound and the `τ`-modulus of the clock functions `μ, λ` at the sanitised
  family (the `hMuB`/`hMuH` of `NsData_C1Jet`), from `mubarData`, the `Jet` of the transport
  zero-mode (`L12f_C1Jet_profFull`'s second slot) and the clock bound `ClockBd` (which controls
  `λ = -2μ/(1+μ)`), using the congruence `muDyn_congr_of_agreeOnQ` + `muDyn_tauExt`.
-/

/-- **The compact `z`-support of the sanitised full profile.**  For every horizon `S > 0` the
profile `z ↦ profFull α (gS α (tauExt g)) z θ τ` vanishes for `z` beyond a per-horizon threshold,
uniformly in `θ` and in `τ ∈ [0,S]`.

Inside `Iθ` this is finite speed of propagation (`RegPkgGal.R7e.support_strip_zL`) applied to the
`R7Block` produced by `r7Block_proved`; the two angular endpoints use `RegPkgMin.vanish`, and off
`Iθ` the sanitiser is *by definition* `-Fstar`, so the profile is `Fstar - Fstar = 0`. -/
private theorem profFull_SG_support {α C₀ : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hSol : Work.FTS.FinalV2.Sol (pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ, g z θ 0 =
      Work.FTS.LocData6.locG6 (pExp α) L β z θ)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g)
    (hVP : ∀ S > 0, Work.FTS.RegExportIface.VelPkg (pExp α)
      (Work.FTS.Final.maxMu (pExp α) (Work.FTS.Nonlin.PsiCan Φs E g) g)
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
      (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) S)
    {S : ℝ} (hS : 0 < S) :
    ∃ Lf : ℝ, 0 < Lf ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, Lf ≤ z →
      Work.FTS.Regularity.profFull α (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
        z θ τ = 0 := by
  obtain ⟨a, b, c, Lz7, hRB⟩ :=
    Work.FTS_RegExport.RXR7.r7Block_proved (Φs := Φs) (E := E) (g := g)
      hα hα13 hSol hOK hdat hμ hVP
  have hB := hRB S hS
  -- the two angular boundary values of the sanitised family
  have hSGθ0 : ∀ (τ : ℝ), 0 ≤ τ → ∀ z : ℝ, SG α g z 0 τ = 0 := by
    intro τ hτ z
    by_cases hz : z ≤ 0
    · exact SG_apply_of_nonpos hz
    · have hz' : 0 < z := lt_of_not_ge hz
      rw [SG_apply_of_pos hz' le_rfl (by linarith [Real.pi_pos]),
        Work.FTS.FinalV2.tauExt_of_nonneg g hτ]
      exact (hOK.1.1.vanish τ hτ z hz'.le).1
  have hSGθπ : ∀ (τ : ℝ), 0 ≤ τ → ∀ z : ℝ, SG α g z (Real.pi / 2) τ = 0 := by
    intro τ hτ z
    by_cases hz : z ≤ 0
    · exact SG_apply_of_nonpos hz
    · have hz' : 0 < z := lt_of_not_ge hz
      rw [SG_apply_of_pos hz' (by linarith [Real.pi_pos]) le_rfl,
        Work.FTS.FinalV2.tauExt_of_nonneg g hτ]
      exact (hOK.1.1.vanish τ hτ z hz'.le).2
  -- finite speed of propagation for the extended profile
  have hsupp7 : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, Lz7 * Real.exp (a * S) < z → 0 < θ →
      θ < Real.pi / 2 → Work.FTS.Regularity.profFull α
        (Work.FTS.RegPkgGal.extG (SG α g)) z θ τ = 0 :=
    Work.FTS.RegPkgGal.R7e.support_strip_zL (S := S) (a := a) (b := b) (c := c) (L := Lz7)
      hS hB.ha hB.hb hB.hc hB.hLz7
      (F := fun z θ τ => Work.FTS.Regularity.profFull α
        (Work.FTS.RegPkgGal.extG (SG α g)) z θ τ)
      hB.hFjoint hB.hVjoint hB.hVlipU hB.hcscont hB.hEq hB.hVz0 hB.hVza hB.hVθb hB.hVθ0 hB.hVθπ
      hB.hcsc hB.hInit
  refine ⟨max 1 (Lz7 * Real.exp (a * S) + 1), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro τ hτ z θ hz
  have hz1 : (1 : ℝ) ≤ z := le_trans (le_max_left _ _) hz
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz1
  have hzbig : Lz7 * Real.exp (a * S) < z :=
    lt_of_lt_of_le (lt_add_one _) (le_trans (le_max_right _ _) hz)
  by_cases hθ : θ ∈ Work.Spaces.Iθ
  · rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · subst h0
      rw [Work.FTS.Regularity.profFull_apply,
        Work.FTS_RegExport.Fstar_zero_left (Work.FTS.Regularity.pExp_pos hα) z,
        show Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z 0 τ = 0
          from hSGθ0 τ hτ.1 z]
      ring
    · rcases eq_or_lt_of_le hθ.2 with hπ | hπ
      · subst hπ
        rw [Work.FTS.Regularity.profFull_apply,
          Work.FTS_RegExport.Fstar_zero_pi (Work.FTS.Regularity.pExp_pos hα) z,
          show Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z (Real.pi / 2) τ = 0
            from hSGθπ τ hτ.1 z]
        ring
      · have hprof : Work.FTS.Regularity.profFull α (SG α g) z θ τ
            = Work.FTS.Regularity.profFull α (Work.FTS.RegPkgGal.extG (SG α g)) z θ τ := by
          rw [Work.FTS.Regularity.profFull_apply, Work.FTS.Regularity.profFull_apply,
            Work.FTS.RegPkgGal.extG_of_pos hz0 hτ.1]
        rw [hprof]
        exact hsupp7 τ hτ z θ hzbig h0 hπ
  · have hnot : ¬ (0 ≤ θ ∧ θ ≤ Real.pi / 2) := fun hh => hθ hh
    have hg : Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ τ
        = - Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ := by
      simp only [Work.FTS.FinalV2.gS, hz0, ↓reduceIte]
      rw [if_neg hnot]
    rw [Work.FTS.Regularity.profFull_apply, hg]
    ring

/-- **The clock data of `N_*` at the sanitised family.**  The bound and the `τ`-modulus of
`μ = muDyn (pExp α) (SΨ α Φs E g) (SG α g)` and `λ = lamDyn (pExp α) (SΨ α Φs E g) (SG α g)`.

`mufunS` makes `μ = (1/(2α))·(μ̄ + T)` with `μ̄` the `mubar` of `mubarData` and `T` the transport
zero-mode of the second slot of `L12f_C1Jet_profFull`; `ClockBd` bounds `|μ| ≤ 1/2`, so
`λ = -2μ/(1+μ)` is bounded by `2` and is `8`-Lipschitz in `μ`. -/
private theorem muDyn_data_SG {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC (pExp α) u →
      Work.FTS.Final.EllPkgGo (pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (pExp α) Cs Φs)
    (hSol : Work.FTS.FinalV2.Sol (pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S)
    (hSt1 : Work.FTS.RegPkgGal.St1Class α S (SG α g))
    (hsupp : ∃ Lf : ℝ, 0 < Lf ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, Lf ≤ z →
      Work.FTS.Regularity.profFull α (SG α g) z θ τ = 0)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g) :
    (∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc 0 S,
      |Work.FTS.Galerkin.muDyn (pExp α) (SΨ α Φs E g) (SG α g) τ| ≤ M ∧
      |Work.FTS.Galerkin.lamDyn (pExp α) (SΨ α Φs E g) (SG α g) τ| ≤ M) ∧
    (∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
      |Work.FTS.Galerkin.muDyn (pExp α) (SΨ α Φs E g) (SG α g) τ
        - Work.FTS.Galerkin.muDyn (pExp α) (SΨ α Φs E g) (SG α g) τ'| ≤ L * |τ - τ'| ^ α ∧
      |Work.FTS.Galerkin.lamDyn (pExp α) (SΨ α Φs E g) (SG α g) τ
        - Work.FTS.Galerkin.lamDyn (pExp α) (SΨ α Φs E g) (SG α g) τ'| ≤ L * |τ - τ'| ^ α) := by
  -- the `μ̄`-data
  obtain ⟨⟨Mub, hMub0, hMubB⟩, ⟨MubH, hMubH0, hMubH⟩⟩ :=
    Work.FTS_RegExport.RXR5L.mubarData (Φs := Φs) (E := E) hα hα13 hEll hEL3 hStar hSol hOK hS
  -- the transport zero-mode
  obtain ⟨N₇, N₈, hN₇, hN₈, hL12g, hL12T⟩ :=
    Work.FTS_RegExport.RXR5L.L12fAux.L12f_C1Jet_profFull (Φs := Φs) (E := E) (g := g)
      hα hα13 hOK hS hSt1 hsupp
  have hpi : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  -- the bound of the transport slot
  have hTb : ∀ τ ∈ Set.Icc 0 S, |Work.Coercivity.L12f (fun z θ' => 3 * Work.Spaces.Dth
      (Work.FTS.Regularity.gSlice (SG α g) τ) z θ' / (1 + z)) 0| ≤ N₈ := by
    intro τ hτ
    have h := hL12T.1.2.1 0 0 τ le_rfl hpi hτ
    simpa using h
  -- the `τ`-modulus of the transport slot
  have hTm : ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
      |Work.Coercivity.L12f (fun z θ' => 3 * Work.Spaces.Dth
          (Work.FTS.Regularity.gSlice (SG α g) τ) z θ' / (1 + z)) 0
        - Work.Coercivity.L12f (fun z θ' => 3 * Work.Spaces.Dth
          (Work.FTS.Regularity.gSlice (SG α g) τ') z θ' / (1 + z)) 0|
        ≤ N₈ * |τ - τ'| ^ α := by
    intro τ hτ τ' hτ'
    have h := hL12T.1.2.2 0 0 0 0 τ τ' le_rfl le_rfl hpi hpi hτ hτ'
    simpa using h
  -- the definitional expansion of `muDyn`
  have hexp : ∀ τ : ℝ,
      Work.FTS.Galerkin.muDyn (pExp α) (SΨ α Φs E g) (SG α g) τ
        = (1 / (2 * pExp α)) *
            (Work.Construction.mubar
                (Work.Construction.N0 (pExp α) (Work.Construction.Ftau (pExp α) (SG α g) τ)
                  (gSlice (SG α g) τ))
                (Work.Construction.N (pExp α) (Work.Construction.Ftau (pExp α) (SG α g) τ)
                  (gSlice (SΨ α Φs E g) τ))
              + Work.Coercivity.L12f (fun z θ' => 3 * Work.Spaces.Dth
                  (gSlice (SG α g) τ) z θ' / (1 + z)) 0) := by
    intro τ
    have hslice : Work.FTS.Galerkin.slice (SG α g) τ = gSlice (SG α g) τ := rfl
    have hslice' : Work.FTS.Galerkin.slice (SΨ α Φs E g) τ = gSlice (SΨ α Φs E g) τ := rfl
    simp only [Work.FTS.Galerkin.muDyn, Work.Construction.mufunS, Work.Construction.mubar,
      Work.Construction.L12, Work.Coercivity.L12f]
    rw [hslice, hslice']
    ring
  have hgc : (0 : ℝ) < 1 / (2 * pExp α) :=
    div_pos one_pos (by linarith [Work.FTS.Regularity.pExp_pos hα])
  -- the clock bound `|μ| ≤ 1/2`
  have hμhalf : ∀ τ : ℝ, 0 ≤ τ →
      |Work.FTS.Galerkin.muDyn (pExp α) (SΨ α Φs E g) (SG α g) τ| ≤ 1 / 2 := by
    intro τ hτ
    rw [muDyn_congr_of_agreeOnQ (α := pExp α) (g := SG α g)
        (g' := Work.FTS.FinalV2.tauExt g) (Φ := SΨ α Φs E g)
        (Φ' := Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.FinalV2.tauExt g))
        (SG_slice_agreeOnQ α g τ) (SΨ_slice_agreeOnQ α Φs E g τ),
      Work.FTS.FinalV2.muDyn_tauExt (Φs := Φs) (E := E) (g := g) hτ]
    exact hμ.1 τ hτ
  -- `lamfun` is bounded and `8`-Lipschitz on `|μ| ≤ 1/2`
  have hlam_abs : ∀ μ : ℝ, |μ| ≤ 1 / 2 → |Work.Construction.lamfun μ| ≤ 2 := by
    intro μ hμ
    have hge : -(1 / 2 : ℝ) ≤ μ := le_trans (neg_le_neg hμ) (neg_abs_le μ)
    have hpos : 0 < 1 + μ := by linarith
    rw [Work.Construction.lamfun, abs_div, abs_of_pos hpos]
    rw [show |(-2 : ℝ) * μ| = 2 * |μ| by
      rw [abs_mul, abs_of_neg (by norm_num : (-2 : ℝ) < 0), neg_neg]]
    rw [div_le_iff₀ hpos]
    nlinarith [hμ, hge]
  have hlam_lip : ∀ μ μ' : ℝ, |μ| ≤ 1 / 2 → |μ'| ≤ 1 / 2 →
      |Work.Construction.lamfun μ - Work.Construction.lamfun μ'| ≤ 8 * |μ - μ'| := by
    intro μ μ' hμ hμ'
    have hge : -(1 / 2 : ℝ) ≤ μ := le_trans (neg_le_neg hμ) (neg_abs_le μ)
    have hge' : -(1 / 2 : ℝ) ≤ μ' := le_trans (neg_le_neg hμ') (neg_abs_le μ')
    have hd1 : 1 + μ ≠ 0 := by linarith
    have hd2 : 1 + μ' ≠ 0 := by linarith
    have hp1 : (0 : ℝ) < 1 + μ := by linarith
    have hp2 : (0 : ℝ) < 1 + μ' := by linarith
    have hq : (1 / 4 : ℝ) ≤ (1 + μ) * (1 + μ') := by nlinarith
    have hkey : -2 * μ / (1 + μ) - -2 * μ' / (1 + μ')
        = 2 * (μ' - μ) / ((1 + μ) * (1 + μ')) := by
      field_simp
      ring
    simp only [Work.Construction.lamfun]
    rw [hkey, abs_div, abs_mul,
      abs_of_pos (mul_pos hp1 hp2)]
    have hnum : |(2 : ℝ)| * |μ' - μ| = 2 * |μ - μ'| := by
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_sub_comm]
    rw [hnum]
    rw [div_le_iff₀ (mul_pos hp1 hp2)]
    have h1 : 2 * |μ - μ'| ≤ 8 * |μ - μ'| * (1 / 4) := by
      nlinarith [abs_nonneg (μ - μ')]
    have h2 : 8 * |μ - μ'| * (1 / 4) ≤ 8 * |μ - μ'| * ((1 + μ) * (1 + μ')) :=
      mul_le_mul_of_nonneg_left hq (mul_nonneg (by norm_num) (abs_nonneg _))
    linarith
  -- the two analytic estimates for `muDyn`
  have hμbnd : ∀ τ ∈ Set.Icc 0 S,
      |Work.FTS.Galerkin.muDyn (pExp α) (SΨ α Φs E g) (SG α g) τ|
        ≤ (1 / (2 * pExp α)) * (max Mub MubH + N₈) := by
    intro τ hτ
    rw [hexp τ, abs_mul, abs_of_pos hgc]
    have h1 : |Work.Construction.mubar
        (Work.Construction.N0 (pExp α) (Work.Construction.Ftau (pExp α) (SG α g) τ)
          (gSlice (SG α g) τ))
        (Work.Construction.N (pExp α) (Work.Construction.Ftau (pExp α) (SG α g) τ)
          (gSlice (SΨ α Φs E g) τ))| ≤ max Mub MubH :=
      le_trans (hMubB τ hτ) (le_max_left _ _)
    have h2 := hTb τ hτ
    refine mul_le_mul_of_nonneg_left ?_ hgc.le
    exact le_trans (abs_add_le _ _) (by linarith)
  have hμmod : ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
      |Work.FTS.Galerkin.muDyn (pExp α) (SΨ α Φs E g) (SG α g) τ
        - Work.FTS.Galerkin.muDyn (pExp α) (SΨ α Φs E g) (SG α g) τ'|
        ≤ (1 / (2 * pExp α)) * (max Mub MubH + N₈) * |τ - τ'| ^ α := by
    intro τ hτ τ' hτ'
    rw [hexp τ, hexp τ']
    have h1 : |Work.Construction.mubar
        (Work.Construction.N0 (pExp α) (Work.Construction.Ftau (pExp α) (SG α g) τ)
          (gSlice (SG α g) τ))
        (Work.Construction.N (pExp α) (Work.Construction.Ftau (pExp α) (SG α g) τ)
          (gSlice (SΨ α Φs E g) τ))
        - Work.Construction.mubar
          (Work.Construction.N0 (pExp α) (Work.Construction.Ftau (pExp α) (SG α g) τ')
            (gSlice (SG α g) τ'))
          (Work.Construction.N (pExp α) (Work.Construction.Ftau (pExp α) (SG α g) τ')
            (gSlice (SΨ α Φs E g) τ'))| ≤ max Mub MubH * |τ - τ'| ^ α :=
      le_trans (hMubH τ hτ τ' hτ')
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (abs_nonneg _) α))
    have h2 := hTm τ hτ τ' hτ'
    have hstep : (1 / (2 * pExp α)) *
            (Work.Construction.mubar
                (Work.Construction.N0 (pExp α) (Work.Construction.Ftau (pExp α) (SG α g) τ)
                  (gSlice (SG α g) τ))
                (Work.Construction.N (pExp α) (Work.Construction.Ftau (pExp α) (SG α g) τ)
                  (gSlice (SΨ α Φs E g) τ))
              + Work.Coercivity.L12f (fun z θ' => 3 * Work.Spaces.Dth
                  (gSlice (SG α g) τ) z θ' / (1 + z)) 0)
          - (1 / (2 * pExp α)) *
              (Work.Construction.mubar
                  (Work.Construction.N0 (pExp α) (Work.Construction.Ftau (pExp α) (SG α g) τ')
                    (gSlice (SG α g) τ'))
                  (Work.Construction.N (pExp α) (Work.Construction.Ftau (pExp α) (SG α g) τ')
                    (gSlice (SΨ α Φs E g) τ'))
                + Work.Coercivity.L12f (fun z θ' => 3 * Work.Spaces.Dth
                    (gSlice (SG α g) τ') z θ' / (1 + z)) 0)
          = (1 / (2 * pExp α)) *
              ((Work.Construction.mubar
                  (Work.Construction.N0 (pExp α) (Work.Construction.Ftau (pExp α) (SG α g) τ)
                    (gSlice (SG α g) τ))
                  (Work.Construction.N (pExp α) (Work.Construction.Ftau (pExp α) (SG α g) τ)
                    (gSlice (SΨ α Φs E g) τ))
                - Work.Construction.mubar
                  (Work.Construction.N0 (pExp α) (Work.Construction.Ftau (pExp α) (SG α g) τ')
                    (gSlice (SG α g) τ'))
                  (Work.Construction.N (pExp α) (Work.Construction.Ftau (pExp α) (SG α g) τ')
                    (gSlice (SΨ α Φs E g) τ')))
              + (Work.Coercivity.L12f (fun z θ' => 3 * Work.Spaces.Dth
                    (gSlice (SG α g) τ) z θ' / (1 + z)) 0
                - Work.Coercivity.L12f (fun z θ' => 3 * Work.Spaces.Dth
                    (gSlice (SG α g) τ') z θ' / (1 + z)) 0)) := by
      ring
    rw [hstep, abs_mul, abs_of_pos hgc, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hgc.le
    refine le_trans (abs_add_le _ _) ?_
    have hsum : max Mub MubH * |τ - τ'| ^ α + N₈ * |τ - τ'| ^ α
        = (max Mub MubH + N₈) * |τ - τ'| ^ α := by ring
    linarith [h1, h2, hsum]
  have hc0 : 0 ≤ (1 / (2 * pExp α)) * (max Mub MubH + N₈) :=
    mul_nonneg hgc.le (add_nonneg (le_trans hMub0 (le_max_left _ _)) hN₈)
  have hkey8 : ∀ r : ℝ, 8 * ((1 / (2 * pExp α)) * (max Mub MubH + N₈)) * r
      = 8 * (((1 / (2 * pExp α)) * (max Mub MubH + N₈)) * r) := by
    intro r; ring
  refine ⟨⟨max ((1 / (2 * pExp α)) * (max Mub MubH + N₈)) 2,
      le_trans hc0 (le_max_left _ _), ?_⟩,
    ⟨8 * ((1 / (2 * pExp α)) * (max Mub MubH + N₈)),
      mul_nonneg (by norm_num) hc0, ?_⟩⟩
  · intro τ hτ
    constructor
    · exact le_trans (hμbnd τ hτ) (le_max_left _ _)
    · exact le_trans (hlam_abs _ (hμhalf τ hτ.1)) (le_max_right _ _)
  · intro τ hτ τ' hτ'
    constructor
    · refine le_trans (hμmod τ hτ τ' hτ') ?_
      rw [hkey8]
      exact le_mul_of_one_le_left (mul_nonneg hc0 (Real.rpow_nonneg (abs_nonneg _) α))
        (by norm_num)
    · refine le_trans (hlam_lip _ _ (hμhalf τ hτ.1) (hμhalf τ' hτ'.1)) ?_
      rw [hkey8]
      exact mul_le_mul_of_nonneg_left (hμmod τ hτ τ' hτ') (by norm_num)

theorem r5Parts_hVP {α Ce C₀ Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hSt1 : ∀ S > 0, Work.FTS.RegPkgGal.St1Class α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)))
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ, g z θ 0 =
      Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β z θ)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g)
    (hVP : ∀ S > 0, Work.FTS.RegExportIface.VelPkg (Work.FTS.Regularity.pExp α)
      (Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α) (Work.FTS.Nonlin.PsiCan Φs E g) g)
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
      (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) S) :
    ∀ S > 0, Work.FTS.RegPkgGal.R5Parts α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))
      (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) := by
  intro S hS
  -- the compact support of the profile (the `hsupp` of `L12f_C1Jet_profFull`)
  obtain ⟨Lf, hLf, hsupp⟩ := profFull_SG_support (Φs := Φs) (E := E) (g := g)
    hα hα13 hSol hOK hdat hμ hVP hS
  have hsuppEx : ∃ Lf : ℝ, 0 < Lf ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, Lf ≤ z →
      Work.FTS.Regularity.profFull α (SG α g) z θ τ = 0 := ⟨Lf, hLf, hsupp⟩
  -- the `z`-uniform angular slots of the sanitised family (the O1 input)
  have hO1 : ∃ N₂ N₃ : ℝ, 0 ≤ N₂ ∧ 0 ≤ N₃ ∧
      Work.FTS.RegPkgGal.C1Jet α S N₂
        (fun z θ τ => Work.Spaces.Dz (fun z θ => SG α g z θ τ) z θ) ∧
      Work.FTS.RegPkgGal.C1Jet α S N₃
        (fun z θ τ => Work.Spaces.Dth (fun z θ => SG α g z θ τ) z θ) :=
    Work.FTS_RegExport.THL.L.DzDthSG_C1Jet_of_inputs (Φs := Φs) (E := E)
      hα hα13 hEll hEL3 hStar hSol hOK hdat hμ S hS
  have hO1c := hO1
  obtain ⟨N₂, N₃, hN₂, hN₃, hDzg, hDthg⟩ := hO1c
  -- the class data of the sanitised family
  obtain ⟨N₁, hN₁, hg⟩ := Work.FTS_RegExport.RXR5L.SG_C1Jet (Φs := Φs) (E := E)
    hα hα13 hOK hS (hSt1 S hS)
  obtain ⟨N₄, hN₄, hF⟩ := Work.FTS_RegExport.RXR5L.Ftau_C1Jet (Φs := Φs) (E := E)
    hα hα13 hOK hS (hSt1 S hS) hO1
  obtain ⟨N₅, hN₅, hDthF⟩ := Work.FTS_RegExport.RXR5L.DthFtau_C1Jet (Φs := Φs) (E := E)
    hα hα13 hOK hS (hSt1 S hS) hO1
  obtain ⟨N₆, hN₆, hDzF⟩ := Work.FTS_RegExport.RXR5L.DzFtau_C1Jet (Φs := Φs) (E := E)
    hα hα13 hOK hS (hSt1 S hS) hO1
  -- the two `L₁₂`-slots of the class data
  obtain ⟨N₇, N₈, hN₇, hN₈, hL12g, hL12T⟩ :=
    Work.FTS_RegExport.RXR5L.L12fAux.L12f_C1Jet_profFull (Φs := Φs) (E := E) (g := g)
      hα hα13 hOK hS (hSt1 S hS) hsuppEx
  -- the `FK`-slot
  obtain ⟨Nf, hNf, hFK⟩ := Work.FTS_RegExport.RXR5L.FK_C1Jet (Φs := Φs) (E := E)
    hα hα13 hOK hS (hSt1 S hS)
  -- the three elliptic product slots
  obtain ⟨N₁₂, N₁₃, Ne, hN₁₂, hN₁₃, hNe, hRopF, hUopF, hVopDzF⟩ :=
    Work.FTS_RegExport.RXR5L.EllProd_C1JetFull (Φs := Φs) (E := E) (g := g)
      hα hα13 hEll hEL3 hStar hSol hOK hdat hμ hVP hSt1 hS
  -- the `N_*`-slot
  have hmudata := muDyn_data_SG (Φs := Φs) (E := E) (g := g) hα hα13 hEll hEL3 hStar hSol hOK
    hS (hSt1 S hS) hsuppEx hμ
  obtain ⟨Nn, hNn, hNsJet, hNsZ⟩ :=
    Work.FTS_RegExport.RXR5L.NsData_C1Jet (Φs := Φs) (E := E) hα hα13 hOK hS (hSt1 S hS) hO1
      hmudata.1 hmudata.2
  -- the `mubar`-data and the boundary values
  obtain ⟨hmb, hmbh⟩ := Work.FTS_RegExport.RXR5L.mubarData (Φs := Φs) (E := E)
    hα hα13 hEll hEL3 hStar hSol hOK hS
  obtain ⟨hRz0, hRθ0, hRθπ⟩ := Work.FTS_RegExport.RXR5L.R0vals (Φs := Φs) (E := E)
    hα hα13 hSol hOK hS
  -- the three static-profile slots
  obtain ⟨N₉, N₁₀, N₁₁, hN₉, hN₁₀, hN₁₁, hL12Fstar, hDthFstar, hDzFstar⟩ :=
    Work.FTS_RegExport.RXR5.Fstar_C1Jet (α := α) hα hα13 hS
  -- ## the two shared constants
  have hg' : Work.FTS.RegPkgGal.C1Jet α S (max N₁ Nn) (SG α g) := by
    refine ⟨Work.FTS_RegExport.RXR5.jet_mono (le_max_left _ _) hg.1, ?_⟩
    intro τ hτ θ hθ z hz
    obtain ⟨d, hd, hb⟩ := hg.2 τ hτ θ hθ z hz
    exact ⟨d, hd, le_trans hb (le_max_left _ _)⟩
  have hNsJet' : Work.FTS.Regularity.Jet α S (max N₁ Nn) (fun z θ τ => Work.Construction.Nstar
      (Work.FTS.Galerkin.muDyn (pExp α) (SΨ α Φs E g) (SG α g) τ)
      (Work.FTS.Galerkin.lamDyn (pExp α) (SΨ α Φs E g) (SG α g) τ)
      (gSlice (SG α g) τ) z θ) :=
    Work.FTS_RegExport.RXR5.jet_mono (le_max_right _ _) hNsJet
  have hNsZ' : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z ∈ Set.Ioi (0 : ℝ),
      ∃ d : ℝ, HasDerivAt (fun z' => Work.Construction.Nstar
        (Work.FTS.Galerkin.muDyn (pExp α) (SΨ α Φs E g) (SG α g) τ)
        (Work.FTS.Galerkin.lamDyn (pExp α) (SΨ α Φs E g) (SG α g) τ)
        (gSlice (SG α g) τ) z' θ) d z ∧ |d| ≤ max N₁ Nn := by
    intro τ hτ θ hθ z hz
    obtain ⟨d, hd, hb⟩ := hNsZ τ hτ θ hθ z hz
    exact ⟨d, hd, le_trans hb (le_max_right _ _)⟩
  have hFK' : Work.FTS.RegPkgGal.C1Jet α S (max Ne Nf) (fun z θ τ =>
      Work.Construction.FK (Work.Construction.Ftau (pExp α) (SG α g) τ) z) := by
    refine ⟨Work.FTS_RegExport.RXR5.jet_mono (le_max_right _ _) hFK.1, ?_⟩
    intro τ hτ θ hθ z hz
    obtain ⟨d, hd, hb⟩ := hFK.2 τ hτ θ hθ z hz
    exact ⟨d, hd, le_trans hb (le_max_right _ _)⟩
  have hVopDzF' : Work.FTS.RegPkgGal.C1Jet α S (max Ne Nf) (fun z θ τ =>
      Work.Construction.Vop (Work.Construction.PhiTil (pExp α)
            (Work.Construction.Ftau (pExp α) (SG α g) τ) (gSlice (SΨ α Φs E g) τ)) z θ
          * Work.Spaces.Dz (fun z θ => Work.Construction.Ftau (pExp α) (SG α g) τ z θ) z θ) := by
    refine ⟨Work.FTS_RegExport.RXR5.jet_mono (le_max_left _ _) hVopDzF.1, ?_⟩
    intro τ hτ θ hθ z hz
    obtain ⟨d, hd, hb⟩ := hVopDzF.2 τ hτ θ hθ z hz
    exact ⟨d, hd, le_trans hb (le_max_left _ _)⟩
  -- ## the assembly
  exact Work.FTS.RegPkgGal.Der.R5Parts_of_pieces_F (α := α) (S := S)
    (g := SG α g) (Φ := SΨ α Φs E g)
    hα hα13 hS (sol_SG (Φs := Φs) (E := E) hSol) (h0_SG (Φs := Φs) (E := E) hSol)
    hg' hDzg hDthg hF hDthF hDzF hL12g hL12T hL12Fstar hDthFstar hDzFstar
    hRopF hUopF hVopDzF' hFK' hNsJet' hNsZ' hmb hmbh hRz0 hRθ0 hRθπ

end Work.FTS_RegExport.RXR5
end
-- ===== merged: Submission.Work.FTS_RegExport.RXVP.NoHdat.velPkgEasy_noHdat =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXVP.NoHdat.velPkgEasy` — the three *provable* clauses of `VelPkg`

The frozen `VelPkg` (RX-VP) is documented to be unprovable: its `cont` clause is equivalent to the
axis-slope condition (★), see `NOTES_area_state.md` §2(a).  The present lemma isolates the three
clauses of `VelPkg`/`VelPkgSup`/`VelPkgEnd` that are *not* tied to (★):

* `VelPkgEnd.vanishK` — the `O(z)` vanishing of `FK(g)` and `L₁₂(g)` at `z = 0`;
* `VelPkgEnd.c2` — the stream-function slice is `C²` on the open quadrant;
* `VelPkgSup.vth_ends` — `Vθ7 = 2·Uop(Φ)` vanishes at `θ = 0` and `θ = π/2`.

The ingredients are all already in the tree (and axiom-clean):

* `RXT/SysAux/FK_jet_pkg_uniform`, `RXT/SysAux/L12_jet_pkg_uniform` — the weighted jet packages of
  `𝔽K u` and `L₁₂ u` for a *generic* slice, with constants depending only on the weighted bound
  `B` of the slice (this is what makes them uniform in `τ`: `B = Cw·C₀α²` is `τ`-independent);
* `RXA2w/lim_mixed_weighted_proved` — that weighted bound for the strong solution (RX-A2w);
* `RXB/l12_zero_lim_proved` — `L₁₂(slice g τ)(0) = 0` (RX-B);
* `RXT/C2Psi/contDiffOn_slice_PhiR_Q0` — `C³` of the `psiR`-slice on the open quadrant;
* `RXR5/Basic` — the quadrant-congruence plumbing (`AgreeOnQ`, `L12_congr_of_agreeOnQ`, …).

The only genuinely new analytic step is the *large*-`z` bound on `L₁₂`: the weighted bound
`|𝔽K u| ≲ z^{3/2}/(1+z)²` decays, so `L₁₂(z) = L₁₂(1) - ∫₁^z 𝔽K(s)/s ds` (the `L₁₂'`-identity of
the package) is uniformly bounded by `|L₁₂(1)| + ∫₁^∞ C₁ s^{-3/2} ds ≤ C₂ + 2C₁`.
-/

namespace Work.FTS_RegExport.RXVP.NoHdat

open scoped Real Topology NNReal
open Set Filter MeasureTheory
open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Regularity (pExp Jet)
open Work.FTS.RegPkgGal (extG RegPkg' St1Class R5Parts Avort Bdyn)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)
open Work.FTS.RegExportIface

set_option autoImplicit false
set_option maxHeartbeats 800000

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn}

/-! ## §1 Elementary estimates for the weight `z^{3/2}/(1+z)²` -/

/-- For `0 < z ≤ 1` the weight `z^{3/2}` is dominated by `z`. -/
private theorem three_halves_le_self {z : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1) :
    z ^ ((3 : ℝ) / 2) ≤ z := by
  have h32 : z ^ ((3 : ℝ) / 2) = z * Real.sqrt z := by
    rw [show (3 : ℝ) / 2 = (1 : ℝ) + 1 / 2 from by norm_num, Real.rpow_add hz0,
      Real.rpow_one, Real.sqrt_eq_rpow, mul_comm]
  rw [h32]
  have h1 := Real.sqrt_le_one.mpr hz1
  have h2 := Real.sqrt_nonneg z
  nlinarith

/-- For `1 ≤ z` the weight `z^{3/2}` is dominated by `(1+z)^2`. -/
private theorem three_halves_le_sq {z : ℝ} (hz1 : 1 ≤ z) :
    z ^ ((3 : ℝ) / 2) ≤ (1 + z) ^ 2 := by
  have hz0 : (0 : ℝ) < z := lt_of_lt_of_le one_pos hz1
  have h1 : z ^ ((3 : ℝ) / 2) ≤ (1 + z) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow hz0.le (by linarith) (by norm_num)
  have h2 : (1 + z) ^ ((3 : ℝ) / 2) ≤ (1 + z) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have h3 : (1 + z) ^ (2 : ℝ) = (1 + z) ^ 2 := Real.rpow_two _
  exact h1.trans (h2.trans h3.le)

/-- `z^{3/2}/(1+z)² ≤ z` for `0 < z ≤ 1`. -/
private theorem rpow_div_le_self {z : ℝ} (hz0 : 0 < z) (hz1 : z ≤ 1) :
    z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2 ≤ z := by
  have h := three_halves_le_self hz0 hz1
  have hden : (1 : ℝ) ≤ (1 + z) ^ 2 := by nlinarith [sq_nonneg z, hz0]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
  nlinarith [Real.rpow_nonneg hz0.le ((3 : ℝ) / 2)]

/-- `z^{3/2}/(1+z)² ≤ 1` for `1 ≤ z`. -/
private theorem rpow_div_le_one {z : ℝ} (hz1 : 1 ≤ z) :
    z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2 ≤ 1 := by
  rw [div_le_one (by positivity : (0 : ℝ) < (1 + z) ^ 2)]
  exact three_halves_le_sq hz1

/-- For `1 ≤ s`, `s^{3/2}/((1+s)²·s) ≤ s^{-3/2}`: the integrand of the `L₁₂`-tail is dominated
by the integrable profile `s^{-3/2}`. -/
private theorem rpow_ratio_le {s : ℝ} (hs : 1 ≤ s) :
    s ^ ((3 : ℝ) / 2) / ((1 + s) ^ 2 * s) ≤ s ^ (-(3 / 2 : ℝ)) := by
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le one_pos hs
  have hsp : (0 : ℝ) < (1 + s) ^ 2 := by positivity
  have h32 : s ^ ((3 : ℝ) / 2) = s * Real.sqrt s := by
    rw [show (3 : ℝ) / 2 = (1 : ℝ) + 1 / 2 from by norm_num, Real.rpow_add hs0,
      Real.rpow_one, Real.sqrt_eq_rpow, mul_comm]
  have hsimp : s ^ ((3 : ℝ) / 2) / ((1 + s) ^ 2 * s) = Real.sqrt s / (1 + s) ^ 2 := by
    rw [h32]; field_simp
  have hneg : s ^ (-(3 / 2 : ℝ)) = 1 / s ^ ((3 : ℝ) / 2) := by
    rw [Real.rpow_neg hs0.le (3 / 2), inv_eq_one_div]
  rw [hsimp, hneg,
    div_le_div_iff₀ hsp (by positivity : (0 : ℝ) < s ^ ((3 : ℝ) / 2)), h32]
  have hsq : Real.sqrt s * Real.sqrt s = s := by rw [← sq]; exact Real.sq_sqrt hs0.le
  nlinarith [sq_nonneg s, hs]

/-- `∫₁^z s^{-3/2} ds ≤ 2` for `1 ≤ z`. -/
private theorem integral_rpow_neg_three_halves_le {z : ℝ} (hz : 1 ≤ z) :
    ∫ s in (1 : ℝ)..z, s ^ (-(3 / 2 : ℝ)) ≤ 2 := by
  have hz0 : (0 : ℝ) < z := lt_of_lt_of_le one_pos hz
  have hneq : (0 : ℝ) ∉ Set.uIcc 1 z := by
    rw [Set.uIcc_of_le hz]
    intro h
    linarith [h.1]
  have hval : ∫ s in (1 : ℝ)..z, s ^ (-(3 / 2 : ℝ)) = 2 - 2 * z ^ (-(1 / 2 : ℝ)) := by
    rw [integral_rpow (Or.inr ⟨by norm_num, hneq⟩)]
    rw [show (-(3 / 2 : ℝ)) + 1 = -(1 / 2 : ℝ) from by norm_num, Real.one_rpow]
    field_simp
    ring
  rw [hval]
  have := Real.rpow_nonneg hz0.le (-(1 / 2 : ℝ))
  linarith

/-! ## §2 The lemma -/


end Work.FTS_RegExport.RXVP.NoHdat
end
