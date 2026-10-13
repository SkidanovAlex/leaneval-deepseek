import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsLocalPStar.SqWeakAux

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
