import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EpsEngine.ClassCStepSlice
import Submission.Work.FTS.EpsEngine.LocalStepXBall
import Submission.Work.FTS.EpsEngine.ThetaFromEps
import Submission.Work.FTS.RegExportIface.Producers
import Submission.Work.FTS.StrongEps.E5G.ExistsLimG_assembly
import Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits.hkSqFepsSub_le
import Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.regFromVolterra
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsMemOfClassCJeps
import Submission.Work.FTS.StrongEps.EpsLocalPStar.profRHS_sub_sup_le
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartAux
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.bump_mixed_EpsSq_le
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6bWork.HkMem_mul_of_WlInf6_cd6
import Submission.Work.FTS.StrongPersist.StarPkg6Assembly
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.Trace
import Submission.Work.FTS_RegExport.RXVP.NoHdat.velPkgEasy_noHdat
import Submission.Work.FTS_RegExport.RXVP.velPkg_proved
import Submission.Work.FTS_RegExport.RXVP3.velPkgOpen_of_vopLower
import Submission.Work.R1G.DecayInZ_gA
import Submission.Work.Spaces.pz_DthIter_mul_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongEps (EpsMem EpsSq epsW)
open Work.FTS.EpsEngine (Feps XBall)
open Work.FTS.StrongEps.EpsLocalPStar (iter epsL2 DomM)

namespace Work.FTS.StrongEps.EpsE4Thr

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The `0`-th Picard slice is the datum. -/
theorem slice_iter_zero_eq (F : Fn → Fn) (h₀ : Fn) (τ : ℝ) : slice (iter F h₀ 0) τ = h₀ := rfl

/-- The `(n+1)`-st Picard slice, unfolded. -/
theorem slice_iter_succ_eq (F : Fn → Fn) (h₀ : Fn) (n : ℕ) (τ : ℝ) :
    slice (iter F h₀ (n + 1)) τ
      = fun z θ => h₀ z θ + ∫ s in (0 : ℝ)..τ, F (slice (iter F h₀ n) s) z θ := by
  funext z θ
  simp only [Work.FTS.Galerkin.slice_apply, Work.FTS.StrongEps.EpsLocalPStar.iter_succ]

/-- The `(n+1)`-st Picard increment, unfolded: `slice (iter … (n+1)) τ − h₀ = ∫₀^τ F(w_s) ds`. -/
theorem slice_iter_succ_sub_eq (F : Fn → Fn) (h₀ : Fn) (n : ℕ) (τ : ℝ) :
    (fun z θ => slice (iter F h₀ (n + 1)) τ z θ - h₀ z θ)
      = fun z θ => ∫ s in (0 : ℝ)..τ, F (slice (iter F h₀ n) s) z θ := by
  funext z θ
  rw [congrFun (congrFun (slice_iter_succ_eq F h₀ n τ) z) θ]
  ring


/-- `Elliptic.sinCos2` is continuous. -/
theorem continuous_sinCos2_fts : Continuous Work.Elliptic.sinCos2 := by
  change Continuous (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2)
  exact Real.continuous_sin.mul (Real.continuous_cos.pow 2)

/-- **`F_*(Pz (J_ε W))` is smooth to all orders on `(0,∞)`** — the `fsm` residual of the class-`C`
clause of the projected `ε`-scheme, from the `ℋ¹`-honesty of the raw profile `W`.

`Pz f = f − (L₁₂ f 0 / pzNorm) • bump` and `bump = zCut · thCut` is a product of a smooth
function of `z` and one of `θ`, so `F_* bump r = zCut r · ∫_θ thCut θ sinθcos²θ dθ` is smooth;
the splitting of `F_*` over the sum is legitimate because the angular moment of `J_ε W` is
integrable (`EpsE4Thr.JepsMulSinCos2Integrable`).  The smoothness of the mollified angular moment
`F_*(J_ε W)` is `XBallIterExistsAux.FstarJepsSmooth`. -/
theorem contDiffOn_fstar_PzJeps {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {ε : ℝ} (hε : 0 < ε) {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {W : Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen W) (hmem : Work.Spaces.HkMem α 1 W) :
    ∀ m : ℕ, ContDiffOn ℝ m
      (Work.Elliptic.Fstar (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε W)))
      (Set.Ioi 0) := by
  intro m
  have hA : ContDiffOn ℝ m (Work.Elliptic.Fstar (Work.FTS.StrongEps.Jeps ρ ε W))
      (Set.Ioi 0) :=
    fun r hr => Work.FTS.StrongEps.EpsE4Thr.XBallIterExistsAux.FstarJepsSmooth hρ hε hsm hmem m r hr
  have hconst : ContDiffOn ℝ m (fun _ : ℝ => ∫ θ in Work.Spaces.Iθ,
      Work.FTS.StrongEps.thCut θ * Work.Elliptic.sinCos2 θ) (Set.Ioi 0) :=
    contDiff_const.contDiffOn
  have hB : ContDiffOn ℝ m (fun r : ℝ => Work.FTS.StrongEps.zCut r *
      (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongEps.thCut θ * Work.Elliptic.sinCos2 θ))
      (Set.Ioi 0) :=
    (Work.FTS.StrongEps.contDiff_zCut m).contDiffOn.mul hconst
  set c : ℝ := Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε W) 0 / Work.FTS.StrongEps.pzNorm
    with hc
  have hBc : ContDiffOn ℝ m (fun r : ℝ => c * (Work.FTS.StrongEps.zCut r *
      (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongEps.thCut θ * Work.Elliptic.sinCos2 θ)))
      (Set.Ioi 0) := (contDiffOn_const (c := c)).mul hB
  refine (hA.sub hBc).congr ?_
  intro r hr
  have hf : IntegrableOn (fun θ : ℝ => Work.FTS.StrongEps.Jeps ρ ε W r θ *
      Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    Work.FTS.StrongEps.EpsE4Thr.JepsMulSinCos2Integrable hρ hε hα hsm hmem r hr
  have hcont : Continuous (fun θ : ℝ => Work.FTS.StrongEps.zCut r *
      (Work.FTS.StrongEps.thCut θ * Work.Elliptic.sinCos2 θ)) :=
    continuous_const.mul ((Work.FTS.StrongEps.contDiff_thCut 0).continuous.mul
      continuous_sinCos2_fts)
  have hb : IntegrableOn (fun θ : ℝ => c * (Work.FTS.StrongEps.zCut r *
      (Work.FTS.StrongEps.thCut θ * Work.Elliptic.sinCos2 θ))) Work.Spaces.Iθ :=
    (hcont.continuousOn.integrableOn_compact isCompact_Icc).const_mul c
  have hkey : ∀ θ : ℝ, Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε W) r θ *
        Work.Elliptic.sinCos2 θ
      = Work.FTS.StrongEps.Jeps ρ ε W r θ * Work.Elliptic.sinCos2 θ
        - c * (Work.FTS.StrongEps.zCut r *
            (Work.FTS.StrongEps.thCut θ * Work.Elliptic.sinCos2 θ)) := by
    intro θ
    rw [Work.FTS.StrongEps.Pz_apply]
    simp only [Work.FTS.StrongEps.bump, hc]
    ring
  have hii : (∫ θ in Work.Spaces.Iθ, Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε W) r θ
        * Work.Elliptic.sinCos2 θ)
      = ∫ θ in Work.Spaces.Iθ, (Work.FTS.StrongEps.Jeps ρ ε W r θ * Work.Elliptic.sinCos2 θ
          - c * (Work.FTS.StrongEps.zCut r *
              (Work.FTS.StrongEps.thCut θ * Work.Elliptic.sinCos2 θ))) :=
    integral_congr_ae (Filter.Eventually.of_forall hkey)
  rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar, hii, MeasureTheory.integral_sub hf hb,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

theorem XBallIterExists {α C₀ Ce Cs M' : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {ε : ℝ}
    (hC₀ : 0 < C₀) (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α (2 * C₀) Φs E)
    (hM : 0 ≤ M') :
    ∃ δ : ℝ, 0 < δ ∧ ∃ R : ℝ, 0 < R ∧
      ∀ h₀ : Work.FTS.Galerkin.Fn,
        Work.FTS.EllipticEst.SmoothOpen h₀ → Work.Spaces.HkMem α 6 h₀ →
        Work.Spaces.HkSq α 6 h₀ ≤ M' →
        Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε h₀)) →
        Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε h₀))
          ≤ C₀ * α ^ 2 →
        Work.FTS.StrongEps.EpsMem α h₀ ∧ Work.FTS.StrongEps.EpsSq α h₀ ≤ R ∧
        (∀ n : ℕ, ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
          Work.FTS.EpsEngine.XBall α ρ ε R (2 * C₀)
            (Work.FTS.Galerkin.slice
              (Work.FTS.StrongEps.EpsLocalPStar.iter
                (Work.FTS.EpsEngine.Feps α ρ ε Φs E) h₀ (n + 1)) τ)) := by
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  -- ## 0. the constants
  obtain ⟨Ceps, hCeps_pos, hCepsD⟩ := Work.FTS.StrongEps.EpsLocalPStar.EpsMemOfClassCJeps ρ hρ
  have hgam1 : 0 < Work.Spaces.gam α - 1 := by
    have := Work.Spaces.one_lt_gam hα0
    linarith
  set R₀ : ℝ := Ceps / (Work.Spaces.gam α - 1) ^ 2 * M' with hR₀def
  have hR₀nn : 0 ≤ R₀ := by
    rw [hR₀def]
    exact mul_nonneg (div_nonneg hCeps_pos.le (sq_nonneg _)) hM
  set R : ℝ := 4 * R₀ + 4 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith
  obtain ⟨L, hLpos, hLsize, _hLlip⟩ :=
    Work.FTS.StrongEps.EpsLocalPStar.EpsRHSPLipX_Sq (α := α) (C₀ := 2 * C₀) (Ce := Ce) (Cs := Cs)
      (R := R) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) hα hρ hε hε1 hEll hstar hml hRpos.le
  obtain ⟨Cpt, hCptpos, hCptD⟩ :=
    Work.FTS.StrongEps.EpsLocalPStar.profRHS_sub_sup_le_Sq (α := α) (C₀ := 2 * C₀) (Ce := Ce)
      (Cs := Cs) (R := R) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) hα hρ hε hε1 hEll hstar hml
      hRpos.le
  obtain ⟨D, hDpos, hDD⟩ := Work.FTS.EpsEngine.exists_Xn_PzJeps_sub_le_sqrt_EpsSq ρ hρ
  set Cg : ℝ := D * (D / ε) ^ (2 * 4) with hCgdef
  have hCgpos : 0 < Cg := by
    rw [hCgdef]
    exact mul_pos hDpos (pow_pos (div_pos hDpos hε) _)
  set δ : ℝ := min 1 (min (1 / (1 + Real.sqrt L)) (C₀ * α ^ 2 / (2 * Real.sqrt (Cg * L))))
    with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min one_pos (lt_min (by positivity)
      (div_pos (mul_pos hC₀ (pow_pos hα0 2)) (by positivity)))
  have hδleL : δ ≤ 1 / (1 + Real.sqrt L) := by
    rw [hδdef]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδleXn : δ ≤ C₀ * α ^ 2 / (2 * Real.sqrt (Cg * L)) := by
    rw [hδdef]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hδL : δ * Real.sqrt L ≤ 1 := by
    have hsL : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
    have h2 : (1 / (1 + Real.sqrt L)) * Real.sqrt L ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_one (by positivity)]
      linarith
    exact le_trans (mul_le_mul_of_nonneg_right hδleL hsL) h2
  have hδsqL : δ ^ 2 * L ≤ 1 := by
    have h : (δ * Real.sqrt L) ^ 2 ≤ (1 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hδpos.le (Real.sqrt_nonneg L)) hδL 2
    rwa [mul_pow, Real.sq_sqrt hLpos.le, one_pow] at h
  have hδXn : δ * Real.sqrt (Cg * L) ≤ C₀ * α ^ 2 / 2 := by
    have hsC : 0 < Real.sqrt (Cg * L) := Real.sqrt_pos.mpr (mul_pos hCgpos hLpos)
    calc δ * Real.sqrt (Cg * L)
        ≤ (C₀ * α ^ 2 / (2 * Real.sqrt (Cg * L))) * Real.sqrt (Cg * L) :=
          mul_le_mul_of_nonneg_right hδleXn hsC.le
      _ = C₀ * α ^ 2 / 2 := by
          rw [div_mul_eq_mul_div]
          exact mul_div_mul_right _ _ hsC.ne'
  have hR₀le : R₀ ≤ R := by rw [hRdef]; linarith
  have hRq : R / 4 = R₀ + 1 := by rw [hRdef]; ring
  have hroom : ∀ τ : ℝ, τ ∈ Set.Icc 0 δ → 2 * (R / 4) + 2 * (τ * (τ * L)) ≤ R := by
    intro τ hτ
    have h1 : τ ^ 2 * L ≤ 1 := by
      have h : τ ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ hτ.1 hτ.2 2
      exact le_trans (mul_le_mul_of_nonneg_right h hLpos.le) hδsqL
    have h2 : τ * (τ * L) = τ ^ 2 * L := by ring
    rw [h2, hRq, hRdef]
    nlinarith [h1, hR₀nn]
  -- ## 1. the gates of the scheme's right-hand side at the class radius `2 C₀` and the ball `R`
  have hbdF : ∀ u : Fn, XBall α ρ ε R (2 * C₀) u →
      EpsMem α (Feps α ρ ε Φs E u) ∧ EpsSq α (Feps α ρ ε Φs E u) ≤ L := by
    intro u hu
    obtain ⟨hm, hb⟩ := hLsize u hu.smoothOpen hu.mem hu.sq_le hu.classC hu.ball
    rw [← Work.FTS.EpsEngine.Feps_eq_epsRHPSlice α ρ ε Φs E 0 u] at hm hb
    exact ⟨hm, hb⟩
  have hptF : ∀ u v : Fn, XBall α ρ ε R (2 * C₀) u → XBall α ρ ε R (2 * C₀) v →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Feps α ρ ε Φs E u z θ - Feps α ρ ε Φs E v z θ|
          ≤ Cpt * Real.sqrt (EpsSq α (fun z θ => u z θ - v z θ)) := by
    intro u v hu hv z θ hz hθ0 hθ2
    have h := hCptD hu.smoothOpen hv.smoothOpen hu.mem hu.sq_le hv.mem hv.sq_le hu.classC
      hv.classC hu.ball hv.ball z θ hz hθ0 hθ2
    rw [Work.FTS.EpsEngine.Feps_eq_epsRHPSlice α ρ ε Φs E 0 u,
      Work.FTS.EpsEngine.Feps_eq_epsRHPSlice α ρ ε Φs E 0 v]
    exact h
  have hcontF : ∀ u : Fn, XBall α ρ ε R (2 * C₀) u →
      ContinuousOn (fun q : ℝ × ℝ => Feps α ρ ε Φs E u q.1 q.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun u hu => (Work.FTS.EpsEngine.continuousOn_Feps_of_XBall (Ce := Ce) (Cs := Cs) (R := R)
      (C₀ := 2 * C₀) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (u := u) hα hρ hε hEll hstar hu).1
  have hzeroF : ∀ u : Fn, XBall α ρ ε R (2 * C₀) u → ∀ q : ℝ × ℝ,
      q ∉ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) → Feps α ρ ε Φs E u q.1 q.2 = 0 :=
    fun u hu => (Work.FTS.EpsEngine.continuousOn_Feps_of_XBall (Ce := Ce) (Cs := Cs) (R := R)
      (C₀ := 2 * C₀) (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (u := u) hα hρ hε hEll hstar hu).2
  refine ⟨δ, hδpos, R, hRpos, ?_⟩
  intro h₀ hsmo hmem6 hsq6 hcl0 hxn0
  -- ## 2. the datum's metric clauses and its membership in the ball
  have hdatum := hCepsD α hα ε hε hε1 h₀ hsmo hmem6 hcl0
  have hmem0 : EpsMem α h₀ := hdatum.1
  have hsq1 : Work.Spaces.HkSq α 1 h₀ ≤ M' :=
    le_trans (Work.FTS.StrongLWP.HkSq_mono_of_mem (α := α) (k := 6) (k' := 1) (by norm_num)
      hmem6) hsq6
  have hsq0 : EpsSq α h₀ ≤ R₀ := by
    rw [hR₀def]
    refine le_trans hdatum.2 (mul_le_mul_of_nonneg_left hsq1 (div_nonneg hCeps_pos.le
      (sq_nonneg _)))
  have hsq0q : EpsSq α h₀ ≤ R / 4 := by rw [hRq]; linarith
  have hmem4 : Work.Spaces.HkMem α 4 h₀ :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmo 4 (by norm_num) hmem6
  have hAK0 : Work.FTS.StrongEps.EpsSqTools.AK α h₀ :=
    Work.FTS.StrongEps.EpsSqTools.AK_of_uncurry
      (Work.Spaces.aesm_of_continuousOn_Qd _
        ((Work.FTS.EllipticEst.smoothOpen_iff_forall h₀).mp hsmo 0).continuousOn)
  have hXn0' : Work.FTS.Nonlin.Xn α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε h₀))
      ≤ 2 * C₀ * α ^ 2 :=
    le_trans hxn0 (by nlinarith [mul_nonneg hC₀.le (sq_nonneg α)])
  have hP0 : XBall α ρ ε R (2 * C₀) h₀ := ⟨hsmo, hmem0, le_trans hsq0 hR₀le, hcl0, hXn0'⟩
  -- ## 3. one Picard step preserves the ball
  have step : ∀ n : ℕ,
      (∀ m ≤ n, ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
        XBall α ρ ε R (2 * C₀) (slice (iter (Feps α ρ ε Φs E) h₀ m) τ)) →
      ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
        XBall α ρ ε R (2 * C₀) (slice (iter (Feps α ρ ε Φs E) h₀ (n + 1)) τ) := by
    intro n PH τ hτ
    -- ### 3a. the time-Lipschitz bound of the level-`n` curve
    have hEq : ∀ s ∈ Set.Icc 0 δ, ∀ t ∈ Set.Icc 0 δ, EpsSq α (fun z θ =>
        slice (iter (Feps α ρ ε Φs E) h₀ n) s z θ
          - slice (iter (Feps α ρ ε Φs E) h₀ n) t z θ) ≤ L * (s - t) ^ 2 :=
      Work.FTS.EpsEngine.EpsSq_iter_sub_sq_le (α := α) (Cpt := Cpt) (L := L) (δ := δ)
        (F := Feps α ρ ε Φs E) (h₀ := h₀) (P := fun u => XBall α ρ ε R (2 * C₀) u) n
        hδpos hLpos.le hCptpos.le PH hcontF hzeroF hbdF hptF
    -- ### 3b. `SmoothOpen` of the `(n+1)`-st slice
    have hsmoS : Work.FTS.EllipticEst.SmoothOpen
        (slice (iter (Feps α ρ ε Φs E) h₀ (n + 1)) τ) :=
      Work.FTS.EpsEngine.smoothOpen_iter_succ_XBall_prefix (α := α) (C₀ := 2 * C₀) (R := R)
        (Ce := Ce) (Cs := Cs) (Cpt := Cpt) (L := L) (δ := δ) (ρ := ρ) (Φs := Φs) (E := E)
        (ε := ε) (h₀ := h₀) n hα hρ hε hε1 hEll hstar hml hRpos.le hδpos hLpos.le hCptpos.le
        hsmo PH hcontF hzeroF hbdF hptF τ hτ
    -- ### 3c. the per-curve right-hand-side data at level `n` and `HkMem α 4` at level `n+1`
    obtain ⟨B, hBpos, hRHSD⟩ := Work.FTS.EpsEngine.exists_RHSData_feps_noTraces (α := α)
      (C₀ := 2 * C₀) (Ce := Ce) (Cs := Cs) (R := R) (Lw := L) (ε := ε) (T := δ) (ρ := ρ)
      (Φs := Φs) (E := E) (g₀ := h₀) hρ hα hε hε1 hRpos.le hLpos.le hδpos.le hEll hstar hml
    have hdata := hRHSD n (fun s hs => PH n le_rfl s hs)
      (fun s hs t ht => hEq s hs t ht)
    have hIsmo : Work.FTS.EllipticEst.SmoothOpen
        (fun z θ => ∫ s in (0 : ℝ)..τ, Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) h₀ n) s)
          z θ) :=
      Work.FTS.EpsEngine.smoothOpen_increment (F := Feps α ρ ε Φs E) (h₀ := h₀) (τ := τ) (n := n)
        hsmo hsmoS
    have hmemS4 : Work.Spaces.HkMem α 4 (slice (iter (Feps α ρ ε Φs E) h₀ (n + 1)) τ) :=
      (Work.FTS.EpsEngine.HkMem_iter_succ_of_data (α := α) (B := B) (F := Feps α ρ ε Φs E)
        (h₀ := h₀) (k := 4) (T := δ) (τ := τ) (n := n) hτ.1 hτ.2 hδpos.le hBpos.le hsmo hmem4
        hIsmo hdata.smo hdata.mem hdata.bd hdata.meas hdata.joint hdata.sup hdata.perz).1
    -- ### 3d. the increment: measurability, a.e. size bound, metric clauses
    obtain ⟨_hcontAll, haesmAll⟩ := Work.FTS.EpsEngine.iter_cont_meas_prefix (α := α)
      (Cpt := Cpt) (L := L) (δ := δ) (F := Feps α ρ ε Φs E) (h₀ := h₀)
      (P := fun u => XBall α ρ ε R (2 * C₀) u) n hδpos hLpos.le hCptpos.le PH hcontF hzeroF
      hbdF hptF
    have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ × ℝ =>
        Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) h₀ n) p.1) p.2.1 p.2.2
          * epsW α p.2.1 p.2.2)
        ((volume.restrict (Set.uIoc 0 τ)).prod DomM) :=
      Work.FTS.EpsEngine.aesm_weighted_uIoc_of_restrict
        (Φ := fun s => Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) h₀ n) s)) hτ
        (haesmAll n le_rfl)
    have hGbd : ∀ᵐ s ∂(volume.restrict (Set.uIoc 0 τ)),
        epsL2 α (Feps α ρ ε Φs E (slice (iter (Feps α ρ ε Φs E) h₀ n) s))
          ≤ ENNReal.ofReal L := by
      rw [MeasureTheory.ae_restrict_iff' (measurableSet_uIoc (a := (0 : ℝ)) (b := τ))]
      refine Filter.Eventually.of_forall (fun s hs => ?_)
      have hsδ : s ∈ Set.Icc 0 δ := by
        rw [Set.uIoc_of_le hτ.1] at hs
        exact ⟨le_of_lt hs.1, le_trans hs.2 hτ.2⟩
      exact Work.FTS.StrongEps.EpsLocalPStar.epsL2_le_ofReal_of_mem
        (hbdF _ (PH n le_rfl s hsδ)).1 (hbdF _ (PH n le_rfl s hsδ)).2
    have hinc := Work.FTS.StrongEps.EpsLocalPStar.VolterraAux.EpsMem_and_EpsSq_intervalIntegral_le
      (α := α) (τ := τ) (B := L) hτ.1 hLpos.le hmeas hGbd
    have hsubEq := slice_iter_succ_sub_eq (Feps α ρ ε Φs E) h₀ n τ
    have hincMem : EpsMem α (fun z θ => slice (iter (Feps α ρ ε Φs E) h₀ (n + 1)) τ z θ
        - h₀ z θ) :=
      Work.FTS.EpsEngine.EpsMem_congr_pt (fun z θ => (congrFun (congrFun hsubEq z) θ).symm)
        hinc.1
    have hincSq : EpsSq α (fun z θ => slice (iter (Feps α ρ ε Φs E) h₀ (n + 1)) τ z θ
        - h₀ z θ) ≤ τ * (τ * L) := by
      rw [hsubEq]
      exact hinc.2
    have hmetric := Work.FTS.EpsEngine.EpsMem_EpsSq_add_intervalIntegral_le (α := α) (τ := τ)
      (B := L) (R₀ := R / 4) (R := R) hτ.1 hLpos.le (hroom τ hτ)
      (Work.FTS.StrongEps.EpsLocalPStar.AK2_intervalIntegral (α := α) hτ.1 hmeas) hAK0 hmem0
      hsq0q hmeas hGbd
    have hmemS : EpsMem α (slice (iter (Feps α ρ ε Φs E) h₀ (n + 1)) τ) :=
      Work.FTS.EpsEngine.EpsMem_congr_pt (fun z θ =>
        (congrFun (congrFun (slice_iter_succ_eq (Feps α ρ ε Φs E) h₀ n τ) z) θ).symm) hmetric.1
    have hsqS : EpsSq α (slice (iter (Feps α ρ ε Φs E) h₀ (n + 1)) τ) ≤ R := by
      rw [slice_iter_succ_eq (Feps α ρ ε Φs E) h₀ n τ]
      exact hmetric.2
    -- ### 3e. the class-`C` clause
    have hfsm := contDiffOn_fstar_PzJeps (ρ := ρ) hρ (ε := ε) hε (α := α) hα hsmoS
      (Work.FTS.OpenPkg.HkMem_mono_open hsmoS 1 (by norm_num) hmemS4)
    have hclS : Work.FTS.ClassC.ClassC α (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε
        (slice (iter (Feps α ρ ε Φs E) h₀ (n + 1)) τ))) :=
      Work.FTS.EpsEngine.ThetaFromEps.classC_Pz_Jeps_of_epsMem (ρ := ρ) hρ hα hα1 hε hε1
        hsmoS hmemS4 hmemS hfsm
    -- ### 3f. the ball clause, from the datum's ball clause and the increment's size
    have hxm := hDD α hα ε hε hε1 (slice (iter (Feps α ρ ε Φs E) h₀ (n + 1)) τ) h₀ hsmoS hsmo
      hmemS4 hmem4 hincMem
    have hsqrt : Real.sqrt (Cg * (τ * (τ * L))) = Real.sqrt (Cg * L) * τ := by
      rw [show Cg * (τ * (τ * L)) = (Cg * L) * τ ^ 2 by ring, Real.sqrt_mul (mul_nonneg
        (le_of_lt hCgpos) hLpos.le), Real.sqrt_sq hτ.1]
    have htail : Real.sqrt (D * (D / ε) ^ (2 * 4) * EpsSq α (fun z θ =>
        slice (iter (Feps α ρ ε Φs E) h₀ (n + 1)) τ z θ - h₀ z θ)) ≤ C₀ * α ^ 2 := by
      have hCg_eq : D * (D / ε) ^ (2 * 4) = Cg := hCgdef.symm
      rw [hCg_eq]
      refine le_trans (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hincSq hCgpos.le)) ?_
      rw [hsqrt]
      have h2 : Real.sqrt (Cg * L) * τ ≤ Real.sqrt (Cg * L) * δ :=
        mul_le_mul_of_nonneg_left hτ.2 (Real.sqrt_nonneg _)
      have h3 : Real.sqrt (Cg * L) * δ ≤ C₀ * α ^ 2 / 2 := by
        rw [mul_comm]
        exact hδXn
      have hCa : 0 ≤ C₀ * α ^ 2 := mul_nonneg hC₀.le (sq_nonneg α)
      linarith
    exact ⟨hsmoS, hmemS, hsqS, hclS, le_trans hxm (by
      have h2C : 2 * C₀ * α ^ 2 = C₀ * α ^ 2 + C₀ * α ^ 2 := by ring
      linarith)⟩
  -- ## 4. the prefix induction
  have hQ : ∀ n : ℕ, ∀ m ≤ n, ∀ τ : ℝ, τ ∈ Set.Icc 0 δ →
      XBall α ρ ε R (2 * C₀) (slice (iter (Feps α ρ ε Φs E) h₀ m) τ) := by
    intro n
    induction n with
    | zero =>
      intro m hm τ _
      have hm0 : m = 0 := Nat.le_zero.mp hm
      subst hm0
      rw [slice_iter_zero_eq]
      exact hP0
    | succ n ih =>
      intro m hm τ hτ
      rcases Nat.lt_or_eq_of_le hm with hlt | heq
      · exact ih m (Nat.lt_succ_iff.mp hlt) τ hτ
      · subst heq
        exact step n ih τ hτ
  exact ⟨hmem0, le_trans hsq0 hR₀le, fun n τ hτ => hQ (n + 1) (n + 1) le_rfl τ hτ⟩

end Work.FTS.StrongEps.EpsE4Thr
