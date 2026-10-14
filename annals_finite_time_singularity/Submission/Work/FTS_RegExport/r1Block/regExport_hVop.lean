import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EpsEngine.LocalStepXBall
import Submission.Work.FTS_RegExport.RXR1.r1Block_proved
import Submission.Work.FTS_RegExport.RXT.Sys.FBZhat
import Submission.Work.FTS_RegExport.RXT.Sys.PullDefs
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.weighted_system
import Submission.Work.FTS_RegExport.RXVP.NoHdat.bnd_open_noHdat
import Submission.Work.FTS_RegExport.RXVP.NoHdat.velPkgEasy_noHdat
import Submission.Work.FTS_RegExport.RXVP.thLip
import Submission.Work.FTS_RegExport.RXVP.velPkg_proved
import Submission.Work.FTS_RegExport.RXVP3.cont_open
import Submission.Work.FTS_RegExport.RXVP3.velPkgOpen_of_vopLower
import Submission.Work.FTS_RegExport.RXVPMain
import Submission.Work.FTS_RegExport.RegExportProved
import Submission.Work.FTS_RegExport.Supp
import Submission.Work.FTS_StreamBdry.SB4.lim_mixed_plainE
import Submission.Work.FTS_StreamBdry.SB4.slice_L12_c2
-- ===== merged: Submission.Work.FTS.EpsEngine.LimSmoothOpen =====
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
open Work.FTS.StrongEps.EpsLocalPStar

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## 1. `logPull` of a parametric interval integral -/

/-- **`logPull` commutes with the parametric interval integral.**  If `x ↦ (s ↦ logPull (G s) x)`
is jointly continuous in `(x, s)` (time clamped to `[0,τ]`), then so is `logPull` of the parametric
integral. -/
theorem continuous_logPull_intervalIntegral {G : ℝ → Fn} {τ : ℝ} (hτ : 0 ≤ τ)
    (hG : Continuous (fun q : ℝ × (ℝ × ℝ) => logPull (G (projIcc 0 τ hτ q.1 : ℝ)) q.2)) :
    Continuous (logPull (fun z θ => ∫ s in (0 : ℝ)..τ, G (projIcc 0 τ hτ s : ℝ) z θ)) := by
  have hc : Continuous (Function.uncurry (fun (x : ℝ × ℝ) (s : ℝ) =>
      logPull (G (projIcc 0 τ hτ s : ℝ)) x)) := hG.comp continuous_swap
  have h := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := (volume : Measure ℝ)) hc (0 : ℝ) τ
  show Continuous (fun x : ℝ × ℝ => ∫ t in (0 : ℝ)..τ,
    G (projIcc 0 τ hτ t : ℝ) (Real.exp x.1) (Real.arctan (Real.exp x.2)))
  exact h

/-! ## 2. `J_ε` for the `logPull`-uniform distance -/

/-- **The quantitative continuity of `J_ε` in the profile.**  If the `logPull`s of two profiles are
uniformly within `b`, then their mollified values agree within `b` at every point of the open
quadrant.  (The kernel has total mass one, so it is an averaging operator.) -/
theorem abs_Jeps_sub_le_of_logPull_le {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ)
    {ε b : ℝ} (hε : 0 < ε) (hb0 : 0 ≤ b) {f g : Fn}
    (hf : Continuous (logPull f)) (hg : Continuous (logPull g))
    (hb : ∀ x : ℝ × ℝ, |logPull f x - logPull g x| ≤ b)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    |Jeps ρ ε f z θ - Jeps ρ ε g z θ| ≤ b := by
  have hJint : Integrable (Jker ρ ε) (volume : Measure (ℝ × ℝ)) := Jker_integrable hρ.moll hε
  have hJmass : ∫ p : ℝ × ℝ, Jker ρ ε p = 1 := Jker_integral_eq_one ρ hρ.moll hε
  have hJnn : ∀ p : ℝ × ℝ, 0 ≤ Jker ρ ε p := fun p => by
    simp only [Jker]
    exact mul_nonneg (by positivity) (hρ.moll.nonneg (ε⁻¹ • p))
  have hJcs : HasCompactSupport (Jker ρ ε) := Jker_hasCompactSupport hρ.moll hε
  have hJcont : Continuous (Jker ρ ε) := Jker_continuous hρ.moll ε
  -- the shift from the log-coordinates back to `(z,θ)`
  have hshiftf : ∀ p : ℝ × ℝ, logPull f (sOf z - p.1, zetaOf θ - p.2)
      = f (zShift z p.1) (thShift θ p.2) := by
    intro p
    have h1 : Real.exp (sOf z - p.1) = z * Real.exp (-p.1) := by
      rw [sOf, Real.exp_sub, Real.exp_log hz, Real.exp_neg, div_eq_mul_inv]
    have h2 : Real.exp (zetaOf θ - p.2) = Real.tan θ * Real.exp (-p.2) := by
      rw [zetaOf, Real.exp_sub,
        Real.exp_log (Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2), Real.exp_neg,
        div_eq_mul_inv]
    show f (Real.exp (sOf z - p.1)) (Real.arctan (Real.exp (zetaOf θ - p.2)))
      = f (z * Real.exp (-p.1)) (Real.arctan (Real.tan θ * Real.exp (-p.2)))
    rw [h1, h2]
  have hshiftg : ∀ p : ℝ × ℝ, logPull g (sOf z - p.1, zetaOf θ - p.2)
      = g (zShift z p.1) (thShift θ p.2) := by
    intro p
    have h1 : Real.exp (sOf z - p.1) = z * Real.exp (-p.1) := by
      rw [sOf, Real.exp_sub, Real.exp_log hz, Real.exp_neg, div_eq_mul_inv]
    have h2 : Real.exp (zetaOf θ - p.2) = Real.tan θ * Real.exp (-p.2) := by
      rw [zetaOf, Real.exp_sub,
        Real.exp_log (Real.tan_pos_of_pos_of_lt_pi_div_two hθ.1 hθ.2), Real.exp_neg,
        div_eq_mul_inv]
    show g (Real.exp (sOf z - p.1)) (Real.arctan (Real.exp (zetaOf θ - p.2)))
      = g (z * Real.exp (-p.1)) (Real.arctan (Real.tan θ * Real.exp (-p.2)))
    rw [h1, h2]
  -- integrability of the two weighted `logPull`s (compact support of the kernel)
  have hIntf : Integrable (fun p : ℝ × ℝ =>
      Jker ρ ε p * logPull f (sOf z - p.1, zetaOf θ - p.2)) := by
    have hc : Continuous (fun p : ℝ × ℝ =>
        Jker ρ ε p * logPull f (sOf z - p.1, zetaOf θ - p.2)) :=
      hJcont.mul (hf.comp (Continuous.prodMk (continuous_const.sub continuous_fst)
        (continuous_const.sub continuous_snd)))
    exact hc.integrable_of_hasCompactSupport hJcs.mul_right
  have hIntg : Integrable (fun p : ℝ × ℝ =>
      Jker ρ ε p * logPull g (sOf z - p.1, zetaOf θ - p.2)) := by
    have hc : Continuous (fun p : ℝ × ℝ =>
        Jker ρ ε p * logPull g (sOf z - p.1, zetaOf θ - p.2)) :=
      hJcont.mul (hg.comp (Continuous.prodMk (continuous_const.sub continuous_fst)
        (continuous_const.sub continuous_snd)))
    exact hc.integrable_of_hasCompactSupport hJcs.mul_right
  have hJf : Jeps ρ ε f z θ
      = ∫ p : ℝ × ℝ, Jker ρ ε p * logPull f (sOf z - p.1, zetaOf θ - p.2) := by
    rw [Jeps_eq_integral ρ ε f hz hθ]
    exact integral_congr_ae (Eventually.of_forall fun p => by simp only [hshiftf p])
  have hJg : Jeps ρ ε g z θ
      = ∫ p : ℝ × ℝ, Jker ρ ε p * logPull g (sOf z - p.1, zetaOf θ - p.2) := by
    rw [Jeps_eq_integral ρ ε g hz hθ]
    exact integral_congr_ae (Eventually.of_forall fun p => by simp only [hshiftg p])
  have hsub : Jeps ρ ε f z θ - Jeps ρ ε g z θ
      = ∫ p : ℝ × ℝ, Jker ρ ε p * (logPull f (sOf z - p.1, zetaOf θ - p.2)
          - logPull g (sOf z - p.1, zetaOf θ - p.2)) := by
    rw [hJf, hJg, ← integral_sub hIntf hIntg]
    exact integral_congr_ae (Eventually.of_forall fun p => by ring)
  rw [hsub]
  have hae : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)),
      ‖Jker ρ ε p * (logPull f (sOf z - p.1, zetaOf θ - p.2)
        - logPull g (sOf z - p.1, zetaOf θ - p.2))‖ ≤ Jker ρ ε p * b := by
    filter_upwards with p
    by_cases hp : Jker ρ ε p = 0
    · simp [hp]
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hJnn p)]
      exact mul_le_mul_of_nonneg_left (hb _) (hJnn p)
  have h := norm_integral_le_of_norm_le (hJint.mul_const b) hae
  rw [integral_mul_const, hJmass, one_mul] at h
  simpa only [Real.norm_eq_abs] using h



/-! ## 3. The `SmoothOpen` clause of `hlimP` -/

/-- The `n`-th Picard iterate of the projected `ε`-scheme. -/
abbrev epsIter (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (Φs : Fn) (E : Fn → Fn) (h₀ : Fn) (n : ℕ) :
    Fam :=
  iter (Feps α ρ ε Φs E) h₀ n

/-- The limit family of the Picard iteration of the projected `ε`-scheme. -/
abbrev epsLim (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (Φs : Fn) (E : Fn → Fn) (h₀ : Fn) : Fam :=
  limFam (Feps α ρ ε Φs E) h₀

/-- The integrand of the mollified form of one Picard step. -/
abbrev epsG (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (Φs : Fn) (E : Fn → Fn) (h₀ : Fn) (n : ℕ)
    (s : ℝ) : Fn :=
  profRHS α Φs E (Pz (Jeps ρ ε (slice (epsIter α ρ ε Φs E h₀ n) s)))

/-- Its time-integral `Ψ_n`. -/
abbrev epsPsi (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (Φs : Fn) (E : Fn → Fn) (h₀ : Fn) (n : ℕ)
    (τ : ℝ) : Fn :=
  fun z θ => ∫ s in (0 : ℝ)..τ, epsG α ρ ε Φs E h₀ n s z θ

/-- The coefficient of the projection bump in the mollified form. -/
abbrev epsC (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (Φs : Fn) (E : Fn → Fn) (h₀ : Fn) (n : ℕ)
    (τ : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..τ, Work.Construction.L12 (Jeps ρ ε (epsG α ρ ε Φs E h₀ n s)) 0 / pzNorm

/-- **The `SmoothOpen` clause of `hlimP`.**  If every Picard iterate of the projected `ε`-scheme
stays in the `X`-ball (`hP`), is time-Lipschitz (`hEq`) and satisfies the geometric pair bound
(`hpair`), and is in the mollified form `hmoll` of one Picard step (with the limit `hconv`), then
every slice of the limit family is `C^∞` on the open quadrant. -/
theorem smoothOpen_limFam_slice {α C₀ R Ce Cs Lw δ q : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn}
    {E : Fn → Fn} {ε : ℝ} {h₀ : Fn}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : MuLamOK α C₀ Φs E) (hR : 0 ≤ R) (hLw : 0 ≤ Lw)
    (h0 : Work.FTS.EllipticEst.SmoothOpen h₀) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hP : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ →
      XBall α ρ ε R C₀ (slice (epsIter α ρ ε Φs E h₀ n) s))
    (hEq : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → ∀ t : ℝ, t ∈ Set.Icc 0 δ →
      EpsSq α (fun z θ => slice (epsIter α ρ ε Φs E h₀ n) s z θ
        - slice (epsIter α ρ ε Φs E h₀ n) t z θ) ≤ Lw * (s - t) ^ 2)
    (hpair : ∀ (n m : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → n ≤ m → EpsSq α (fun z θ =>
        slice (epsIter α ρ ε Φs E h₀ n) s z θ
          - slice (epsIter α ρ ε Φs E h₀ m) s z θ) ≤ q ^ n)
    (hmoll : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z →
      θ ∈ Set.Ioo 0 (π / 2) →
      slice (epsIter α ρ ε Φs E h₀ (n + 1)) s z θ
        = h₀ z θ + Jeps ρ ε (epsPsi α ρ ε Φs E h₀ n s) z θ
          - epsC α ρ ε Φs E h₀ n s * bump z θ)
    (hconv : ∀ (s : ℝ), s ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Tendsto (fun N : ℕ => slice (epsIter α ρ ε Φs E h₀ N) s z θ) atTop
        (𝓝 (slice (epsLim α ρ ε Φs E h₀) s z θ)))
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 δ) :
    Work.FTS.EllipticEst.SmoothOpen (slice (epsLim α ρ ε Φs E h₀) τ) := by
  obtain ⟨C, hCpos, hC⟩ := profRHS_pre_sub_pt_le_Sq (ρ := ρ) (Φs := Φs) (E := E)
    hα hρ hε hε1 hEll hstar hml hR
  have hCnn : 0 ≤ C := hCpos.le
  set r : ℝ := Real.sqrt q with hrdef
  have hr0 : 0 ≤ r := Real.sqrt_nonneg q
  have hr2 : r ^ 2 = q := by rw [hrdef]; exact Real.sq_sqrt hq0
  have hr1 : r < 1 := by
    have h := Real.sqrt_nonneg q
    rw [hrdef] at hr2 ⊢
    nlinarith
  have hrpow : ∀ n : ℕ, Real.sqrt (q ^ n) = r ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', Real.sqrt_mul hq0, ← hrdef, ih, pow_succ']
  set K : ℝ := C * Real.sqrt Lw with hKdef
  have hKnn : 0 ≤ K := mul_nonneg hCnn (Real.sqrt_nonneg _)
  -- ### the pointwise Lipschitz bound of the pre-mollified right-hand side along the iterates
  have hGLip : ∀ (n m : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → n ≤ m → ∀ z θ : ℝ, 0 < z →
      θ ∈ Set.Ioo 0 (π / 2) →
      |epsG α ρ ε Φs E h₀ n s z θ - epsG α ρ ε Φs E h₀ m s z θ|
        ≤ C * Real.sqrt (q ^ n) := by
    intro n m s hs hnm z θ hz hθ
    refine (hC (hP n s hs).smoothOpen (hP m s hs).smoothOpen (hP n s hs).mem (hP n s hs).sq_le
      (hP m s hs).mem (hP m s hs).sq_le (hP n s hs).classC (hP m s hs).classC
      (hP n s hs).ball (hP m s hs).ball z θ hz hθ.1 hθ.2).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hpair n m s hs hnm)) hCnn
  -- ### the time-Lipschitz bound of the integrand
  have hTimeLip : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → ∀ t : ℝ, t ∈ Set.Icc 0 δ →
      ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      |epsG α ρ ε Φs E h₀ n s z θ - epsG α ρ ε Φs E h₀ n t z θ| ≤ K * |s - t| := by
    intro n s hs t ht z θ hz hθ
    have h1 := hC (hP n s hs).smoothOpen (hP n t ht).smoothOpen (hP n s hs).mem (hP n s hs).sq_le
      (hP n t ht).mem (hP n t ht).sq_le (hP n s hs).classC (hP n t ht).classC
      (hP n s hs).ball (hP n t ht).ball z θ hz hθ.1 hθ.2
    have h2 : Real.sqrt (EpsSq α (fun z θ => slice (epsIter α ρ ε Φs E h₀ n) s z θ
        - slice (epsIter α ρ ε Φs E h₀ n) t z θ)) ≤ Real.sqrt Lw * |s - t| := by
      rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hLw]
      exact Real.sqrt_le_sqrt (hEq n s hs t ht)
    rw [hKdef]
    calc |epsG α ρ ε Φs E h₀ n s z θ - epsG α ρ ε Φs E h₀ n t z θ|
        ≤ C * Real.sqrt (EpsSq α (fun z θ => slice (epsIter α ρ ε Φs E h₀ n) s z θ
            - slice (epsIter α ρ ε Φs E h₀ n) t z θ)) := h1
      _ ≤ C * (Real.sqrt Lw * |s - t|) := mul_le_mul_of_nonneg_left h2 hCnn
      _ = C * Real.sqrt Lw * |s - t| := by ring
  -- ### continuity in the fake time of the integrand at a fixed point
  have hcontSlice : ∀ (k : ℕ) (z θ : ℝ), 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      ContinuousOn (fun s => epsG α ρ ε Φs E h₀ k s z θ) (Set.Icc 0 δ) := by
    intro k z θ hz hθ
    rw [Metric.continuousOn_iff]
    intro s hs η hη
    refine ⟨η / (K + 1), div_pos hη (by linarith), fun t ht hst => ?_⟩
    rw [Real.dist_eq] at hst ⊢
    have h1 : |epsG α ρ ε Φs E h₀ k t z θ - epsG α ρ ε Φs E h₀ k s z θ| ≤ K * |t - s| :=
      hTimeLip k t ht s hs z θ hz hθ
    have h2 : K * |t - s| < η := by
      rcases eq_or_lt_of_le hKnn with h | h
      · rw [← h]; simpa using hη
      · have h3 : K * |t - s| < K * (η / (K + 1)) := mul_lt_mul_of_pos_left hst h
        have h4 : K * (η / (K + 1)) = η * (K / (K + 1)) := by ring_nf
        have h5 : K / (K + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
        have h6 : η * (K / (K + 1)) < η * 1 := mul_lt_mul_of_pos_left h5 hη
        rw [h4] at h3
        linarith
    linarith
  -- ### the pair bound for `Ψ`
  have hPsiPair : ∀ (n m : ℕ), n ≤ m → ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      |epsPsi α ρ ε Φs E h₀ n τ z θ - epsPsi α ρ ε Φs E h₀ m τ z θ|
        ≤ τ * (C * Real.sqrt (q ^ n)) := by
    intro n m hnm z θ hz hθ
    have hint : ∀ k : ℕ, IntervalIntegrable (fun s => epsG α ρ ε Φs E h₀ k s z θ) volume 0 τ :=
      fun k => ContinuousOn.intervalIntegrable_of_Icc hτ.1
        ((hcontSlice k z θ hz hθ).mono (Set.Icc_subset_Icc_right hτ.2))
    have hsub : epsPsi α ρ ε Φs E h₀ n τ z θ - epsPsi α ρ ε Φs E h₀ m τ z θ
        = ∫ s in (0 : ℝ)..τ, (epsG α ρ ε Φs E h₀ n s z θ
            - epsG α ρ ε Φs E h₀ m s z θ) := by
      simp only [epsPsi]
      exact (intervalIntegral.integral_sub (hint n) (hint m)).symm
    rw [hsub]
    have hbdd : ∀ s ∈ Set.uIoc (0 : ℝ) τ,
        ‖epsG α ρ ε Φs E h₀ n s z θ - epsG α ρ ε Φs E h₀ m s z θ‖
          ≤ C * Real.sqrt (q ^ n) := by
      intro s hs
      rw [Set.uIoc_of_le hτ.1] at hs
      rw [Real.norm_eq_abs]
      exact hGLip n m s ⟨le_of_lt hs.1, le_trans hs.2 hτ.2⟩ hnm z θ hz hθ
    have h2 := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := τ)
      (C := C * Real.sqrt (q ^ n))
      (f := fun s => epsG α ρ ε Φs E h₀ n s z θ - epsG α ρ ε Φs E h₀ m s z θ) hbdd
    rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hτ.1] at h2
    exact h2.trans (le_of_eq (by ring))
  -- ### `Ψ n` is Cauchy
  have hcauchy : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      CauchySeq (fun n : ℕ => epsPsi α ρ ε Φs E h₀ n τ z θ) := by
    intro z θ hz hθ
    refine cauchySeq_of_le_geometric r (τ * C) hr1 (fun n => ?_)
    rw [Real.dist_eq]
    have h := hPsiPair n (n + 1) (by omega) z θ hz hθ
    rw [hrpow n] at h
    refine h.trans (le_of_eq ?_)
    ring
  have hex : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      ∃ L : ℝ, Tendsto (fun n : ℕ => epsPsi α ρ ε Φs E h₀ n τ z θ) atTop (𝓝 L) :=
    fun z θ hz hθ => cauchySeq_tendsto_of_complete (hcauchy z θ hz hθ)
  let PsiL : Fn := fun z θ => if h : 0 < z ∧ θ ∈ Set.Ioo 0 (π / 2) then
      Classical.choose (hex z θ h.1 h.2) else 0
  have hPsiL : ∀ (z θ : ℝ) (h : 0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)),
      Tendsto (fun n : ℕ => epsPsi α ρ ε Φs E h₀ n τ z θ) atTop (𝓝 (PsiL z θ)) := by
    intro z θ h
    have h1 : PsiL z θ = Classical.choose (hex z θ h.1 h.2) := dif_pos h
    rw [h1]
    exact Classical.choose_spec (hex z θ h.1 h.2)
  have hPsiUniform : ∀ (n : ℕ) (z θ : ℝ), 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      |epsPsi α ρ ε Φs E h₀ n τ z θ - PsiL z θ| ≤ (τ * C) * r ^ n := by
    intro n z θ hz hθ
    have hb : ∀ m : ℕ, n ≤ m →
        |epsPsi α ρ ε Φs E h₀ n τ z θ - epsPsi α ρ ε Φs E h₀ m τ z θ| ≤ (τ * C) * r ^ n := by
      intro m hm
      have h := hPsiPair n m hm z θ hz hθ
      rw [hrpow n] at h
      refine h.trans (le_of_eq ?_)
      ring
    have htend : Tendsto (fun m : ℕ => |epsPsi α ρ ε Φs E h₀ n τ z θ
        - epsPsi α ρ ε Φs E h₀ m τ z θ|) atTop
        (𝓝 |epsPsi α ρ ε Φs E h₀ n τ z θ - PsiL z θ|) := by
      have h1 : Tendsto (fun m : ℕ => epsPsi α ρ ε Φs E h₀ n τ z θ
          - epsPsi α ρ ε Φs E h₀ m τ z θ) atTop
          (𝓝 (epsPsi α ρ ε Φs E h₀ n τ z θ - PsiL z θ)) :=
        (hPsiL z θ ⟨hz, hθ⟩).const_sub _
      exact (continuous_abs.tendsto _).comp h1
    exact le_of_tendsto htend (Filter.eventually_atTop.2 ⟨n, hb⟩)
  -- ### continuity of `logPull (Ψ n)`
  have hcontPsiLog : ∀ n : ℕ, Continuous (logPull (epsPsi α ρ ε Φs E h₀ n τ)) := by
    intro n
    have h1 : Continuous (fun q : ℝ × (ℝ × ℝ) =>
        logPull (epsG α ρ ε Φs E h₀ n (projIcc 0 τ hτ.1 q.1 : ℝ)) q.2) :=
      SORuling.continuous_logPull_family hτ.1 (K := ⟨K, hKnn⟩)
        (fun s hs => by
          have hs' : s ∈ Set.Icc 0 δ := ⟨hs.1, le_trans hs.2 hτ.2⟩
          exact ((smoothOpen_profRHS_of_classC hα hEll hstar
            (hP n s hs').classC).forall 0).continuousOn)
        (fun s hs t ht z θ hz hθ => by
          have hs' : s ∈ Set.Icc 0 δ := ⟨hs.1, le_trans hs.2 hτ.2⟩
          have ht' : t ∈ Set.Icc 0 δ := ⟨ht.1, le_trans ht.2 hτ.2⟩
          exact hTimeLip n s hs' t ht' z θ hz hθ)
    have h2 := continuous_logPull_intervalIntegral (G := epsG α ρ ε Φs E h₀ n) hτ.1 h1
    have heq : (fun z θ => ∫ s in (0 : ℝ)..τ,
          epsG α ρ ε Φs E h₀ n (projIcc 0 τ hτ.1 s : ℝ) z θ) = epsPsi α ρ ε Φs E h₀ n τ := by
      funext z θ
      show (∫ s in (0 : ℝ)..τ, epsG α ρ ε Φs E h₀ n (projIcc 0 τ hτ.1 s : ℝ) z θ)
        = ∫ s in (0 : ℝ)..τ, epsG α ρ ε Φs E h₀ n s z θ
      refine intervalIntegral.integral_congr (fun s hs => ?_)
      rw [Set.uIcc_of_le hτ.1] at hs
      show epsG α ρ ε Φs E h₀ n (projIcc 0 τ hτ.1 s : ℝ) z θ = epsG α ρ ε Φs E h₀ n s z θ
      rw [show (projIcc 0 τ hτ.1 s : ℝ) = s from
        congrArg Subtype.val (projIcc_of_mem hτ.1 hs)]
    rw [heq] at h2
    exact h2
  -- ### uniform convergence and the limit
  have hPsiUniformLog : ∀ (n : ℕ) (x : ℝ × ℝ),
      |logPull (epsPsi α ρ ε Φs E h₀ n τ) x - logPull PsiL x| ≤ (τ * C) * r ^ n := by
    intro n x
    have hz : 0 < Real.exp x.1 := Real.exp_pos x.1
    have hθ : Real.arctan (Real.exp x.2) ∈ Set.Ioo 0 (π / 2) :=
      ⟨(Real.arctan_pos).mpr (Real.exp_pos x.2), Real.arctan_lt_pi_div_two _⟩
    show |epsPsi α ρ ε Φs E h₀ n τ (Real.exp x.1) (Real.arctan (Real.exp x.2))
      - PsiL (Real.exp x.1) (Real.arctan (Real.exp x.2))| ≤ (τ * C) * r ^ n
    exact hPsiUniform n _ _ hz hθ
  have hbgeo : Tendsto (fun n : ℕ => (τ * C) * r ^ n) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    simpa using h.const_mul (τ * C)
  have hTU : TendstoUniformly (fun n : ℕ => logPull (epsPsi α ρ ε Φs E h₀ n τ))
      (logPull PsiL) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hbgeo.eventually (Iio_mem_nhds hε))
    filter_upwards [Filter.eventually_ge_atTop N] with n hn x
    rw [Real.dist_eq, abs_sub_comm]
    exact lt_of_le_of_lt (hPsiUniformLog n x) (hN n hn)
  have hcontPsiL : Continuous (logPull PsiL) :=
    hTU.continuous (Filter.frequently_atTop.2 fun n => ⟨n, le_refl n, hcontPsiLog n⟩)
  -- ### the mollified values converge
  have hJepsTend : ∀ (z θ : ℝ) (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)),
      Tendsto (fun n : ℕ => Jeps ρ ε (epsPsi α ρ ε Φs E h₀ n τ) z θ) atTop
        (𝓝 (Jeps ρ ε PsiL z θ)) := by
    intro z θ hz hθ
    have hsq : Tendsto (fun n : ℕ => |Jeps ρ ε (epsPsi α ρ ε Φs E h₀ n τ) z θ
        - Jeps ρ ε PsiL z θ|) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbgeo
        (fun n => abs_nonneg _) (fun n => ?_)
      exact abs_Jeps_sub_le_of_logPull_le hρ hε
        (mul_nonneg (mul_nonneg hτ.1 hCnn) (pow_nonneg hr0 n))
        (hcontPsiLog n) hcontPsiL (hPsiUniformLog n) hz hθ
    exact (tendsto_iff_norm_sub_tendsto_zero).mpr
      (by simpa only [Real.norm_eq_abs] using hsq)
  -- ### the point where `bump` does not vanish, and the limit coefficient
  have hyz : 0 < (3 : ℝ) / 4 := by norm_num
  have hyθ : (5 * Real.pi / 16) ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hbumpne : bump ((3 : ℝ) / 4) (5 * Real.pi / 16) ≠ 0 := by
    intro h
    have h' := bump_eq_zero_iff.mp h
    rcases h' with h' | h' | h' | h'
    · norm_num at h'
    · norm_num at h'
    · have := Real.pi_pos; nlinarith
    · have := Real.pi_pos; nlinarith
  set cLim : ℝ := (h₀ ((3 : ℝ) / 4) (5 * Real.pi / 16)
      + Jeps ρ ε PsiL ((3 : ℝ) / 4) (5 * Real.pi / 16)
      - slice (epsLim α ρ ε Φs E h₀) τ ((3 : ℝ) / 4) (5 * Real.pi / 16))
      / bump ((3 : ℝ) / 4) (5 * Real.pi / 16) with hcLimdef
  have hClim : Tendsto (fun n : ℕ => epsC α ρ ε Φs E h₀ n τ) atTop (𝓝 cLim) := by
    have hcongr : ∀ n : ℕ, epsC α ρ ε Φs E h₀ n τ
        = (h₀ ((3 : ℝ) / 4) (5 * Real.pi / 16)
            + Jeps ρ ε (epsPsi α ρ ε Φs E h₀ n τ) ((3 : ℝ) / 4) (5 * Real.pi / 16)
            - slice (epsIter α ρ ε Φs E h₀ (n + 1)) τ ((3 : ℝ) / 4) (5 * Real.pi / 16))
          / bump ((3 : ℝ) / 4) (5 * Real.pi / 16) := by
      intro n
      have h := hmoll n τ hτ ((3 : ℝ) / 4) (5 * Real.pi / 16) hyz hyθ
      have h2 : epsC α ρ ε Φs E h₀ n τ * bump ((3 : ℝ) / 4) (5 * Real.pi / 16)
          = h₀ ((3 : ℝ) / 4) (5 * Real.pi / 16)
            + Jeps ρ ε (epsPsi α ρ ε Φs E h₀ n τ) ((3 : ℝ) / 4) (5 * Real.pi / 16)
            - slice (epsIter α ρ ε Φs E h₀ (n + 1)) τ ((3 : ℝ) / 4)
                (5 * Real.pi / 16) := by
        linarith [h]
      field_simp [hbumpne]
      linarith [h2]
    have hnum : Tendsto (fun n : ℕ => h₀ ((3 : ℝ) / 4) (5 * Real.pi / 16)
        + Jeps ρ ε (epsPsi α ρ ε Φs E h₀ n τ) ((3 : ℝ) / 4) (5 * Real.pi / 16)
        - slice (epsIter α ρ ε Φs E h₀ (n + 1)) τ ((3 : ℝ) / 4) (5 * Real.pi / 16)) atTop
        (𝓝 (h₀ ((3 : ℝ) / 4) (5 * Real.pi / 16)
          + Jeps ρ ε PsiL ((3 : ℝ) / 4) (5 * Real.pi / 16)
          - slice (epsLim α ρ ε Φs E h₀) τ ((3 : ℝ) / 4) (5 * Real.pi / 16))) := by
      refine (tendsto_const_nhds.add (hJepsTend _ _ hyz hyθ)).sub ?_
      exact ((hconv τ hτ ((3 : ℝ) / 4) (5 * Real.pi / 16) hyz hyθ.1 hyθ.2).comp
        (tendsto_add_atTop_nat 1))
    have hdiv := hnum.div_const (bump ((3 : ℝ) / 4) (5 * Real.pi / 16))
    rw [hcLimdef]
    refine (Filter.Tendsto.congr' ?_ hdiv)
    exact Eventually.of_forall fun n => (hcongr n).symm
  -- ### the identity defining the limit family on the quadrant
  have hIdent : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      slice (epsLim α ρ ε Φs E h₀) τ z θ = h₀ z θ + Jeps ρ ε PsiL z θ - cLim * bump z θ := by
    intro z θ hz hθ
    have hL : Tendsto (fun n : ℕ => slice (epsIter α ρ ε Φs E h₀ (n + 1)) τ z θ) atTop
        (𝓝 (slice (epsLim α ρ ε Φs E h₀) τ z θ)) :=
      (hconv τ hτ z θ hz hθ.1 hθ.2).comp (tendsto_add_atTop_nat 1)
    have hR : Tendsto (fun n : ℕ => h₀ z θ + Jeps ρ ε (epsPsi α ρ ε Φs E h₀ n τ) z θ
        - epsC α ρ ε Φs E h₀ n τ * bump z θ) atTop
        (𝓝 (h₀ z θ + Jeps ρ ε PsiL z θ - cLim * bump z θ)) :=
      ((tendsto_const_nhds.add (hJepsTend z θ hz hθ)).sub (hClim.mul_const (bump z θ)))
    have heq : (fun n : ℕ => slice (epsIter α ρ ε Φs E h₀ (n + 1)) τ z θ)
        =ᶠ[atTop] (fun n : ℕ => h₀ z θ + Jeps ρ ε (epsPsi α ρ ε Φs E h₀ n τ) z θ
          - epsC α ρ ε Φs E h₀ n τ * bump z θ) :=
      Eventually.of_forall fun n => hmoll n τ hτ z θ hz hθ
    exact tendsto_nhds_unique hL ((Filter.tendsto_congr' heq).mpr hR)
  exact SORuling.smoothOpen_of_mollForm hρ hε h0 hcontPsiL hIdent

end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.UnifTraceDefs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

namespace Work.FTS.EpsEngine

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The uniform (ε-δ) boundary-trace data of a profile up to order `k`**: the four conditions
consumed by `StrongEps.BdryTraces_Jeps` (radial and angular, at both ends, uniform in the *other*
variable) together with the `ε`-`δ` axis condition of `StrongEps.axis_Jeps` and the sup bounds of
`SoftClass.hbdd`.  This is exactly `SoftClass`'s hypothesis list about the *source* profile. -/
structure UnifTrace (α : ℝ) (k : ℕ) (f : Fn) : Prop where
  /-- the slots are bounded on the whole open quadrant. -/
  bdd : ∀ a b : ℕ, a + b ≤ k → ∃ M : ℝ, ∀ z θ : ℝ, 0 < z →
    θ ∈ Set.Ioo 0 (Real.pi / 2) → |Work.Spaces.mixed b a f z θ| ≤ M
  /-- radial vanishing at `z → 0⁺`, uniformly in `θ`. -/
  z0 : ∀ a b : ℕ, a + b ≤ k → ∀ ε' > 0, ∃ δ > 0, ∀ z : ℝ, 0 < z → z < δ →
    ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2 ≤ ε'
  /-- radial vanishing at `z → ∞`, uniformly in `θ`. -/
  zin : ∀ a b : ℕ, a + b ≤ k → ∀ ε' > 0, ∃ Z : ℝ, ∀ z : ℝ, Z < z →
    ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2 ≤ ε'
  /-- angular vanishing at `θ → 0⁺`, uniformly in `z`. -/
  t0 : ∀ a b : ℕ, a + b ≤ k → ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, 0 < θ → θ < δ →
    ∀ z : ℝ, 0 < z →
      Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ ε'
  /-- angular vanishing at `θ → (π/2)⁻`, uniformly in `z`. -/
  t1 : ∀ a b : ℕ, a + b ≤ k → ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, θ < Real.pi / 2 →
    Real.pi / 2 - δ < θ → ∀ z : ℝ, 0 < z →
      Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ ε'
  /-- the axis condition `f = o(z)` at `z → 0⁺`, uniformly in `θ`. -/
  ax : ∀ ε' > 0, ∃ δ > 0, ∀ z : ℝ, 0 < z → z < δ →
    ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) → |f z θ / z| ≤ ε'

/-- **The uniform ANGULAR flatness alone** (the two ε-δ conditions at the θ-ends, uniform in
`z`).  This is the input that the mollifier consumes for the angular half of the traces, and — by
contrast with `UnifTrace` — it carries *no* radial condition, which is what lets the class-`C`
invariance of the local step avoid the (*hard*) radial flatness `profRHS = O(z²)`: the radial half
of `BdryTraces` is obtained from honesty through the leaf (T1). -/
structure ThetaUnif (α : ℝ) (k : ℕ) (f : Fn) : Prop where
  /-- angular vanishing at `θ → 0⁺`, uniformly in `z`. -/
  t0 : ∀ a b : ℕ, a + b ≤ k → ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, 0 < θ → θ < δ →
    ∀ z : ℝ, 0 < z →
      Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ ε'
  /-- angular vanishing at `θ → (π/2)⁻`, uniformly in `z`. -/
  t1 : ∀ a b : ℕ, a + b ≤ k → ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, θ < Real.pi / 2 →
    Real.pi / 2 - δ < θ → ∀ z : ℝ, 0 < z →
      Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ ε'


/-- The two angular ε-δ conditions give the pointwise θ-half `TauTraces` (a shared helper). -/
theorem tauTraces_of_theta {α : ℝ} {k : ℕ} {f : Fn}
    (t0 : ∀ a b : ℕ, a + b ≤ k → ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, 0 < θ → θ < δ →
      ∀ z : ℝ, 0 < z →
        Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ ε')
    (t1 : ∀ a b : ℕ, a + b ≤ k → ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, θ < Real.pi / 2 →
      Real.pi / 2 - δ < θ → ∀ z : ℝ, 0 < z →
        Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ ε') :
    TauTraces α k f := by
  intro a b hab z hz
  have hzpos : 0 < z := hz
  refine ⟨?_, ?_⟩
  · rw [Metric.tendsto_nhds]
    intro η hη
    have htol : (0 : ℝ) < min 1 (η / 2) := lt_min one_pos (by linarith)
    obtain ⟨δ, hδpos, hδ⟩ := t0 a b hab (min 1 (η / 2)) htol
    have hlt : (0 : ℝ) < min δ 1 := lt_min hδpos one_pos
    filter_upwards [Ioo_mem_nhdsGT hlt] with θ hθ
    have hθδ : θ < δ := lt_of_lt_of_le hθ.2 (min_le_left _ _)
    have hθ1 : θ < 1 := lt_of_lt_of_le hθ.2 (min_le_right _ _)
    have h1 := hδ θ hθ.1 hθδ z hzpos
    have harg : 0 ≤ 2 * θ ∧ 2 * θ ≤ Real.pi :=
      ⟨by linarith [hθ.1], by linarith [hθ1, Real.pi_gt_three]⟩
    have hs : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
      Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi harg.1 harg.2) _
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hs (sq_nonneg _))]
    linarith [le_trans h1 (min_le_right _ _)]
  · rw [Metric.tendsto_nhds]
    intro η hη
    have htol : (0 : ℝ) < min 1 (η / 2) := lt_min one_pos (by linarith)
    obtain ⟨δ, hδpos, hδ⟩ := t1 a b hab (min 1 (η / 2)) htol
    have hlt : Real.pi / 2 - min δ 1 < Real.pi / 2 := by
      have hpos : 0 < min δ 1 := lt_min hδpos one_pos
      linarith
    filter_upwards [Ioo_mem_nhdsLT hlt] with θ hθ
    have hθδ : Real.pi / 2 - δ < θ := by
      have h1 : Real.pi / 2 - δ ≤ Real.pi / 2 - min δ 1 := by
        linarith [min_le_left δ (1 : ℝ)]
      linarith [hθ.1]
    have hθu : 1 < Real.pi / 2 := by linarith [Real.pi_gt_three]
    have hθ1 : Real.pi / 2 - 1 < θ := by
      have h1 : Real.pi / 2 - 1 ≤ Real.pi / 2 - min δ 1 := by
        linarith [min_le_right δ (1 : ℝ)]
      linarith [hθ.1]
    have h1 := hδ θ hθ.2 hθδ z hzpos
    have harg : 0 ≤ 2 * θ ∧ 2 * θ ≤ Real.pi :=
      ⟨by linarith [hθ1, hθu], by linarith [hθ.2]⟩
    have hs : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
      Real.rpow_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi harg.1 harg.2) _
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hs (sq_nonneg _))]
    linarith [le_trans h1 (min_le_right _ _)]

/-- `ThetaUnif` gives the pointwise θ-half `TauTraces`. -/
theorem ThetaUnif.tauTraces {α : ℝ} {k : ℕ} {f : Fn} (h : ThetaUnif α k f) :
    TauTraces α k f := tauTraces_of_theta h.t0 h.t1

/-- **The uniform data gives the pointwise θ-half `TauTraces`.** -/
theorem UnifTrace.tauTraces {α : ℝ} {k : ℕ} {f : Fn} (h : UnifTrace α k f) :
    TauTraces α k f := tauTraces_of_theta h.t0 h.t1


end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.hmeas_slot_epsRHSP_fam_of_gate =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The difference-quotient limit step -/

/-- `((n : ℝ) + 1)⁻¹ → 0`, avoiding `0`. -/
lemma tendsto_inv_succ_nhdsNE_zero :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝[≠] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, Filter.Eventually.of_forall (fun n => ?_)⟩
  · simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  · show ((n : ℝ) + 1)⁻¹ ≠ 0
    positivity

/-- **A derivative slot is a.e. strongly measurable as soon as it is so at the limit point and at
all points of an approximating sequence, and the function is a.e. differentiable at the limit
point.**

The derivative `deriv (fun u => A s u) c` is the limit of the difference quotients
`(A s (c + d n) − A s c) / d n`, which are a.e. strongly measurable by hypothesis; the conclusion
follows from `aestronglyMeasurable_of_tendsto_ae` (`d n → 0` avoiding `0` by `hd`). -/
lemma aesm_deriv_of_increments {μ : Measure ℝ} {A : ℝ → ℝ → ℝ} {c : ℝ} {d : ℕ → ℝ}
    (hd : Tendsto d atTop (𝓝[≠] (0 : ℝ)))
    (hAn : ∀ n, AEStronglyMeasurable (fun s => A s (c + d n)) μ)
    (hAc : AEStronglyMeasurable (fun s => A s c) μ)
    (hdiff : ∀ᵐ s ∂μ, DifferentiableAt ℝ (fun u => A s u) c) :
    AEStronglyMeasurable (fun s => deriv (fun u => A s u) c) μ := by
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n s => (A s (c + d n) - A s c) * (d n)⁻¹) (fun n => ?_) ?_
  · exact ((hAn n).sub hAc).mul_const _
  · filter_upwards [hdiff] with s hs
    have hlim := (hs.hasDerivAt).tendsto_slope_zero.comp hd
    refine Tendsto.congr' (Filter.Eventually.of_forall (fun n => ?_)) hlim
    simp only [Function.comp_apply, smul_eq_mul]
    ring

/-! ## The two one-dimensional specialisations -/

/-- **The `z`-derivative slot**: if `s ↦ B s z' θ` is a.e. strongly measurable at every `z' > 0`,
and `z' ↦ B s z' θ` is a.e. differentiable at `z > 0`, then so is the derivative slot. -/
lemma aesm_deriv_z_slot_of_pointwise {μ : Measure ℝ} {B : ℝ → ℝ → ℝ → ℝ} {z θ : ℝ}
    (hz : 0 < z)
    (hB : ∀ z' : ℝ, 0 < z' → AEStronglyMeasurable (fun s => B s z' θ) μ)
    (hdiff : ∀ᵐ s ∂μ, DifferentiableAt ℝ (fun z' => B s z' θ) z) :
    AEStronglyMeasurable (fun s => deriv (fun z' => B s z' θ) z) μ :=
  aesm_deriv_of_increments (A := fun s u => B s u θ) (c := z)
    (d := fun n : ℕ => ((n : ℝ) + 1)⁻¹) tendsto_inv_succ_nhdsNE_zero
    (fun n => hB _ (by positivity)) (hB z hz) hdiff

/-- **The `θ`-derivative slot**: if `s ↦ B s z θ'` is a.e. strongly measurable at every interior
angle `θ'`, and `θ' ↦ B s z θ'` is a.e. differentiable at `θ ∈ (0,π/2)`, then so is the derivative
slot.  The approximating angles are `θ − (θ/2) / (n+1)`, which lie in the open quadrant. -/
lemma aesm_deriv_theta_slot_of_pointwise {μ : Measure ℝ} {B : ℝ → ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hB : ∀ θ' : ℝ, θ' ∈ Set.Ioo 0 (π / 2) →
      AEStronglyMeasurable (fun s => B s z θ') μ)
    (hdiff : ∀ᵐ s ∂μ, DifferentiableAt ℝ (fun θ' => B s z θ') θ) :
    AEStronglyMeasurable (fun s => deriv (fun θ' => B s z θ') θ) μ := by
  have hθ0 : 0 < θ := hθ.1
  have hθ1 : θ < π / 2 := hθ.2
  refine aesm_deriv_of_increments (A := fun s u => B s z u) (c := θ)
    (d := fun n : ℕ => -((θ / 2) * ((n : ℝ) + 1)⁻¹)) ?_ ?_ (hB θ hθ) hdiff
  · rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Filter.Eventually.of_forall (fun n => ?_)⟩
    · have h := (tendsto_inv_succ_nhdsNE_zero.mono_right nhdsWithin_le_nhds).const_mul (-(θ / 2))
      simpa using h
    · show -((θ / 2) * ((n : ℝ) + 1)⁻¹) ≠ 0
      have hn : ((n : ℝ) + 1)⁻¹ ≠ 0 := by positivity
      exact neg_ne_zero.mpr (mul_ne_zero (by linarith) hn)
  · intro n
    have hnle : ((n : ℝ) + 1)⁻¹ ≤ 1 :=
      (inv_le_one₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)).mpr (by
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith)
    have hnn : 0 ≤ (θ / 2) * ((n : ℝ) + 1)⁻¹ := by positivity
    have hmem : θ + -((θ / 2) * ((n : ℝ) + 1)⁻¹) ∈ Set.Ioo 0 (π / 2) := by
      have hb : (θ / 2) * ((n : ℝ) + 1)⁻¹ ≤ θ / 2 :=
        mul_le_of_le_one_right (by linarith) hnle
      constructor <;> linarith
    exact hB _ hmem

/-! ## Assembly: measurability of every jet from the zeroth order slots -/

/-- **Every jet is a.e. strongly measurable** as soon as each slice is `C^∞` on the open quadrant
(for `s` in the horizon) and the zeroth order slots are a.e. strongly measurable there.

The proof is the double induction on `mixed j i = D_z^j D_θ^i`: the `i`-induction uses
`aesm_deriv_theta_slot_of_pointwise` (via `D_θ = sin 2θ · ∂_θ`), the `j`-induction its
`z`-counterpart (via `D_z = z · ∂_z`), and at each step the differentiability of the intermediate
slot is `SmoothOpen` of that slot at the interior point. -/
lemma aesm_mixed_of_slicewise {B : ℝ → ℝ → ℝ → ℝ} {δ : ℝ}
    (hsm : ∀ s ∈ Set.Icc 0 δ, Work.FTS.EllipticEst.SmoothOpen (B s))
    (hB : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      AEStronglyMeasurable (fun s => B s z θ) (volume.restrict (Set.Icc 0 δ)))
    (j i : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    AEStronglyMeasurable (fun s => Work.Spaces.mixed j i (B s) z θ)
      (volume.restrict (Set.Icc 0 δ)) := by
  let μ : Measure ℝ := volume.restrict (Set.Icc 0 δ)
  have hae : ∀ᵐ s ∂μ, s ∈ Set.Icc 0 δ := ae_restrict_mem measurableSet_Icc
  have main : ∀ j : ℕ, ∀ i : ℕ, ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      AEStronglyMeasurable (fun s => Work.Spaces.mixed j i (B s) z θ) μ := by
    intro j
    induction j with
    | zero =>
      have inner : ∀ i : ℕ, ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
          AEStronglyMeasurable (fun s => Work.Spaces.DthIter i (B s) z θ) μ := by
        intro i
        induction i with
        | zero => intro z θ hz hθ; simpa using hB z θ hz hθ
        | succ i ih =>
          intro z θ hz hθ
          have h1 : AEStronglyMeasurable
              (fun s => deriv (fun θ' => Work.Spaces.DthIter i (B s) z θ') θ) μ :=
            aesm_deriv_theta_slot_of_pointwise hθ (fun θ' hθ' => ih z θ' hz hθ')
              (by
                filter_upwards [hae] with s hs
                exact (((hsm s hs).DthIter i).curry_θ hz).differentiableOn
                  Work.FTS.LocData.smoothOrder_ne_zero |>.differentiableAt
                    (isOpen_Ioo.mem_nhds hθ))
          have h2 := h1.const_mul (Real.sin (2 * θ))
          simpa only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth] using h2
      intro i z θ hz hθ
      simpa only [Work.Spaces.mixed_zero_left] using inner i z θ hz hθ
    | succ j ih =>
      intro i z θ hz hθ
      have h1 : AEStronglyMeasurable
          (fun s => deriv (fun z' => Work.Spaces.mixed j i (B s) z' θ) z) μ :=
        aesm_deriv_z_slot_of_pointwise hz (fun z' hz' => ih i z' θ hz' hθ)
          (by
            filter_upwards [hae] with s hs
            exact (((hsm s hs).mixed j i).hasDerivAt_slice hθ hz).differentiableAt)
      have h2 := h1.const_mul z
      simpa only [Work.Spaces.mixed, Work.Spaces.DzIter_succ, Work.Spaces.Dz,
        Work.Spaces.pz] using h2
  exact main j i z θ hz hθ

/-! ## The target -/

theorem hmeas_slot_epsRHSP_fam_of_gate {α C₀ R Ce Cs Lw δ : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {ε : ℝ} {g : Work.FTS.Galerkin.Fam}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hR : 0 ≤ R) (hLw : 0 ≤ Lw)
    (hP : ∀ s ∈ Set.Icc 0 δ, Work.FTS.EpsEngine.XBall α ρ ε R C₀ (Work.FTS.Galerkin.slice g s))
    (hEq : ∀ s ∈ Set.Icc 0 δ, ∀ t ∈ Set.Icc 0 δ, Work.FTS.StrongEps.EpsSq α (fun z θ =>
      Work.FTS.Galerkin.slice g s z θ - Work.FTS.Galerkin.slice g t z θ) ≤ Lw * (s - t) ^ 2)
    (j i : ℕ) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    MeasureTheory.AEStronglyMeasurable
      (fun s : ℝ => Work.Spaces.mixed j i (Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g s) z θ)
      (MeasureTheory.volume.restrict (Set.Icc 0 δ)) := by
  -- each slice is `C^∞` on the open quadrant
  have hBsm : ∀ s ∈ Set.Icc 0 δ,
      Work.FTS.EllipticEst.SmoothOpen (Feps α ρ ε Φs E (slice g s)) := fun s hs =>
    smoothOpen_Feps_of_classC (α := α) (Ce := Ce) (Cs := Cs) (ρ := ρ) (Φs := Φs) (E := E)
      (ε := ε) (u := slice g s) hα hρ hε hEll hstar (hP s hs).classC
  -- the order-zero slots are a.e. strongly measurable (the slicewise half of the parent's gate)
  have hBAe : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      MeasureTheory.AEStronglyMeasurable
        (fun s : ℝ => Feps α ρ ε Φs E (slice g s) z θ)
        (MeasureTheory.volume.restrict (Set.Icc 0 δ)) := by
    intro z θ hz hθ
    by_cases hδ : 0 ≤ δ
    · obtain ⟨C, hCpos, hpt⟩ :=
        pt_of_XBall (α := α) (C₀ := C₀) (R := R) (Ce := Ce) (Cs := Cs) (ρ := ρ)
          (Φs := Φs) (E := E) (ε := ε) hα hρ hε hε1 hEll hstar hml hR
      have hcont : ∀ w : Fn, XBall α ρ ε R C₀ w →
          ContinuousOn (fun q : ℝ × ℝ => Feps α ρ ε Φs E w q.1 q.2)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := fun w hw =>
        (continuousOn_Feps_of_XBall (α := α) (Ce := Ce) (Cs := Cs) (R := R) (C₀ := C₀)
          (ρ := ρ) (Φs := Φs) (E := E) (ε := ε) (u := w) hα hρ hε hEll hstar hw).1
      have hzero : ∀ (w : Fn) (q : ℝ × ℝ),
          q ∉ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) → Feps α ρ ε Φs E w q.1 q.2 = 0 :=
        fun w q hq => Feps_eq_zero_off_Q0 α ρ ε Φs E w q hq
      exact MeasAlt.aesm_slice_of_lipschitz_gate (F := fun u : Fn => Feps α ρ ε Φs E u)
        (V := fun s : ℝ => slice g s) (P := fun u : Fn => XBall α ρ ε R C₀ u)
        (α := α) (δ := δ) (Cpt := C) (Lb := Lw) hδ hLw hCpos.le hP hcont hzero hpt
        (fun s t hs ht => hEq s hs t ht) z θ
    · -- `δ < 0`: the horizon is empty, hence the restricted measure vanishes
      have hIcc : Set.Icc (0 : ℝ) δ = ∅ := Set.Icc_eq_empty_of_lt (lt_of_not_ge hδ)
      rw [hIcc, Measure.restrict_empty]
      exact aestronglyMeasurable_zero_measure _
  have hmain := aesm_mixed_of_slicewise (B := fun s => Feps α ρ ε Φs E (slice g s))
    hBsm hBAe j i hz hθ
  refine hmain.congr (Filter.Eventually.of_forall (fun s => ?_))
  exact congrArg (fun f : Fn => Work.Spaces.mixed j i f z θ)
    (epsRHSP_eq_Feps_slice α ρ ε Φs E g s).symm

end Work.FTS.EpsEngine
end
-- ===== merged: Submission.Work.FTS_RegExport.RXVP.velPkg_proved_noHdat =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXVP.velPkg_proved_noHdat` — RX-VP **without** the datum hypothesis

`RXVP.velPkg_proved` proves the frozen `RegExportIface.VelPkg` for the constructed family from
`hα, hα13, hEll, hEL3, hStar, hSol, hOK, hdat, hμ, hVop`.  The extra hypothesis there is the
**datum clause**

  `hdat : ∃ L β, 1 ≤ L ∧ ∀ z θ, g z θ 0 = locG6 (pExp α) L β z θ`,

i.e. the assertion that the initial datum of the family is the localized datum of the strong
route.  It is not a consequence of `hSol`/`hDynOK'` (the strong route produces solutions from
*arbitrary* admissible data, `FinalV2.Inputs'.4'`), but it is **unused by the proof**: in each of
the four RX-VP ingredients that carried it —

* `Work.FTS_RegExport.RXVP3.velPkgEasy` (the `vanishK`, `c2`, `vth_ends` clauses),
* `Work.FTS_RegExport.RXVP3.bnd_open` (the `bnd` clause),
* `Work.FTS_RegExport.RXVP3.cont_open` (the `cont` clause),
* `Work.FTS_RegExport.RXVP3.vz0_of_vopLower` (the `vz0` clause),

— the binder `hdat` does not occur anywhere in the proof term (`#print` shows the proof as a
lambda whose `hdat`-slot is invisible to the body).  Hence the same proofs establish the four
results with `hdat` deleted, and the RX-VP package follows for an *arbitrary* family satisfying
`Sol ∧ DynOK' ∧ ClockBd`.

The hdat-free ingredients are proved in `Submission/Work/FTS_RegExport/RXVP/NoHdat/`:

* `NoHdat.velPkgEasy_noHdat`, `NoHdat.cont_open_noHdat`, `NoHdat.vz0_of_vopLower_noHdat`
  (verbatim copies of the sources, minus the unused binder);
* `NoHdat.bnd_open_noHdat`;

together with the *already* hdat-free `RXT.velVanish2` (`vanish0`), `RXT.Sys.coeff_dbnd` (`dbnd`)
and `RXVP.thHol_proved` (`thHol`).  The assembly below is the exact analogue of
`RXVP3.velPkgOpen_of_vopLower` with the four hdat-free calls, glued to the frozen `VelPkg` by
`VelPkg_of_open`.
-/

noncomputable section
open scoped Real Topology NNReal
open Set Filter
open Work.FTS.Galerkin (Fn Fam slice IsDynGSolWith)
open Work.FTS.Nonlin (PsiCan)
open Work.FTS.Regularity (pExp Jet)
open Work.FTS.RegPkgGal (extG RegPkg' St1Class R5Parts Avort Bdyn)
open Work.FTS.FinalV2 (gS tauExt LimApprox DynOK' EllLimOK3 Sol)
open Work.FTS.RegExportIface

namespace Work.FTS_RegExport.RXVP

set_option autoImplicit false
set_option maxHeartbeats 800000

variable {α C₀ Ce Cs : ℝ} {Φs : Fn} {E : Fn →ₗ[ℝ] Fn} {g : Fam}



end Work.FTS_RegExport.RXVP
end
end
-- ===== merged: Submission.Work.FTS_RegExport.r1Block.regExport_hVop =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.r1Block

noncomputable section

open scoped Topology Real
open Set Filter

/-- The clock function of the sanitised family — the `m` of `RegExportIface.GalMin'`. -/
abbrev MM (α : ℝ) (Φs : Work.FTS.Galerkin.Fn)
    (E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn) (g : Work.FTS.Galerkin.Fam) : ℝ → ℝ :=
  Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α) (Work.FTS.Nonlin.PsiCan Φs E g) g

theorem regExport_hVop {α C₀ Ce Cs : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) u →
      Work.FTS.Final.EllPkgGo (Work.FTS.Regularity.pExp α) Ce u (E u) ∧
        Work.FTS.ClassC.EllPkgK (Work.FTS.Regularity.pExp α) 6 Ce u (E u))
    (hEL3 : Work.FTS.FinalV2.EllLimOK3 (Work.FTS.Regularity.pExp α) E)
    (hStar : Work.FTS.Final.StarPkgo2 (Work.FTS.Regularity.pExp α) Cs Φs)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hdat : ∃ L β : ℝ, 1 ≤ L ∧ ∀ z θ, g z θ 0 =
      Work.FTS.LocData6.locG6 (Work.FTS.Regularity.pExp α) L β z θ)
    (hclock : (∀ τ : ℝ, 0 ≤ τ →
        |Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α) (Work.FTS.Nonlin.PsiCan Φs E g) g τ|
          ≤ 1 / 2) ∧
      ContinuousOn (Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
        (Work.FTS.Nonlin.PsiCan Φs E g) g) (Set.Ici 0) ∧
      (∀ S : ℝ, 0 < S → ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ τ' ∈ Set.Icc (0 : ℝ) S,
        |Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
            (Work.FTS.Nonlin.PsiCan Φs E g) g τ
          - Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
            (Work.FTS.Nonlin.PsiCan Φs E g) g τ'| ≤ L * |τ - τ'| ^ α))
    (hVop : ∀ z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 ≤ τ →
      -(1 - Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α)
            (Work.FTS.Nonlin.PsiCan Φs E g) g τ)
        ≤ 2 * Work.FTS.Regularity.pExp α *
          Work.Construction.Vop (Work.FTS.Galerkin.slice
            (Work.FTS.RegExportIface.psiR α Φs E (Work.FTS.FinalV2.tauExt g)) τ) z θ) :
    ∀ S > 0, Work.FTS.RegPkgGal.RegPkg' α S
      (Work.FTS.RegPkgGal.Avort (Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α)
        (Work.FTS.Nonlin.PsiCan Φs E g) g))
      (Work.FTS.RegPkgGal.Bdyn (Work.FTS.Final.maxMu (Work.FTS.Regularity.pExp α)
        (Work.FTS.Nonlin.PsiCan Φs E g) g))
      (Work.FTS.RegPkgGal.extG (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))) := by
  -- ## the three derived hypotheses of the assembly
  have hμ : Work.FTS.RegExportIface.ClockBd α Φs E g :=
    Work.FTS.RegExportIface.ClockBd.of_clock hclock
  have hVP : ∀ S > 0, Work.FTS.RegExportIface.VelPkg (Work.FTS.Regularity.pExp α)
      (MM α Φs E g) (Work.FTS_RegExport.RXR5.SG α g)
      (Work.FTS_RegExport.RXR5.SΨ α Φs E g) S := fun S hS =>
    Work.FTS_RegExport.RXVP.velPkg_proved (Φs := Φs) (E := E) (g := g)
      hα hα13 hEll hEL3 hStar hSol hOK hdat hμ hVop S hS
  have hSt1 : ∀ S > 0, Work.FTS.RegPkgGal.St1Class α S (Work.FTS_RegExport.RXR5.SG α g) :=
    fun S hS => Work.FTS_RegExport.st1Export_proved (Φs := Φs) (E := E) (g := g)
      hα hα13 hEll hEL3 hStar hSol hOK hdat hμ S hS
  have H5 : ∀ S > 0, Work.FTS.RegPkgGal.R5Parts α S (Work.FTS_RegExport.RXR5.SG α g)
      (Work.FTS_RegExport.RXR5.SΨ α Φs E g) := fun S hS =>
    Work.FTS_RegExport.RXR5.r5Parts_hVP (Φs := Φs) (E := E) (g := g)
      hα hα13 hEll hEL3 hStar hSol hOK hSt1 hdat hμ hVP S hS
  -- ## the two blocks
  obtain ⟨a, b, c, Lz7, hR7⟩ := Work.FTS_RegExport.RXR7.r7Block_proved
    (Φs := Φs) (E := E) (g := g) hα hα13 hSol hOK hdat hμ hVP
  have hR1 : ∀ S > 0, Work.FTS.RegExportIface.R1Block α S (Work.FTS_RegExport.RXR5.SG α g) :=
    Work.FTS_RegExport.RXR1.r1Block_proved (Φs := Φs) (E := E) (g := g)
      hα hα13 hSol hOK hdat hSt1 H5
  -- ## the assembly: the `GalMin'` bundle for every horizon
  refine Work.FTS_RegExport.RX0.forallRegPkgOfParts (g := Work.FTS_RegExport.RXR5.SG α g)
    (Φ := Work.FTS_RegExport.RXR5.SΨ α Φs E g) (m := MM α Φs E g)
    (Vz := Work.FTS.RegExportIface.edgeExt (Work.FTS.RegExportIface.Vz7
      (Work.FTS.Regularity.pExp α) (MM α Φs E g) (Work.FTS_RegExport.RXR5.SG α g)
      (Work.FTS_RegExport.RXR5.SΨ α Φs E g)))
    (Vθ := Work.FTS.RegExportIface.Vθ7 (Work.FTS.Regularity.pExp α)
      (Work.FTS_RegExport.RXR5.SΨ α Φs E g))
    (cs := Work.FTS.RegExportIface.edgeExt (Work.FTS.RegExportIface.cs7
      (Work.FTS.Regularity.pExp α) (MM α Φs E g) (Work.FTS_RegExport.RXR5.SG α g)
      (Work.FTS_RegExport.RXR5.SΨ α Φs E g)))
    (a := a) (b := b) (c := c) ?_ H5
  intro S hS
  refine ⟨Lz7, ?_⟩
  -- the regularity package of the raw family, read on the quadrant
  have hreg : Work.FTS.StrongGlobal.RegPkgMin (Work.FTS.Regularity.pExp α) g := hOK.1.1
  have hC₀nn : (0 : ℝ) ≤ C₀ * (Work.FTS.Regularity.pExp α) ^ 2 :=
    le_trans (Real.sqrt_nonneg (Work.Spaces.HkSq (Work.FTS.Regularity.pExp α) 4
      (Work.FTS.Galerkin.slice g 0))) (hOK.1.Xn_le 0 le_rfl)
  -- ## the `RegPkgMin` of the sanitised family
  have hmin : Work.FTS.RegPkgGal.RegPkgMin (Work.FTS.Regularity.pExp α)
      (Work.FTS_RegExport.RXR5.SG α g) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- joint `C¹`
      refine hreg.c1.congr ?_
      rintro ⟨z, θ, τ⟩ ⟨hz, hθ, hτ⟩
      show Work.FTS_RegExport.RXR5.SG α g z θ τ = g z θ τ
      rw [Work.FTS_RegExport.RXR5.SG_apply_of_pos hz hθ.1.le hθ.2.le,
        Work.FTS.FinalV2.tauExt_of_nonneg g hτ.le]
    · -- `C⁴` in space
      intro τ hτ
      refine (hreg.c4 τ hτ).congr ?_
      rintro ⟨z, θ⟩ ⟨hz, hθ⟩
      show Work.FTS_RegExport.RXR5.SG α g z θ τ = g z θ τ
      rw [Work.FTS_RegExport.RXR5.SG_apply_of_pos hz hθ.1.le hθ.2.le,
        Work.FTS.FinalV2.tauExt_of_nonneg g hτ]
    · -- continuity in fake time
      intro z θ hzθ
      refine (hreg.cont z θ hzθ).congr ?_
      intro τ hτ
      show Work.FTS_RegExport.RXR5.SG α g z θ τ = g z θ τ
      rw [Work.FTS_RegExport.RXR5.SG_apply_of_pos hzθ.1 hzθ.2.1.le hzθ.2.2.le,
        Work.FTS.FinalV2.tauExt_of_nonneg g hτ]
    · -- `ℋ⁴`-membership of the slices
      intro τ hτ
      refine Work.Coercivity.HkMem_congr_of_eqOn_Ioi (Work.FTS.Regularity.pExp α) 4
        (u := Work.FTS.Galerkin.slice (Work.FTS.FinalV2.tauExt g) τ) ?_ ?_
      · rw [Work.FTS.FinalV2.slice_tauExt g hτ]
        exact hreg.mem4 τ hτ
      · intro z hz θ hθ
        show Work.FTS.FinalV2.tauExt g z θ τ = Work.FTS_RegExport.RXR5.SG α g z θ τ
        rw [Work.FTS_RegExport.RXR5.SG_apply_of_pos hz hθ.1 hθ.2]
    · -- the `ℋ³`-bound on `∂_τ`
      intro T hT
      obtain ⟨Cd, hCd⟩ := hreg.dbd T hT
      refine ⟨Cd, fun τ hτ hτT => ⟨?_, ?_⟩⟩
      · have hmem : Work.Spaces.HkMem (Work.FTS.Regularity.pExp α) 3
            (Work.FTS.Galerkin.gdot (Work.FTS.FinalV2.tauExt g) τ) := by
          rw [Work.FTS.FinalV2.gdot_tauExt hτ]
          exact (hCd τ hτ hτT).1
        refine Work.Coercivity.HkMem_congr_of_eqOn_Ioi (Work.FTS.Regularity.pExp α) 3 hmem ?_
        intro z hz θ hθ
        show Work.FTS.Galerkin.gdot (Work.FTS.FinalV2.tauExt g) τ z θ
            = Work.FTS.Galerkin.gdot (Work.FTS_RegExport.RXR5.SG α g) τ z θ
        simp only [Work.FTS.Galerkin.gdot]
        rw [show (fun s => Work.FTS_RegExport.RXR5.SG α g z θ s)
              = fun s => Work.FTS.FinalV2.tauExt g z θ s from
            funext fun s => Work.FTS_RegExport.RXR5.SG_apply_of_pos hz hθ.1 hθ.2]
      · have hnorm : Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 3
            (Work.FTS.Galerkin.gdot (Work.FTS_RegExport.RXR5.SG α g) τ)
            = Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 3
              (Work.FTS.Galerkin.gdot (Work.FTS.FinalV2.tauExt g) τ) := by
          show Real.sqrt (Work.Spaces.HkSq (Work.FTS.Regularity.pExp α) 3
              (Work.FTS.Galerkin.gdot (Work.FTS_RegExport.RXR5.SG α g) τ))
            = Real.sqrt (Work.Spaces.HkSq (Work.FTS.Regularity.pExp α) 3
              (Work.FTS.Galerkin.gdot (Work.FTS.FinalV2.tauExt g) τ))
          congr 1
          exact Work.FTS.EllipticEst.HkSq_congr_open (Work.FTS.Regularity.pExp α) 3
            (fun z θ hz hθ hθ2 => by
              show Work.FTS.Galerkin.gdot (Work.FTS_RegExport.RXR5.SG α g) τ z θ
                  = Work.FTS.Galerkin.gdot (Work.FTS.FinalV2.tauExt g) τ z θ
              simp only [Work.FTS.Galerkin.gdot]
              rw [show (fun s => Work.FTS_RegExport.RXR5.SG α g z θ s)
                    = fun s => Work.FTS.FinalV2.tauExt g z θ s from
                  funext fun s => Work.FTS_RegExport.RXR5.SG_apply_of_pos hz hθ.le hθ2.le])
        rw [hnorm, Work.FTS.FinalV2.gdot_tauExt hτ]
        exact (hCd τ hτ hτT).2
    · -- the angular vanishing
      intro τ hτ z hz
      by_cases hz0 : 0 < z
      · have h0 := hreg.vanish τ hτ z hz0.le
        refine ⟨?_, ?_⟩
        · rw [Work.FTS_RegExport.RXR5.SG_apply_of_pos hz0 (le_refl (0 : ℝ))
              (by linarith [Real.pi_pos]), Work.FTS.FinalV2.tauExt_of_nonneg g hτ]
          exact h0.1
        · rw [Work.FTS_RegExport.RXR5.SG_apply_of_pos hz0 (by linarith [Real.pi_pos])
              (le_refl (Real.pi / 2)), Work.FTS.FinalV2.tauExt_of_nonneg g hτ]
          exact h0.2
      · have hz' : z ≤ 0 := le_of_not_gt hz0
        exact ⟨Work.FTS_RegExport.RXR5.SG_apply_of_nonpos (α := α) (g := g) hz',
          Work.FTS_RegExport.RXR5.SG_apply_of_nonpos (α := α) (g := g) hz'⟩
  -- ## the clock fields, for `M = maxMu …`
  have hm : ContinuousOn (MM α Φs E g) (Set.Ioo (-1 : ℝ) (S + 1)) := by
    have hmax : ContinuousOn (fun s : ℝ => max s 0) (Set.Ioo (-1 : ℝ) (S + 1)) :=
      (continuous_id.max continuous_const).continuousOn
    have hcomp := hclock.2.1.comp hmax (fun s _ => le_max_right s 0)
    show ContinuousOn (fun s : ℝ => Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
      (Work.FTS.Nonlin.PsiCan Φs E g) g (max s 0)) (Set.Ioo (-1 : ℝ) (S + 1))
    exact hcomp
  have hmb : ∀ τ : ℝ, τ ∈ Set.Ioo (-1 : ℝ) (S + 1) → |MM α Φs E g τ| ≤ 1 / 2 := by
    intro τ hτ
    show |Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
      (Work.FTS.Nonlin.PsiCan Φs E g) g (max τ 0)| ≤ 1 / 2
    exact hclock.1 (max τ 0) (le_max_right τ 0)
  have hmh : ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ τ' ∈ Set.Icc (0 : ℝ) S,
      |MM α Φs E g τ - MM α Φs E g τ'| ≤ L * |τ - τ'| ^ α := by
    obtain ⟨L, hL0, hL⟩ := hclock.2.2 S hS
    refine ⟨L, hL0, fun τ hτ τ' hτ' => ?_⟩
    have e1 : MM α Φs E g τ = Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
        (Work.FTS.Nonlin.PsiCan Φs E g) g τ := by
      show Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
        (Work.FTS.Nonlin.PsiCan Φs E g) g (max τ 0) = _
      rw [max_eq_left hτ.1]
    have e2 : MM α Φs E g τ' = Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
        (Work.FTS.Nonlin.PsiCan Φs E g) g τ' := by
      show Work.FTS.Galerkin.muDyn (Work.FTS.Regularity.pExp α)
        (Work.FTS.Nonlin.PsiCan Φs E g) g (max τ' 0) = _
      rw [max_eq_left hτ'.1]
    simpa only [e1, e2] using hL τ hτ τ' hτ'
  -- ## the interior sup bound `hIS`
  have hIS : ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Set.Icc (0 : ℝ) S, ∀ b a : ℕ, a + b ≤ 2 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        |Work.Spaces.mixed b a (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SG α g) τ)
          z θ| ≤ M := by
    obtain ⟨Lm, hLm0, hLm⟩ := Work.FTS_RegExport.RXA2.lim_mixed_bounds_proved
      (αG := Work.FTS.Regularity.pExp α) (C₀ := C₀) (g := g)
      (Work.FTS.Regularity.pExp_pos hα) (Work.FTS.Regularity.pExp_le_one hα13) hOK.2 S hS
    refine ⟨10 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1)
      * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2), ?_, ?_⟩
    · exact mul_nonneg (div_nonneg (by norm_num) (Real.sqrt_nonneg _)) hC₀nn
    · intro τ hτ b a hab z θ hz hθ hθ2
      have hb := (hLm τ hτ τ hτ b a hab z θ hz hθ hθ2).1
      have hEQ : Set.EqOn (Function.uncurry
            (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SG α g) τ))
          (Function.uncurry (Work.FTS.Galerkin.slice g τ)) Work.FTS.EllipticEst.Q0 := by
        rintro ⟨z', θ'⟩ ⟨hz', hθ'0, hθ'1⟩
        show Work.FTS_RegExport.RXR5.SG α g z' θ' τ = g z' θ' τ
        rw [Work.FTS_RegExport.RXR5.SG_apply_of_pos hz' hθ'0.le hθ'1.le,
          Work.FTS.FinalV2.tauExt_of_nonneg g hτ.1]
      have hcongr : Work.Spaces.mixed b a
            (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SG α g) τ) z θ
          = Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ) z θ := by
        have h := Work.FTS.RegPkgGal.mixed_congr_of_isOpen (V := Work.FTS.EllipticEst.Q0)
          (isOpen_Ioi.prod isOpen_Ioo) hEQ b a
          (show (z, θ) ∈ Work.FTS.EllipticEst.Q0 from ⟨hz, hθ, hθ2⟩)
        simpa only [Function.uncurry] using h
      rw [hcongr]
      exact hb
  -- ## the uniform `ℋ⁴` bound `hHkn`
  have hHkn : ∃ C₀' : ℝ, 0 ≤ C₀' ∧ ∀ τ ∈ Set.Icc (0 : ℝ) S,
      Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4
        (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SG α g) τ) ≤ C₀' := by
    refine ⟨C₀ * (Work.FTS.Regularity.pExp α) ^ 2, hC₀nn, fun τ hτ => ?_⟩
    have h1 : Work.Spaces.HkSq (Work.FTS.Regularity.pExp α) 4
          (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SG α g) τ)
        = Work.Spaces.HkSq (Work.FTS.Regularity.pExp α) 4
          (Work.FTS.Regularity.gSlice (Work.FTS.FinalV2.tauExt g) τ) :=
      Work.FTS.EllipticEst.HkSq_congr_open (Work.FTS.Regularity.pExp α) 4
        (fun z θ hz hθ hθ2 => by
          show Work.FTS_RegExport.RXR5.SG α g z θ τ = Work.FTS.FinalV2.tauExt g z θ τ
          exact Work.FTS_RegExport.RXR5.SG_apply_of_pos hz hθ.le hθ2.le)
    have h2 : Work.FTS.Regularity.gSlice (Work.FTS.FinalV2.tauExt g) τ
        = Work.FTS.Regularity.gSlice g τ := by
      funext z θ
      exact Work.FTS.FinalV2.tauExt_of_nonneg g hτ.1
    show Real.sqrt (Work.Spaces.HkSq (Work.FTS.Regularity.pExp α) 4
      (Work.FTS.Regularity.gSlice (Work.FTS_RegExport.RXR5.SG α g) τ))
      ≤ C₀ * (Work.FTS.Regularity.pExp α) ^ 2
    rw [h1, h2]
    exact hOK.1.Xn_le τ hτ.1
  -- ## the bundle
  exact
    { toR1Block := hR1 S hS
      toR7Block := hR7 S hS
      hα := hα
      hα13 := hα13
      hS := hS
      hmin := hmin
      hm := hm
      hmb := hmb
      hmh := hmh
      hSt1 := hSt1 S hS
      hIS := hIS
      hHkn := hHkn
      hsuppOut := Work.FTS.FinalV2.hsuppOut_gS α S (Work.FTS.FinalV2.tauExt g) }

end

end Work.FTS_RegExport.r1Block
end
