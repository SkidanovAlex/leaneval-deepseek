/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/LimSmoothOpen.lean`

**The `SmoothOpen` clause of `hlimP`**: the limit family of the Picard iteration of the projected
`ε`-scheme has `C^∞` slices on the open quadrant.

The route is the lead's ruling (`../EpsEngine/NOTES_LocalStep.md`, addendum 2): every Picard iterate
satisfies the *mollified identity*

    u_{n+1} = h₀ + J_ε (Ψ_n) − c_n · bump       on the open quadrant,

with `Ψ_n = ∫₀^τ profRHS(W_uₙ) ds`; passing to the limit in `n` only requires

* `Ψ_n` uniformly Cauchy — the pointwise Lipschitz bound (`profRHS_pre_sub_pt_le_Sq`) of the
  pre-mollified right-hand side along the iterates plus the geometric pair bound of `iter_bounds_v4`;
* `J_ε` continuous in the profile for the `logPull`-uniform distance (`abs_Jeps_sub_le_of_logPull_le`).

The limit is then in the same mollified form, so the lead's `smoothOpen_of_mollForm` applies
directly.  In particular **no class data of the limit profile is needed** (which is what makes the
argument non-circular).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.FTS.EpsEngine.SmoothOpenIterProd
import Submission.Work.FTS.StrongEps.Jker_integral_eq_one

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
