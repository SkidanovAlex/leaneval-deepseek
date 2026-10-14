import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.StrongEps.EpsE4Thr.Leaves.FlowBits.hkSqFepsSub_le
import Submission.Work.FTS_RegExport.r1Block.regExport_hVop
-- ===== merged: Submission.Work.FTS.EpsEngine.epsC_tendsto_and_limIdent =====
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

set_option linter.unusedVariables false

theorem epsC_tendsto_and_limIdent {α C₀ R Ce Cs Lw q : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {ε : ℝ}
    {h₀ : Work.FTS.Galerkin.Fn} {δ : ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε)
    (hmoll : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z →
      θ ∈ Set.Ioo 0 (π / 2) →
      Work.FTS.Galerkin.slice (Work.FTS.EpsEngine.epsIter α ρ ε Φs E h₀ (n + 1)) s z θ
        = h₀ z θ + Work.FTS.StrongEps.Jeps ρ ε
            (Work.FTS.EpsEngine.epsPsi α ρ ε Φs E h₀ n s) z θ
          - Work.FTS.EpsEngine.epsC α ρ ε Φs E h₀ n s
            * Work.FTS.StrongEps.bump z θ)
    (hconv : ∀ (s : ℝ), s ∈ Set.Icc 0 δ → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      Filter.Tendsto (fun N : ℕ =>
          Work.FTS.Galerkin.slice (Work.FTS.EpsEngine.epsIter α ρ ε Φs E h₀ N) s z θ)
        Filter.atTop
        (nhds (Work.FTS.Galerkin.slice (Work.FTS.EpsEngine.epsLim α ρ ε Φs E h₀) s z θ)))
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 δ) {PsiL : Work.FTS.Galerkin.Fn}
    (hJeps : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Filter.Tendsto (fun n : ℕ => Work.FTS.StrongEps.Jeps ρ ε
          (Work.FTS.EpsEngine.epsPsi α ρ ε Φs E h₀ n τ) z θ)
        Filter.atTop (nhds (Work.FTS.StrongEps.Jeps ρ ε PsiL z θ))) :
    ∃ cLim : ℝ, Filter.Tendsto (fun n : ℕ => Work.FTS.EpsEngine.epsC α ρ ε Φs E h₀ n τ)
        Filter.atTop (nhds cLim) ∧
      ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
        Work.FTS.Galerkin.slice (Work.FTS.EpsEngine.epsLim α ρ ε Φs E h₀) τ z θ
          = h₀ z θ + Work.FTS.StrongEps.Jeps ρ ε PsiL z θ - cLim * Work.FTS.StrongEps.bump z θ := by
  -- the point where the projection bump does not vanish
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
  -- the limit coefficient, read off the mollified form at `(3/4, 5π/16)`
  set cLim : ℝ := (h₀ ((3 : ℝ) / 4) (5 * Real.pi / 16)
      + Jeps ρ ε PsiL ((3 : ℝ) / 4) (5 * Real.pi / 16)
      - slice (epsLim α ρ ε Φs E h₀) τ ((3 : ℝ) / 4) (5 * Real.pi / 16))
      / bump ((3 : ℝ) / 4) (5 * Real.pi / 16) with hcLimdef
  have hClim : Filter.Tendsto (fun n : ℕ => epsC α ρ ε Φs E h₀ n τ) Filter.atTop
      (nhds cLim) := by
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
    have hnum : Filter.Tendsto (fun n : ℕ => h₀ ((3 : ℝ) / 4) (5 * Real.pi / 16)
        + Jeps ρ ε (epsPsi α ρ ε Φs E h₀ n τ) ((3 : ℝ) / 4) (5 * Real.pi / 16)
        - slice (epsIter α ρ ε Φs E h₀ (n + 1)) τ ((3 : ℝ) / 4) (5 * Real.pi / 16)) Filter.atTop
        (nhds (h₀ ((3 : ℝ) / 4) (5 * Real.pi / 16)
          + Jeps ρ ε PsiL ((3 : ℝ) / 4) (5 * Real.pi / 16)
          - slice (epsLim α ρ ε Φs E h₀) τ ((3 : ℝ) / 4) (5 * Real.pi / 16))) := by
      refine (tendsto_const_nhds.add (hJeps _ _ hyz hyθ)).sub ?_
      exact ((hconv τ hτ ((3 : ℝ) / 4) (5 * Real.pi / 16) hyz hyθ.1 hyθ.2).comp
        (tendsto_add_atTop_nat 1))
    have hdiv := hnum.div_const (bump ((3 : ℝ) / 4) (5 * Real.pi / 16))
    rw [hcLimdef]
    refine (Filter.Tendsto.congr' ?_ hdiv)
    exact Eventually.of_forall fun n => (hcongr n).symm
  refine ⟨cLim, hClim, ?_⟩
  -- the identity at every point of the open quadrant, by uniqueness of limits
  intro z θ hz hθ
  have hL : Filter.Tendsto (fun n : ℕ => slice (epsIter α ρ ε Φs E h₀ (n + 1)) τ z θ)
      Filter.atTop (nhds (slice (epsLim α ρ ε Φs E h₀) τ z θ)) :=
    (hconv τ hτ z θ hz hθ.1 hθ.2).comp (tendsto_add_atTop_nat 1)
  have hR : Filter.Tendsto (fun n : ℕ => h₀ z θ + Jeps ρ ε (epsPsi α ρ ε Φs E h₀ n τ) z θ
      - epsC α ρ ε Φs E h₀ n τ * bump z θ) Filter.atTop
      (nhds (h₀ z θ + Jeps ρ ε PsiL z θ - cLim * bump z θ)) :=
    ((tendsto_const_nhds.add (hJeps z θ hz hθ)).sub (hClim.mul_const (bump z θ)))
  have heq : (fun n : ℕ => slice (epsIter α ρ ε Φs E h₀ (n + 1)) τ z θ)
      =ᶠ[Filter.atTop] (fun n : ℕ => h₀ z θ + Jeps ρ ε (epsPsi α ρ ε Φs E h₀ n τ) z θ
        - epsC α ρ ε Φs E h₀ n τ * bump z θ) :=
    Eventually.of_forall fun n => hmoll n τ hτ z θ hz hθ
  exact tendsto_nhds_unique hL ((Filter.tendsto_congr' heq).mpr hR)

end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.EpsEngine.exists_epsPsi_limit =====
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

set_option linter.unusedVariables false

theorem exists_epsPsi_limit {α C₀ R Ce Cs Lw δ q : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {ε : ℝ}
    {h₀ : Work.FTS.Galerkin.Fn}
    (hα : α ∈ Set.Ioc 0 1) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hml : Work.FTS.StrongEps.MuLamOK α C₀ Φs E) (hR : 0 ≤ R) (hLw : 0 ≤ Lw)
    (h0 : Work.FTS.EllipticEst.SmoothOpen h₀) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hP : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ →
      Work.FTS.EpsEngine.XBall α ρ ε R C₀
        (Work.FTS.Galerkin.slice (Work.FTS.EpsEngine.epsIter α ρ ε Φs E h₀ n) s))
    (hEq : ∀ (n : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → ∀ t : ℝ, t ∈ Set.Icc 0 δ →
      Work.FTS.StrongEps.EpsSq α (fun z θ =>
        Work.FTS.Galerkin.slice (Work.FTS.EpsEngine.epsIter α ρ ε Φs E h₀ n) s z θ
          - Work.FTS.Galerkin.slice (Work.FTS.EpsEngine.epsIter α ρ ε Φs E h₀ n) t z θ)
        ≤ Lw * (s - t) ^ 2)
    (hpair : ∀ (n m : ℕ) (s : ℝ), s ∈ Set.Icc 0 δ → n ≤ m →
      Work.FTS.StrongEps.EpsSq α (fun z θ =>
        Work.FTS.Galerkin.slice (Work.FTS.EpsEngine.epsIter α ρ ε Φs E h₀ n) s z θ
          - Work.FTS.Galerkin.slice (Work.FTS.EpsEngine.epsIter α ρ ε Φs E h₀ m) s z θ)
        ≤ q ^ n)
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 δ) :
    ∃ (C r : ℝ) (PsiL : Work.FTS.Galerkin.Fn), 0 ≤ C ∧ 0 ≤ r ∧ r < 1 ∧
      Continuous (Work.FTS.StrongEps.logPull PsiL) ∧
      (∀ n : ℕ, Continuous (Work.FTS.StrongEps.logPull
        (Work.FTS.EpsEngine.epsPsi α ρ ε Φs E h₀ n τ))) ∧
      (∀ (n : ℕ) (z θ : ℝ), 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |Work.FTS.EpsEngine.epsPsi α ρ ε Φs E h₀ n τ z θ - PsiL z θ| ≤ C * r ^ n) ∧
      (∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
        Filter.Tendsto (fun n : ℕ => Work.FTS.EpsEngine.epsPsi α ρ ε Φs E h₀ n τ z θ)
          Filter.atTop (nhds (PsiL z θ))) := by
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
  have hcontPsiL : Continuous (logPull PsiL) := by
    have hTU : TendstoUniformly (fun n : ℕ => logPull (epsPsi α ρ ε Φs E h₀ n τ))
        (logPull PsiL) atTop := by
      rw [Metric.tendstoUniformly_iff]
      intro ε hε
      have hbgeo : Tendsto (fun n : ℕ => (τ * C) * r ^ n) atTop (𝓝 0) := by
        have h := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
        simpa using h.const_mul (τ * C)
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hbgeo.eventually (Iio_mem_nhds hε))
      filter_upwards [Filter.eventually_ge_atTop N] with n hn x
      have hz : 0 < Real.exp x.1 := Real.exp_pos x.1
      have hθ : Real.arctan (Real.exp x.2) ∈ Set.Ioo 0 (π / 2) :=
        ⟨(Real.arctan_pos).mpr (Real.exp_pos x.2), Real.arctan_lt_pi_div_two _⟩
      rw [Real.dist_eq, abs_sub_comm]
      exact lt_of_le_of_lt (hPsiUniform n _ _ hz hθ) (hN n hn)
    exact hTU.continuous (Filter.frequently_atTop.2 fun n => ⟨n, le_refl n, hcontPsiLog n⟩)
  refine ⟨τ * C, r, PsiL, mul_nonneg hτ.1 hCnn, hr0, hr1, hcontPsiL, hcontPsiLog, ?_, ?_⟩
  · intro n z θ hz hθ
    exact hPsiUniform n z θ hz hθ
  · intro z θ hz hθ
    exact hPsiL z θ ⟨hz, hθ⟩

end Work.FTS.EpsEngine
end
end
