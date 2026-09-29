import Mathlib
import Submission.Work.Holonomy3.jensen_mean_ineq
import Submission.Work.Holonomy3.smoothed_jensen
import Submission.Work.Holonomy3.pi_integral_cons
import Submission.Work.Holonomy3.le_integral_log_of_smoothed

/-!
# The polydisc logarithmic mean-value inequality

For `H : (Fin d → ℂ) → ℂ` holomorphic on the polydisc of radius `ρ > 1` with `H 0 ≠ 0`, the
logarithmic mean-value inequality holds:

`Real.log ‖H 0‖ ≤ ∫ t, Real.log ‖H (exp (2πi t_j))_j‖`.

The proof first establishes the *smoothed* inequality (with `ε > 0` added inside every logarithm) by
iterating the one-variable smoothed Jensen inequality over the coordinates together with Fubini, and
then passes to the limit `ε → 0` with a monotone-convergence argument
(`Work.Holonomy3.le_integral_log_of_smoothed`).
-/

namespace Work.Holonomy3

open MeasureTheory Filter Topology
open scoped Real

noncomputable section

/-- The unit-circle parametrisation `t ↦ exp (2 π i t)`. -/
def circlePt (t : ℝ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))

/-- The unit-polytorus parametrisation `t ↦ (exp (2 π i t_j))_j`. -/
def torusPt {d : ℕ} (t : Fin d → ℝ) : Fin d → ℂ := fun j => circlePt (t j)

@[simp] lemma norm_circlePt (t : ℝ) : ‖circlePt t‖ = 1 := by
  have h : circlePt t = Complex.exp (((2 * Real.pi * t : ℝ)) * Complex.I) := by
    rw [circlePt]
    push_cast
    ring_nf
  rw [h, Complex.norm_exp_ofReal_mul_I]

@[simp] lemma norm_torusPt_apply {d : ℕ} (t : Fin d → ℝ) (j : Fin d) : ‖torusPt t j‖ = 1 := by
  simp [torusPt]

lemma continuous_circlePt : Continuous circlePt := by
  unfold circlePt
  fun_prop

lemma continuous_torusPt {d : ℕ} : Continuous (torusPt : (Fin d → ℝ) → (Fin d → ℂ)) := by
  unfold torusPt
  exact continuous_pi (fun j => continuous_circlePt.comp (continuous_apply j))

lemma continuous_finCons {d : ℕ} :
    Continuous (fun p : ℝ × (Fin d → ℝ) => (Fin.cons p.1 p.2 : Fin (d+1) → ℝ)) := by
  apply continuous_pi
  intro j
  cases j using Fin.cases with
  | zero =>
      simpa [Fin.cons_zero] using (continuous_fst : Continuous (fun p : ℝ × (Fin d → ℝ) => p.1))
  | succ i =>
      simpa only [Function.comp_def, Fin.cons_succ] using
        ((continuous_apply i).comp continuous_snd :
          Continuous (fun p : ℝ × (Fin d → ℝ) => p.2 i))

lemma torusPt_cons {d : ℕ} (s : ℝ) (t : Fin d → ℝ) :
    torusPt (Fin.cons s t) = Fin.cons (circlePt s) (torusPt t) := by
  funext j
  cases j using Fin.cases <;> simp [torusPt]

/-- `H` is continuous on the closed unit polydisc. -/
lemma continuousOn_unitPolydisc {d : ℕ} {H : (Fin d → ℂ) → ℂ} {ρ : ℝ} (hρ : 1 < ρ)
    (hHol : ∀ z : Fin d → ℂ, (∀ j, ‖z j‖ ≤ ρ) → DifferentiableAt ℂ H z) :
    ContinuousOn H {z : Fin d → ℂ | ∀ j, ‖z j‖ ≤ 1} := fun z hz =>
  ((hHol z (fun j => le_trans (hz j) hρ.le)).continuousAt).continuousWithinAt

/-- A uniform bound for `‖H‖` on the closed unit polydisc. -/
lemma exists_norm_bound {d : ℕ} {H : (Fin d → ℂ) → ℂ} {ρ : ℝ} (hρ : 1 < ρ)
    (hHol : ∀ z : Fin d → ℂ, (∀ j, ‖z j‖ ≤ ρ) → DifferentiableAt ℂ H z) :
    ∃ M : ℝ, ∀ z : Fin d → ℂ, (∀ j, ‖z j‖ ≤ 1) → ‖H z‖ ≤ M := by
  have hcontH := continuousOn_unitPolydisc hρ hHol
  have hK : IsCompact {z : Fin d → ℂ | ∀ j, ‖z j‖ ≤ 1} := by
    have hset : {z : Fin d → ℂ | ∀ j, ‖z j‖ ≤ 1}
        = Set.pi Set.univ (fun _ : Fin d => Metric.closedBall (0 : ℂ) 1) := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies,
        Metric.mem_closedBall, dist_zero_right]
    rw [hset]
    exact isCompact_univ_pi (fun _ => isCompact_closedBall (0 : ℂ) 1)
  obtain ⟨z₀, -, hmax⟩ := hK.exists_isMaxOn ⟨0, by simp⟩ hcontH.norm
  exact ⟨‖H z₀‖, fun z hz => hmax hz⟩

theorem polydisc_log_mean_smoothed (d : ℕ) :
    ∀ (H : (Fin d → ℂ) → ℂ) (ρ : ℝ), 1 < ρ →
      (∀ z : Fin d → ℂ, (∀ j, ‖z j‖ ≤ ρ) → DifferentiableAt ℂ H z) →
      ∀ ε : ℝ, 0 < ε →
      Real.log (‖H 0‖ + ε) ≤
        ∫ t : Fin d → ℝ, Real.log (‖H (torusPt t)‖ + ε)
          ∂(Measure.pi (fun _ : Fin d => volume.restrict (Set.Icc (0:ℝ) 1))) := by
  induction d with
  | zero =>
    intro H ρ hρ hHol ε hε
    rw [Measure.pi_of_empty (fun _ : Fin 0 => volume.restrict (Set.Icc (0:ℝ) 1)),
      integral_dirac]
    refine le_of_eq (congrArg (fun p : Fin 0 → ℂ => Real.log (‖H p‖ + ε)) ?_)
    exact Subsingleton.elim _ _
  | succ d ih =>
    intro H ρ hρ hHol ε hε
    -- a uniform bound `M` for `‖H‖` on the closed unit polydisc, and the integrand bound `B`
    obtain ⟨M, hM⟩ := exists_norm_bound hρ hHol
    have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (by simp))
    set B : ℝ := max |Real.log ε| |Real.log (M + ε)| with hB
    have hlogB : ∀ z : Fin (d+1) → ℂ, (∀ j, ‖z j‖ ≤ 1) →
        ‖Real.log (‖H z‖ + ε)‖ ≤ B := by
      intro z hz
      rw [Real.norm_eq_abs, abs_le]
      have h1 : ε ≤ ‖H z‖ + ε := le_add_of_nonneg_left (norm_nonneg _)
      have h2 : ‖H z‖ + ε ≤ M + ε := add_le_add (hM z hz) le_rfl
      have h3 : Real.log ε ≤ Real.log (‖H z‖ + ε) := Real.log_le_log hε h1
      have h4 : Real.log (‖H z‖ + ε) ≤ Real.log (M + ε) :=
        Real.log_le_log (by positivity) h2
      rw [hB]
      refine ⟨?_, ?_⟩
      · have h5 : -|Real.log ε| ≤ Real.log ε := neg_abs_le _
        have h6 : |Real.log ε| ≤ max |Real.log ε| |Real.log (M + ε)| := le_max_left _ _
        linarith
      · have h5 : Real.log (M + ε) ≤ |Real.log (M + ε)| := le_abs_self _
        have h6 : |Real.log (M + ε)| ≤ max |Real.log ε| |Real.log (M + ε)| := le_max_right _ _
        linarith
    -- continuity of the two torus functions
    have hcontT : Continuous (fun t : Fin (d+1) → ℝ => H (torusPt t)) :=
      (continuousOn_unitPolydisc hρ hHol).comp_continuous (continuous_torusPt (d := d+1))
        (fun t => fun j => by simp)
    have hcontC : Continuous (fun p : ℝ × (Fin d → ℝ) => H (torusPt (Fin.cons p.1 p.2))) :=
      (continuousOn_unitPolydisc hρ hHol).comp_continuous
        (continuous_torusPt.comp continuous_finCons) (fun p => fun j => by simp)
    -- the joint integrand on `ℝ × (Fin d → ℝ)`
    have hjoint : Integrable (fun p : ℝ × (Fin d → ℝ) =>
        Real.log (‖H (torusPt (Fin.cons p.1 p.2))‖ + ε))
        (volume.restrict (Set.Icc (0:ℝ) 1) |>.prod <|
          Measure.pi (fun _ : Fin d => volume.restrict (Set.Icc (0:ℝ) 1))) := by
      have hc : Continuous (fun p : ℝ × (Fin d → ℝ) =>
          ‖H (torusPt (Fin.cons p.1 p.2))‖ + ε) := hcontC.norm.add continuous_const
      refine Integrable.of_bound (hc.log (fun p => by positivity)).aestronglyMeasurable
        B (Filter.Eventually.of_forall fun p => ?_)
      simpa using hlogB (torusPt (Fin.cons p.1 p.2)) (fun j => by cases j using Fin.cases <;> simp)
    -- the slice through the origin
    let F : ℂ → ℂ := fun w => H (Fin.cons w (0 : Fin d → ℂ))
    have hF_an : AnalyticOnNhd ℂ F (Metric.closedBall 0 1) := by
      show AnalyticOnNhd ℂ (fun w : ℂ => H (Fin.cons w (0 : Fin d → ℂ))) (Metric.closedBall 0 1)
      intro z hz
      have hzρ : z ∈ Metric.ball (0:ℂ) ρ := by
        rw [Metric.mem_ball, dist_zero_right]
        exact lt_of_le_of_lt (by simpa [Metric.mem_closedBall, dist_zero_right] using hz) hρ
      refine (DifferentiableOn.analyticAt (s := Metric.closedBall (0:ℂ) ρ) ?_
        (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hzρ) Metric.ball_subset_closedBall))
      intro w hw
      have hwρ : ‖w‖ ≤ ρ := by simpa [Metric.mem_closedBall, dist_zero_right] using hw
      have hin : ∀ j : Fin (d+1), ‖(Fin.cons w (0 : Fin d → ℂ) : Fin (d+1) → ℂ) j‖ ≤ ρ :=
        fun j => by
          cases j using Fin.cases with
          | zero => simpa [Fin.cons_zero] using hwρ
          | succ i => simpa [Fin.cons_succ] using (le_trans zero_le_one hρ.le)
      have hH : DifferentiableAt ℂ H (Fin.cons w (0 : Fin d → ℂ)) := hHol _ hin
      have hi : DifferentiableAt ℂ
          (fun w : ℂ => (Fin.cons w (0 : Fin d → ℂ) : Fin (d+1) → ℂ)) w := by
        apply differentiableAt_pi.mpr
        intro j
        cases j using Fin.cases with
        | zero =>
            simpa [Fin.cons_zero] using (differentiableAt_id (𝕜 := ℂ) (x := w))
        | succ i =>
            simpa [Fin.cons_succ] using (differentiableAt_const (c := (0:ℂ)) (x := w))
      have hcomp : DifferentiableAt ℂ (fun w : ℂ => H (Fin.cons w (0 : Fin d → ℂ))) w :=
        (hH.hasFDerivAt.comp w hi.hasFDerivAt).differentiableAt
      exact hcomp.differentiableWithinAt
    -- step 1: the one-variable smoothed Jensen inequality for `F`
    have h1 : Real.log (‖H 0‖ + ε) ≤
        ∫ s : ℝ, Real.log (‖F (circlePt s)‖ + ε) ∂(volume.restrict (Set.Icc (0:ℝ) 1)) := by
      have h := smoothed_jensen F hF_an hε
      have hF0 : F 0 = H 0 := by
        show H (Fin.cons (0:ℂ) (0 : Fin d → ℂ)) = H (0 : Fin (d+1) → ℂ)
        congr 1
        funext j
        cases j using Fin.cases <;> simp
      rwa [hF0] at h
    -- step 2: the induction hypothesis applied to the slices in the first variable
    have h2 : ∀ s : ℝ, Real.log (‖F (circlePt s)‖ + ε) ≤
        ∫ t' : Fin d → ℝ, Real.log (‖H (torusPt (Fin.cons s t'))‖ + ε)
          ∂(Measure.pi (fun _ : Fin d => volume.restrict (Set.Icc (0:ℝ) 1))) := by
      intro s
      have hsl : ∀ ζ : Fin d → ℂ, (∀ j, ‖ζ j‖ ≤ ρ) →
          DifferentiableAt ℂ (fun ζ : Fin d → ℂ => H (Fin.cons (circlePt s) ζ)) ζ := by
        intro ζ hζ
        have hin : ∀ j : Fin (d+1), ‖(Fin.cons (circlePt s) ζ : Fin (d+1) → ℂ) j‖ ≤ ρ :=
          fun j => by
            cases j using Fin.cases with
            | zero => simpa [Fin.cons_zero] using le_trans (le_of_eq (norm_circlePt s)) hρ.le
            | succ i => simpa [Fin.cons_succ] using hζ i
        have hH : DifferentiableAt ℂ H (Fin.cons (circlePt s) ζ) := hHol _ hin
        have hi : DifferentiableAt ℂ
            (fun ζ : Fin d → ℂ => (Fin.cons (circlePt s) ζ : Fin (d+1) → ℂ)) ζ := by
          apply differentiableAt_pi.mpr
          intro j
          cases j using Fin.cases with
          | zero =>
              simpa [Fin.cons_zero] using (differentiableAt_const (c := circlePt s) (x := ζ))
          | succ i =>
              simpa [Fin.cons_succ] using (differentiableAt_apply (𝕜 := ℂ) i ζ)
        exact (hH.hasFDerivAt.comp ζ hi.hasFDerivAt).differentiableAt
      have his := ih (fun ζ : Fin d → ℂ => H (Fin.cons (circlePt s) ζ)) ρ hρ hsl ε hε
      have hpt : ∀ t' : Fin d → ℝ,
          (fun ζ : Fin d → ℂ => H (Fin.cons (circlePt s) ζ)) (torusPt t')
            = H (torusPt (Fin.cons s t')) := by
        intro t'
        rw [torusPt_cons]
      simpa only [hpt] using his
    -- step 3: integrate the pointwise bound over `s`
    have h3 : (∫ s : ℝ, Real.log (‖F (circlePt s)‖ + ε) ∂(volume.restrict (Set.Icc (0:ℝ) 1)))
        ≤ ∫ s : ℝ, (∫ t' : Fin d → ℝ, Real.log (‖H (torusPt (Fin.cons s t'))‖ + ε)
          ∂(Measure.pi (fun _ : Fin d => volume.restrict (Set.Icc (0:ℝ) 1))))
          ∂(volume.restrict (Set.Icc (0:ℝ) 1)) := by
      refine integral_mono_ae ?_ hjoint.integral_prod_left (Filter.Eventually.of_forall h2)
      have hc : Continuous (fun s : ℝ => ‖F (circlePt s)‖ + ε) :=
        ((hF_an.mono Metric.sphere_subset_closedBall).continuousOn.comp_continuous
          continuous_circlePt (fun s => by
            rw [mem_sphere_zero_iff_norm]; exact norm_circlePt s)).norm.add continuous_const
      refine Integrable.of_bound (hc.log (fun s => by positivity)).aestronglyMeasurable
        B (Filter.Eventually.of_forall fun s => ?_)
      simpa using hlogB (Fin.cons (circlePt s) (0 : Fin d → ℂ)) (fun j => by cases j using Fin.cases <;> simp)
    -- step 4: Fubini
    have h4 : (∫ t : Fin (d+1) → ℝ, Real.log (‖H (torusPt t)‖ + ε)
        ∂(Measure.pi (fun _ : Fin (d+1) => volume.restrict (Set.Icc (0:ℝ) 1))))
        = ∫ s : ℝ, (∫ t' : Fin d → ℝ, Real.log (‖H (torusPt (Fin.cons s t'))‖ + ε)
          ∂(Measure.pi (fun _ : Fin d => volume.restrict (Set.Icc (0:ℝ) 1))))
          ∂(volume.restrict (Set.Icc (0:ℝ) 1)) := by
      refine pi_integral_cons (volume.restrict (Set.Icc (0:ℝ) 1)) _ ?_
      have hc : Continuous (fun t : Fin (d+1) → ℝ => ‖H (torusPt t)‖ + ε) :=
        hcontT.norm.add continuous_const
      refine Integrable.of_bound (hc.log (fun t => by positivity)).aestronglyMeasurable
        B (Filter.Eventually.of_forall fun t => ?_)
      simpa using hlogB (torusPt t) (fun j => by simp)
    rw [h4]
    exact le_trans h1 h3

theorem polydisc_log_mean {d : ℕ} (H : (Fin d → ℂ) → ℂ) (ρ : ℝ) (hρ : 1 < ρ)
    (hHol : ∀ z : Fin d → ℂ, (∀ j, ‖z j‖ ≤ ρ) → DifferentiableAt ℂ H z)
    (h0 : H 0 ≠ 0) :
    Real.log ‖H 0‖ ≤
      ∫ t : Fin d → ℝ,
        Real.log ‖H (fun j => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t j : ℂ)))‖
        ∂(MeasureTheory.Measure.pi (fun _ : Fin d =>
            MeasureTheory.volume.restrict (Set.Icc (0:ℝ) 1))) := by
  obtain ⟨M, hM⟩ := exists_norm_bound hρ hHol
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (by simp))
  set C : ℝ := max 0 (Real.log (M + 1)) with hC
  have hCnn : 0 ≤ C := by rw [hC]; exact le_max_left _ _
  have hCg : ∀ t : Fin d → ℝ, Real.log (‖H (torusPt t)‖ + 1) ≤ C := by
    intro t
    rw [hC]
    refine le_trans (Real.log_le_log (by positivity) (by linarith [hM (torusPt t) (fun _ => by simp)]))
      (le_max_right _ _)
  have hg_meas : Measurable (fun t : Fin d → ℝ => ‖H (torusPt t)‖) :=
    (((continuousOn_unitPolydisc hρ hHol).comp_continuous continuous_torusPt
      (fun t => fun j => by simp)).norm).measurable
  haveI : IsProbabilityMeasure (volume.restrict (Set.Icc (0:ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; norm_num⟩
  haveI : IsProbabilityMeasure
      (Measure.pi (fun _ : Fin d => volume.restrict (Set.Icc (0:ℝ) 1))) := inferInstance
  have hsm : ∀ ε : ℝ, 0 < ε → Real.log (‖H 0‖ + ε) ≤
      ∫ t : Fin d → ℝ, Real.log (‖H (torusPt t)‖ + ε)
        ∂(Measure.pi (fun _ : Fin d => volume.restrict (Set.Icc (0:ℝ) 1))) :=
    fun ε hε => polydisc_log_mean_smoothed d H ρ hρ hHol ε hε
  have hε0 : ∀ n : ℕ, 0 < (1:ℝ)/((n:ℝ)+1) := fun n => by positivity
  have hε1 : ∀ n : ℕ, (1:ℝ)/((n:ℝ)+1) ≤ 1 := fun n => by
    rw [div_le_one (by positivity)]
    exact_mod_cast Nat.le_add_left 1 n
  have hεt : Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hεm : Antitone (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)) := by
    intro a b hab
    have h2 : ((a:ℝ)+1) ≤ ((b:ℝ)+1) := by
      have : (a:ℝ) ≤ (b:ℝ) := by exact_mod_cast hab
      linarith
    exact one_div_le_one_div_of_le (by positivity) h2
  have hc : ∀ n : ℕ, Real.log (‖H 0‖ + (1:ℝ)/((n:ℝ)+1)) ≤
      ∫ x : Fin d → ℝ, Real.log (‖H (torusPt x)‖ + (1:ℝ)/((n:ℝ)+1))
        ∂(Measure.pi (fun _ : Fin d => volume.restrict (Set.Icc (0:ℝ) 1))) :=
    fun n => hsm _ (hε0 n)
  have hcm : Antitone (fun n : ℕ => Real.log (‖H 0‖ + (1:ℝ)/((n:ℝ)+1))) := by
    intro a b hab
    refine Real.log_le_log (by positivity) ?_
    have := hεm hab
    linarith
  have hct : Tendsto (fun n : ℕ => Real.log (‖H 0‖ + (1:ℝ)/((n:ℝ)+1))) atTop
      (nhds (Real.log ‖H 0‖)) := by
    have h1 : Tendsto (fun n : ℕ => ‖H 0‖ + (1:ℝ)/((n:ℝ)+1)) atTop (nhds ‖H 0‖) := by
      simpa using (tendsto_const_nhds.add hεt :
        Tendsto (fun n : ℕ => ‖H 0‖ + (1:ℝ)/((n:ℝ)+1)) atTop (nhds (‖H 0‖ + 0)))
    exact (Real.continuousAt_log (norm_ne_zero_iff.mpr h0)).tendsto.comp h1
  have key := le_integral_log_of_smoothed (μ := Measure.pi (fun _ : Fin d =>
      volume.restrict (Set.Icc (0:ℝ) 1))) (g := fun t : Fin d → ℝ => ‖H (torusPt t)‖)
    hg_meas (fun t => norm_nonneg _) hCnn hCg hε0 hε1 hεt hεm hc hcm hct
  have hfun : (fun t : Fin d → ℝ => Real.log ‖H (torusPt t)‖)
      = (fun t : Fin d → ℝ =>
          Real.log ‖H (fun j => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t j : ℂ)))‖) := by
    funext t
    rw [show torusPt t = (fun j => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t j : ℂ)))
      from funext (fun j => rfl)]
  rw [hfun] at key
  exact key

end

end Work.Holonomy3
