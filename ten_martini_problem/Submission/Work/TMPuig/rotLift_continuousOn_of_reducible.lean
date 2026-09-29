import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.TMPuig.Defs
import Submission.Work.TMComp.IDSPrufer.rotLift_approx
import Submission.Work.TMComp.IDSPrufer.contx

/-!
# Continuity of `rotLift` in the energy on a reducible spectral interval

The lifted fibered rotation number `E ↦ rotLift α lam E` is the uniform limit, with rate
`1/n` and *no* dependence on `E`, of the Cesàro averages

`A_n(E) = (∫ x in 0..1, F^n_x(E, 0)) / n`,

where `F^n_x(E, ·)` is the `n`-th Prüfer iterate at energy `E` (`Work.TMComp.IDSPrufer.rotLift_approx`
gives `|rotLift α lam E - A_n(E)| ≤ 1/n` for every `α`, `lam`, `E` and `n ≥ 1`).

Each `A_n` is continuous in `E`: the `n`-th Prüfer angle `(E, x) ↦ pruferIter α lam E n x 0`
is jointly continuous (`pruferStep` is jointly continuous in its two arguments), and on the
compact box `[E₀-1, E₀+1] × [0,1]` it is bounded by a constant, which provides the dominating
function that lets `continuousAt_of_dominated` swap the parametric integral with the limit in
`E`.

A uniform limit of continuous functions is continuous, so `E ↦ rotLift α lam E` is continuous
on all of `ℝ` — in particular on `Ioo c d`.  (The hypotheses `hα`, `hpos`, `hsub`, `hred`
are therefore not needed; they are kept because the statement is the one requested.)
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology Set

noncomputable section

namespace Work.TMPuig

/-- The `n`-th Prüfer angle is jointly continuous in the pair `(E, x)` (energy, phase). -/
theorem pruferIter_continuous_Ex (α lam : ℝ) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ => Work.TMContract.pruferIter α lam p.1 n p.2 0) := by
  induction n with
  | zero =>
    simp only [Work.TMContract.pruferIter]
    exact continuous_const
  | succ n ih =>
    have hstep : (fun p : ℝ × ℝ => Work.TMContract.pruferIter α lam p.1 (n + 1) p.2 0)
        = fun p : ℝ × ℝ => Work.TMContract.pruferStep
            (p.1 - 2 * lam * Real.cos (2 * Real.pi * (p.2 + (n : ℝ) * α)))
            (Work.TMContract.pruferIter α lam p.1 n p.2 0) := by
      funext p
      rw [Work.TMContract.pruferIter]
    rw [hstep]
    exact Work.TMComp.IDSPrufer.pruferStep_pair_cont.comp (Continuous.prodMk (by fun_prop) ih)

/-- The `n`-th integrated Prüfer angle is continuous in the energy. -/
theorem continuous_intervalIntegral_prufer (α lam : ℝ) (n : ℕ) :
    Continuous (fun E : ℝ =>
      ∫ x in Set.Ioc (0 : ℝ) 1, Work.TMContract.pruferIter α lam E n x 0) := by
  rw [continuous_iff_continuousAt]
  intro E₀
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    ((pruferIter_continuous_Ex α lam n).continuousOn
      (s := Set.Icc (E₀ - 1) (E₀ + 1) ×ˢ Set.Icc (0 : ℝ) 1))
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) := ⟨by
    rw [Measure.restrict_apply_univ, Real.volume_Ioc]
    simp⟩
  refine continuousAt_of_dominated (bound := fun _ : ℝ => C) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun E =>
      (Work.TMComp.IDSPrufer.contx α lam E n).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds E₀ (by norm_num : (0 : ℝ) < 1)] with E hE
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hE' : E ∈ Set.Icc (E₀ - 1) (E₀ + 1) := by
      rw [Metric.mem_ball, Real.dist_eq] at hE
      exact ⟨by linarith [(abs_lt.mp hE).1], by linarith [(abs_lt.mp hE).2]⟩
    exact hC (E, x) ⟨hE', Set.mem_Icc.mpr ⟨le_of_lt hx.1, hx.2⟩⟩
  · exact integrable_const C
  · exact Eventually.of_forall fun x =>
      ((pruferIter_continuous_Ex α lam n).comp
        (continuous_id.prodMk continuous_const)).continuousAt

/-- The `n`-th Cesàro average of the Prüfer angle is continuous in the energy. -/
theorem continuous_avg_prufer (α lam : ℝ) (n : ℕ) :
    Continuous (fun E : ℝ =>
      (∫ x in (0 : ℝ)..1, Work.TMContract.pruferIter α lam E n x 0) / (n : ℝ)) := by
  refine (continuous_intervalIntegral_prufer α lam n).div_const (n : ℝ) |>.congr ?_
  intro E
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

/-- `E ↦ rotLift α lam E` is continuous: `rotLift` is the uniform limit, with rate `1/n`
independent of `E`, of the continuous Cesàro averages `A_n`. -/
theorem continuous_rotLift (α lam : ℝ) :
    Continuous (fun E : ℝ => Work.TMContract.rotLift α lam E) := by
  rw [Metric.continuous_iff]
  intro E₀ ε hε
  have hε3 : (0 : ℝ) < ε / 3 := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (3 / ε)
  have hsmall : (1 : ℝ) / ((N + 1 : ℕ) : ℝ) < ε / 3 := by
    have hN2 : (3 : ℝ) / ε < ((N + 1 : ℕ) : ℝ) := by push_cast; linarith
    have hNpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
    rw [div_lt_iff₀ hNpos]
    have h3 : (3 : ℝ) < ε * ((N + 1 : ℕ) : ℝ) := by
      have h := hN2
      rw [div_lt_iff₀ hε] at h
      linarith [h]
    nlinarith [h3, hε, hNpos]
  obtain ⟨δ, hδpos, hδ⟩ :=
    Metric.continuous_iff.mp (continuous_avg_prufer α lam (N + 1)) E₀ (ε / 3) hε3
  refine ⟨δ, hδpos, fun E hE => ?_⟩
  set An : ℝ → ℝ := fun E => (∫ x in (0 : ℝ)..1,
    Work.TMContract.pruferIter α lam E (N + 1) x 0) / ((N + 1 : ℕ) : ℝ) with hAn
  have h1 : dist (Work.TMContract.rotLift α lam E) (An E) ≤ 1 / ((N + 1 : ℕ) : ℝ) := by
    rw [Real.dist_eq, hAn]
    exact Work.TMComp.IDSPrufer.rotLift_approx α lam E (Nat.le_add_left 1 N)
  have h2 : dist (An E₀) (Work.TMContract.rotLift α lam E₀) ≤ 1 / ((N + 1 : ℕ) : ℝ) := by
    rw [dist_comm, Real.dist_eq, hAn]
    exact Work.TMComp.IDSPrufer.rotLift_approx α lam E₀ (Nat.le_add_left 1 N)
  have h3 : dist (An E) (An E₀) < ε / 3 := hδ E hE
  calc dist (Work.TMContract.rotLift α lam E) (Work.TMContract.rotLift α lam E₀)
      ≤ dist (Work.TMContract.rotLift α lam E) (An E) + dist (An E) (An E₀)
        + dist (An E₀) (Work.TMContract.rotLift α lam E₀) := dist_triangle4 _ _ _ _
    _ ≤ 1 / ((N + 1 : ℕ) : ℝ) + ε / 3 + 1 / ((N + 1 : ℕ) : ℝ) := by
        linarith [h1, h2, le_of_lt h3]
    _ < ε := by linarith [hsmall]

/-- **Continuity of the lifted rotation number on a reducible spectral interval.** -/
theorem rotLift_continuousOn_of_reducible {α lam : ℝ} (hα : Irrational α) (hpos : 0 < lam)
    {c d : ℝ} (hcd : c < d) (hsub : Set.Ioo c d ⊆ Work.TMContract.amoSpec α lam)
    (hred : Set.Ioo c d ⊆ Work.TMContract.RedSet α lam) :
    ContinuousOn (fun E : ℝ => Work.TMContract.rotLift α lam E) (Set.Ioo c d) :=
  (continuous_rotLift α lam).continuousOn

end Work.TMPuig
