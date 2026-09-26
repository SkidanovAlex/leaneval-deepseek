import Mathlib
import ChallengeDeps
import Submission.Work.Sweep.Defs
import Submission.Work.Sweep.Coarea

/-!
# The coarea formula for coordinate planes

This file is the companion of `SweepCount.lean`: applying the abstract
one-dimensional coarea inequality to the third coordinate function along the
knot gives

* `lintegral_coordCount_le`: the integral over the levels `s ∈ [-ε, ε]` of the
  number of intersections of the knot with the plane `{y | y 2 = s}` inside the
  ball of radius `R` about `x` is at most the arclength of the part of the knot
  inside that ball.

Together with the length bound for sets of small diameter this gives the estimate
`∫_{-ε}^{ε} #(knot ∩ ball ∩ {y 2 = s}) ds ≤ 2 d · diam`, which is the second
integral-geometric input of Pardon's sweep argument.
-/

noncomputable section

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set
open scoped ENNReal Topology

namespace Work.Sweep

/-- **Coarea formula over the coordinate planes.**

For a point `x`, a radius `R` and `ε`, the integral over the levels
`s ∈ [-ε, ε]` of the number of parameters at which the knot lies in the open ball
of radius `R` about `x` and has third coordinate `s` is at most the arclength of
the part of the knot inside that ball. -/
theorem lintegral_coordCount_le (K : Knot) (x : R3) (R ε : ℝ) :
    ∫⁻ s in Set.Icc (-ε) ε, coordCount K x R s ≤
      arclengthIn K (paramSetIn K (Metric.ball x R)) := by
  classical
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  obtain ⟨f, hfdef⟩ : ∃ f : ℝ → ℝ, f = fun t => (K.curve t) 2 := ⟨_, rfl⟩
  obtain ⟨f', hf'def⟩ : ∃ f' : ℝ → ℝ, f' = fun t => (deriv K.curve t) 2 := ⟨_, rfl⟩
  have hderiv : ∀ t : ℝ, HasDerivAt f (f' t) t := by
    intro t
    rw [hfdef, hf'def]
    have h := ((K.smooth.differentiable (by simp)) t).hasDerivAt
    exact (PiLp.proj (𝕜 := ℝ) (p := 2) (fun _ : Fin 3 => ℝ) (2 : Fin 3)).hasFDerivAt.comp_hasDerivAt
      t h
  have hcont : ContinuousOn f' (Set.Icc (0 : ℝ) (2 * Real.pi)) := by
    rw [hf'def]
    exact ((PiLp.proj (𝕜 := ℝ) (p := 2) (fun _ : Fin 3 => ℝ) (2 : Fin 3)).continuous.comp
      (K.smooth.continuous_deriv (by simp))).continuousOn
  have hSmeas : MeasurableSet (paramSetIn K (Metric.ball x R)) :=
    ((Metric.isOpen_ball.measurableSet).preimage K.smooth.continuous.measurable).inter
      measurableSet_Icc
  have hsub : paramSetIn K (Metric.ball x R) ⊆ Set.Icc (0 : ℝ) (2 * Real.pi) :=
    Set.inter_subset_right
  have hwmeas : AEMeasurable ((Set.Icc (-ε) ε).indicator (fun _ => (1 : ENNReal))) :=
    (measurable_const.indicator measurableSet_Icc).aemeasurable
  have hcoa := lintegral_mul_levelCount_le_subset hπ.le hSmeas hsub (w := (Set.Icc (-ε) ε).indicator
    (fun _ => (1 : ENNReal))) hwmeas (fun t _ => hderiv t) hcont
  -- identify the level count with the coordinate count
  have hlevel : levelCount f (paramSetIn K (Metric.ball x R)) = coordCount K x R := by
    funext s
    rw [hfdef]
    unfold levelCount coordCount coordParamSet paramSetIn
    congr 2
    ext t
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    tauto
  -- the left-hand side is the integral of the coordinate counts
  have hLHS : ∫⁻ s, (Set.Icc (-ε) ε).indicator (fun _ => (1 : ENNReal)) s *
      levelCount f (paramSetIn K (Metric.ball x R)) s =
      ∫⁻ s in Set.Icc (-ε) ε, coordCount K x R s := by
    rw [hlevel]
    rw [show (fun s : ℝ => (Set.Icc (-ε) ε).indicator (fun _ => (1 : ENNReal)) s *
        coordCount K x R s) = (Set.Icc (-ε) ε).indicator (fun s => coordCount K x R s) from ?_]
    · exact lintegral_indicator measurableSet_Icc _
    · funext s
      by_cases hs : s ∈ Set.Icc (-ε) ε <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hs]
  -- the right-hand side is bounded by the arclength in the ball
  have hRHS : ∫⁻ t in paramSetIn K (Metric.ball x R),
      ENNReal.ofReal |f' t| * (Set.Icc (-ε) ε).indicator (fun _ => (1 : ENNReal)) (f t) ≤
      arclengthIn K (paramSetIn K (Metric.ball x R)) := by
    have hpt : ∀ t ∈ paramSetIn K (Metric.ball x R),
        ENNReal.ofReal |f' t| * (Set.Icc (-ε) ε).indicator (fun _ => (1 : ENNReal)) (f t) ≤
          ENNReal.ofReal (speed K t) := by
      intro t _
      have hcoord : |f' t| ≤ speed K t := by
        rw [hf'def]
        have := PiLp.norm_apply_le (deriv K.curve t) 2
        rw [Real.norm_eq_abs] at this
        exact this
      have hind : (Set.Icc (-ε) ε).indicator (fun _ => (1 : ENNReal)) (f t) ≤ 1 := by
        by_cases h : f t ∈ Set.Icc (-ε) ε <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
      calc ENNReal.ofReal |f' t| * (Set.Icc (-ε) ε).indicator (fun _ => (1 : ENNReal)) (f t)
          ≤ ENNReal.ofReal |f' t| * 1 := by gcongr
        _ = ENNReal.ofReal |f' t| := mul_one _
        _ ≤ ENNReal.ofReal (speed K t) := ENNReal.ofReal_le_ofReal hcoord
    calc ∫⁻ t in paramSetIn K (Metric.ball x R),
            ENNReal.ofReal |f' t| * (Set.Icc (-ε) ε).indicator (fun _ => (1 : ENNReal)) (f t)
        ≤ ∫⁻ t in paramSetIn K (Metric.ball x R), ENNReal.ofReal (speed K t) :=
          setLIntegral_mono
            (ENNReal.measurable_ofReal.comp
              ((K.smooth.continuous_deriv (by simp)).norm.measurable)) hpt
      _ = arclengthIn K (paramSetIn K (Metric.ball x R)) := rfl
  rw [← hLHS]
  exact hcoa.trans hRHS

end Work.Sweep
