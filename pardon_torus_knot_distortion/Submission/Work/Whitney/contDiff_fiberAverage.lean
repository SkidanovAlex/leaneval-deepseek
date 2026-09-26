import Mathlib

/-!
# Smoothness of parametric interval integrals

We prove that if `Φ : ℝ × E → V` is jointly `C^n` (in the smooth sense `∞`, or at any
finite order), then the parametric interval integral `y ↦ ∫ t in a..b, Φ (t, y)` is `C^n`.

The proof follows the standard pattern: differentiate once under the integral sign
(`intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`), observe that the
derivative is again an integral of the same shape (built from the partial derivative in
the second variable), and run an induction.  For the `C^∞` statement we combine this with
`contDiff_infty`.

As an application we obtain `contDiff_fiberAverage`: the average of a smooth function
along the line `t ↦ y + t • c` over a compact interval is smooth.
-/

namespace Work.Whitney

open scoped ContDiff
open MeasureTheory Set

universe u

/-- One-step differentiation under the integral sign.  If `Φ : ℝ × E → V` is `C^1` jointly
then `y ↦ ∫ t in a..b, Φ (t, y)` is differentiable with derivative the integral of the
partial derivative in the second variable. -/
private lemma hasFDerivAt_intervalIntegral_one {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E] {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] (a b : ℝ) {Φ : ℝ × E → V} (hΦ : ContDiff ℝ 1 Φ) (y : E) :
    HasFDerivAt (fun y' : E => ∫ t in a..b, Φ (t, y'))
      (∫ t in a..b, fderiv ℝ (fun z : E => Φ (t, z)) y) y := by
  -- Continuity of the joint partial derivative `(t, y) ↦ fderiv ℝ (fun z => Φ (t, z)) y`.
  have hGc : Continuous (fun p : ℝ × E => fderiv ℝ (fun z : E => Φ (p.1, z)) p.2) := by
    have h1 : ContDiff ℝ (0 : ℕ∞) (fun p : ℝ × E => fderiv ℝ (fun z : E => Φ (p.1, z)) p.2) := by
      have h1' : ContDiff ℝ ((0 : ℕ) + 1)
          (Function.uncurry (fun p : ℝ × E => fun z : E => Φ (p.1, z))) := by
        have : Function.uncurry (fun p : ℝ × E => fun z : E => Φ (p.1, z))
            = Φ ∘ (fun q : (ℝ × E) × E => (q.1.1, q.2)) := rfl
        rw [this]; exact hΦ.comp (by fun_prop)
      have h2 : ContDiff ℝ (0 : ℕ∞) (fun p : ℝ × E => p.2) := contDiff_snd
      have := ContDiff.fderiv (𝕜 := ℝ) (f := fun p : ℝ × E => fun z : E => Φ (p.1, z))
        (g := fun p : ℝ × E => p.2) h1' h2 (le_refl _)
      simpa using this
    exact contDiff_zero.mp h1
  -- A uniform bound on the partial derivative over the compact set `[a,b] × closedBall y 1`.
  obtain ⟨C, hC⟩ : ∃ C, ∀ p ∈ Set.uIcc a b ×ˢ Metric.closedBall y 1,
      ‖fderiv ℝ (fun z : E => Φ (p.1, z)) p.2‖ ≤ C :=
    (isCompact_uIcc.prod (isCompact_closedBall y 1)).exists_bound_of_continuousOn hGc.continuousOn
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (𝕜 := ℝ) (μ := volume)
    (s := Metric.closedBall y 1) (bound := fun _ => C)
    (F := fun x t => Φ (t, x)) (F' := fun x t => fderiv ℝ (fun z : E => Φ (t, z)) x)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact Metric.closedBall_mem_nhds y zero_lt_one
  · exact Filter.Eventually.of_forall fun x =>
      (hΦ.continuous.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · exact (hΦ.continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable a b
  · exact (hGc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · filter_upwards with t ht x hx
    exact hC (t, x) ⟨Set.uIoc_subset_uIcc ht, hx⟩
  · exact intervalIntegrable_const
  · filter_upwards with t ht x hx
    exact ((hΦ.differentiable one_ne_zero).differentiableAt.comp x
      ((differentiableAt_const t).prodMk differentiableAt_id)).hasFDerivAt

/-- The parametric interval integral of a jointly `C^k` function (finite `k`) is `C^k`. -/
private lemma contDiff_intervalIntegral_nat {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E] {a b : ℝ} :
    ∀ (k : ℕ) (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
      (Φ : ℝ × E → V), ContDiff ℝ (k : WithTop ℕ∞) Φ →
        ContDiff ℝ (k : WithTop ℕ∞) (fun y : E => ∫ t in a..b, Φ (t, y)) := by
  intro k
  induction k with
  | zero =>
    intro V _ _ _ Φ hΦ
    rw [show ((0 : ℕ) : WithTop ℕ∞) = (0 : WithTop ℕ∞) from rfl] at hΦ ⊢
    rw [contDiff_zero] at hΦ ⊢
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun y t => Φ (t, y)) (hΦ.comp (continuous_snd.prodMk continuous_fst)) a b
  | succ k ih =>
    intro V _ _ _ Φ hΦ
    have hkey : ((k + 1 : ℕ) : WithTop ℕ∞) = ((k : WithTop ℕ∞) + 1) := by push_cast; ring
    rw [hkey] at hΦ ⊢
    rw [contDiff_succ_iff_hasFDerivAt]
    refine ⟨fun y : E => ∫ t in a..b, fderiv ℝ (fun z : E => Φ (t, z)) y, ?_, ?_⟩
    · -- The derivative is again a parametric integral, of the jointly `C^k` function
      -- `(t, y) ↦ fderiv ℝ (fun z => Φ (t, z)) y`.
      have hΨ : ContDiff ℝ (k : WithTop ℕ∞)
          (fun p : ℝ × E => fderiv ℝ (fun z : E => Φ (p.1, z)) p.2) := by
        have h1 : ContDiff ℝ (((k : WithTop ℕ∞)) + 1)
            (Function.uncurry (fun p : ℝ × E => fun z : E => Φ (p.1, z))) := by
          have : Function.uncurry (fun p : ℝ × E => fun z : E => Φ (p.1, z))
              = Φ ∘ (fun q : (ℝ × E) × E => (q.1.1, q.2)) := rfl
          rw [this]; exact hΦ.comp (by fun_prop)
        have h2 : ContDiff ℝ ((k : WithTop ℕ∞)) (fun p : ℝ × E => p.2) := contDiff_snd
        have := ContDiff.fderiv (𝕜 := ℝ) (f := fun p : ℝ × E => fun z : E => Φ (p.1, z))
          (g := fun p : ℝ × E => p.2) h1 h2 (le_refl _)
        simpa using this
      simpa using ih (E →L[ℝ] V)
        (fun p : ℝ × E => fderiv ℝ (fun z : E => Φ (p.1, z)) p.2) hΨ
    · intro y
      exact hasFDerivAt_intervalIntegral_one a b (hΦ.of_le (by simp)) y

/-- The parametric interval integral of a jointly smooth function is smooth. -/
private lemma contDiff_intervalIntegral_infty {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E] {a b : ℝ} {V : Type u} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V] {Φ : ℝ × E → V}
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : E => ∫ t in a..b, Φ (t, y)) := by
  rw [contDiff_infty] at hΦ ⊢
  exact fun n => contDiff_intervalIntegral_nat n V Φ (hΦ n)

/-- The average of a smooth function `G` along the affine line `t ↦ y + t • c`, over the
interval `[0, W]`, is a smooth function of `y`. -/
theorem contDiff_fiberAverage {N : ℕ} (c : EuclideanSpace ℝ (Fin N)) (W : ℝ)
    (G : EuclideanSpace ℝ (Fin N) → ℝ)
    (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin N) => ∫ t in (0:ℝ)..W, G (y + t • c)) := by
  have hL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin N) => p.2 + p.1 • c) := by fun_prop
  have hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin N) => G (p.2 + p.1 • c)) := hG.comp hL
  have := contDiff_intervalIntegral_infty (E := EuclideanSpace ℝ (Fin N)) (a := (0 : ℝ))
    (b := W) (V := ℝ)
    (Φ := fun p : ℝ × EuclideanSpace ℝ (Fin N) => G (p.2 + p.1 • c)) hΦ
  simpa using this

end Work.Whitney
