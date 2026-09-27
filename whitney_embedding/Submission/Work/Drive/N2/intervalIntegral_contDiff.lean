import Mathlib
import Submission.Work.Whitney.contDiff_fiberAverage

/-!
# Smoothness of parametric interval integrals

If `f : E × ℝ → F` is jointly `C^∞`, then `x ↦ ∫ t in a..b, f (x, t)` is `C^∞`.

The proof differentiates under the integral sign once (Mathlib's
`intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`), notes that the
derivative is again an integral of the same shape (built from the partial derivative in
the first variable), and inducts on the order of differentiability.  The induction has to
be run in a situation where the relevant spaces live in a single universe (so that the
step "the codomain becomes `E →L F`" does not change universes); this is achieved by
raising the codomain into `ULift` at the universe `max u v`, and transferring the result
back along the linear isometry equivalence `ULift F ≃ₗᵢ[ℝ] F`.
-/

namespace Work.Drive.N2

open MeasureTheory Set
open scoped ContDiff

universe u v w u₁ u₂

/-- One-step differentiation under the integral sign: if `Φ : ℝ × E → V` is `C^1` jointly,
then `y ↦ ∫ t in a..b, Φ (t, y)` is differentiable at `y`, with derivative the integral of
the partial derivative in the second variable. -/
private lemma hasFDerivAt_intervalIntegral_one {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E] {V : Type w} [NormedAddCommGroup V] [NormedSpace ℝ V]
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

/-- The parametric interval integral of a jointly `C^k` function (finite `k`) is `C^k`.

The codomain is placed in the universe `max u v`, where `u` is the universe of the domain:
this is exactly what makes the induction step (`V ↝ E →L[ℝ] V`) universe-stable. -/
private lemma contDiff_intervalIntegral_nat {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E] {a b : ℝ} :
    ∀ (k : ℕ) (V : Type (max u v)) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
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

/-- The parametric interval integral of a jointly smooth function (with domain and codomain
in the universes `u` and `max u v` respectively) is smooth. -/
private lemma contDiff_intervalIntegral_infty {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [ProperSpace E] {a b : ℝ} {V : Type (max u v)} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V] {Φ : ℝ × E → V}
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : E => ∫ t in a..b, Φ (t, y)) := by
  rw [contDiff_infty] at hΦ ⊢
  exact fun n => contDiff_intervalIntegral_nat n V Φ (hΦ n)

/-- The parametric interval integral of a jointly smooth function is smooth, for arbitrary
universes of the domain and codomain.  The codomain is lifted into the universe
`max u₁ u₂` so that the induction above applies, then transferred back. -/
private theorem intervalIntegral_contDiff_aux
    {E : Type u₁} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {F : Type u₂} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E × ℝ → F} {a b : ℝ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : E => ∫ t in a..b, f (x, t)) := by
  let L : ULift.{max u₁ u₂, u₂} F ≃ₗᵢ[ℝ] F := LinearIsometryEquiv.ulift (R := ℝ) (E := F)
  let Φ : ℝ × E → ULift.{max u₁ u₂, u₂} F := fun p => L.symm (f (p.2, p.1))
  have hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × E => (p.2, p.1)) := by fun_prop
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × E => f (p.2, p.1)) := by
      simpa [Function.comp_def] using hf.comp h1
    have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × E => L.symm (f (p.2, p.1))) :=
      L.symm.contDiff.comp h2
    simpa [Φ] using h3
  have hmain : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : E => ∫ t in a..b, Φ (t, y)) :=
    contDiff_intervalIntegral_infty (E := E) (V := ULift.{max u₁ u₂, u₂} F) (Φ := Φ) hΦ
  have hcongr : (fun y : E => ∫ t in a..b, Φ (t, y))
      = fun y : E => L.symm (∫ t in a..b, f (y, t)) := by
    funext y
    exact LinearIsometry.intervalIntegral_comp_comm L.symm.toLinearIsometry (fun t : ℝ => f (y, t))
  rw [hcongr] at hmain
  have h4 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : E => L (L.symm (∫ t in a..b, f (y, t)))) := L.contDiff.comp hmain
  simpa [Function.comp_def, LinearIsometryEquiv.apply_symm_apply] using h4

theorem intervalIntegral_contDiff
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f : E × ℝ → F} {a b : ℝ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : E => ∫ t in a..b, f (x, t)) :=
  intervalIntegral_contDiff_aux hf

end Work.Drive.N2
