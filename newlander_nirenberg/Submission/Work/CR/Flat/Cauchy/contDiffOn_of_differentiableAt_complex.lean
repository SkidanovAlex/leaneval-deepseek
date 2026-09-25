import Mathlib
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Holder.holderNorm_le_wirtinger_coord
import Submission.Work.CR.Flat.Cauchy.dCoord_contDiffOn_one_of_holomorphic_global
import Submission.Work.CR.Flat.Cauchy.CR_contDiffOn_smooth

/-!
# Holomorphic (complex differentiable) functions on open sets of `ℂⁿ` are real smooth

The main result of this file is `contDiffOn_of_differentiableAt_complex`: a function
`f : (Fin n → ℂ) → ℂ` which is complex differentiable at every point of an open set `Ω` is
`C^k` (in the real sense) on `Ω`, for every `k : ℕ`.

The proof has two parts.

* **`C¹`-regularity** (`contDiffOn_one_of_differentiableAt_complex`).  The real derivative of a
  holomorphic function is continuous.  The pointwise `(1,0)`-derivative `∂_j f = dCoord j f`
  equals the derivative of the `j`-th complex slice, which by the one-variable Cauchy integral
  formula is given *on a small ball* by a parametrised integral with continuous integrand; hence
  it is continuous (`continuousOn_dCoord_of_differentiableAt_complex`).  The `(0,1)`-derivatives
  vanish (`dbarCoord_eq_zero_of_differentiableAt_complex`), so the Wirtinger reconstruction
  `fderiv_eq_sum_PhiN_PsiN` expresses `fderiv ℝ f` as a finite sum of continuous functions and
  `contDiffAt_one_iff` concludes.

* **Higher regularity** (`CR_contDiffOn_smooth`): a `C¹` function on an open set whose flat
  `∂̄`-derivatives vanish is `C^∞`; this is the elliptic bootstrap already available in
  `Submission.Work.CR.Flat.Cauchy.CR_contDiffOn_smooth`.
-/

open scoped ContDiff
open Set Filter MeasureTheory

namespace Work.CR.Flat.Cauchy

/-- **Holomorphic functions satisfy the flat `∂̄`-equations.**

If `f : ℂⁿ → ℂ` is complex differentiable at `w`, then the `(0,1)`-Wirtinger derivative
`dbarCoord j f w` vanishes: the real derivative is the scalar restriction of the `ℂ`-linear
complex derivative, and `Pi.single j I = I • Pi.single j 1`. -/
theorem dbarCoord_eq_zero_of_differentiableAt_complex {n : ℕ} {f : (Fin n → ℂ) → ℂ}
    {w : Fin n → ℂ} {j : Fin n}
    (h : DifferentiableAt ℂ f w) : Work.CR.Flat.dbarCoord j f w = 0 := by
  rw [Work.CR.Flat.dbarCoord, h.fderiv_restrictScalars ℝ]
  have hcoe : ∀ v : Fin n → ℂ,
      (ContinuousLinearMap.restrictScalars ℝ (fderiv ℂ f w)) v = (fderiv ℂ f w) v :=
    fun v => rfl
  simp only [hcoe]
  have hsingle : (Pi.single j (Complex.I : ℂ) : Fin n → ℂ) = Complex.I • Pi.single j (1 : ℂ) := by
    ext i; by_cases hi : i = j <;> simp [hi]
  rw [hsingle, map_smul]
  simp only [smul_eq_mul]
  rw [show Complex.I * (Complex.I * (fderiv ℂ f w) (Pi.single j 1))
      = -(fderiv ℂ f w) (Pi.single j 1) from by
        rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]]
  ring

/-- **Continuity of the `(1,0)`-derivatives of a holomorphic function.**

For `f` complex differentiable on an open `Ω ⊆ ℂⁿ`, the function `z ↦ dCoord j f z` is
continuous on `Ω`.

The proof is local.  Around a point `z₀` we take a ball `B(z₀, ρ) ⊆ Ω` and set `R = ρ/4`; for
`y ∈ B(z₀, R)` the one-variable Cauchy formula for the `j`-th slice (whose `∂̄`-derivative
vanishes, so the slice is holomorphic) gives
`dCoord j f y = (2πI)⁻¹ ∮_{C(y_j, R)} (ζ - y_j)⁻² f(y with y_j ↦ ζ) dζ`, and after the
circle parametrisation `ζ = y_j + R e^{iθ}` the right hand side is the parameter integral
`(2πI)⁻¹ ∫₀^{2π} I (R e^{iθ})⁻¹ f(y + R e^{iθ} e_j) dθ`, whose integrand is continuous in
`(y, θ)` and bounded on a neighbourhood; dominated convergence gives continuity at `z₀`. -/
theorem continuousOn_dCoord_of_differentiableAt_complex {n : ℕ} {Ω : Set (Fin n → ℂ)}
    (hΩ : IsOpen Ω) {f : (Fin n → ℂ) → ℂ} (hhol : ∀ w ∈ Ω, DifferentiableAt ℂ f w)
    (j : Fin n) : ContinuousOn (fun z => Work.CR.Flat.dCoord j f z) Ω := by
  have hdbar : ∀ z ∈ Ω, Work.CR.Flat.dbarCoord j f z = 0 :=
    fun z hz => dbarCoord_eq_zero_of_differentiableAt_complex (hhol z hz)
  refine (IsOpen.continuousOn_iff hΩ).mpr (fun z₀ hz₀ => ?_)
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hΩ z₀ hz₀
  set R : ℝ := ρ / 4 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith
  have hcontΩ : ContinuousOn f Ω := fun z hz => (hhol z hz).continuousAt.continuousWithinAt
  have hsub : Metric.closedBall z₀ (ρ/2) ⊆ Ω := fun z hz => hball (by
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    rw [Metric.mem_ball, dist_eq_norm]; linarith)
  obtain ⟨M, hM⟩ := (isCompact_closedBall z₀ (ρ/2)).exists_bound_of_continuousOn
    (hcontΩ.mono hsub)
  set e : Fin n → ℂ := Pi.single j (1 : ℂ) with hedef
  set F : (Fin n → ℂ) → ℝ → ℂ := fun y θ =>
      Complex.I * (circleMap 0 R θ)⁻¹ * f (y + circleMap 0 R θ • e) with hFdef
  have hmem : ∀ y ∈ Metric.ball z₀ R, ∀ θ : ℝ,
      y + circleMap 0 R θ • e ∈ Metric.closedBall z₀ (ρ/2) := by
    intro y hy θ
    rw [Metric.mem_ball, dist_eq_norm] at hy
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hcalc : ‖y + circleMap 0 R θ • e - z₀‖ < ρ/2 := by
      calc ‖y + circleMap 0 R θ • e - z₀‖
          ≤ ‖y - z₀‖ + ‖circleMap 0 R θ • e‖ := by
            rw [show y + circleMap 0 R θ • e - z₀ = (y - z₀) + circleMap 0 R θ • e by abel]
            exact norm_add_le _ _
        _ = ‖y - z₀‖ + R := by
            rw [norm_smul, norm_circleMap_zero, abs_of_pos hRpos, hedef, Pi.norm_single, norm_one,
              mul_one]
        _ < ρ/4 + ρ/4 := by rw [hRdef] at hy; linarith
        _ = ρ/2 := by ring
    exact hcalc.le
  have hF_cont : ∀ y ∈ Metric.ball z₀ R, Continuous (F y) := by
    intro y hy
    have h1 : Continuous (fun θ : ℝ => y + circleMap 0 R θ • e) :=
      continuous_const.add ((continuous_circleMap 0 R).smul continuous_const)
    have h2 : Continuous (fun θ : ℝ => f (y + circleMap 0 R θ • e)) := by
      rw [continuous_iff_continuousAt]
      intro θ
      exact ContinuousAt.comp (x := θ) (f := fun θ' : ℝ => y + circleMap 0 R θ' • e) (g := f)
        (hcontΩ.continuousAt (hΩ.mem_nhds (hsub (hmem y hy θ)))) h1.continuousAt
    have h3 : Continuous (fun θ : ℝ => Complex.I * (circleMap 0 R θ)⁻¹) :=
      continuous_const.mul ((continuous_circleMap 0 R).inv₀
        (fun θ => circleMap_ne_center (ne_of_gt hRpos)))
    have h4 : Continuous (fun θ : ℝ =>
        Complex.I * (circleMap 0 R θ)⁻¹ * f (y + circleMap 0 R θ • e)) :=
      h3.mul h2
    rw [hFdef]
    exact h4
  have hint_cont : ContinuousAt (fun y => ∫ θ in (0:ℝ)..(2*Real.pi), F y θ) z₀ := by
    refine intervalIntegral.continuousAt_of_dominated_interval (μ := volume)
      (bound := fun _ => R⁻¹ * M) ?_ ?_ ?_ ?_
    · filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hRpos)] with y hy
      exact (hF_cont y hy).aestronglyMeasurable
    · filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hRpos)] with y hy
      refine Eventually.of_forall (fun θ hθ => ?_)
      rw [hFdef]
      simp only
      rw [norm_mul, norm_mul, norm_inv, norm_circleMap_zero, abs_of_pos hRpos, Complex.norm_I,
        one_mul]
      exact mul_le_mul_of_nonneg_left (hM _ (hmem y hy θ)) (by positivity)
    · exact intervalIntegrable_const
    · refine Eventually.of_forall (fun t ht => ?_)
      rw [hFdef]
      simp only
      have hc : ContinuousAt (fun x : Fin n → ℂ => f (x + circleMap 0 R t • e)) z₀ :=
        ContinuousAt.comp (x := z₀) (f := fun x : Fin n → ℂ => x + circleMap 0 R t • e) (g := f)
          (hcontΩ.continuousAt (hΩ.mem_nhds (hsub (hmem z₀ (Metric.mem_ball_self hRpos) t))))
          ((continuous_id.add continuous_const).continuousAt)
      exact hc.const_mul _
  set Ψ : (Fin n → ℂ) → ℂ := fun y =>
      (2 * (Real.pi : ℂ) * Complex.I)⁻¹ • ∫ θ in (0:ℝ)..(2*Real.pi), F y θ with hΨdef
  have hEqOn : ∀ y ∈ Metric.ball z₀ R, Work.CR.Flat.dCoord j f y = Ψ y := by
    intro y hy
    have hyR : ‖y - z₀‖ + R < ρ := by
      rw [Metric.mem_ball, dist_eq_norm] at hy
      rw [hRdef] at *; linarith
    rw [Work.CR.Flat.Cauchy.DCoordGlobal.dCoord_eq_circleIntegral_self (j := j) (u := f)
        hRpos hyR (fun z hz => (hhol z (hball hz)).restrictScalars ℝ)
        (fun z hz => hdbar z (hball hz)),
      Work.CR.Flat.Cauchy.DCoordGlobal.circleIntegral_reparam j f (ne_of_gt hRpos) y]
  have hΨ_cont : ContinuousAt Ψ z₀ := by
    rw [hΨdef]
    exact ContinuousAt.const_smul hint_cont ((2 * (Real.pi : ℂ) * Complex.I)⁻¹)
  exact hΨ_cont.congr
    (Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hRpos))
      (fun y hy => (hEqOn y hy).symm))

/-- **Continuity of the real derivative of a holomorphic function.**

Since `fderiv ℝ f` is reconstructed from the Wirtinger derivatives by the fixed linear maps
`PhiN j`, `PsiN j` (`fderiv_eq_sum_PhiN_PsiN`), and the `(0,1)`-derivatives vanish while the
`(1,0)`-derivatives are continuous, `fderiv ℝ f` is continuous on `Ω`. -/
theorem continuousOn_fderiv_of_differentiableAt_complex {n : ℕ} {Ω : Set (Fin n → ℂ)}
    (hΩ : IsOpen Ω) {f : (Fin n → ℂ) → ℂ} (hhol : ∀ w ∈ Ω, DifferentiableAt ℂ f w) :
    ContinuousOn (fun z => fderiv ℝ f z) Ω := by
  have hdcoord : ∀ j : Fin n, ContinuousOn (fun z => Work.CR.Flat.dCoord j f z) Ω :=
    fun j => continuousOn_dCoord_of_differentiableAt_complex hΩ hhol j
  have hdbar : ∀ j : Fin n, ∀ z ∈ Ω, Work.CR.Flat.dbarCoord j f z = 0 :=
    fun j z hz => dbarCoord_eq_zero_of_differentiableAt_complex (hhol z hz)
  have hsum : ContinuousOn (fun z => ∑ j : Fin n,
      (Work.CR.Flat.Holder.PhiN j (Work.CR.Flat.dCoord j f z)
        + Work.CR.Flat.Holder.PsiN j (Work.CR.Flat.dbarCoord j f z))) Ω := by
    refine continuousOn_finsetSum Finset.univ (fun j _ => ?_)
    refine ContinuousOn.add ?_ ?_
    · exact ((Work.CR.Flat.Holder.PhiN j).continuous.comp_continuousOn (hdcoord j))
    · refine ContinuousOn.congr (continuousOn_const (c := (0 : (Fin n → ℂ) →L[ℝ] ℂ))) ?_
      intro z hz
      simp only [hdbar j z hz, map_zero]
  refine ContinuousOn.congr hsum (fun z _ => ?_)
  exact Work.CR.Flat.Holder.fderiv_eq_sum_PhiN_PsiN f z

/-- **A holomorphic function on an open set is `C¹` in the real sense.**

Differentiability over `ℂ` gives differentiability over `ℝ`; the real derivative is continuous by
`continuousOn_fderiv_of_differentiableAt_complex`; `contDiffAt_one_iff` then gives `C¹` at each
point, and `IsOpen.contDiffOn_iff` globalises. -/
theorem contDiffOn_one_of_differentiableAt_complex {n : ℕ} {Ω : Set (Fin n → ℂ)}
    (hΩ : IsOpen Ω) {f : (Fin n → ℂ) → ℂ} (hhol : ∀ w ∈ Ω, DifferentiableAt ℂ f w) :
    ContDiffOn ℝ 1 f Ω := by
  refine (IsOpen.contDiffOn_iff hΩ).mpr (fun z₀ hz₀ => ?_)
  refine contDiffAt_one_iff.mpr ⟨fun z => fderiv ℝ f z, Ω, hΩ.mem_nhds hz₀,
    continuousOn_fderiv_of_differentiableAt_complex hΩ hhol, fun z hz => ?_⟩
  exact ((hhol z hz).restrictScalars ℝ).hasFDerivAt

/-- **A complex differentiable function on an open set of `ℂⁿ` is real `C^k` for every `k`.**

`f` is `C¹` by `contDiffOn_one_of_differentiableAt_complex` and satisfies the flat
Cauchy–Riemann equations `dbarCoord j f = 0` by
`dbarCoord_eq_zero_of_differentiableAt_complex`, so the elliptic bootstrap
`CR_contDiffOn_smooth` upgrades `C¹` to `C^∞`, which is in particular `C^k`. -/
theorem contDiffOn_of_differentiableAt_complex {n : ℕ} {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω)
    {f : (Fin n → ℂ) → ℂ} (hhol : ∀ w ∈ Ω, DifferentiableAt ℂ f w) (k : ℕ) :
    ContDiffOn ℝ (k : WithTop ℕ∞) f Ω := by
  have h := CR_contDiffOn_smooth hΩ (contDiffOn_one_of_differentiableAt_complex hΩ hhol)
    (fun j z hz => dbarCoord_eq_zero_of_differentiableAt_complex (hhol z hz))
  rw [contDiffOn_infty] at h
  exact h k

end Work.CR.Flat.Cauchy
