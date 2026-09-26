import Mathlib

/-!
# Differentiability under the integral sign, holomorphic in the parameter

Let `F : ℂ → ℝ → ℂ` be a family of functions of a complex parameter `z`, and suppose that for
almost every `u` (with respect to `volume` restricted to an interval `(a,b)`) the map
`z ↦ F z u` is holomorphic on a ball `ball x₀ ρ` and bounded there by a constant `C`.  If
moreover `F z` is a.e. strongly measurable in `u` for `z` near `x₀`, then the parametric
integral `z ↦ ∫ u in (a,b), F z u` is complex differentiable at `x₀`.

The proof is the classical one: Cauchy's estimate upgrades the *value* bound on `ball x₀ ρ` to a
*derivative* bound on the concentric half-ball `ball x₀ (ρ/2)` (a family of Cauchy estimates, one
for each `u`), the derivative of the integrand is a.e. strongly measurable because it is an a.e.
pointwise limit of difference quotients of the measurable integrand, and then Mathlib's
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` finishes the job.

The two auxiliary lemmas are stated for an *arbitrary* measure `μ` on `ℝ`; the versions needed
for the main theorem are the specializations to `volume.restrict (Set.Ioo a b)`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped Topology

namespace Work.Asymptotics

/-! ## Cauchy's estimate: a value bound gives a derivative bound -/

/-- **Cauchy's estimate, family version.**  If for a.e. `t` the function `z ↦ f z t` is
holomorphic on `ball τ₀ R` and bounded there by `bound t`, then its `z`-derivative is bounded by
`(2/R) * bound t` on the concentric half-ball `ball τ₀ (R/2)`. -/
lemma deriv_bound_of_bound_of_measure {μ : Measure ℝ} {f : ℂ → ℝ → ℂ} {τ₀ : ℂ} {R : ℝ}
    (hR : 0 < R) {bound : ℝ → ℝ}
    (hdiff : ∀ᵐ t ∂μ, ∀ z ∈ Metric.ball τ₀ R, DifferentiableAt ℂ (fun z' => f z' t) z)
    (hbb : ∀ᵐ t ∂μ, ∀ z ∈ Metric.ball τ₀ R, ‖f z t‖ ≤ bound t) :
    ∀ᵐ t ∂μ, ∀ z ∈ Metric.ball τ₀ (R / 2), ‖deriv (fun z' => f z' t) z‖ ≤ (2 / R) * bound t := by
  filter_upwards [hdiff, hbb] with t ht hb
  intro z hz
  have hz' : dist z τ₀ < R / 2 := by simpa [Metric.mem_ball] using hz
  have hsub : Metric.closedBall z (R / 2) ⊆ Metric.ball τ₀ R := by
    intro w hw
    rw [Metric.mem_closedBall] at hw
    rw [Metric.mem_ball]
    calc dist w τ₀ ≤ dist w z + dist z τ₀ := dist_triangle _ _ _
      _ < R / 2 + R / 2 := by linarith
      _ = R := by ring
  have hdiffOn : DiffContOnCl ℂ (fun w => f w t) (Metric.ball z (R / 2)) := by
    refine DifferentiableOn.diffContOnCl fun w hw => ?_
    have hcl : closure (Metric.ball z (R / 2)) ⊆ Metric.closedBall z (R / 2) :=
      closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall
    have hw' : dist w z ≤ R / 2 := Metric.mem_closedBall.mp (hcl hw)
    have hmem : w ∈ Metric.ball τ₀ R := by
      rw [Metric.mem_ball]
      calc dist w τ₀ ≤ dist w z + dist z τ₀ := dist_triangle _ _ _
        _ < R / 2 + R / 2 := by linarith
        _ = R := by ring
    exact (ht w hmem).differentiableWithinAt
  have hsphere : ∀ w ∈ Metric.sphere z (R / 2), ‖f w t‖ ≤ bound t := by
    intro w hw
    exact hb w (hsub (Metric.mem_closedBall.mpr (le_of_eq (Metric.mem_sphere.mp hw))))
  have hkey := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (f := fun w => f w t)
    (c := z) (R := R / 2) (C := bound t) (by linarith) hdiffOn hsphere
  calc ‖deriv (fun z' => f z' t) z‖ ≤ bound t / (R / 2) := hkey
    _ = (2 / R) * bound t := by field_simp

/-! ## Measurability of the derivative in the parameter -/

/-- If for a.e. `t` the function `z ↦ f z t` is holomorphic on the open set `U`, and `f z` is
a.e. strongly measurable in `t` for every `z ∈ U`, then its `z`-derivative is a.e. strongly
measurable in `t` as well.  The proof writes the derivative as an a.e. pointwise limit of
difference quotients and uses that a.e. limits of a.e. strongly measurable functions are a.e.
strongly measurable. -/
lemma aestronglyMeasurable_deriv_of_measure {μ : Measure ℝ} {f : ℂ → ℝ → ℂ} {U : Set ℂ}
    (hU : IsOpen U)
    (hmeas : ∀ z ∈ U, AEStronglyMeasurable (fun t : ℝ => f z t) μ)
    (hdiff : ∀ᵐ t ∂μ, ∀ z ∈ U, DifferentiableAt ℂ (fun z' : ℂ => f z' t) z) :
    ∀ z ∈ U, AEStronglyMeasurable (fun t : ℝ => deriv (fun z' : ℂ => f z' t) z) μ := by
  intro z hz
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (hU.mem_nhds hz)
  let c : ℝ := r / 2
  have hc : 0 < c := by positivity
  let hq : ℕ → ℂ := fun n => ((c / (n + 1) : ℝ) : ℂ)
  have hq_ne : ∀ n, hq n ≠ 0 := by
    intro n
    simp only [hq]
    exact Complex.ofReal_ne_zero.mpr (div_ne_zero (by positivity) (by positivity))
  have hq_tendsto : Tendsto hq atTop (𝓝 0) := by
    have hreal : Tendsto (fun n : ℕ => (c / (n + 1) : ℝ)) atTop (𝓝 0) := by
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul c
      simpa [div_eq_mul_inv, Nat.cast_add, Nat.cast_one] using h
    have h2 := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hreal
    simpa [hq, Function.comp_def] using h2
  have hq_tendstoNE : Tendsto hq atTop (𝓝[≠] (0 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hq_tendsto, eventually_atTop.mpr ⟨0, fun n _ => by simpa using hq_ne n⟩⟩
  have hq_mem : ∀ n, z + hq n ∈ U := by
    intro n
    apply hball
    rw [Metric.mem_ball]
    have hnorm : ‖hq n‖ = c / (n + 1) := by
      have h1 := RCLike.norm_ofReal (K := ℂ) (c / (n + 1))
      rw [abs_of_nonneg (by positivity)] at h1
      simpa [hq] using h1
    have hlt : c / (n + 1) < r := by
      have hle : c / (n + 1) ≤ c := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hc.le, (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
      have hcr : c = r / 2 := rfl
      linarith
    calc dist (z + hq n) z = ‖hq n‖ := by rw [dist_eq_norm]; simp
      _ = c / (n + 1) := hnorm
      _ < r := hlt
  have hFmeas : ∀ n, AEStronglyMeasurable
      (fun t : ℝ => (hq n)⁻¹ * (f (z + hq n) t - f z t)) μ := by
    intro n
    exact ((hmeas (z + hq n) (hq_mem n)).sub (hmeas z hz)).const_mul _
  have hlim : ∀ᵐ t ∂μ,
      Tendsto (fun n => (hq n)⁻¹ * (f (z + hq n) t - f z t)) atTop
        (𝓝 (deriv (fun z' : ℂ => f z' t) z)) := by
    filter_upwards [hdiff] with t ht
    have hd := (ht z hz).hasDerivAt
    have hcomp := hd.tendsto_slope_zero.comp hq_tendstoNE
    simpa [Function.comp_def, smul_eq_mul] using hcomp
  exact aestronglyMeasurable_of_tendsto_ae (μ := μ) atTop hFmeas hlim

/-! ## The main theorem -/

/-- **Differentiation under the integral sign for an interval, holomorphic parameter.**
If for a.e. `u ∈ (a,b)` the function `z ↦ F z u` is complex differentiable on `ball x₀ ρ` and
bounded there by `C`, and `F z` is a.e. strongly measurable in `u` for `z` near `x₀`, then
`z ↦ ∫ u in (a,b), F z u` is complex differentiable at `x₀`. -/
theorem differentiableAt_integral_Ioo {a b : ℝ} {F : ℂ → ℝ → ℂ} {x₀ : ℂ} {ρ C : ℝ}
    (hρ : 0 < ρ)
    (hbound : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Set.Ioo a b)),
      ∀ z ∈ Metric.ball x₀ ρ, ‖F z u‖ ≤ C)
    (hdiff : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Set.Ioo a b)),
      ∀ z ∈ Metric.ball x₀ ρ, DifferentiableAt ℂ (fun z' => F z' u) z)
    (hmeas : ∀ᶠ z in nhds x₀, MeasureTheory.AEStronglyMeasurable (fun u : ℝ => F z u)
      (MeasureTheory.volume.restrict (Set.Ioo a b))) :
    DifferentiableAt ℂ (fun z => ∫ u in Set.Ioo a b, F z u) x₀ := by
  have hρ2 : (0 : ℝ) < ρ / 2 := by linarith
  -- A ball around `x₀` on which the integrand is a.e. strongly measurable and which is
  -- contained in `ball x₀ ρ`.
  have hev : ∀ᶠ z in 𝓝 x₀,
      AEStronglyMeasurable (fun u : ℝ => F z u) (volume.restrict (Set.Ioo a b)) ∧
        z ∈ Metric.ball x₀ ρ :=
    hmeas.and (Metric.ball_mem_nhds x₀ hρ)
  obtain ⟨r, hr, hsub⟩ := Metric.eventually_nhds_iff.mp hev
  have hmeasU : ∀ z ∈ Metric.ball x₀ r,
      AEStronglyMeasurable (fun u : ℝ => F z u) (volume.restrict (Set.Ioo a b)) :=
    fun z hz => (hsub (Metric.mem_ball.mp hz)).1
  have hUsub : Metric.ball x₀ r ⊆ Metric.ball x₀ ρ :=
    fun z hz => (hsub (Metric.mem_ball.mp hz)).2
  have hx0mem : x₀ ∈ Metric.ball x₀ r := Metric.mem_ball_self hr
  -- Differentiability on `ball x₀ r`, hence (via the previous lemma) measurability in `u` of
  -- the `z`-derivative at `x₀`.
  have hdiffU : ∀ᵐ u ∂(volume.restrict (Set.Ioo a b)),
      ∀ z ∈ Metric.ball x₀ r, DifferentiableAt ℂ (fun z' => F z' u) z :=
    hdiff.mono (fun u hu z hz => hu z (hUsub hz))
  have hF'_meas : AEStronglyMeasurable (fun u : ℝ => deriv (fun z' => F z' u) x₀)
      (volume.restrict (Set.Ioo a b)) :=
    aestronglyMeasurable_deriv_of_measure (μ := volume.restrict (Set.Ioo a b)) (f := F)
      Metric.isOpen_ball hmeasU hdiffU x₀ hx0mem
  -- Cauchy's estimate on `ball x₀ (ρ/2)`.
  have hdb : ∀ᵐ u ∂(volume.restrict (Set.Ioo a b)),
      ∀ z ∈ Metric.ball x₀ (ρ / 2), ‖deriv (fun z' => F z' u) z‖ ≤ (2 / ρ) * C :=
    deriv_bound_of_bound_of_measure (μ := volume.restrict (Set.Ioo a b)) (f := F) (τ₀ := x₀)
      (R := ρ) hρ hdiff hbound
  -- Integrability of the constants (the interval has finite measure).
  have hfin : IsFiniteMeasure (volume.restrict (Set.Ioo a b)) :=
    isFiniteMeasure_restrict.mpr (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have hCint : Integrable (fun _ : ℝ => C) (volume.restrict (Set.Ioo a b)) :=
    integrable_const_iff.mpr (Or.inr hfin)
  have hbnd_int : Integrable (fun _ : ℝ => (2 / ρ) * C) (volume.restrict (Set.Ioo a b)) :=
    integrable_const_iff.mpr (Or.inr hfin)
  have hF_int : Integrable (fun u : ℝ => F x₀ u) (volume.restrict (Set.Ioo a b)) :=
    hCint.mono' (hmeasU x₀ hx0mem)
      (hbound.mono (fun u hu => hu x₀ (Metric.mem_ball_self hρ)))
  have h_diff : ∀ᵐ u ∂(volume.restrict (Set.Ioo a b)),
      ∀ z ∈ Metric.ball x₀ (ρ / 2),
        HasDerivAt (fun z' => F z' u) (deriv (fun z' => F z' u) z) z :=
    hdiff.mono (fun u hu z hz => (hu z (Metric.ball_subset_ball (by linarith) hz)).hasDerivAt)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioo a b))
    (F := F) (F' := fun x u => deriv (fun z' => F z' u) x)
    (bound := fun _ : ℝ => (2 / ρ) * C) (x₀ := x₀) (s := Metric.ball x₀ (ρ / 2))
    (Metric.ball_mem_nhds x₀ hρ2) hmeas hF_int hF'_meas hdb hbnd_int h_diff
  exact key.2.differentiableAt

end Work.Asymptotics
