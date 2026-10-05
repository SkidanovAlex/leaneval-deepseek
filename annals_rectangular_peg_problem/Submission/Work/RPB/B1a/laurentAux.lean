import Mathlib
import Submission.Work.RPB.B1a.Defs

/-!
# Auxiliary lemmas for the Laurent collar (node N3 of the `B1a` conformal-map route)

`laurent_collar` states that the Laurent polynomial `Γ = laurentPoly N a` of a trigonometric loop
`v = trigPoly N a` is injective with nonvanishing derivative on a thin inversion-symmetric annulus
`annulus ρ = {ρ < ‖w‖ < ρ⁻¹}`.

This file collects the analytic facts about `laurentPoly` (identity on the circle, derivative formula,
continuity of `deriv`, analyticity, local injectivity) and two elementary metric lemmas about
`annulus`.  The compactness argument itself lives in `laurent_collar.lean`.
-/

open Complex Set Metric Filter
open scoped ContDiff Real Topology BigOperators

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B1a

/-! ## `Γ(e^{it}) = v(t)` -/

/-- On the unit circle the Laurent polynomial agrees with the trigonometric polynomial. -/
theorem laurentPoly_exp (N : ℕ) (a : ℤ → ℂ) (t : ℝ) :
    laurentPoly N a (Complex.exp (t * I)) = trigPoly N a t := by
  simp only [laurentPoly, trigPoly]
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  rw [← Complex.exp_int_mul]
  congr 1
  ring

/-! ## The derivative of a Laurent polynomial -/

/-- The derivative of a Laurent polynomial at a nonzero point. -/
theorem hasDerivAt_laurentPoly (N : ℕ) (a : ℤ → ℂ) {w : ℂ} (hw : w ≠ 0) :
    HasDerivAt (laurentPoly N a)
      (∑ n ∈ Finset.Icc (-(N : ℤ)) N, a n * (n : ℂ) * w ^ (n - 1)) w := by
  unfold laurentPoly
  convert (HasDerivAt.sum (𝕜 := ℂ) (F := ℂ) (x := w) (u := Finset.Icc (-(N : ℤ)) N)
      (A := fun n y => a n * y ^ n)
      (A' := fun n => a n * (n : ℂ) * w ^ (n - 1)) ?_) using 1
  · ext y; simp only [Finset.sum_apply]
  · intro n _
    simpa only [mul_assoc] using (hasDerivAt_zpow n w (Or.inl hw)).const_mul (a n)

/-- Value of the derivative of a Laurent polynomial at a nonzero point. -/
theorem deriv_laurentPoly (N : ℕ) (a : ℤ → ℂ) {w : ℂ} (hw : w ≠ 0) :
    deriv (laurentPoly N a) w =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) N, a n * (n : ℂ) * w ^ (n - 1) :=
  (hasDerivAt_laurentPoly N a hw).deriv

/-- A Laurent polynomial is continuous at every nonzero point. -/
theorem continuousAt_laurentPoly (N : ℕ) (a : ℤ → ℂ) {w : ℂ} (hw : w ≠ 0) :
    ContinuousAt (laurentPoly N a) w :=
  (hasDerivAt_laurentPoly N a hw).continuousAt

/-- The derivative of a Laurent polynomial is continuous at every nonzero point. -/
theorem continuousAt_deriv_laurentPoly (N : ℕ) (a : ℤ → ℂ) {w : ℂ} (hw : w ≠ 0) :
    ContinuousAt (deriv (laurentPoly N a)) w := by
  have hcont : ContinuousAt
      (fun y : ℂ => ∑ n ∈ Finset.Icc (-(N : ℤ)) N, a n * (n : ℂ) * y ^ (n - 1)) w :=
    tendsto_finsetSum _ fun n _ =>
      (continuousAt_zpow₀ w (n - 1) (Or.inl hw)).const_mul (a n * (n : ℂ))
  refine hcont.congr ?_
  filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using hw)] with y hy
  exact (deriv_laurentPoly N a (by simpa using hy)).symm

/-! ## Analyticity and local injectivity -/

/-- A Laurent polynomial is analytic away from the origin. -/
theorem analyticOn_laurentPoly (N : ℕ) (a : ℤ → ℂ) :
    AnalyticOn ℂ (laurentPoly N a) {0}ᶜ := by
  refine DifferentiableOn.analyticOn ?_ isOpen_compl_singleton
  intro w hw
  exact (hasDerivAt_laurentPoly N a (by simpa using hw)).differentiableAt.differentiableWithinAt

/-- A Laurent polynomial is analytic at every nonzero point. -/
theorem analyticAt_laurentPoly (N : ℕ) (a : ℤ → ℂ) {w : ℂ} (hw : w ≠ 0) :
    AnalyticAt ℂ (laurentPoly N a) w :=
  (analyticOn_laurentPoly N a).analyticAt (isOpen_compl_singleton.mem_nhds (by simpa using hw))

/-- A holomorphic function with nonvanishing derivative is locally injective. -/
theorem exists_nhds_injOn_of_analyticAt {f : ℂ → ℂ} {z : ℂ} (hz : AnalyticAt ℂ f z)
    (h : deriv f z ≠ 0) : ∃ U ∈ 𝓝 z, Set.InjOn f U := by
  have hev := hz.hasStrictDerivAt.eventually_left_inverse h
  rw [Filter.eventually_iff_exists_mem] at hev
  obtain ⟨U, hU, hUm⟩ := hev
  exact ⟨U, hU, fun x hx y hy hxy => by
    have hx' := hUm x hx
    have hy' := hUm y hy
    rw [hxy] at hx'
    exact hx'.symm.trans hy'⟩

/-- A Laurent polynomial is locally injective at every point where its derivative does not vanish. -/
theorem exists_nhds_injOn_laurentPoly (N : ℕ) (a : ℤ → ℂ) {z : ℂ} (hz : z ≠ 0)
    (hdz : deriv (laurentPoly N a) z ≠ 0) :
    ∃ U ∈ 𝓝 z, Set.InjOn (laurentPoly N a) U :=
  exists_nhds_injOn_of_analyticAt (analyticAt_laurentPoly N a hz) hdz

/-! ## Elementary facts about `annulus` -/

/-- The annuli are nested: a larger `ρ` gives a smaller annulus. -/
theorem annulus_mono {ρ ρ' : ℝ} (h0 : 0 < ρ) (h : ρ ≤ ρ') : annulus ρ' ⊆ annulus ρ := by
  intro w hw
  obtain ⟨h1, h2⟩ := hw
  exact ⟨lt_of_le_of_lt h h1, lt_of_lt_of_le h2 (inv_anti₀ h0 h)⟩

/-- Points of `annulus ρ` are within `max (1 - ρ) (ρ⁻¹ - 1)` of the unit circle. -/
theorem abs_norm_sub_one_lt_max_of_mem_annulus {ρ : ℝ} {w : ℂ}
    (hw : w ∈ annulus ρ) : |‖w‖ - 1| < max (1 - ρ) (ρ⁻¹ - 1) := by
  obtain ⟨h1, h2⟩ := hw
  refine abs_lt.mpr ⟨?_, ?_⟩
  · have : 1 - ‖w‖ < max (1 - ρ) (ρ⁻¹ - 1) :=
      lt_of_lt_of_le (by linarith) (le_max_left _ _)
    linarith
  · exact lt_of_lt_of_le (by linarith) (le_max_right _ _)

/-- Every point of the unit circle is `e^{it}` for some real `t`. -/
theorem exists_exp_of_mem_sphere {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) :
    ∃ t : ℝ, Complex.exp (t * I) = z := by
  obtain ⟨t, ht⟩ := Circle.exp_surjective ⟨z, hz⟩
  exact ⟨t, by rw [← Circle.coe_exp t, congrArg Subtype.val ht]⟩

end Work.RPB.B1a
