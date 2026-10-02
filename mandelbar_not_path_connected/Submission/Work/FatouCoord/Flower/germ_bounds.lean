import Mathlib
import Submission.Work.FatouCoord.Flower

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Normal form of a simple parabolic germ

Given an entire `F : ℂ → ℂ` with a **simple parabolic fixed point** at `z₀` — that is
`F z₀ = z₀`, `deriv F z₀ = 1` and `iteratedDeriv 2 F z₀ ≠ 0` — this file produces a
`ParabolicBounds` germ in the standard normal form `z + z ^ 2 * h z` with `h 0 = 1`.

The construction is the classical one: the Taylor expansion of `F` at `z₀` reads
`F (z₀ + w) = z₀ + w + c₂ w² + O(w³)` with `c₂ = F''(z₀)/2 ≠ 0`, so the affine change of
variables `w = lam * u` with `lam = 2 / F''(z₀)` turns the germ into
`u ↦ u + u² + O(u³)`.  Dividing the cubic remainder by `u²` gives the required `h`.

The only non-elementary ingredient is Mathlib's analytic Taylor theorem
`AnalyticAt.exists_eq_sum_add_pow_mul`, which exhibits the remainder of the Taylor
expansion of an analytic function as `z ^ n` times a function analytic at `0`.
-/

namespace Work.FatouCoord.Flower

open Work.FatouCoord Metric Set
open scoped Topology
open Filter

/-- Derivative of `u ↦ g (a + b * u)` for a differentiable `g`. -/
private lemma deriv_comp_affine_germ {g : ℂ → ℂ} (hg : Differentiable ℂ g) (a b : ℂ) :
    deriv (fun u : ℂ => g (a + b * u)) = fun u : ℂ => deriv g (a + b * u) * b := by
  funext u
  have h1 : deriv (fun v : ℂ => a + b * v) u = b := by
    rw [deriv_const_add, deriv_const_mul _ (by fun_prop : DifferentiableAt ℂ (fun v : ℂ => v) u),
      deriv_id'']
    simp
  change deriv (g ∘ fun v : ℂ => a + b * v) u = deriv g (a + b * u) * b
  rw [deriv_comp u (hg.differentiableAt) (by fun_prop), h1]

/-- An `Eventually` statement at `0 : ℂ` holds on a ball of positive radius. -/
private lemma exists_pos_ball_of_eventually {P : ℂ → Prop}
    (h : ∀ᶠ z : ℂ in 𝓝 (0 : ℂ), P z) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z‖ < r → P z := by
  rcases Metric.eventually_nhds_iff.mp h with ⟨r, hr, h⟩
  exact ⟨r, hr, fun z hz => h (y := z) (by simpa only [dist_zero_right] using hz)⟩

/-- **Normal form of a simple parabolic germ.**  An entire map `F` with
`F z₀ = z₀`, `deriv F z₀ = 1` and `iteratedDeriv 2 F z₀ ≠ 0` is, after the linear change of
variables `w = z₀ + lam * u`, the germ `f u = (F (z₀ + lam * u) - z₀) / lam` of the form
`f u = u + u ^ 2 * h u` with `h 0 = 1`, and it satisfies the quantitative hypotheses
`ParabolicBounds` of the Fatou–Leau construction. -/
theorem germ_bounds {F : ℂ → ℂ} {z₀ : ℂ} (hF : Differentiable ℂ F) (h0 : F z₀ = z₀) (h1 : deriv F z₀ = 1) (h2 : iteratedDeriv 2 F z₀ ≠ 0) : ∃ (f h : ℂ → ℂ) (a : ℂ) (r A A' : ℝ) (lam : ℂ), lam ≠ 0 ∧ ParabolicBounds f h a r A A' ∧ ∀ u ∈ ball 0 r, f u = (F (z₀ + lam * u) - z₀) / lam := by
  -- `iteratedDeriv 2 F z₀` is the second derivative of `F` at `z₀`
  have h2' : deriv (deriv F) z₀ ≠ 0 := by
    have he : iteratedDeriv 2 F z₀ = deriv (deriv F) z₀ := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rwa [he] at h2
  -- the scaling making the quadratic coefficient of the germ equal to `1`
  let lam : ℂ := 2 / deriv (deriv F) z₀
  have hlam_ne : lam ≠ 0 := by
    simp only [lam]
    exact div_ne_zero two_ne_zero h2'
  have hlam_mul : deriv (deriv F) z₀ * lam = 2 := by
    simp only [lam]
    field_simp
  -- the germ itself
  let f : ℂ → ℂ := fun u => (F (z₀ + lam * u) - z₀) / lam
  have hf_diff : Differentiable ℂ f := by
    simp only [f]
    fun_prop
  have hf_deriv_eq : deriv f = fun u : ℂ => deriv F (z₀ + lam * u) := by
    simp only [f]
    funext u
    rw [deriv_div_const, deriv_sub_const, deriv_comp_affine_germ hF]
    exact mul_div_cancel_right₀ _ hlam_ne
  have hf_f0 : f 0 = 0 := by
    simp only [f]
    simp [h0]
  have hf_d1 : deriv f 0 = 1 := by
    rw [hf_deriv_eq]
    simp [h1]
  have hf_d2 : iteratedDeriv 2 f 0 = 2 := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, hf_deriv_eq,
      deriv_comp_affine_germ hF.deriv]
    simp only [mul_zero, add_zero]
    exact hlam_mul
  -- Taylor expansion of the germ to third order
  have hf_an : AnalyticAt ℂ f 0 := hf_diff.analyticAt 0
  obtain ⟨Fs, hFs_an, hFs_eq⟩ := hf_an.exists_eq_sum_add_pow_mul 3
  let h : ℂ → ℂ := fun u => 1 + u * Fs u
  have hh_an : AnalyticAt ℂ h 0 := by
    simp only [h]
    fun_prop
  -- the normal form `f z = z + z ^ 2 * h z`
  have hf_eq : ∀ z : ℂ, f z = z + z ^ 2 * h z := by
    intro z
    rw [hFs_eq z]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    simp only [iteratedDeriv_zero, iteratedDeriv_one, hf_f0, hf_d1, hf_d2]
    norm_num
    simp only [h]
    ring
  -- second order Taylor expansion of `h`, giving the bound `‖h z - 1 - a z‖ ≤ A ‖z‖²`
  obtain ⟨G, hG_an, hG_eq⟩ := hh_an.exists_eq_sum_add_pow_mul 2
  let a : ℂ := iteratedDeriv 1 h 0
  have hh_sub : ∀ z : ℂ, h z - 1 - a * z = z ^ 2 * G z := by
    intro z
    rw [hG_eq z]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, iteratedDeriv_zero]
    simp only [h, a]
    ring
  -- the four eventual bounds at `0`
  have hG_bound : ∀ᶠ z : ℂ in 𝓝 0, ‖G z‖ ≤ ‖G 0‖ + 1 := by
    have ht : Tendsto (fun z : ℂ => ‖G z‖) (𝓝 0) (𝓝 ‖G 0‖) := hG_an.continuousAt.norm
    have h2b := (tendsto_order.mp ht).2 (‖G 0‖ + 1) (by linarith)
    filter_upwards [h2b] with z hz using le_of_lt hz
  have hdh_bound : ∀ᶠ z : ℂ in 𝓝 0, ‖deriv h z‖ ≤ ‖deriv h 0‖ + 1 := by
    have ht : Tendsto (fun z : ℂ => ‖deriv h z‖) (𝓝 0) (𝓝 ‖deriv h 0‖) :=
      (hh_an.deriv).continuousAt.norm
    have h2b := (tendsto_order.mp ht).2 (‖deriv h 0‖ + 1) (by linarith)
    filter_upwards [h2b] with z hz using le_of_lt hz
  have hbnd : ∀ᶠ z : ℂ in 𝓝 0, ‖h z‖ ≤ 2 := by
    have ht : Tendsto (fun z : ℂ => ‖h z‖) (𝓝 0) (𝓝 ‖h 0‖) := hh_an.continuousAt.norm
    have h0h : ‖h 0‖ = 1 := by simp [h]
    have h2b := (tendsto_order.mp ht).2 2 (by rw [h0h]; norm_num)
    filter_upwards [h2b] with z hz using le_of_lt hz
  have hd : ∀ᶠ z : ℂ in 𝓝 0, DifferentiableAt ℂ h z :=
    hh_an.eventually_analyticAt.mono fun z hz => hz.differentiableAt
  have hall : ∀ᶠ z : ℂ in 𝓝 0,
      DifferentiableAt ℂ h z ∧ (‖h z‖ ≤ 2 ∧ ‖G z‖ ≤ ‖G 0‖ + 1 ∧ ‖deriv h z‖ ≤ ‖deriv h 0‖ + 1) :=
    hd.and (hbnd.and (hG_bound.and hdh_bound))
  obtain ⟨r, hr, hrall⟩ := exists_pos_ball_of_eventually hall
  refine ⟨f, h, a, r, ‖G 0‖ + 1, ‖deriv h 0‖ + 1, lam, hlam_ne, ?_, ?_⟩
  · refine ⟨hr, by positivity, by positivity, ?_, ?_, ?_, ?_, ?_⟩
    · intro z hz; exact hf_eq z
    · intro z hz
      exact (hrall z (by simpa [mem_ball_zero_iff] using hz)).1.differentiableWithinAt
    · intro z hz
      have hz' : ‖z‖ < r := by simpa [mem_ball_zero_iff] using hz
      have hb := (hrall z hz').2.2.1
      rw [hh_sub z, norm_mul, norm_pow]
      calc ‖z‖ ^ 2 * ‖G z‖ ≤ ‖z‖ ^ 2 * (‖G 0‖ + 1) :=
            mul_le_mul_of_nonneg_left hb (by positivity)
        _ = (‖G 0‖ + 1) * ‖z‖ ^ 2 := by ring
    · intro z hz
      exact (hrall z (by simpa [mem_ball_zero_iff] using hz)).2.1
    · intro z hz
      exact (hrall z (by simpa [mem_ball_zero_iff] using hz)).2.2.2
  · intro u hu; rfl

end Work.FatouCoord.Flower
