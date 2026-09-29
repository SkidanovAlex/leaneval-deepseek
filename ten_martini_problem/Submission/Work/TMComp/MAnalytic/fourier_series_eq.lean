import Mathlib
import Submission.Work.TMComp.MAnalytic.fourierCoeff_decay
import Submission.Work.TMComp.MAnalytic.fourier_series_analytic
import Submission.Work.TMComp.MAnalytic.addCircle_fourier_expansion
import Submission.Work.TMComp.MAnalytic.summable_int_exp_neg_abs

/-!
# Fourier expansion of a `1`-periodic function holomorphic in a strip

Let `g : ℂ → ℂ` be holomorphic on the strip `S_δ = {z : ℂ | |z.im| < δ}` (`δ > 0`),
`1`-periodic and bounded by `B` on `S_δ`.  Then for every `z ∈ S_δ` the Fourier series of `g`
converges to `g z`:

`g z = ∑'_k ĉ_k · exp (2π i k z)`,  `ĉ_k = ∫_0^1 g t · exp (-2π i k t) dt`.

The proof combines three independent ingredients (proved in sibling modules of this
directory):

* `fourierCoeff_decay`: the coefficients decay like `‖ĉ_k‖ ≤ B · exp (-2π |k| r)` for every
  `0 < r < δ` (shift the contour to `Im = ±r`);
* `addCircle_fourier_expansion`: Fourier inversion for a continuous periodic function whose
  Fourier coefficients are summable (Mathlib's circle Fourier theory);
* `fourier_series_analytic`: if `‖c k‖ ≤ B · exp (-2π |k| ρ)` then `∑_k c k · exp (2π i k z)`
  is holomorphic on the strip `{|z.im| < ρ}` (Weierstrass, locally uniform convergence).

These give the identity on the real axis; the identity theorem (`AnalyticOnNhd` uniqueness)
extends it to the whole strip.
-/

namespace Work.TMComp.MAnalytic

open Filter
open scoped Topology

/-- The horizontal strip `{z : ℂ | |z.im| < δ}` is convex, hence preconnected. -/
theorem convex_strip (δ : ℝ) : Convex ℝ {z : ℂ | |z.im| < δ} := by
  have h : {z : ℂ | |z.im| < δ} = Complex.imCLM ⁻¹' Set.Ioo (-δ) δ := by
    ext z
    simp [abs_lt]
  rw [h]
  exact (convex_Ioo _ _).linear_preimage Complex.imCLM.toLinearMap

theorem fourier_series_eq {δ : ℝ} (hδ : 0 < δ) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g {x : ℂ | |x.im| < δ}) (hper : ∀ x, g (x + 1) = g x) {B : ℝ}
    (hB : ∀ x, |x.im| < δ → ‖g x‖ ≤ B) :
    ∀ x : ℂ, |x.im| < δ →
      g x = ∑' k : ℤ,
        (∫ t in (0 : ℝ)..1, g (t : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ) * (t : ℂ))))
          * Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * x) := by
  -- the Fourier coefficients of `g`
  let c : ℤ → ℂ := fun k =>
    ∫ t in (0 : ℝ)..1, g (t : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ) * (t : ℂ)))
  have hB0 : 0 ≤ B := by
    have h1 := hB 0 (by simpa using hδ)
    have h2 : (0 : ℝ) ≤ ‖g 0‖ := norm_nonneg _
    linarith
  -- exponential decay of the Fourier coefficients
  have hdec : ∀ (k : ℤ) (r : ℝ), 0 < r → r < δ →
      ‖c k‖ ≤ B * Real.exp (-(2 * Real.pi * |(k : ℝ)| * r)) :=
    fun k r hr hrδ => fourierCoeff_decay hδ hg hper hB hr hrδ k
  -- the Fourier series, viewed as a function on the whole plane
  let F : ℂ → ℂ := fun z => ∑' k : ℤ, c k * Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) * z)
  -- `F` is holomorphic on the strip
  have hF : AnalyticOnNhd ℂ F {z : ℂ | |z.im| < δ} := by
    intro z hz
    obtain ⟨r, hzr, hrδ⟩ := exists_between (show |z.im| < δ from hz)
    have hr : 0 < r := lt_of_le_of_lt (abs_nonneg _) hzr
    have h := fourier_series_analytic (c := c) (B := B) (ρ := r) hB0 hr (fun k => hdec k r hr hrδ)
    exact h z hzr
  -- on the real axis the Fourier series converges to `g`
  have hreal : ∀ t : ℝ, F (t : ℂ) = g (t : ℂ) := by
    intro t
    obtain ⟨r, hr, hrδ⟩ : ∃ r : ℝ, 0 < r ∧ r < δ := ⟨δ / 2, by linarith, by linarith⟩
    have hsum : Summable (fun k : ℤ =>
        ∫ s in (0 : ℝ)..1, g (s : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * (k : ℂ) * (s : ℂ)))) := by
      refine Summable.of_norm_bounded
        (g := fun k : ℤ => B * Real.exp (-(2 * Real.pi * r * |(k : ℝ)|))) ?_ ?_
      · simpa using summable_int_exp_neg_abs B (2 * Real.pi * r) (by positivity)
      · intro k
        rw [show 2 * Real.pi * r * |(k : ℝ)| = 2 * Real.pi * |(k : ℝ)| * r by ring]
        exact hdec k r hr hrδ
    have hcont : Continuous fun t : ℝ => g (t : ℂ) :=
      hg.continuousOn.comp_continuous Complex.continuous_ofReal (fun t => by simpa using hδ)
    have hper' : ∀ x : ℝ, (fun t : ℝ => g (t : ℂ)) (x + 1) = (fun t : ℝ => g (t : ℂ)) x := by
      intro x
      simp only
      rw [Complex.ofReal_add, Complex.ofReal_one]
      exact hper (x : ℂ)
    exact (addCircle_fourier_expansion hcont hper' hsum t).symm
  -- the identity theorem extends the identity to the strip
  have hpre : IsPreconnected {z : ℂ | |z.im| < δ} := (convex_strip δ).isPreconnected
  have h0 : (0 : ℂ) ∈ {z : ℂ | |z.im| < δ} := by simpa using hδ
  have hclos : (0 : ℂ) ∈ closure ({z : ℂ | F z = g z} \ {0}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    set u : ℝ := min (1 / 2) (ε / 2) with hu
    have hu0 : 0 < u := lt_min (by norm_num) (by linarith)
    have hult : u < ε := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    refine ⟨(u : ℂ), ⟨hreal u, ?_⟩, ?_⟩
    · simp only [Set.mem_singleton_iff]
      intro hc
      have hz : u = 0 := by
        have h := congrArg (fun z : ℂ => z.re) hc
        simpa using h
      linarith
    · have hd : dist (0 : ℂ) ((u : ℝ) : ℂ) = u := by
        rw [← Complex.ofReal_zero, Complex.isometry_ofReal.dist_eq, Real.dist_eq,
          zero_sub, abs_neg, abs_of_pos hu0]
      rw [hd]
      exact hult
  have heq := AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure hF hg hpre h0 hclos
  intro x hx
  exact (heq hx).symm

end Work.TMComp.MAnalytic
