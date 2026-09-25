import Mathlib
import Submission.Work.BourgainPlan.Oscillation.commons_deps

namespace Work.BourgainPlan.Oscillation

open MeasureTheory Finset
open scoped ENNReal
open Work.BourgainPlan.Oscillation

noncomputable section

/-!
# Trigonometric polynomials are dense in `L²((0,1])`

The main result of this file, `trigP_dense`, states that every `h ∈ L²(μ₀₁)` (`μ₀₁` being
Lebesgue measure restricted to `(0,1]`) can be `L²`-approximated, to arbitrary accuracy, by a
trigonometric polynomial `Lacunary.trigP s f`.

The proof goes through the unit circle `AddCircle 1 = ℝ/ℤ`: pushing `h` forward along the
(measure preserving) quotient map `ℝ → AddCircle 1` gives an `L²` function `F` on the circle,
and Mathlib's completeness of the Fourier system on the circle
(`span_fourierLp_closure_eq_top`) provides finite linear combinations of the characters
`fourier n` which approximate `F`.  Pulling back to `(0,1]` gives the trigonometric polynomial. -/

/-- From a `HasSum` one can extract a finite partial sum which is within `δ` of the sum.
This is the (only) passage from the convergence of the Fourier series of an `L²` function on the
circle to the existence of a *finite* trigonometric polynomial approximating it. -/
lemma exists_finset_dist_lt {ι E : Type*} [NormedAddCommGroup E] {f : ι → E} {a : E}
    (h : HasSum f a) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s : Finset ι, dist (∑ i ∈ s, f i) a < δ := by
  have h2 : ∀ᶠ s : Finset ι in Filter.atTop, dist (∑ i ∈ s, f i) a < δ :=
    h.eventually (Metric.ball_mem_nhds a hδ)
  obtain ⟨s, hs⟩ := Filter.mem_atTop_sets.mp h2
  exact ⟨s, hs s (le_refl s)⟩

/-- **Density of trigonometric polynomials on the circle.**  For `F ∈ L²(AddCircle 1)` and any
`δ > 0` there are a finite set `s : Finset ℤ` and coefficients `c`, vanishing outside `s`, with
`eLpNorm (F - ∑_{n ∈ s} c n · fourier n) 2 ≤ δ`. -/
lemma circle_trigPoly_density (F : AddCircle (1:ℝ) → ℂ)
    (hF : MemLp F 2 (AddCircle.haarAddCircle (T := 1)))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (s : Finset ℤ) (c : ℤ → ℂ), (∀ n, n ∉ s → c n = 0) ∧
      eLpNorm (fun x => F x - ∑ n ∈ s, c n * (fourier (T := 1) n) x) 2
          (AddCircle.haarAddCircle (T := 1)) ≤ ENNReal.ofReal δ := by
  classical
  set x : Lp ℂ 2 (AddCircle.haarAddCircle (T := 1)) := hF.toLp F with hxdef
  -- the Fourier series of `x` sums to `x`, hence a finite partial sum is within `δ`
  obtain ⟨s, hs⟩ := exists_finset_dist_lt (hasSum_fourier_series_L2 (T := 1) x) hδ
  set c : ℤ → ℂ := fun n => if n ∈ s then fourierCoeff (x : AddCircle (1:ℝ) → ℂ) n else 0
    with hcdef
  have hc : ∀ n, n ∉ s → c n = 0 := by intro n hn; simp [hcdef, hn]
  refine ⟨s, c, hc, ?_⟩
  -- the corresponding continuous (and hence `L²`) function
  set P : C(AddCircle (1:ℝ), ℂ) := ∑ n ∈ s, c n • fourier (T := 1) n with hPdef
  have hLsum : (ContinuousMap.toLp 2 (AddCircle.haarAddCircle (T := 1)) ℂ) P
      = ∑ n ∈ s, c n • fourierLp (T := 1) 2 n := by
    rw [hPdef, map_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [map_smul]
  have hsum_eq : (∑ n ∈ s, c n • fourierLp (T := 1) 2 n)
      = ∑ n ∈ s, fourierCoeff (x : AddCircle (1:ℝ) → ℂ) n • fourierLp (T := 1) 2 n := by
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [show c n = fourierCoeff (x : AddCircle (1:ℝ) → ℂ) n from by simp [hcdef, hn]]
  have hdist : ‖x - (ContinuousMap.toLp 2 (AddCircle.haarAddCircle (T := 1)) ℂ) P‖ < δ := by
    rw [hLsum, hsum_eq, norm_sub_rev]
    simpa [dist_eq_norm] using hs
  have h1 : eLpNorm (x - (ContinuousMap.toLp 2 (AddCircle.haarAddCircle (T := 1)) ℂ) P) 2
        (AddCircle.haarAddCircle (T := 1)) ≤ ENNReal.ofReal δ := by
    rw [← Lp.enorm_def, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (le_of_lt hdist)
  have h3 : (x - (ContinuousMap.toLp 2 (AddCircle.haarAddCircle (T := 1)) ℂ) P)
      =ᵐ[AddCircle.haarAddCircle (T := 1)]
      (fun z => F z - ∑ n ∈ s, c n * (fourier (T := 1) n) z) := by
    filter_upwards [MemLp.coeFn_toLp hF,
      ContinuousMap.coeFn_toLp (p := 2) (μ := AddCircle.haarAddCircle (T := 1)) (𝕜 := ℂ) P,
      Lp.coeFn_sub x ((ContinuousMap.toLp 2 (AddCircle.haarAddCircle (T := 1)) ℂ) P)]
      with z hz1 hz2 hz3
    rw [hz3, Pi.sub_apply, hz1, hz2, hPdef]
    simp
  rwa [eLpNorm_congr_ae h3] at h1

/-- The characters `fourier n` on the circle, evaluated at `θ ∈ ℝ`, are the exponentials
`e^{2πinθ}` appearing in `Lacunary.trigP`. -/
lemma fourier_eq_trig (s : Finset ℤ) (c : ℤ → ℂ) (θ : ℝ) :
    (∑ n ∈ s, c n * (fourier (T := 1) n) (θ : AddCircle (1:ℝ))) = Lacunary.trigP s c θ := by
  rw [Lacunary.trigP]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [fourier_coe_apply]
  simp

/-- **Trigonometric polynomials are dense in `L²(μ₀₁)`.**  For every `h ∈ L²(μ₀₁)` and every
`ε > 0` there is a finitely supported sequence `f` with `∫⁻ ‖h - trigP s f‖² dμ₀₁ ≤ ε`. -/
theorem trigP_dense (h : ℝ → ℂ) (hh : MemLp h 2 Lacunary.mu01) (ε : ℝ) (hε : 0 < ε) :
    ∃ (s : Finset ℤ) (f : ℤ → ℂ), (∀ n, n ∉ s → f n = 0) ∧
      (∫⁻ θ : ℝ, ‖h θ - Lacunary.trigP s f θ‖ₑ ^ (2 : ℝ) ∂Lacunary.mu01)
        ≤ ENNReal.ofReal ε := by
  -- pick `δ > 0` with `δ ^ 2 ≤ ε`
  obtain ⟨δ, hδ0, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ^ 2 ≤ ε :=
    ⟨Real.sqrt ε, Real.sqrt_pos.mpr hε, by rw [Real.sq_sqrt hε.le]⟩
  -- push `h` to the circle
  set F : AddCircle (1:ℝ) → ℂ := AddCircle.liftIoc 1 0 h with hFdef
  have hF : MemLp F 2 (AddCircle.haarAddCircle (T := 1)) := by
    have h1 : MemLp h 2 (volume.restrict (Set.Ioc (0:ℝ) (0 + 1))) := by
      simpa [Lacunary.mu01] using hh
    have h2 : MemLp (AddCircle.liftIoc (1:ℝ) 0 h) 2 (AddCircle.haarAddCircle (T := 1)) :=
      (MemLp.memLp_liftIoc (T := 1) (t := 0) h1).haarAddCircle
    rwa [hFdef]
  obtain ⟨s, c, hc, hbound⟩ := circle_trigPoly_density F hF hδ0
  refine ⟨s, c, hc, ?_⟩
  -- the interval `(0,1]` carries the Haar measure of the circle
  have hvol : (AddCircle.haarAddCircle (T := 1)) = volume := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]; simp
  -- transfer the integral to the circle
  have hkey : (∫⁻ θ : ℝ, ‖h θ - Lacunary.trigP s c θ‖ₑ ^ (2 : ℝ) ∂Lacunary.mu01)
      = ∫⁻ x : AddCircle (1:ℝ),
          ‖F x - ∑ n ∈ s, c n * (fourier (T := 1) n) x‖ₑ ^ (2:ℝ)
            ∂AddCircle.haarAddCircle (T := 1) := by
    rw [hvol]
    rw [← AddCircle.lintegral_preimage (T := 1) 0
      (fun x : AddCircle (1:ℝ) =>
        ‖F x - ∑ n ∈ s, c n * (fourier (T := 1) n) x‖ₑ ^ (2:ℝ))]
    simp only [Lacunary.mu01, zero_add]
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    rw [hFdef, AddCircle.liftIoc_coe_apply (by simpa using hθ), fourier_eq_trig]
  have hpow : (eLpNorm (fun x => F x - ∑ n ∈ s, c n * (fourier (T := 1) n) x) 2
        (AddCircle.haarAddCircle (T := 1))) ^ (2:ℝ)
      = ∫⁻ x : AddCircle (1:ℝ),
          ‖F x - ∑ n ∈ s, c n * (fourier (T := 1) n) x‖ₑ ^ (2:ℝ)
            ∂AddCircle.haarAddCircle (T := 1) :=
    eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num)
      (hF.aestronglyMeasurable.sub (Continuous.aestronglyMeasurable
        (continuous_finset_sum _ (fun n _ => continuous_const.mul (fourier (T := 1) n).continuous))))
  calc (∫⁻ θ : ℝ, ‖h θ - Lacunary.trigP s c θ‖ₑ ^ (2 : ℝ) ∂Lacunary.mu01)
      = ∫⁻ x : AddCircle (1:ℝ),
          ‖F x - ∑ n ∈ s, c n * (fourier (T := 1) n) x‖ₑ ^ (2:ℝ)
            ∂AddCircle.haarAddCircle (T := 1) := hkey
    _ = (eLpNorm (fun x => F x - ∑ n ∈ s, c n * (fourier (T := 1) n) x) 2
          (AddCircle.haarAddCircle (T := 1))) ^ (2:ℝ) := hpow.symm
    _ ≤ (ENNReal.ofReal δ) ^ (2:ℝ) := ENNReal.rpow_le_rpow hbound (by norm_num)
    _ = ENNReal.ofReal (δ^2) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hδ0.le (by norm_num), Real.rpow_two]
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hδε

end

end Work.BourgainPlan.Oscillation
