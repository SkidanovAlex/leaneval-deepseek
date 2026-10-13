import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllSol.FlatFT.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.FlatFT

open MeasureTheory Set Filter
open scoped Real Topology

noncomputable section

/-- The Fourier kernel `t ↦ exp (-(2π i ξ t))` has complex norm one. -/
private lemma norm_exp_fourierKernel (ξ t : ℝ) :
    ‖Complex.exp (-(2 * Real.pi * Complex.I * ξ * t))‖ = 1 := by
  have h : -(2 * Real.pi * Complex.I * ξ * t)
      = ((↑(-(2 * Real.pi * ξ * t)) : ℂ)) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- For a fixed angle `θ` in the open interval, the `t`-slice of `φ` is continuous on `ℝ`
(this only needs the joint continuity at points whose second coordinate is in the open interval,
whereas the values of `φ t θ` for `θ ∉ (0, π/2)` are irrelevant). -/
private lemma continuous_slice_fst {φ : ℝ → ℝ → ℝ}
    (hφ : ContinuousOn (Function.uncurry φ) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Continuous fun t : ℝ => φ t θ := by
  rw [continuous_iff_continuousAt]
  rintro s
  have hmem : (s, θ) ∈ Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2) := ⟨trivial, hθ⟩
  have h1 : ContinuousAt (Function.uncurry φ) (s, θ) :=
    (hφ.continuousWithinAt hmem).continuousAt
      (IsOpen.mem_nhds (isOpen_univ.prod isOpen_Ioo) hmem)
  exact h1.comp (x := s) (f := fun y : ℝ => (y, θ))
    (continuousAt_id.prodMk continuousAt_const)

/-- For a fixed `t`, the map `q ↦ φ t q.2` is continuous on the half-strip. -/
private lemma continuousOn_slice_snd {φ : ℝ → ℝ → ℝ}
    (hφ : ContinuousOn (Function.uncurry φ) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (t : ℝ) :
    ContinuousOn (fun q : ℝ × ℝ => φ t q.2) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
  hφ.comp ((continuous_const.prodMk continuous_snd).continuousOn)
    (fun _ hq => ⟨trivial, hq.2⟩)

/-- Joint continuity at a point `(ξ, θ)` with `θ ∈ (0, π/2)` of the `t`-Fourier slice of a
function `φ` which is continuous on the half-strip and uniformly compactly supported in `t`.

Proof: dominated convergence (`MeasureTheory.continuousAt_of_dominated`) with respect to the
restricted measure on the support interval `[-M, M]`.  The dominating function is the constant
`K := sup_{|t| ≤ M, θ' ∈ [θ/2, (θ+π/2)/2]} |φ t θ'|`, which exists because the corresponding
product of compact intervals lies inside the half-strip on which `φ` is continuous.  The
integrand vanishes off the support interval, whence the restricted integral is the slice. -/
private theorem continuousAt_slice {φ : ℝ → ℝ → ℝ}
    (hφ : ContinuousOn (Function.uncurry φ) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hsupp : ∃ M : ℝ, 0 ≤ M ∧ ∀ t θ : ℝ, M < |t| → φ t θ = 0)
    {ξ θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ContinuousAt (fun p : ℝ × ℝ => slice φ p.1 p.2) (ξ, θ) := by
  obtain ⟨M, hM, hsuppM⟩ := hsupp
  have hθlo : 0 < θ / 2 := by linarith [hθ.1]
  have hθhi : (θ + Real.pi / 2) / 2 < Real.pi / 2 := by linarith [hθ.2]
  have hθ1 : θ / 2 < θ := by linarith [hθ.1]
  have hθ2 : θ < (θ + Real.pi / 2) / 2 := by linarith [hθ.2]
  -- a point outside the support interval is beyond the support radius
  have habs : ∀ t : ℝ, t ∉ Set.Icc (-M) M → M < |t| := by
    intro t ht
    by_contra hcon
    exact ht (abs_le.mp (le_of_not_gt hcon))
  -- uniform bound for the angular parameters in a compact sub-interval
  have hsub : Set.Icc (-M) M ×ˢ Set.Icc (θ / 2) ((θ + Real.pi / 2) / 2)
      ⊆ Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2) := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    exact ⟨trivial, ⟨lt_of_lt_of_le hθlo hb.1, lt_of_le_of_lt hb.2 hθhi⟩⟩
  obtain ⟨K₀, hK₀⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hφ.mono hsub)
  set K : ℝ := max K₀ 0 with hKdef
  have hK0 : 0 ≤ K := le_max_right K₀ 0
  have hK : ∀ t ∈ Set.Icc (-M) M, ∀ θ' ∈ Set.Icc (θ / 2) ((θ + Real.pi / 2) / 2),
      ‖φ t θ'‖ ≤ K :=
    fun t ht θ' hθ' => le_trans (hK₀ (t, θ') ⟨ht, hθ'⟩) (le_max_left K₀ 0)
  -- the relevant neighbourhoods of the parameter point
  have hU : Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2) ∈ 𝓝 (ξ, θ) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod Filter.univ_mem (Ioo_mem_nhds hθ.1 hθ.2)
  have hU' : Set.univ ×ˢ Set.Ioo (θ / 2) ((θ + Real.pi / 2) / 2) ∈ 𝓝 (ξ, θ) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod Filter.univ_mem (Ioo_mem_nhds hθ1 hθ2)
  -- the integrand
  set F : ℝ × ℝ → ℝ → ℂ := fun q t =>
    (φ t q.2 : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * q.1 * t)) with hFdef
  -- dominated convergence for the restricted integral
  have hmain : ContinuousAt
      (fun q : ℝ × ℝ => ∫ t, F q t ∂(volume.restrict (Set.Icc (-M) M))) (ξ, θ) := by
    refine MeasureTheory.continuousAt_of_dominated (μ := volume.restrict (Set.Icc (-M) M))
      (F := F) (bound := fun _ : ℝ => K) ?_ ?_ ?_ ?_
    · -- a.e. strong measurability: the slices are continuous in `t`
      filter_upwards [hU] with q hq
      have h1 : Continuous fun t : ℝ => φ t q.2 := continuous_slice_fst hφ hq.2
      have h2 : Continuous fun t : ℝ =>
          Complex.exp (-(2 * Real.pi * Complex.I * q.1 * t)) := by fun_prop
      have hc : Continuous fun t : ℝ => F q t := by
        simp only [F]
        exact (Complex.continuous_ofReal.comp h1).mul h2
      exact hc.aestronglyMeasurable.mono_measure MeasureTheory.Measure.restrict_le_self
    · -- the pointwise domination by the constant `K`
      filter_upwards [hU'] with q hq
      filter_upwards with t
      by_cases ht : t ∈ Set.Icc (-M) M
      · have hb : ‖φ t q.2‖ ≤ K := hK t ht q.2 ⟨le_of_lt hq.2.1, le_of_lt hq.2.2⟩
        calc ‖F q t‖
            = ‖(φ t q.2 : ℂ)‖ * ‖Complex.exp (-(2 * Real.pi * Complex.I * q.1 * t))‖ := by
              simp only [F, norm_mul]
          _ = ‖φ t q.2‖ * 1 := by rw [Complex.norm_real, norm_exp_fourierKernel]
          _ ≤ K := by rw [mul_one]; exact hb
      · have hz : φ t q.2 = 0 := hsuppM t q.2 (habs t ht)
        rw [show F q t = 0 by simp only [F, hz, Complex.ofReal_zero, zero_mul]]
        simpa using hK0
    · -- the dominating constant is integrable on a finite interval
      exact MeasureTheory.integrableOn_const (s := Set.Icc (-M) M) (C := K)
        (isCompact_Icc.measure_lt_top (μ := volume)).ne enorm_ne_top
    · -- a.e. continuity in the parameter
      filter_upwards with t
      have h1 : ContinuousAt (fun q : ℝ × ℝ => (φ t q.2 : ℂ)) (ξ, θ) :=
        ContinuousAt.comp (x := (ξ, θ)) (f := fun q : ℝ × ℝ => φ t q.2)
          Complex.continuous_ofReal.continuousAt
          ((continuousOn_slice_snd hφ t).continuousAt hU)
      have h2 : ContinuousAt
          (fun q : ℝ × ℝ => Complex.exp (-(2 * Real.pi * Complex.I * q.1 * t))) (ξ, θ) := by
        fun_prop
      exact h1.mul h2
  -- the restricted integral is the slice, since the integrand vanishes off the support interval
  refine hmain.congr ?_
  filter_upwards [hU] with q _
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Icc (-M) M)
    (f := F q) (fun t ht => by
      have hz : φ t q.2 = 0 := hsuppM t q.2 (habs t ht)
      simp only [F, hz, Complex.ofReal_zero, zero_mul])]
  simp only [slice, hFdef]

theorem continuousOn_slice_joint {φ : ℝ → ℝ → ℝ}
    (hφ : ContinuousOn (Function.uncurry φ) (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hsupp : ∃ M : ℝ, 0 ≤ M ∧ ∀ t θ : ℝ, M < |t| → φ t θ = 0) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllSol.FlatFT.slice φ p.1 p.2)
      (Set.univ ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  intro p hp
  obtain ⟨ξ, θ⟩ := p
  simp only [Set.mem_prod, Set.mem_univ, true_and] at hp
  exact (continuousAt_slice hφ hsupp hp).continuousWithinAt

end

end Work.FTS.EllSol.FlatFT
