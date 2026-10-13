/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `θ`-slice Step-4 identity

`Work.FTS.EllipticEst.remov.Step4.slice_step4_identity` is the *identity* half of Step 4 of the
`H²` estimate of T. M. Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. 194 (3) 2021 (tex 931–953), in
one-dimensional (`θ`-slice) form.

Writing `σ(θ) = sin(2θ)^{2-γ}` for the weight of the top-order term, the pointwise relation

  `(L₀ u)'(θ) = -u'''(θ) + (tan θ·u)''(θ) - 6u'(θ)`

of `Work.FTS.EllipticEst.remov.slice_gprime_ident` (which holds on `(0, π/2)` because `g` agrees
there with `L₀ u`) multiplies by `-u'''(θ)·σ(θ)` into the *pointwise* identity

  `(u''')²σ = -(g'·u'''σ) + ((tan θ·u)''·u'''σ) - 6(u'·u'''σ)`,

and integrating over `Iθ = [0, π/2]` (only `0` is a point where the weight `σ` degenerates, and it
is a null set) gives

  `∫_θ (u''')²σ = -∫_θ g'·u'''σ + ∫_θ (tan θ·u)''·u'''σ - 6∫_θ u'·u'''σ`.

This is the starting point of the Step-4 chain: combined with the expansions
`u''' = sin θ·v'' - 4cos θ·v' + 5 sin θ·v - g'` and
`(tan θ·u)'' = sin θ·v'' + 2cos θ·v' - sin θ·v` (with `v = u/cos θ`) it produces the `A ≤ C·…`
bound of `Work.FTS.EllipticEst.remov.slice_step4`.

The measure-theoretic content is small: the two intervals `Iθ` and `(0, π/2)` differ by the
two-point null set `{0, π/2}`, so `volume.restrict Iθ = volume.restrict (0, π/2)`; on the open
interval all the functions involved (`u'`, `u'''`, `tan θ·u`, its two derivatives, `σ`) are
continuous, and `g'` agrees there with a continuous function, which supplies the a.e. strong
measurability that the dominated-convergence bookkeeping needs.

The purely measure-theoretic algebra (from `v = -α + β - 6δ` on a set, the four integrals
`∫v²κ`, `∫αvκ`, `∫βvκ`, `∫δvκ` split linearly) is isolated in
`Work.FTS.EllipticEst.remov.Step4.integral_sq_eq_of_rel`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.remov.Step4.integral_sq_eq_of_rel

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.Step4

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ### The null set: `[0, π/2]` versus `(0, π/2)` -/

/-- `[0, π/2]` and `(0, π/2)` agree up to a null set. -/
private lemma ae_eq_Icc_Ioo :
    (Set.Icc 0 (Real.pi / 2) : Set ℝ) =ᵐ[volume] Set.Ioo 0 (Real.pi / 2) := by
  rw [MeasureTheory.ae_eq_set]
  refine ⟨?_, ?_⟩
  · have hsub : Set.Icc 0 (Real.pi / 2) \ Set.Ioo 0 (Real.pi / 2) ⊆ ({0, Real.pi / 2} : Set ℝ) := by
      intro x hx
      simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_Ioo, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx ⊢
      rcases eq_or_lt_of_le hx.1.1 with h | h
      · exact Or.inl h.symm
      · refine Or.inr ?_
        by_contra hne
        exact hx.2 ⟨h, lt_of_le_of_ne hx.1.2 hne⟩
    have hnull : volume ({0, Real.pi / 2} : Set ℝ) = 0 :=
      (Set.Finite.insert (0 : ℝ) (Set.finite_singleton (Real.pi / 2))).measure_zero _
    exact MeasureTheory.measure_mono_null hsub hnull
  · have h0 : Set.Ioo 0 (Real.pi / 2) \ Set.Icc 0 (Real.pi / 2) = ∅ :=
      Set.sdiff_eq_empty.mpr Set.Ioo_subset_Icc_self
    rw [h0, MeasureTheory.measure_empty]

/-- Consequently `volume.restrict Iθ = volume.restrict (0, π/2)`. -/
private lemma restrict_Iθ_eq_Ioo :
    (volume.restrict Work.Spaces.Iθ : Measure ℝ)
      = volume.restrict (Set.Ioo 0 (Real.pi / 2)) := by
  simpa [Work.Spaces.Iθ] using MeasureTheory.Measure.restrict_congr_set ae_eq_Icc_Ioo

/-! ### The identity -/

theorem slice_step4_identity (γ : ℝ) (hγ : γ ≤ 2) {u g : ℝ → ℝ}
    (hu : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ)
    (hA : MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv u)) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ)
    (hD : MeasureTheory.IntegrableOn (fun θ => (deriv g θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ)
    (hC1 : MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ))
      = - (∫ θ in Work.Spaces.Iθ, deriv g θ * deriv (deriv (deriv u)) θ *
            Real.rpow (Real.sin (2 * θ)) (2 - γ))
        + (∫ θ in Work.Spaces.Iθ, deriv (deriv (fun t => Real.tan t * u t)) θ *
            deriv (deriv (deriv u)) θ * Real.rpow (Real.sin (2 * θ)) (2 - γ))
        - 6 * (∫ θ in Work.Spaces.Iθ, deriv u θ * deriv (deriv (deriv u)) θ *
            Real.rpow (Real.sin (2 * θ)) (2 - γ)) := by
  -- Work on the open interval, where all the functions involved are continuous.
  set s : Set ℝ := Set.Ioo 0 (Real.pi / 2) with hs_def
  have hsopen : IsOpen s := by rw [hs_def]; exact isOpen_Ioo
  have hsmeas : MeasurableSet s := hsopen.measurableSet
  have hset : (Work.Spaces.Iθ : Set ℝ) =ᵐ[volume] s := by
    rw [hs_def]; exact ae_eq_Icc_Ioo
  have hrestrict : (volume.restrict Work.Spaces.Iθ : Measure ℝ) = volume.restrict s := by
    rw [hs_def]; exact restrict_Iθ_eq_Ioo
  -- The weight `σ = sin(2θ)^{2-γ}` on the open interval.
  have hsinpos : ∀ θ ∈ s, 0 < Real.sin (2 * θ) := by
    intro θ hθ
    rw [hs_def] at hθ
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hκ0 : ∀ θ ∈ s, 0 ≤ Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
    fun θ hθ => Real.rpow_nonneg (le_of_lt (hsinpos θ hθ)) _
  have hκ1 : ∀ θ ∈ s, Real.rpow (Real.sin (2 * θ)) (2 - γ) ≤ 1 := by
    intro θ hθ
    exact Real.rpow_le_one (le_of_lt (hsinpos θ hθ)) (Real.sin_le_one _) (by linarith)
  have hmκ : AEStronglyMeasurable (fun θ => Real.rpow (Real.sin (2 * θ)) (2 - γ))
      (volume.restrict s) := by
    refine (ContinuousOn.rpow_const ?_ ?_).aestronglyMeasurable hsmeas
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    · intro θ hθ
      exact Or.inl (ne_of_gt (hsinpos θ hθ))
  -- The three `u`-derivatives and `(tan θ·u)''` are continuous on the open interval.
  have hT : ContDiffOn ℝ 0 (fun θ => deriv (deriv (deriv u)) θ) s := by
    have h1 : ContDiffOn ℝ 2 (deriv u) s := hu.deriv_of_isOpen hsopen (by norm_num)
    have h2 : ContDiffOn ℝ 1 (deriv (deriv u)) s := h1.deriv_of_isOpen hsopen (by norm_num)
    exact h2.deriv_of_isOpen hsopen (by norm_num)
  have hmv : AEStronglyMeasurable (fun θ => deriv (deriv (deriv u)) θ)
      (volume.restrict s) := hT.continuousOn.aestronglyMeasurable hsmeas
  have hU : ContinuousOn (fun θ => deriv u θ) s :=
    hu.continuousOn_deriv_of_isOpen hsopen (by norm_num)
  have hmδ : AEStronglyMeasurable (fun θ => deriv u θ) (volume.restrict s) :=
    hU.aestronglyMeasurable hsmeas
  have htu : ContDiffOn ℝ 2 (fun t => Real.tan t * u t) s := by
    intro θ hθ
    rw [hs_def] at hθ
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos],
        by linarith [hθ.2, Real.pi_pos]⟩)
    exact (((Real.contDiffAt_tan.mpr hcos).mul
      ((hu.contDiffAt (hsopen.mem_nhds hθ)).of_le (by norm_num))).contDiffWithinAt)
  have hβ : ContDiffOn ℝ 0 (fun θ => deriv (deriv (fun t => Real.tan t * u t)) θ) s := by
    have h1 : ContDiffOn ℝ 1 (deriv (fun t => Real.tan t * u t)) s :=
      htu.deriv_of_isOpen hsopen (by norm_num)
    exact h1.deriv_of_isOpen hsopen (by norm_num)
  have hmβ : AEStronglyMeasurable (fun θ => deriv (deriv (fun t => Real.tan t * u t)) θ)
      (volume.restrict s) := hβ.continuousOn.aestronglyMeasurable hsmeas
  -- `g'` agrees on `s` with the continuous function `-u''' + (tan θ·u)'' - 6u'`.
  have hmα : AEStronglyMeasurable (fun θ => deriv g θ) (volume.restrict s) := by
    have hF : ContinuousOn (fun θ => -deriv (deriv (deriv u)) θ
        + deriv (deriv (fun t => Real.tan t * u t)) θ - 6 * deriv u θ) s :=
      ((hT.continuousOn.neg).add hβ.continuousOn).sub (hU.const_mul 6)
    refine (hF.aestronglyMeasurable hsmeas).congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hsmeas] with θ hθ
    exact (slice_gprime_ident u g hu hode θ hθ).symm
  -- The pointwise relation on `s`, in the shape used by the integral lemma.
  have hrel : ∀ θ ∈ s, deriv (deriv (deriv u)) θ = -deriv g θ
      + deriv (deriv (fun t => Real.tan t * u t)) θ - 6 * deriv u θ := by
    intro θ hθ
    have h := slice_gprime_ident u g hu hode θ hθ
    linarith
  -- Integrability, transported from `Iθ` to the open interval.
  have hIv : IntegrableOn (fun θ => (deriv (deriv (deriv u)) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ)) s := by
    show MeasureTheory.Integrable _ (volume.restrict s)
    rw [← hrestrict]
    exact hA
  have hIα : IntegrableOn (fun θ => (deriv g θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ)) s := by
    show MeasureTheory.Integrable _ (volume.restrict s)
    rw [← hrestrict]
    exact hD
  have hU2 : IntegrableOn (fun θ => (deriv u θ) ^ 2) s := by
    show MeasureTheory.Integrable _ (volume.restrict s)
    rw [← hrestrict]
    exact hC1
  have hIδ : IntegrableOn (fun θ => (deriv u θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ)) s := by
    show MeasureTheory.Integrable _ (volume.restrict s)
    refine MeasureTheory.Integrable.mono' (g := fun θ => (deriv u θ) ^ 2) hU2
      ((hmδ.pow 2).mul hmκ) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hsmeas] with θ hθ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hκ0 θ hθ), abs_of_nonneg (sq_nonneg _)]
    nlinarith [hκ1 θ hθ, sq_nonneg (deriv u θ)]
  -- The abstract integral identity, then back to `Iθ`.
  have hmain := integral_sq_eq_of_rel (s := s) (α := fun θ => deriv g θ)
    (β := fun θ => deriv (deriv (fun t => Real.tan t * u t)) θ)
    (δ := fun θ => deriv u θ) (v := fun θ => deriv (deriv (deriv u)) θ)
    (κ := fun θ => Real.rpow (Real.sin (2 * θ)) (2 - γ))
    hsmeas hκ0 hκ1 hrel hmα hmv hmδ hmκ hIα hIv hIδ
  rw [MeasureTheory.setIntegral_congr_set hset, MeasureTheory.setIntegral_congr_set hset,
    MeasureTheory.setIntegral_congr_set hset, MeasureTheory.setIntegral_congr_set hset]
  exact hmain

end Work.FTS.EllipticEst.remov.Step4
