import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.TT.interpGammaDefs
import Submission.Work.FTS.EllipticEst.TT.sliceIBPLight
import Submission.Work.Blocks.IMC.cs_integral_mul_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores

open MeasureTheory Set Filter
open scoped Real Topology

/-!
# The vanishing-boundary slice interpolation for the light weight `σ_A = sin(2θ)^{2-γ}`

This file proves `sliceInterpVanishing`.  With `a := 2 - γ(α) = 1 - α/10 ∈ (0,1)` and
`σ_A = sigA α = sigR a`, the *double angular integration by parts for the light weight*
(`TT.slice_ibp_light`) gives, whenever the four boundary products of `Φ` vanish,

  `∫ (Φ')²σ_A = -∫ Φ Φ'' σ_A - 2a ∫ Φ² σ_A - 2a(1-a) ∫ Φ² cos²(2θ) sin(2θ)^{a-2}`,

and the last two terms are `≤ 0` because their integrands are nonnegative and `0 < a < 1`.
Hence `∫ (Φ')²σ_A ≤ -∫ ΦΦ''σ_A ≤ |∫ ΦΦ''σ_A|`, and the Cauchy–Schwarz inequality for the
weighted pairing `(Φ, Φ'') ↦ ∫ Φ Φ'' σ_A` bounds this by `√(∫Φ²σ_A · ∫(Φ'')²σ_A)`.
The constant is therefore `C = 1`.

The weighted Cauchy–Schwarz is applied with the two half-weighted functions
`Φ·√σ_A` and `Φ''·√σ_A` in `L²(Iθ)`.
-/

/-- `Iθ` and the open interval `(0, π/2)` differ only by the two endpoints, so they carry the
same restricted Lebesgue measure. -/
theorem restrict_Iθ_eq_Ioo :
    volume.restrict Work.Spaces.Iθ = volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  apply MeasureTheory.Measure.restrict_congr_set
  change ∀ᵐ x ∂volume, (x ∈ Work.Spaces.Iθ) = (x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2))
  rw [MeasureTheory.ae_iff]
  have hsub : {a : ℝ | ¬((a ∈ Work.Spaces.Iθ) = (a ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)))}
      ⊆ ({0, Real.pi / 2} : Set ℝ) := by
    intro x hx
    by_contra hx2
    refine hx (propext ⟨?_, ?_⟩)
    · intro h1
      simp only [Work.Spaces.Iθ, Set.mem_Icc] at h1
      have h0 : x ≠ 0 := by intro h; exact hx2 (by simp [h])
      have hp : x ≠ Real.pi / 2 := by intro h; exact hx2 (by simp [h])
      exact ⟨lt_of_le_of_ne h1.1 (Ne.symm h0), lt_of_le_of_ne h1.2 hp⟩
    · intro h1
      simp only [Work.Spaces.Iθ, Set.mem_Icc]
      exact ⟨le_of_lt h1.1, le_of_lt h1.2⟩
  have h2 : volume ({0, Real.pi / 2} : Set ℝ) = 0 := by
    rw [show ({0, Real.pi / 2} : Set ℝ) = {0} ∪ {Real.pi / 2} by
      ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]]
    exact MeasureTheory.measure_union_null (MeasureTheory.measure_singleton 0)
      (MeasureTheory.measure_singleton (Real.pi / 2))
  exact MeasureTheory.measure_mono_null hsub h2

/-- A function continuous on the open interval is a.e.-strongly-measurable on `Iθ`. -/
theorem aesm_of_continuousOn_Ioo (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    AEStronglyMeasurable f (volume.restrict Work.Spaces.Iθ) := by
  rw [restrict_Iθ_eq_Ioo]
  exact hf.aestronglyMeasurable measurableSet_Ioo

theorem sliceInterpVanishing (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Φ : ℝ → ℝ),
      ContDiffOn ℝ 2 Φ (Set.Ioo (0 : ℝ) (Real.pi / 2)) →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv Φ θ) ^ 2 * Work.FTS.EllipticEst.TT.sigA α θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ : ℝ => Φ θ * deriv (deriv Φ) θ * Work.FTS.EllipticEst.TT.sigA α θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ : ℝ => Φ θ * deriv Φ θ * Work.FTS.EllipticEst.TT.sigDR (2 - Work.Spaces.gam α) θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (Φ θ) ^ 2 * Work.FTS.EllipticEst.TT.sigA α θ) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (Φ θ) ^ 2 * (Real.cos (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ ((2 - Work.Spaces.gam α) - 2)) Work.Spaces.Iθ →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv Φ) θ) ^ 2 * Work.FTS.EllipticEst.TT.sigA α θ) Work.Spaces.Iθ →
      Filter.Tendsto (fun t : ℝ => Φ t * deriv Φ t * Work.FTS.EllipticEst.TT.sigA α t) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto (fun t : ℝ => Φ t * deriv Φ t * Work.FTS.EllipticEst.TT.sigA α t) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      Filter.Tendsto (fun t : ℝ => (Φ t) ^ 2 * Work.FTS.EllipticEst.TT.sigDR (2 - Work.Spaces.gam α) t) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto (fun t : ℝ => (Φ t) ^ 2 * Work.FTS.EllipticEst.TT.sigDR (2 - Work.Spaces.gam α) t) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      (∫ θ in Work.Spaces.Iθ, (deriv Φ θ) ^ 2 * Work.FTS.EllipticEst.TT.sigA α θ)
        ≤ C * Real.sqrt ((∫ θ in Work.Spaces.Iθ, (Φ θ) ^ 2 * Work.FTS.EllipticEst.TT.sigA α θ)
            * (∫ θ in Work.Spaces.Iθ, (deriv (deriv Φ) θ) ^ 2
                * Work.FTS.EllipticEst.TT.sigA α θ)) := by
  refine ⟨1, one_pos, ?_⟩
  intro Φ hcd hI1 hI2 hI3 hI4 hI5 hI6 hb1 hb2 hb3 hb4
  -- the exponent `a := 2 - γ(α) = 1 - α/10` lies in `(0,1)`
  have hgam : Work.Spaces.gam α = 1 + α / 10 := rfl
  have ha0 : 0 < 2 - Work.Spaces.gam α := by rw [hgam]; linarith
  have ha1 : 2 - Work.Spaces.gam α < 1 := by rw [hgam]; linarith
  have h1a : 0 < 1 - (2 - Work.Spaces.gam α) := by rw [hgam]; linarith
  -- ## The double angular integration by parts for the light weight
  have hibp := Work.FTS.EllipticEst.TT.slice_ibp_light (2 - Work.Spaces.gam α) ha0 ha1 hcd
    hI1 hI2 hI3 hI4 hI5 hb1 hb2 hb3 hb4
  have hibp' :
      (∫ θ in Work.Spaces.Iθ, (deriv Φ θ) ^ 2 * Work.FTS.EllipticEst.TT.sigA α θ)
        = - (∫ θ in Work.Spaces.Iθ,
              Φ θ * deriv (deriv Φ) θ * Work.FTS.EllipticEst.TT.sigA α θ)
          - 2 * (2 - Work.Spaces.gam α)
            * (∫ θ in Work.Spaces.Iθ,
                (Φ θ) ^ 2 * Work.FTS.EllipticEst.TT.sigA α θ)
          - 2 * (2 - Work.Spaces.gam α) * (1 - (2 - Work.Spaces.gam α))
            * (∫ θ in Work.Spaces.Iθ, (Φ θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
                * (Real.sin (2 * θ)) ^ ((2 - Work.Spaces.gam α) - 2)) := hibp
  -- ## Nonnegativity of the two extra terms
  have hD0 : 0 ≤ ∫ θ in Work.Spaces.Iθ,
      (Φ θ) ^ 2 * Work.FTS.EllipticEst.TT.sigA α θ :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ =>
      mul_nonneg (sq_nonneg (Φ θ)) (Work.FTS.EllipticEst.TT.sigA_nonneg α θ hθ))
  have hE0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Φ θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
      * (Real.sin (2 * θ)) ^ ((2 - Work.Spaces.gam α) - 2) :=
    MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ =>
      mul_nonneg (mul_nonneg (sq_nonneg (Φ θ)) (sq_nonneg (Real.cos (2 * θ))))
        (Real.rpow_nonneg (Work.FTS.EllipticEst.TT.sin_two_nonneg_of_mem_Iθ hθ) _))
  -- ## The interpolation inequality in the form `LHS ≤ -∫ Φ Φ'' σ_A`
  have hkey : (∫ θ in Work.Spaces.Iθ, (deriv Φ θ) ^ 2 * Work.FTS.EllipticEst.TT.sigA α θ)
      ≤ - (∫ θ in Work.Spaces.Iθ,
            Φ θ * deriv (deriv Φ) θ * Work.FTS.EllipticEst.TT.sigA α θ) := by
    have h2a : 0 ≤ 2 * (2 - Work.Spaces.gam α)
        * (∫ θ in Work.Spaces.Iθ, (Φ θ) ^ 2 * Work.FTS.EllipticEst.TT.sigA α θ) :=
      mul_nonneg (mul_nonneg (by norm_num) ha0.le) hD0
    have h2b : 0 ≤ 2 * (2 - Work.Spaces.gam α) * (1 - (2 - Work.Spaces.gam α))
        * (∫ θ in Work.Spaces.Iθ, (Φ θ) ^ 2 * (Real.cos (2 * θ)) ^ 2
            * (Real.sin (2 * θ)) ^ ((2 - Work.Spaces.gam α) - 2)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha0.le) h1a.le) hE0
    rw [hibp']
    linarith
  -- ## Measurability of the two half-weighted functions
  have hcont_sig : ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.TT.sigA α θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    have h : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      hsin.rpow_const (fun x hx =>
        Or.inl (ne_of_gt (Work.FTS.EllipticEst.TT.sin_two_pos_of_mem_Ioo hx)))
    simpa only [Work.FTS.EllipticEst.TT.sigA] using h
  have haesm_Φ : AEStronglyMeasurable Φ (volume.restrict Work.Spaces.Iθ) :=
    aesm_of_continuousOn_Ioo Φ hcd.continuousOn
  have haesm_sig : AEStronglyMeasurable (fun θ : ℝ => Real.sqrt
      (Work.FTS.EllipticEst.TT.sigA α θ)) (volume.restrict Work.Spaces.Iθ) :=
    aesm_of_continuousOn_Ioo _ hcont_sig.sqrt
  have hfm : AEStronglyMeasurable
      (fun θ : ℝ => Φ θ * Real.sqrt (Work.FTS.EllipticEst.TT.sigA α θ))
      (volume.restrict Work.Spaces.Iθ) := haesm_Φ.mul haesm_sig
  have hcont_ddΦ : ContinuousOn (deriv (deriv Φ)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    ((hcd.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).deriv_of_isOpen isOpen_Ioo
      (m := 0) (by norm_num)).continuousOn
  have haesm_ddΦ : AEStronglyMeasurable (deriv (deriv Φ))
      (volume.restrict Work.Spaces.Iθ) :=
    aesm_of_continuousOn_Ioo _ hcont_ddΦ
  have hgm : AEStronglyMeasurable
      (fun θ : ℝ => deriv (deriv Φ) θ * Real.sqrt (Work.FTS.EllipticEst.TT.sigA α θ))
      (volume.restrict Work.Spaces.Iθ) := haesm_ddΦ.mul haesm_sig
  -- ## Square-integrability of the two half-weighted functions
  have hf2 : Integrable (fun θ : ℝ =>
      (Φ θ * Real.sqrt (Work.FTS.EllipticEst.TT.sigA α θ)) ^ 2)
      (volume.restrict Work.Spaces.Iθ) :=
    hI4.congr (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [mul_pow, Real.sq_sqrt (Work.FTS.EllipticEst.TT.sigA_nonneg α θ hθ)])
  have hg2 : Integrable (fun θ : ℝ =>
      (deriv (deriv Φ) θ * Real.sqrt (Work.FTS.EllipticEst.TT.sigA α θ)) ^ 2)
      (volume.restrict Work.Spaces.Iθ) :=
    hI6.congr (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [mul_pow, Real.sq_sqrt (Work.FTS.EllipticEst.TT.sigA_nonneg α θ hθ)])
  -- ## Cauchy–Schwarz for the weighted pairing
  have hcs := Work.Blocks.IMC.cs_integral_mul_le (volume.restrict Work.Spaces.Iθ)
    (f := fun θ : ℝ => Φ θ * Real.sqrt (Work.FTS.EllipticEst.TT.sigA α θ))
    (g := fun θ : ℝ => deriv (deriv Φ) θ * Real.sqrt (Work.FTS.EllipticEst.TT.sigA α θ))
    hfm hgm hf2 hg2
  have hX1 : (∫ x : ℝ, (Φ x * Real.sqrt (Work.FTS.EllipticEst.TT.sigA α x))
        * (deriv (deriv Φ) x * Real.sqrt (Work.FTS.EllipticEst.TT.sigA α x))
        ∂(volume.restrict Work.Spaces.Iθ))
      = ∫ θ in Work.Spaces.Iθ,
          Φ θ * deriv (deriv Φ) θ * Work.FTS.EllipticEst.TT.sigA α θ := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    have hs : Real.sqrt (Work.FTS.EllipticEst.TT.sigA α θ)
        * Real.sqrt (Work.FTS.EllipticEst.TT.sigA α θ)
        = Work.FTS.EllipticEst.TT.sigA α θ := by
      rw [← sq, Real.sq_sqrt (Work.FTS.EllipticEst.TT.sigA_nonneg α θ hθ)]
    rw [show (Φ θ * Real.sqrt (Work.FTS.EllipticEst.TT.sigA α θ))
          * (deriv (deriv Φ) θ * Real.sqrt (Work.FTS.EllipticEst.TT.sigA α θ))
        = Φ θ * deriv (deriv Φ) θ
          * (Real.sqrt (Work.FTS.EllipticEst.TT.sigA α θ)
            * Real.sqrt (Work.FTS.EllipticEst.TT.sigA α θ)) from by ring, hs]
  have hX2 : (∫ x : ℝ, (Φ x * Real.sqrt (Work.FTS.EllipticEst.TT.sigA α x)) ^ 2
        ∂(volume.restrict Work.Spaces.Iθ))
      = ∫ θ in Work.Spaces.Iθ, (Φ θ) ^ 2 * Work.FTS.EllipticEst.TT.sigA α θ := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [mul_pow, Real.sq_sqrt (Work.FTS.EllipticEst.TT.sigA_nonneg α θ hθ)]
  have hX3 : (∫ x : ℝ, (deriv (deriv Φ) x * Real.sqrt (Work.FTS.EllipticEst.TT.sigA α x)) ^ 2
        ∂(volume.restrict Work.Spaces.Iθ))
      = ∫ θ in Work.Spaces.Iθ, (deriv (deriv Φ) θ) ^ 2
          * Work.FTS.EllipticEst.TT.sigA α θ := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [mul_pow, Real.sq_sqrt (Work.FTS.EllipticEst.TT.sigA_nonneg α θ hθ)]
  have hcs' : |∫ θ in Work.Spaces.Iθ,
        Φ θ * deriv (deriv Φ) θ * Work.FTS.EllipticEst.TT.sigA α θ|
      ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ,
            (Φ θ) ^ 2 * Work.FTS.EllipticEst.TT.sigA α θ)
        * Real.sqrt (∫ θ in Work.Spaces.Iθ, (deriv (deriv Φ) θ) ^ 2
            * Work.FTS.EllipticEst.TT.sigA α θ) := by
    rw [← hX1, ← hX2, ← hX3]
    exact hcs
  -- ## Assembly
  have hle : (∫ θ in Work.Spaces.Iθ, (deriv Φ θ) ^ 2 * Work.FTS.EllipticEst.TT.sigA α θ)
      ≤ Real.sqrt ((∫ θ in Work.Spaces.Iθ,
              (Φ θ) ^ 2 * Work.FTS.EllipticEst.TT.sigA α θ)
          * (∫ θ in Work.Spaces.Iθ, (deriv (deriv Φ) θ) ^ 2
              * Work.FTS.EllipticEst.TT.sigA α θ)) :=
    calc (∫ θ in Work.Spaces.Iθ, (deriv Φ θ) ^ 2 * Work.FTS.EllipticEst.TT.sigA α θ)
        ≤ - (∫ θ in Work.Spaces.Iθ,
              Φ θ * deriv (deriv Φ) θ * Work.FTS.EllipticEst.TT.sigA α θ) := hkey
      _ ≤ |∫ θ in Work.Spaces.Iθ,
              Φ θ * deriv (deriv Φ) θ * Work.FTS.EllipticEst.TT.sigA α θ| := neg_le_abs _
      _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ,
              (Φ θ) ^ 2 * Work.FTS.EllipticEst.TT.sigA α θ)
            * Real.sqrt (∫ θ in Work.Spaces.Iθ, (deriv (deriv Φ) θ) ^ 2
                * Work.FTS.EllipticEst.TT.sigA α θ) := hcs'
      _ = Real.sqrt ((∫ θ in Work.Spaces.Iθ,
              (Φ θ) ^ 2 * Work.FTS.EllipticEst.TT.sigA α θ)
            * (∫ θ in Work.Spaces.Iθ, (deriv (deriv Φ) θ) ^ 2
                * Work.FTS.EllipticEst.TT.sigA α θ)) :=
          (Real.sqrt_mul hD0 (∫ θ in Work.Spaces.Iθ, (deriv (deriv Φ) θ) ^ 2
                * Work.FTS.EllipticEst.TT.sigA α θ)).symm
  simpa using hle

end Work.FTS.EllipticEst.Cores
