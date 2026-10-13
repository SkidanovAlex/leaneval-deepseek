import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.E5Aux3.hasDerivWithinAt_L12_slice_of_majorant
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS.StrongEps.E5Aux3

/-!
# `Work.FTS.StrongEps.E5Aux3.epsRHSP_dens_aesm_slice`

**Joint a.e. strong measurability of the averaged angular density of a `IsEpsSolP` family.**

The scheme `IsEpsSolP` provides the fake-time derivative of `g` only through the
*within-`Icc 0 T`* derivative of the pointwise function `τ ↦ g z θ τ`; the value of that
derivative, `epsRHSP α ρ ε Φs E g σ z θ`, is therefore **not** known to be measurable in
`(z,θ)` (a derivative is not a continuous function of its base point) and the hypothesis
`hcont` does not mention it.  It is nevertheless a.e.-strongly-measurable, because it is an
a.e. limit of *continuous* difference quotients of the family slices, which `hcont` does
control.

Route.  Fix the time `σ ∈ (0,T)` and the sequence `ts n = σ + (T-σ)/(n+1) ↓ σ`, which lies in
`Icc 0 T \ {σ}`.  On the open quadrant `S = Ioi 0 ×ˢ Ioo 0 (π/2)` each difference quotient

  `p ↦ slope (fun s => (K p.2 / p.1) * g p.1 p.2 s) σ (ts n)`

is continuous (`K` continuous, `g ∘ (p ↦ (p.1,p.2,ts n))` continuous by `hcont`, `p.1 ≠ 0`),
hence a.e.-strongly-measurable for `(volume|_(Ioi 0)).prod (volume|_Iθ)` once one rewrites that
measure as the restriction of the planar Lebesgue measure to `Ioi 0 ×ˢ Iθ`, which agrees with
`S` up to the null set `Ioi 0 ×ˢ {0, π/2}`.  Finally, for a.e. `p` of the quadrant the sequence
converges to `K p.2 * epsRHSP … σ p.1 p.2 / p.1`, by `hsol` (the base point `σ` is interior, so
the within-`Icc 0 T` derivative is a genuine derivative) combined with
`hasDerivWithinAt_iff_tendsto_slope`, and `aestronglyMeasurable_of_tendsto_ae` concludes.

Note on the statement: the angular cut-off `π / 2` in `hcont` is the notation for `Real.pi / 2`
(the file opens `scoped Real`), matching `Work.Spaces.Iθ = Icc 0 (Real.pi / 2)`.
-/
theorem epsRHSP_dens_aesm_slice {α T ε : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g₀ : Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hsol : Work.FTS.StrongEps.IsEpsSolP α ρ ε T Φs E g₀ g)
    (hcont : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T))
    {σ : ℝ} (hσ : σ ∈ Set.Ioo 0 T) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.K p.2 *
        Work.FTS.StrongEps.epsRHSP α ρ ε Φs E g σ p.1 p.2 / p.1)
      ((MeasureTheory.volume.restrict (Set.Ioi 0)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  -- the open quadrant and the approximating times
  set S : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) with hSdef
  set ts : ℕ → ℝ := fun n => σ + (T - σ) / ((n : ℝ) + 1) with htsdef
  have hTσ : 0 < T - σ := by linarith [hσ.2]
  have hIcc : σ ∈ Set.Icc (0 : ℝ) T := ⟨hσ.1.le, hσ.2.le⟩
  have hts_eq : ∀ n : ℕ, ts n = σ + (T - σ) / ((n : ℝ) + 1) := fun n => by simp only [htsdef]
  have hts_mem : ∀ n : ℕ, ts n ∈ Set.Icc (0 : ℝ) T := by
    intro n
    have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hq0 : 0 < (T - σ) / ((n : ℝ) + 1) := div_pos hTσ hden
    have hq : (T - σ) / ((n : ℝ) + 1) ≤ T - σ := by
      rw [div_le_iff₀ hden]; nlinarith [Nat.cast_nonneg (α := ℝ) n]
    rw [hts_eq n]
    exact ⟨by linarith [hσ.1], by linarith⟩
  have hts_ne : ∀ n : ℕ, ts n ≠ σ := by
    intro n h
    have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hq0 : 0 < (T - σ) / ((n : ℝ) + 1) := div_pos hTσ hden
    rw [hts_eq n] at h
    linarith
  have hts_tend : Tendsto ts atTop (𝓝 σ) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      Filter.tendsto_atTop_add_const_right _ 1 (tendsto_natCast_atTop_atTop (R := ℝ))
    have h2 : Tendsto (fun n : ℕ => (T - σ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds h1
    have h3 : Tendsto (fun n : ℕ => σ + (T - σ) / ((n : ℝ) + 1)) atTop (𝓝 (σ + 0)) :=
      h2.const_add σ
    rw [htsdef]
    simpa only [add_zero] using h3
  have hts_within : Tendsto ts atTop (𝓝[Set.Icc (0 : ℝ) T \ {σ}] σ) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within ts hts_tend
      (Eventually.of_forall fun n => ⟨hts_mem n, hts_ne n⟩)
  -- membership in the open quadrant
  have hS_mem : ∀ p : ℝ × ℝ, p ∈ S ↔ 0 < p.1 ∧ p.2 ∈ Set.Ioo 0 (π / 2) := by
    intro p
    rw [hSdef, Set.mem_prod, Set.mem_Ioi]
  -- the multiplier `K p.2 / p.1` is continuous on the quadrant
  have hKc : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.K p.2 / p.1) S := by
    refine ((continuous_K.comp continuous_snd).continuousOn).div continuous_fst.continuousOn ?_
    intro p hp
    exact ne_of_gt ((hS_mem p).mp hp).1
  -- the slices of the family are continuous on the quadrant
  have hgc : ∀ τ ∈ Set.Icc (0 : ℝ) T, ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2 τ) S := by
    intro τ hτ
    have hmap : ContinuousOn (fun p : ℝ × ℝ => (p.1, (p.2, τ))) S :=
      (continuous_fst.prodMk (continuous_snd.prodMk continuous_const)).continuousOn
    refine (hcont.continuousOn).comp hmap ?_
    intro p hp
    exact ⟨((hS_mem p).mp hp).1, ((hS_mem p).mp hp).2, hτ⟩
  -- the (unfolded) difference quotients are continuous on the quadrant
  have hφc : ∀ n : ℕ, ContinuousOn (fun p : ℝ × ℝ => (ts n - σ)⁻¹ *
      (Work.Spaces.K p.2 / p.1 * g p.1 p.2 (ts n) - Work.Spaces.K p.2 / p.1 * g p.1 p.2 σ)) S :=
    fun n => ((hKc.mul (hgc (ts n) (hts_mem n))).sub
      (hKc.mul (hgc σ hIcc))).const_mul ((ts n - σ)⁻¹)
  -- hence the difference quotients in `slope` form are continuous on the quadrant
  have hφs : ∀ n : ℕ, ContinuousOn (fun p : ℝ × ℝ =>
      slope (fun s : ℝ => (Work.Spaces.K p.2 / p.1) * g p.1 p.2 s) σ (ts n)) S := by
    intro n
    have heq : ∀ p ∈ S, slope (fun s : ℝ => (Work.Spaces.K p.2 / p.1) * g p.1 p.2 s) σ (ts n)
        = (ts n - σ)⁻¹ * (Work.Spaces.K p.2 / p.1 * g p.1 p.2 (ts n)
            - Work.Spaces.K p.2 / p.1 * g p.1 p.2 σ) := by
      intro p hp
      simp only [slope, vsub_eq_sub, smul_eq_mul]
    exact ContinuousOn.congr (hφc n) heq
  -- the product measure is the planar Lebesgue measure restricted to the quadrant, up to null
  have hθae : Work.Spaces.Iθ =ᵐ[volume] Set.Ioo (0 : ℝ) (π / 2) :=
    (MeasureTheory.Ioo_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := π / 2)).symm
  have hprod : (Set.Ioi (0 : ℝ) ×ˢ Work.Spaces.Iθ : Set (ℝ × ℝ)) =ᵐ[volume.prod volume] S := by
    rw [hSdef]
    exact MeasureTheory.Measure.set_prod_ae_eq (Filter.EventuallyEq.refl _ _) hθae
  have hS_meas : MeasurableSet S := (isOpen_Ioi.prod isOpen_Ioo).measurableSet
  -- each difference quotient is a.e.-strongly-measurable
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (fun p : ℝ × ℝ =>
      slope (fun s : ℝ => (Work.Spaces.K p.2 / p.1) * g p.1 p.2 s) σ (ts n))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict Work.Spaces.Iθ)) := by
    intro n
    rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.restrict_congr_set hprod]
    exact (hφs n).aestronglyMeasurable hS_meas
  -- the quadrant is conull
  have haeS : ∀ᵐ p ∂((volume.restrict (Set.Ioi 0)).prod
      (volume.restrict Work.Spaces.Iθ)), p ∈ S := by
    rw [MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.restrict_congr_set hprod]
    exact MeasureTheory.self_mem_ae_restrict hS_meas
  -- and the a.e. limit is the angular density of the right-hand side
  have hlim : ∀ᵐ p ∂((volume.restrict (Set.Ioi 0)).prod
      (volume.restrict Work.Spaces.Iθ)),
      Tendsto (fun n : ℕ => slope (fun s : ℝ => (Work.Spaces.K p.2 / p.1) * g p.1 p.2 s) σ (ts n))
        atTop (𝓝 (Work.Spaces.K p.2 * epsRHSP α ρ ε Φs E g σ p.1 p.2 / p.1)) := by
    filter_upwards [haeS] with p hp
    obtain ⟨hp1, hp2⟩ := (hS_mem p).mp hp
    have h1 : HasDerivWithinAt (fun s : ℝ => (Work.Spaces.K p.2 / p.1) * g p.1 p.2 s)
        ((Work.Spaces.K p.2 / p.1) * epsRHSP α ρ ε Φs E g σ p.1 p.2) (Set.Icc 0 T) σ :=
      (hsol.2 p.1 p.2 σ hp1 hp2 hIcc).const_mul (Work.Spaces.K p.2 / p.1)
    have h2 := (hasDerivWithinAt_iff_tendsto_slope.mp h1).comp hts_within
    have h3 : (Work.Spaces.K p.2 / p.1) * epsRHSP α ρ ε Φs E g σ p.1 p.2
        = Work.Spaces.K p.2 * epsRHSP α ρ ε Φs E g σ p.1 p.2 / p.1 := by ring
    rw [h3] at h2
    exact h2
  exact aestronglyMeasurable_of_tendsto_ae atTop hmeas hlim

end Work.FTS.StrongEps.E5Aux3
