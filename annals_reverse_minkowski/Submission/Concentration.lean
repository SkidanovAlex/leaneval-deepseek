import Mathlib
import Submission.GaussianMeasure
import Submission.Commons.Analysis.GaussianMeasure.gauss_cdf_tail_split
import Submission.Commons.Analysis.GaussianMeasure.tail_shift_le
import Submission.Commons.Analysis.GaussianMeasure.two_thirds_quantile_exists
import Submission.Commons.Analysis.Convex.smul_add_ball_subset_smul
import Submission.GaussIsoperimetricBlowup

open Module Real MeasureTheory
open scoped Real BigOperators Pointwise
set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Gaussian concentration for the [F] boundary step of `gamma_stable` (paper §7.2)

This module contains the concentration half of the paper's `gamma_concentration`
(Lemma 2.3): for a convex body `K` with Gaussian mass `γ_{1/t}(K) ≥ 2/3` and inradius
`≥ r`, the mass at the smaller parameter `1/(t+τ)` is at least `1 − e^{−π r²τ²}/3`.

It is **scaffolding for the rank-`m ≥ 2` induction step** (`gamma_stable_of_two_le`):
the rank-`d` factor will be a (transported, closed convex) Voronoi cell `K` with
`γ_{1/t(d)}(K) ≥ 2/3` by the induction hypothesis, `r ≥ 1/2` by stability, and
`τ := t(m) − t(d) = 10·log(m/d)`.

## Status

COMPLETE (no sorries): the sole deep ingredient, the Gaussian isoperimetric inequality
(Sudakov–Tsirelson 1974 / Borell 1975) in the halfspace-threshold "blowup" form, is now
the commons theorem `Commons.Analysis.GaussianMeasure.gaussian_isoperimetric_blowup`
(imported above), used directly in `concentration_neighborhood_two_thirds`.

`gamma_concentration` (paper Lemma 2.3) is the delivered statement consumed by the
[F] boundary branch (`Submission/StableBoundary.lean`).
-/

namespace Submission.Concentration

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- A set of Gaussian mass at least `2/3` has its Euclidean `ρ`-neighbourhood of mass at
least `1 − e^{−πρ²}/3`.  (Assembly: Borell blowup at the `2/3`-quantile `σ₀` +
`tail_shift_le`.) -/
lemma concentration_neighborhood_two_thirds (U : Set E) (hU : MeasurableSet U)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hUγ : (2 : ℝ) / 3 ≤ Submission.GaussianMeasure.gammaMass 1 U) :
    1 - Real.exp (-Real.pi * ρ ^ 2) / 3 ≤
      Submission.GaussianMeasure.gammaMass 1 {x : E | ∃ u ∈ U, dist x u ≤ ρ} := by
  rcases Commons.Analysis.GaussianMeasure.two_thirds_quantile_exists with ⟨σ₀, hσ₀pos, hσ₀⟩
  have hσ₀nonneg : 0 ≤ σ₀ := le_of_lt hσ₀pos
  have hUγ' : (∫ x : ℝ in {x : ℝ | x ≤ σ₀}, Real.exp (-Real.pi * x ^ 2)) ≤
      ∫ x in U, Real.exp (-Real.pi * ‖x‖ ^ 2) := by
    have heq : (∫ x : ℝ in {x : ℝ | x ≤ σ₀}, Real.exp (-Real.pi * x ^ 2)) =
        ∫ x in Set.Iio σ₀, Real.exp (-Real.pi * x ^ 2) := by
      exact MeasureTheory.integral_Iic_eq_integral_Iio (μ := (volume : Measure ℝ))
        (x := σ₀) (f := fun x => Real.exp (-Real.pi * x ^ 2))
    calc
      (∫ x : ℝ in {x : ℝ | x ≤ σ₀}, Real.exp (-Real.pi * x ^ 2))
          = ∫ x in Set.Iio σ₀, Real.exp (-Real.pi * x ^ 2) := heq
      _ = (2 : ℝ) / 3 := hσ₀
      _ ≤ ∫ x in U, Real.exp (-Real.pi * ‖x‖ ^ 2) := by
        simpa [Submission.GaussianMeasure.gammaMass_one] using hUγ
  have hb := Commons.Analysis.GaussianMeasure.gaussian_isoperimetric_blowup U hU σ₀ ρ hρ hUγ'
  have htail_split (t : ℝ) : (∫ x : ℝ in Set.Iio t, Real.exp (-Real.pi * x ^ 2)) +
      (∫ x in Set.Ioi t, Real.exp (-Real.pi * x ^ 2)) = 1 :=
    Commons.Analysis.GaussianMeasure.gauss_cdf_tail_split t
  have htail₀ : (∫ x in Set.Ioi σ₀, Real.exp (-Real.pi * x ^ 2)) = 1 / 3 := by
    have hs := htail_split σ₀
    have hIio₀ : (∫ x in Set.Iio σ₀, Real.exp (-Real.pi * x ^ 2)) = (2 : ℝ) / 3 := hσ₀
    nlinarith
  have htail : (∫ x in Set.Ioi (σ₀ + ρ), Real.exp (-Real.pi * x ^ 2)) ≤
      Real.exp (-Real.pi * ρ ^ 2) / 3 := by
    have hts := Commons.Analysis.GaussianMeasure.tail_shift_le σ₀ ρ hσ₀nonneg hρ
    rw [htail₀] at hts
    simpa [div_eq_mul_inv] using hts
  have hLHS : 1 - Real.exp (-Real.pi * ρ ^ 2) / 3 ≤
      (∫ x : ℝ in {x : ℝ | x ≤ σ₀ + ρ}, Real.exp (-Real.pi * x ^ 2)) := by
    have heq2 : (∫ x : ℝ in {x : ℝ | x ≤ σ₀ + ρ}, Real.exp (-Real.pi * x ^ 2)) =
        ∫ x in Set.Iio (σ₀ + ρ), Real.exp (-Real.pi * x ^ 2) := by
      exact MeasureTheory.integral_Iic_eq_integral_Iio (μ := (volume : Measure ℝ))
        (x := σ₀ + ρ) (f := fun x => Real.exp (-Real.pi * x ^ 2))
    rw [heq2]
    have hsplit3 := htail_split (σ₀ + ρ)
    have hle : (∫ x in Set.Ioi (σ₀ + ρ), Real.exp (-Real.pi * x ^ 2)) ≤
        Real.exp (-Real.pi * ρ ^ 2) / 3 := htail
    nlinarith
  have hgoal : 1 - Real.exp (-Real.pi * ρ ^ 2) / 3 ≤
      ∫ x in {x : E | ∃ u ∈ U, dist x u ≤ ρ}, Real.exp (-Real.pi * ‖x‖ ^ 2) := by
    exact le_trans hLHS hb
  rwa [Submission.GaussianMeasure.gammaMass_one]

/-- A nonzero scalar multiple of a closed set is closed. -/
lemma smul_isClosed (c : ℝ) (_hc : c ≠ 0) {K : Set E} (hK : IsClosed K) :
    IsClosed (c • K) := by
  have hf : IsClosedMap (fun x : E => c • x) := isClosedMap_smul₀ c
  have himg : IsClosed ((fun x : E => c • x) '' K) := hf K hK
  simpa using himg

/-- The closed `ρ`-neighbourhood of a closed set is its closed `ρ`-thickening (hence closed,
hence measurable). -/
lemma closed_neighborhood_thickening (S : Set E) (hS : IsClosed S) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    {x : E | ∃ u ∈ S, dist x u ≤ ρ} = Metric.cthickening ρ S := by
  have hproper : ProperSpace E := by infer_instance
  rw [Metric.cthickening_eq_biUnion_closedBall S hρ]
  have hcl : closure S = S := hS.closure_eq
  rw [hcl]
  ext x
  simp [Metric.mem_closedBall]

/--
**`gamma_concentration` (paper Lemma 2.3).** For a convex closed body `K` with
`r·B ⊆ K` and Gaussian mass `γ_{1/t}(K) ≥ 2/3` at parameter `t > 0`, the mass at the
smaller parameter `1/(t+τ)` (`τ ≥ 0`) is at least `1 − e^{−π r²τ²}/3`.

Boundary-step use: `K` = (transported) Voronoi cell of a stable rank-`d` lattice
(closed, convex), `r` = inradius ≥ `1/2`, `t = t(d) = 10(log d + 2)`,
`τ = t(m) − t(d) = 10·log(m/d)`.
-/
lemma gamma_concentration (K : Set E) (hKcvx : Convex ℝ K) (hKcl : IsClosed K)
    (t τ r : ℝ) (ht : 0 < t) (hτ : 0 ≤ τ) (hr : 0 ≤ r)
    (hball : Metric.closedBall (0 : E) r ⊆ K)
    (hγ : (2 : ℝ) / 3 ≤ Submission.GaussianMeasure.gammaMass (1 / t) K) :
    1 - Real.exp (-Real.pi * (r * τ) ^ 2) / 3 ≤
      Submission.GaussianMeasure.gammaMass (1 / (t + τ)) K := by
  have htpos : 0 ≤ t := le_of_lt ht
  have htpτ : 0 < t + τ := by linarith
  have htne : t ≠ 0 := ne_of_gt ht
  have htpτne : t + τ ≠ 0 := ne_of_gt htpτ
  have hρnonneg : 0 ≤ r * τ := mul_nonneg hr hτ
  have h0K : (0 : E) ∈ K := by
    have hb0 : (0 : E) ∈ Metric.closedBall (0 : E) r := by
      rw [Metric.mem_closedBall, dist_self]
      exact hr
    exact hball hb0
  have hinc0 : t • K +ᵥ Metric.closedBall (0 : E) ((t + τ - t) * r) ⊆ (t + τ) • K := by
    exact Commons.Analysis.Convex.smul_add_ball_subset_smul (C := K) hKcvx h0K hr htpos
      (by linarith) hball
  have hrad : (t + τ - t) * r = r * τ := by ring
  have hinc : t • K +ᵥ Metric.closedBall (0 : E) (r * τ) ⊆ (t + τ) • K := by
    rwa [hrad] at hinc0
  let N : Set E := {x : E | ∃ u ∈ t • K, dist x u ≤ r * τ}
  have hNcth : N = Metric.cthickening (r * τ) (t • K) := by
    dsimp [N]
    exact closed_neighborhood_thickening (t • K) (smul_isClosed t htne hKcl) (r * τ) hρnonneg
  have hNmeas : MeasurableSet N := by
    rw [hNcth]
    exact Metric.isClosed_cthickening.measurableSet
  have hNKmeas : MeasurableSet (t • K) := (smul_isClosed t htne hKcl).measurableSet
  have hBtmeas : MeasurableSet ((t + τ) • K) :=
    (smul_isClosed (t + τ) htpτne hKcl).measurableSet
  have hγ₁ : (2 : ℝ) / 3 ≤ Submission.GaussianMeasure.gammaMass 1 (t • K) := by
    have h1 : Submission.GaussianMeasure.gammaMass 1 (t • K) =
        Submission.GaussianMeasure.gammaMass (1 / t) K := by
      rw [Submission.GaussianMeasure.gammaMass_one]
      rw [Submission.GaussianMeasure.gammaMass_inv_smul_set t htne K]
    rw [h1]
    exact hγ
  have hconc : 1 - Real.exp (-Real.pi * (r * τ) ^ 2) / 3 ≤
      Submission.GaussianMeasure.gammaMass 1 N := by
    dsimp [N]
    exact concentration_neighborhood_two_thirds (t • K) hNKmeas (r * τ) hρnonneg hγ₁
  have hNinc : N ⊆ (t + τ) • K := by
    intro x hx
    rcases hx with ⟨u, huK, hdist⟩
    have hballmem : x - u ∈ Metric.closedBall (0 : E) (r * τ) := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      simpa [dist_eq_norm] using hdist
    have hvadd : x ∈ t • K +ᵥ Metric.closedBall (0 : E) (r * τ) := by
      refine ⟨u, huK, x - u, hballmem, ?_⟩
      abel
    exact hinc hvadd
  calc
    1 - Real.exp (-Real.pi * (r * τ) ^ 2) / 3
        ≤ Submission.GaussianMeasure.gammaMass 1 N := hconc
    _ ≤ Submission.GaussianMeasure.gammaMass 1 ((t + τ) • K) := by
        exact Submission.GaussianMeasure.gammaMass_mono_set 1 hNinc hNmeas hBtmeas
    _ = Submission.GaussianMeasure.gammaMass (1 / (t + τ)) K := by
        rw [Submission.GaussianMeasure.gammaMass_one]
        rw [Submission.GaussianMeasure.gammaMass_inv_smul_set (t + τ) htpτne K]

end Submission.Concentration
