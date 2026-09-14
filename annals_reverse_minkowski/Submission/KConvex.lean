import Mathlib
import Submission.GaussianChaos
import Submission.GaugeNormed
import Submission.Commons.GeometryOfNumbers.EllNorm.sSup_inner_image_eq_gauge_polar
import Submission.Commons.GeometryOfNumbers.Lattice.exists_gauge_euclidean_comparison
import Submission.Commons.Analysis.Normed.analytic_coeff_bound
import Submission.Commons.Analysis.GaussianMeasure.ou_multivariate_hermite_eigenfunction_gen
import Submission.Commons.Analysis.GaussianMeasure.mehler_operator_contraction_l2
import Submission.Commons.Analysis.GaussianMeasure.mehler_hermite_sum
import Submission.Commons.Analysis.GaussianMeasure.mehler_gauge_le
-- ⚠ IMPORT-CLASH WORKAROUND (session 123): the commons modules below transitively import
-- `bobkov_strong_nD`, whose `toLp_norm_sq` clashes with `brascamp_lieb_truncated` (needed by the
-- (B)-conjecture chain).  The `Submission.Fix.*` copies have that import chain redirected.
import Submission.Fix.IntegrableMehlerData
import Submission.Fix.IntegrableMehlerSq
import Submission.Commons.Geometry.Convex.smul_mem_iff_le_inv_gauge
import Submission.Commons.GeometryOfNumbers.EllNorm.sSup_inner_image_eq_gauge_polar

/-!
# Pisier's K-convexity bound for `X = (ℝⁿ, ‖·‖_K)`

This file proves the finite-dimensional K-convexity estimate which is the analytic core of the
`ℓℓ*` theorem (Figiel–Tomczak-Jaegermann / Lewis / Pisier), and hence of the last missing input
`Submission.IsotropicMass.EllEllStarHyp`.

Setup: `K ⊆ ℝⁿ` is a symmetric convex body, `T` a linear isomorphism with
`‖T x‖ ≤ gauge K x ≤ d ‖T x‖` (so `d` bounds the Banach–Mazur distance to `ℓ₂ⁿ`, `d = √n` by John),
and `μ N` the Gaussian weight measure on `ℝ^N` (`Submission.GaussianChaos.μ`).

The first-chaos projection
`Q₁Φ x = ∑ᵢ xᵢ • (∫ y, yᵢ • Φ y ∂μ N)/(∫ y, yᵢ^2 ∂μ N)`
satisfies `‖Q₁Φ‖_{L²(μ N; X)} ≤ 4 (1 + log₂ d) ‖Φ‖_{L²(μ N; X)}`; for finite Hermite sums this
follows from Pisier's Lemma 2.6 (`Commons.Analysis.Normed.analytic_coeff_bound`), the componentwise
Bessel bound and the Mehler/OU contraction, and it extends to all of `L²` by continuity.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

namespace Submission.KConvex

open MeasureTheory Polynomial Filter
open scoped BigOperators ENNReal Pointwise Topology

variable {n N : ℕ}

/-- The degree `|α| = ∑ᵢ αᵢ` of a multi-index. -/
def deg {N : ℕ} (α : Fin N → ℕ) : ℕ := ∑ i, α i

/-- The `k`-th Hermite chaos component of a finite Hermite sum. -/
noncomputable def comp (k : ℕ) (s : Finset (Fin N → ℕ))
    (C : (Fin N → ℕ) → EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin n) :=
  fun x => ∑ α ∈ s.filter (fun α => deg α = k), (Submission.GaussianChaos.herm α x) • C α

/-- `T` commutes with finite Hermite sums (it is linear and acts on the coefficients). -/
theorem map_hermSum (T : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (s : Finset (Fin N → ℕ)) (C : (Fin N → ℕ) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin N)) :
    T (Submission.GaussianChaos.hermSum s C x)
      = Submission.GaussianChaos.hermSum s (fun α => T (C α)) x := by
  have h : T.toLinearMap (Submission.GaussianChaos.hermSum s C x)
      = Submission.GaussianChaos.hermSum s (fun α => T (C α)) x := by
    simp only [Submission.GaussianChaos.hermSum]
    rw [map_sum]
    exact Finset.sum_congr rfl fun α _ => by simp [map_smul]
  exact h

/-- Finite Hermite sums are in `L²(μ N)`. -/
theorem memLp_hermSum (s : Finset (Fin N → ℕ))
    (C : (Fin N → ℕ) → EuclideanSpace ℝ (Fin n)) :
    MemLp (Submission.GaussianChaos.hermSum s C) 2 (Submission.GaussianChaos.μ N) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact memLp_const (μ := Submission.GaussianChaos.μ N) (p := 2) (c := 0)
  | insert α s hα ih =>
      have h1 : MemLp (fun x : EuclideanSpace ℝ (Fin N) => (Submission.GaussianChaos.herm α x) • C α)
          2 (Submission.GaussianChaos.μ N) :=
        (Submission.GaussianChaos.memLp_herm α).continuousLinearMap_comp
          (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (C α))
      have hsum := h1.add ih
      have heq : Submission.GaussianChaos.hermSum (insert α s) C
          = (fun x : EuclideanSpace ℝ (Fin N) => (Submission.GaussianChaos.herm α x) • C α)
            + (fun x : EuclideanSpace ℝ (Fin N) => Submission.GaussianChaos.hermSum s C x) := by
        funext x
        simp [Submission.GaussianChaos.hermSum, Finset.sum_insert hα]
      rw [heq]
      exact hsum

/-- `‖hermSum s C ·‖ ^ 2` is integrable. -/
theorem integrable_norm_sq_hermSum (s : Finset (Fin N → ℕ))
    (C : (Fin N → ℕ) → EuclideanSpace ℝ (Fin n)) :
    Integrable (fun x => ‖Submission.GaussianChaos.hermSum s C x‖ ^ 2)
      (Submission.GaussianChaos.μ N) := by
  have h := (memLp_hermSum s C).norm_rpow (by norm_num) (by norm_num)
  simpa using h.integrable le_rfl

/-- The Hermite product is continuous. -/
theorem continuous_herm {N : ℕ} (α : Fin N → ℕ) :
    Continuous (fun x : EuclideanSpace ℝ (Fin N) => Submission.GaussianChaos.herm α x) := by
  simp only [Submission.GaussianChaos.herm]
  fun_prop

/-- Finite Hermite sums are continuous. -/
theorem continuous_hermSum (s : Finset (Fin N → ℕ))
    (C : (Fin N → ℕ) → EuclideanSpace ℝ (Fin n)) :
    Continuous (fun x : EuclideanSpace ℝ (Fin N) => Submission.GaussianChaos.hermSum s C x) := by
  simp only [Submission.GaussianChaos.hermSum, Submission.GaussianChaos.herm]
  fun_prop

section ComponentBound

variable {d : ℝ}

/-- **Bessel bound for one chaos component.**  The `k`-th Hermite component of a finite Hermite
sum is bounded in `L²` by `d` times the whole sum, where `d` is the Banach–Mazur factor of the
comparison `‖T x‖ ≤ gauge K x ≤ d ‖T x‖`. -/
theorem integral_gauge_comp_le (K : Set (EuclideanSpace ℝ (Fin n))) (hcvx : Convex ℝ K)
    (habs : Absorbent ℝ K) (hKint : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior K) (hd : 0 ≤ d)
    (T : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hT1 : ∀ x, ‖T x‖ ≤ gauge K x) (hT2 : ∀ x, gauge K x ≤ d * ‖T x‖)
    (s : Finset (Fin N → ℕ)) (C : (Fin N → ℕ) → EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    ∫ x, (gauge K (comp k s C x)) ^ 2 ∂Submission.GaussianChaos.μ N
      ≤ d ^ 2 * ∫ x, (gauge K (Submission.GaussianChaos.hermSum s C x)) ^ 2
          ∂Submission.GaussianChaos.μ N := by
  classical
  set sf : Finset (Fin N → ℕ) := s.filter (fun α => deg α = k) with hsf
  have hpt : ∀ x, (gauge K (comp k s C x)) ^ 2
      ≤ (d * ‖Submission.GaussianChaos.hermSum sf (fun α => T (C α)) x‖) ^ 2 := by
    intro x
    have h1 : gauge K (comp k s C x)
        ≤ d * ‖Submission.GaussianChaos.hermSum sf (fun α => T (C α)) x‖ := by
      have hcomp : comp k s C x = Submission.GaussianChaos.hermSum sf C x := rfl
      rw [hcomp]
      calc gauge K (Submission.GaussianChaos.hermSum sf C x)
          ≤ d * ‖T (Submission.GaussianChaos.hermSum sf C x)‖ := hT2 _
        _ = d * ‖Submission.GaussianChaos.hermSum sf (fun α => T (C α)) x‖ := by
            rw [map_hermSum T sf C x]
    exact pow_le_pow_left₀ (gauge_nonneg _) h1 2
  have hintT : Integrable (fun x => (d * ‖Submission.GaussianChaos.hermSum sf
      (fun α => T (C α)) x‖) ^ 2) (Submission.GaussianChaos.μ N) := by
    have h := (integrable_norm_sq_hermSum sf (fun α => T (C α))).const_mul (d ^ 2)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    ring
  have hstep1 : ∫ x, (gauge K (comp k s C x)) ^ 2 ∂Submission.GaussianChaos.μ N
      ≤ ∫ x, (d * ‖Submission.GaussianChaos.hermSum sf (fun α => T (C α)) x‖) ^ 2
          ∂Submission.GaussianChaos.μ N := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => ?_) hintT
      (Filter.Eventually.of_forall hpt)
    positivity
  have hpyth_comp : ∫ x, ‖Submission.GaussianChaos.hermSum sf (fun α => T (C α)) x‖ ^ 2
      ∂Submission.GaussianChaos.μ N = ∑ α ∈ sf, ‖T (C α)‖ ^ 2 * Submission.GaussianChaos.energy α :=
    Submission.GaussianChaos.integral_norm_sq_finset_sum sf _
  have hpyth_all : ∫ x, ‖Submission.GaussianChaos.hermSum s (fun α => T (C α)) x‖ ^ 2
      ∂Submission.GaussianChaos.μ N = ∑ α ∈ s, ‖T (C α)‖ ^ 2 * Submission.GaussianChaos.energy α :=
    Submission.GaussianChaos.integral_norm_sq_finset_sum s _
  have hmono : ∑ α ∈ sf, ‖T (C α)‖ ^ 2 * Submission.GaussianChaos.energy α
      ≤ ∑ α ∈ s, ‖T (C α)‖ ^ 2 * Submission.GaussianChaos.energy α := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · exact Finset.filter_subset _ _
    · intro α _ _
      exact mul_nonneg (pow_nonneg (norm_nonneg _) 2) (Submission.GaussianChaos.energy_pos α).le
  have hTsum : ∫ x, ‖Submission.GaussianChaos.hermSum s (fun α => T (C α)) x‖ ^ 2
      ∂Submission.GaussianChaos.μ N
      = ∫ x, ‖T (Submission.GaussianChaos.hermSum s C x)‖ ^ 2 ∂Submission.GaussianChaos.μ N := by
    apply integral_congr_ae
    filter_upwards with x
    exact (congrArg (fun w => ‖w‖ ^ 2) (map_hermSum T s C x)).symm
  have hpt2 : ∀ x, (‖T (Submission.GaussianChaos.hermSum s C x)‖) ^ 2
      ≤ (gauge K (Submission.GaussianChaos.hermSum s C x)) ^ 2 := by
    intro x
    exact pow_le_pow_left₀ (norm_nonneg _) (hT1 _) 2
  have hInt : Integrable (fun x => ‖T (Submission.GaussianChaos.hermSum s C x)‖ ^ 2)
      (Submission.GaussianChaos.μ N) := by
    have h := integrable_norm_sq_hermSum s (fun α => T (C α))
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    exact (congrArg (fun w => ‖w‖ ^ 2) (map_hermSum T s C x)).symm
  have hInt2 : Integrable (fun x => (gauge K (Submission.GaussianChaos.hermSum s C x)) ^ 2)
      (Submission.GaussianChaos.μ N) := by
    refine (hInt.const_mul (d ^ 2)).mono'
      (((continuous_gauge hcvx (Filter.mem_of_superset (isOpen_interior.mem_nhds hKint)
          interior_subset)).comp
        (continuous_hermSum s C)).pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (pow_nonneg (gauge_nonneg _) 2)]
    calc gauge K (Submission.GaussianChaos.hermSum s C x) ^ 2
        ≤ (d * ‖T (Submission.GaussianChaos.hermSum s C x)‖) ^ 2 :=
          pow_le_pow_left₀ (gauge_nonneg _) (hT2 _) 2
      _ = d ^ 2 * ‖T (Submission.GaussianChaos.hermSum s C x)‖ ^ 2 := by ring
  have hstep2 : ∫ x, (d * ‖Submission.GaussianChaos.hermSum sf (fun α => T (C α)) x‖) ^ 2
      ∂Submission.GaussianChaos.μ N
      ≤ d ^ 2 * ∫ x, (gauge K (Submission.GaussianChaos.hermSum s C x)) ^ 2
          ∂Submission.GaussianChaos.μ N := by
    rw [show (fun x => (d * ‖Submission.GaussianChaos.hermSum sf (fun α => T (C α)) x‖) ^ 2)
        = (fun x => d ^ 2 * ‖Submission.GaussianChaos.hermSum sf (fun α => T (C α)) x‖ ^ 2) from
          by funext x; ring]
    rw [integral_const_mul, hpyth_comp]
    have hkey : ∑ α ∈ s, ‖T (C α)‖ ^ 2 * Submission.GaussianChaos.energy α
        = ∫ x, ‖T (Submission.GaussianChaos.hermSum s C x)‖ ^ 2 ∂Submission.GaussianChaos.μ N :=
      hpyth_all.symm.trans hTsum
    calc d ^ 2 * ∑ α ∈ sf, ‖T (C α)‖ ^ 2 * Submission.GaussianChaos.energy α
        ≤ d ^ 2 * ∑ α ∈ s, ‖T (C α)‖ ^ 2 * Submission.GaussianChaos.energy α :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = d ^ 2 * ∫ x, ‖T (Submission.GaussianChaos.hermSum s C x)‖ ^ 2
            ∂Submission.GaussianChaos.μ N := by rw [hkey]
      _ ≤ d ^ 2 * ∫ x, (gauge K (Submission.GaussianChaos.hermSum s C x)) ^ 2
            ∂Submission.GaussianChaos.μ N :=
          mul_le_mul_of_nonneg_left (integral_mono hInt hInt2 (fun x => hpt2 x)) (by positivity)
  exact le_trans hstep1 hstep2

end ComponentBound

/-! ### The Mehler (Ornstein–Uhlenbeck) operator

`mehler ρ Φ x = (2π(1-ρ²))^{-N/2} ∫ exp(-‖y-ρx‖²/(2(1-ρ²))) • Φ y dy`.  On the `k`-th Hermite
chaos it acts as multiplication by `ρ^k` (`Commons.Analysis.GaussianMeasure.mehler_hermite_sum`),
and being given by a nonnegative kernel it is a contraction in the `gauge K` norm by Jensen
(`Commons.Analysis.GaussianMeasure.mehler_gauge_le`). -/

noncomputable def mehlerK (ρ : ℝ) (x y : EuclideanSpace ℝ (Fin N)) : ℝ :=
  (2 * Real.pi * (1 - ρ ^ 2)) ^ (-(N : ℝ) / 2) *
    Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2)))

noncomputable def mehler (ρ : ℝ)
    (Φ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin n) :=
  fun x => ∫ y, (mehlerK ρ x y) • Φ y

/-- The Mehler operator acts on a finite Hermite sum by `ρ^{|α|}` on each coefficient. -/
theorem mehler_hermSum (s : Finset (Fin N → ℕ))
    (C : (Fin N → ℕ) → EuclideanSpace ℝ (Fin n)) (ρ : ℝ) (hρ : ρ ^ 2 < 1)
    (x : EuclideanSpace ℝ (Fin N)) :
    mehler ρ (Submission.GaussianChaos.hermSum s C) x
      = Submission.GaussianChaos.hermSum s (fun α => (ρ ^ deg α) • C α) x := by
  have h1ρ : 0 < 1 - ρ ^ 2 := by linarith
  have hc : (2 * Real.pi * (1 - ρ ^ 2)) ^ (-(N : ℝ) / 2)
      = ((2 * Real.pi * (1 - ρ ^ 2)) ^ ((N : ℝ) / 2))⁻¹ := by
    rw [← Real.rpow_neg (show (0:ℝ) ≤ 2 * Real.pi * (1 - ρ ^ 2) by positivity)]
    ring_nf
  have hpoint : ∀ y : EuclideanSpace ℝ (Fin N),
      (mehlerK ρ x y) • (Submission.GaussianChaos.hermSum s C y)
        = ((2 * Real.pi * (1 - ρ ^ 2)) ^ (-(N : ℝ) / 2)) •
            ((Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2))) : ℝ)
              • (∑ α ∈ s, ((∏ i, Polynomial.aeval (y i) (Polynomial.hermite (α i))) • C α))) := by
    intro y
    simp only [mehlerK, Submission.GaussianChaos.hermSum, Submission.GaussianChaos.herm]
    rw [smul_smul]
  have hfun : (fun y : EuclideanSpace ℝ (Fin N) =>
        (mehlerK ρ x y) • (Submission.GaussianChaos.hermSum s C y))
      = (fun y : EuclideanSpace ℝ (Fin N) => ((2 * Real.pi * (1 - ρ ^ 2)) ^ (-(N : ℝ) / 2)) •
            ((Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2))) : ℝ)
              • (∑ α ∈ s, ((∏ i, Polynomial.aeval (y i) (Polynomial.hermite (α i))) • C α)))) := by
    funext y
    exact hpoint y
  rw [mehler, hfun, integral_smul]
  have hcomm : ∀ α : Fin N → ℕ, (∏ i, Polynomial.aeval (x.ofLp i) (Polynomial.hermite (α i)))
      = (∏ i, Polynomial.aeval (x i) (Polynomial.hermite (α i))) := fun α => rfl
  simp only [hcomm]
  rw [Commons.Analysis.GaussianMeasure.mehler_hermite_sum s C ρ hρ x]
  simp only [Submission.GaussianChaos.hermSum]
  apply Finset.sum_congr rfl
  intro α _
  simp only [Submission.GaussianChaos.herm, deg]
  rw [smul_smul, mul_comm]

/-- Regrouping a damped Hermite sum by chaos degree. -/
theorem hermSum_damped (s : Finset (Fin N → ℕ)) (C : (Fin N → ℕ) → EuclideanSpace ℝ (Fin n))
    (ρ : ℝ) (x : EuclideanSpace ℝ (Fin N)) :
    Submission.GaussianChaos.hermSum s (fun α => (ρ ^ deg α) • C α) x
      = ∑ k ∈ s.image deg, (ρ ^ k) • comp k s C x := by
  have hdisp : ∀ a ∈ s.image deg, ∀ b ∈ s.image deg, a ≠ b →
      Disjoint (s.filter (fun α => deg α = a)) (s.filter (fun α => deg α = b)) := by
    intro a _ b _ hab
    rw [Finset.disjoint_left]
    intro c h1 h2
    rw [Finset.mem_filter] at h1 h2
    exact hab (h1.2.symm.trans h2.2)
  have hcomp : ∀ k ∈ s.image deg, (ρ ^ k) • comp k s C x
      = ∑ α ∈ s.filter (fun α => deg α = k),
          (ρ ^ deg α) • ((Submission.GaussianChaos.herm α x) • C α) := by
    intro k _
    simp only [comp]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro α hα
    rw [Finset.mem_filter] at hα
    rw [hα.2, smul_smul]
  rw [Finset.sum_congr rfl hcomp, ← Finset.sum_biUnion hdisp,
    Finset.image_biUnion_filter_eq]
  apply Finset.sum_congr rfl
  intro α _
  simp only [Submission.GaussianChaos.hermSum, Submission.GaussianChaos.herm]
  rw [smul_smul, smul_comm (ρ ^ deg α) (∏ i, Polynomial.aeval (x.ofLp i) (Polynomial.hermite (α i))),
    smul_smul]

section MehlerContraction

/-- The Mehler operator with the normalised kernel is a contraction for the `gauge K` norm
(pointwise version: it is an average of the values of `gauge K ∘ Φ`). -/
theorem mehler_gauge_le_normalized (K : Set (EuclideanSpace ℝ (Fin n))) (hcvx : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ K) (habs : Absorbent ℝ K)
    (hbdd : Bornology.IsVonNBounded ℝ K) (hbal : Balanced ℝ K)
    (ρ : ℝ) (hρ : ρ ^ 2 < 1) (x : EuclideanSpace ℝ (Fin N))
    (Φ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin n))
    (hΦ : Integrable (fun y : EuclideanSpace ℝ (Fin N) =>
        (Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2))) : ℝ) • Φ y) volume)
    (hΦg : Integrable (fun y : EuclideanSpace ℝ (Fin N) =>
        Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2))) * gauge K (Φ y)) volume) :
    gauge K (mehler ρ Φ x)
      ≤ ∫ y, mehlerK ρ x y * gauge K (Φ y) ∂volume := by
  have h1ρ : 0 < 1 - ρ ^ 2 := by linarith
  have hc0 : 0 ≤ (2 * Real.pi * (1 - ρ ^ 2)) ^ (-(N : ℝ) / 2) := Real.rpow_nonneg (by positivity) _
  have hpoint : ∀ y : EuclideanSpace ℝ (Fin N),
      (mehlerK ρ x y) • Φ y
        = ((2 * Real.pi * (1 - ρ ^ 2)) ^ (-(N : ℝ) / 2)) •
            ((Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2))) : ℝ) • Φ y) := by
    intro y
    simp only [mehlerK]
    rw [smul_smul]
  have hfun : (fun y : EuclideanSpace ℝ (Fin N) => (mehlerK ρ x y) • Φ y)
      = (fun y : EuclideanSpace ℝ (Fin N) => ((2 * Real.pi * (1 - ρ ^ 2)) ^ (-(N : ℝ) / 2)) •
          ((Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2))) : ℝ) • Φ y)) := by
    funext y; exact hpoint y
  have hmehler : mehler ρ Φ x
      = ((2 * Real.pi * (1 - ρ ^ 2)) ^ (-(N : ℝ) / 2)) •
          ∫ y, (Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2))) : ℝ) • Φ y ∂volume := by
    simp only [mehler]
    rw [hfun, integral_smul]
  rw [hmehler, gauge_smul_of_nonneg hc0, smul_eq_mul]
  have hkey := Commons.Analysis.GaussianMeasure.mehler_gauge_le K hcvx h0 habs hbdd hbal ρ hρ x Φ hΦ hΦg
  have hstep : ((2 * Real.pi * (1 - ρ ^ 2)) ^ (-(N : ℝ) / 2)) *
        gauge K (∫ y, (Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2))) : ℝ) • Φ y ∂volume)
      ≤ ((2 * Real.pi * (1 - ρ ^ 2)) ^ (-(N : ℝ) / 2)) *
        ∫ y, Real.exp (-‖y - ρ • x‖ ^ 2 / (2 * (1 - ρ ^ 2))) * gauge K (Φ y) ∂volume :=
    mul_le_mul_of_nonneg_left hkey hc0
  refine hstep.trans (le_of_eq ?_)
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  simp only [mehlerK]
  ring

/-- The Mehler operator is an `L²(μ N)` contraction for `x ↦ gauge K (hermSum s C x)`. -/
theorem mehler_scalar_contraction (K : Set (EuclideanSpace ℝ (Fin n))) (hcvx : Convex ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ K) (habs : Absorbent ℝ K)
    (hbdd : Bornology.IsVonNBounded ℝ K) (hbal : Balanced ℝ K)
    (ρ : ℝ) (hρ : ρ ^ 2 < 1) (s : Finset (Fin N → ℕ))
    (C : (Fin N → ℕ) → EuclideanSpace ℝ (Fin n)) :
    ∫ x, (∫ y : EuclideanSpace ℝ (Fin N), mehlerK ρ x y * gauge K (Submission.GaussianChaos.hermSum s C y) ∂volume) ^ 2
        ∂Submission.GaussianChaos.μ N
      ≤ ∫ x, (gauge K (Submission.GaussianChaos.hermSum s C x)) ^ 2
          ∂Submission.GaussianChaos.μ N := by
  have hmem := Commons.Analysis.GaussianMeasure.memLp_gauge_hermite_sum K hcvx h0 habs hbdd hbal s C
  have hρ' : |ρ| < 1 := by nlinarith [sq_abs ρ, abs_nonneg ρ, hρ]
  have h := Commons.Analysis.GaussianMeasure.mehler_operator_contraction_l2 ρ hρ'
    (fun x => gauge K (Submission.GaussianChaos.hermSum s C x)) hmem
  rw [Submission.GaussianChaos.integral_μ, Submission.GaussianChaos.integral_μ]
  refine le_of_eq_of_le ?_ h
  congr 1
  funext x
  congr 2
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  simp only [mehlerK]
  ring

end MehlerContraction

section Polar

/-- The polar body of `K`. -/
def polar (K : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n)) :=
  {z | ∀ y ∈ K, inner ℝ z y ≤ 1}

/-- Duality of the gauge and the polar gauge: `⟪ψ,v⟫ ≤ gauge K° ψ · gauge K v`. -/
theorem inner_le_gauge_polar (K : Set (EuclideanSpace ℝ (Fin n))) (hcvx : Convex ℝ K)
    (hcpt : IsCompact K) (habs : Absorbent ℝ K) (hbdd : Bornology.IsVonNBounded ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior K) (hKsymm : (-K : Set _) = K)
    (ψ v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ ψ v ≤ gauge (polar K) ψ * gauge K v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hvpos : 0 < gauge K v := by
    rcases lt_or_eq_of_le (gauge_nonneg v) with h | h
    · exact h
    · exact absurd ((gauge_eq_zero habs hbdd).mp h.symm) hv
  have hmem : v ∈ gauge K v • K :=
    (Commons.Geometry.Convex.gauge_le_iff_of_pos hcpt hcvx h0 hvpos).mp le_rfl
  obtain ⟨y, hy, hyv⟩ := hmem
  have hsup : gauge (polar K) ψ = sSup ((fun y : EuclideanSpace ℝ (Fin n) => inner ℝ y ψ) '' K) :=
    (Commons.GeometryOfNumbers.EllNorm.sSup_inner_image_eq_gauge_polar K
      (fun x hx => by
        have h : -x ∈ -K := by simpa using hx
        rwa [hKsymm] at h) hcpt.isBounded ψ).symm
  have hbdd' : BddAbove ((fun y : EuclideanSpace ℝ (Fin n) => inner ℝ y ψ) '' K) :=
    (hcpt.image (continuous_id.inner continuous_const)).bddAbove
  calc inner ℝ ψ v = gauge K v * inner ℝ y ψ := by
        conv_lhs => rw [← hyv]
        rw [inner_smul_right, real_inner_comm]
    _ ≤ gauge K v * gauge (polar K) ψ := by
        refine mul_le_mul_of_nonneg_left ?_ (gauge_nonneg v)
        rw [hsup]
        exact le_csSup hbdd' (Set.mem_image_of_mem _ hy)
    _ = gauge (polar K) ψ * gauge K v := by ring

/-- Two-sided form of `inner_le_gauge_polar`. -/
theorem abs_inner_le_gauge_polar (K : Set (EuclideanSpace ℝ (Fin n))) (hcvx : Convex ℝ K)
    (hcpt : IsCompact K) (habs : Absorbent ℝ K) (hbdd : Bornology.IsVonNBounded ℝ K)
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior K) (hKsymm : (-K : Set _) = K)
    (ψ v : EuclideanSpace ℝ (Fin n)) :
    |inner ℝ ψ v| ≤ gauge (polar K) ψ * gauge K v := by
  have hsym : ∀ z ∈ polar K, -z ∈ polar K := by
    intro z hz y hy
    have hy' : -y ∈ K := by
      have : -y ∈ -K := by simpa using hy
      rwa [hKsymm] at this
    have h1 := hz (-y) hy'
    rw [inner_neg_right] at h1
    rw [inner_neg_left]
    linarith
  refine abs_le.mpr ⟨?_, ?_⟩
  · have h := inner_le_gauge_polar K hcvx hcpt habs hbdd h0 hKsymm (-ψ) v
    rw [inner_neg_left, gauge_neg hsym] at h
    linarith
  · exact inner_le_gauge_polar K hcvx hcpt habs hbdd h0 hKsymm ψ v

end Polar

section ScalarBound

/-- The `L²(μ N)` norm of an `Lp` element given by an a.e. equal function. -/
theorem norm_Lp_eq_sqrt {F : Lp ℝ 2 (Submission.GaussianChaos.μ N)}
    {f : EuclideanSpace ℝ (Fin N) → ℝ} (hf : ⇑F =ᵐ[Submission.GaussianChaos.μ N] f)
    (hfm : AEStronglyMeasurable f (Submission.GaussianChaos.μ N)) :
    ‖F‖ = Real.sqrt (∫ x, (f x) ^ 2 ∂Submission.GaussianChaos.μ N) := by
  rw [Lp.norm_def]
  rw [show eLpNorm (⇑F) 2 (Submission.GaussianChaos.μ N)
      = eLpNorm f 2 (Submission.GaussianChaos.μ N) from eLpNorm_congr_ae hf]
  rw [MeasureTheory.toReal_eLpNorm hfm]
  rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hfm]
  norm_num
  rw [Real.sqrt_eq_rpow]

/-- The `L²(μ N)` norm of a `toLp` class (scalar case). -/
theorem norm_toLp_sqrt {f : EuclideanSpace ℝ (Fin N) → ℝ}
    (hf : MemLp f 2 (Submission.GaussianChaos.μ N)) :
    ‖hf.toLp f‖ = Real.sqrt (∫ x, (f x) ^ 2 ∂Submission.GaussianChaos.μ N) := by
  rw [Lp.norm_toLp, MeasureTheory.toReal_eLpNorm hf.aestronglyMeasurable]
  rw [MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
    hf.aestronglyMeasurable]
  norm_num
  rw [Real.sqrt_eq_rpow]

end ScalarBound

section Helpers

variable {d : ℝ}

/-- `MemLp` of the gauge-norm of a finite Hermite sum, with respect to `μ N`. -/
theorem memLp_gauge_hermSum (K : Set (EuclideanSpace ℝ (Fin n))) (hcvx : Convex ℝ K)
    (hKnhds : K ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n))) (d : ℝ) (hd : 0 ≤ d)
    (T : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hT1 : ∀ x, ‖T x‖ ≤ gauge K x) (hT2 : ∀ x, gauge K x ≤ d * ‖T x‖)
    (s : Finset (Fin N → ℕ)) (C : (Fin N → ℕ) → EuclideanSpace ℝ (Fin n)) :
    MemLp (fun x => gauge K (Submission.GaussianChaos.hermSum s C x)) 2
      (Submission.GaussianChaos.μ N) := by
  have hTE : MemLp (fun x => T (Submission.GaussianChaos.hermSum s C x)) 2
      (Submission.GaussianChaos.μ N) :=
    (memLp_hermSum s C).continuousLinearMap_comp T.toContinuousLinearMap
  have hnorm : MemLp (fun x => ‖T (Submission.GaussianChaos.hermSum s C x)‖) 2
      (Submission.GaussianChaos.μ N) := hTE.norm
  refine MemLp.of_le_mul (f := fun x => gauge K (Submission.GaussianChaos.hermSum s C x))
    (g := fun x => ‖T (Submission.GaussianChaos.hermSum s C x)‖) (c := d) hnorm ?_ ?_
  · exact ((continuous_gauge hcvx hKnhds).comp (continuous_hermSum s C)).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_of_nonneg (gauge_nonneg _), Real.norm_of_nonneg (norm_nonneg _)]
    exact hT2 _

/-- Integrability of the square of the gauge norm of a finite Hermite sum. -/
theorem integrable_sq_gauge_hermSum (K : Set (EuclideanSpace ℝ (Fin n))) (hcvx : Convex ℝ K)
    (hKnhds : K ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n))) (d : ℝ) (hd : 0 ≤ d)
    (T : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hT1 : ∀ x, ‖T x‖ ≤ gauge K x) (hT2 : ∀ x, gauge K x ≤ d * ‖T x‖)
    (s : Finset (Fin N → ℕ)) (C : (Fin N → ℕ) → EuclideanSpace ℝ (Fin n)) :
    Integrable (fun x => (gauge K (Submission.GaussianChaos.hermSum s C x)) ^ 2)
      (Submission.GaussianChaos.μ N) := by
  have h := (memLp_gauge_hermSum K hcvx hKnhds d hd T hT1 hT2 s C).norm_rpow
    (by norm_num) (by norm_num)
  have h2 := h.integrable le_rfl
  simpa using h2

end Helpers


/-- The `L²(μ N)` norm of a finite `Lp`-combination, computed through the pointwise combination. -/
theorem norm_finsetSum_toLp {ι : Type*} (t : Finset ι) (c : ι → ℝ)
    (f : ι → EuclideanSpace ℝ (Fin N) → ℝ)
    (hf : ∀ i, MemLp (f i) 2 (Submission.GaussianChaos.μ N))
    (g : EuclideanSpace ℝ (Fin N) → ℝ) (hgm : AEStronglyMeasurable g (Submission.GaussianChaos.μ N))
    (hae : (fun x => ∑ i ∈ t, c i * f i x) =ᵐ[Submission.GaussianChaos.μ N] g) :
    ‖∑ i ∈ t, c i • (hf i).toLp (f i)‖
      = Real.sqrt (∫ x, (g x) ^ 2 ∂Submission.GaussianChaos.μ N) := by
  classical
  have hsm : ∀ i, ⇑(c i • (hf i).toLp (f i))
      =ᵐ[Submission.GaussianChaos.μ N] (fun x => c i * f i x) := by
    intro i
    filter_upwards [Lp.coeFn_smul (c i) ((hf i).toLp (f i)), MemLp.coeFn_toLp (hf i)]
      with x h1 h2
    rw [h1, Pi.smul_apply, smul_eq_mul, h2]
  have hsum_ae_gen : ∀ (u : Finset ι),
      (∀ i ∈ u, ⇑(c i • (hf i).toLp (f i)) =ᵐ[Submission.GaussianChaos.μ N]
        (fun x => c i * f i x)) →
      (∑ i ∈ u, ⇑(c i • (hf i).toLp (f i)))
        =ᵐ[Submission.GaussianChaos.μ N] (∑ i ∈ u, fun x => c i * f i x) := by
    intro u
    induction u using Finset.induction_on with
    | empty => intro _; simp
    | insert a s ha ih =>
        intro h
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        exact EventuallyEq.add (h a (Finset.mem_insert_self a s))
          (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
  have hsum_ae := hsum_ae_gen t fun i _ => hsm i
  refine norm_Lp_eq_sqrt ?_ hgm
  refine ((Lp.coeFn_finsetSum t (fun i => c i • (hf i).toLp (f i))).trans hsum_ae).trans ?_
  filter_upwards [hae] with x hx
  rw [Finset.sum_apply, hx]


section ScalarBound

variable {d : ℝ}

/-- **Scalar-tested K-convexity bound for one Hermite component.**  For a symmetric convex body
`K`, a comparison map `T` with `‖T x‖ ≤ gauge K x ≤ d ‖T x‖`, a finite Hermite sum
`Φ = hermSum s C`, and any test field `Ψ` with values in the polar `K°`,

`∫ ⟪Ψ, (first chaos component of Φ)⟫² dμ ≤ (4 (1 + log₂ d))² ∫ (gauge K ∘ Φ)² dμ`. -/
theorem kconvex_scalar (K : Set (EuclideanSpace ℝ (Fin n))) (hcvx : Convex ℝ K)
    (habs : Absorbent ℝ K) (hbdd : Bornology.IsVonNBounded ℝ K) (hbal : Balanced ℝ K)
    (hcpt : IsCompact K) (hKnhds : K ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin n)))
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior K)
    (hKsymm : (-K : Set (EuclideanSpace ℝ (Fin n))) = K)
    (hd : 1 ≤ d) (T : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hT1 : ∀ x, ‖T x‖ ≤ gauge K x) (hT2 : ∀ x, gauge K x ≤ d * ‖T x‖)
    (s : Finset (Fin N → ℕ)) (C : (Fin N → ℕ) → EuclideanSpace ℝ (Fin n))
    (Ψ : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin n))
    (hΨ : ∀ x, gauge (polar K) (Ψ x) ≤ 1)
    (hΨm : AEStronglyMeasurable Ψ (Submission.GaussianChaos.μ N)) :
    ∫ x, (inner ℝ (Ψ x) (comp 1 s C x)) ^ 2 ∂Submission.GaussianChaos.μ N
      ≤ (4 * (1 + Real.log d / Real.log 2)) ^ 2 *
        ∫ x, (gauge K (Submission.GaussianChaos.hermSum s C x)) ^ 2
          ∂Submission.GaussianChaos.μ N := by
  classical
  set A : ℝ := ∫ x, (gauge K (Submission.GaussianChaos.hermSum s C x)) ^ 2
      ∂Submission.GaussianChaos.μ N with hA
  have hA0 : 0 ≤ A := by
    rw [hA]; exact integral_nonneg (fun x => sq_nonneg _)
  have hint_h : Integrable (fun x => (gauge K (Submission.GaussianChaos.hermSum s C x)) ^ 2)
      (Submission.GaussianChaos.μ N) :=
    integrable_sq_gauge_hermSum K hcvx hKnhds d (le_trans zero_le_one hd) T hT1 hT2 s C
  -- the scalar test functions
  have hfmem : ∀ k : ℕ, MemLp (fun x => inner ℝ (Ψ x) (comp k s C x)) 2
      (Submission.GaussianChaos.μ N) := by
    intro k
    have hmem_comp : MemLp (fun x => gauge K (comp k s C x)) 2
        (Submission.GaussianChaos.μ N) := by
      exact memLp_gauge_hermSum K hcvx hKnhds d (le_trans zero_le_one hd) T hT1 hT2
        (s.filter (fun α => deg α = k)) C
    refine MemLp.of_le_mul (f := fun x => inner ℝ (Ψ x) (comp k s C x))
      (g := fun x => gauge K (comp k s C x)) (c := 1) hmem_comp ?_ ?_
    · have hcomp : Continuous (fun x : EuclideanSpace ℝ (Fin N) => comp k s C x) := by
        simp only [comp, Submission.GaussianChaos.herm]
        fun_prop
      exact hΨm.inner hcomp.aestronglyMeasurable
    · filter_upwards with x
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (gauge_nonneg _)]
      have h2 : gauge (polar K) (Ψ x) * gauge K (comp k s C x) ≤ 1 * gauge K (comp k s C x) :=
        mul_le_mul_of_nonneg_right (hΨ x) (gauge_nonneg _)
      have h3 := abs_inner_le_gauge_polar K hcvx hcpt habs hbdd h0 hKsymm (Ψ x) (comp k s C x)
      exact le_trans h3 h2
  -- the Bessel bound for each component
  have hiii : ∀ k : ℕ, ∫ x, (inner ℝ (Ψ x) (comp k s C x)) ^ 2 ∂Submission.GaussianChaos.μ N
      ≤ d ^ 2 * A := by
    intro k
    have hpt : ∀ x, (inner ℝ (Ψ x) (comp k s C x)) ^ 2 ≤ (gauge K (comp k s C x)) ^ 2 := by
      intro x
      have h2 : gauge (polar K) (Ψ x) * gauge K (comp k s C x) ≤ gauge K (comp k s C x) := by
        simpa using mul_le_mul_of_nonneg_right (hΨ x) (gauge_nonneg _)
      have h1 : |inner ℝ (Ψ x) (comp k s C x)| ≤ gauge K (comp k s C x) :=
        le_trans (abs_inner_le_gauge_polar K hcvx hcpt habs hbdd h0 hKsymm (Ψ x) (comp k s C x)) h2
      rw [← sq_abs (inner ℝ (Ψ x) (comp k s C x))]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have hint1 : Integrable (fun x => (inner ℝ (Ψ x) (comp k s C x)) ^ 2)
        (Submission.GaussianChaos.μ N) := by
      have h := (hfmem k).norm_rpow (by norm_num) (by norm_num)
      have := h.integrable le_rfl
      simpa [sq_abs] using this
    have hint2 : Integrable (fun x => (gauge K (comp k s C x)) ^ 2)
        (Submission.GaussianChaos.μ N) := by
      have hmem_comp : MemLp (fun x => gauge K (comp k s C x)) 2
          (Submission.GaussianChaos.μ N) := by
        exact memLp_gauge_hermSum K hcvx hKnhds d (le_trans zero_le_one hd) T hT1 hT2
          (s.filter (fun α => deg α = k)) C
      have h := hmem_comp.norm_rpow (by norm_num) (by norm_num)
      have := h.integrable le_rfl
      simpa using this
    calc ∫ x, (inner ℝ (Ψ x) (comp k s C x)) ^ 2 ∂Submission.GaussianChaos.μ N
        ≤ ∫ x, (gauge K (comp k s C x)) ^ 2 ∂Submission.GaussianChaos.μ N :=
          integral_mono hint1 hint2 hpt
      _ ≤ d ^ 2 * A := by
          rw [hA]
          exact integral_gauge_comp_le K hcvx habs h0 (le_trans zero_le_one hd) T hT1 hT2 s C k
  -- the chaos components vanish outside the degree set
  have hcomp_zero : ∀ k : ℕ, k ∉ s.image deg →
      comp k s C = fun _ => (0 : EuclideanSpace ℝ (Fin n)) := by
    intro k hk
    funext x
    simp only [comp]
    apply Finset.sum_eq_zero
    intro α hα
    rw [Finset.mem_filter] at hα
    exact absurd (hα.2 ▸ Finset.mem_image_of_mem deg hα.1) hk
  have hmehler : ∀ (ρ : ℝ), ρ ^ 2 < 1 → ∀ x : EuclideanSpace ℝ (Fin N),
      ∑ k ∈ s.image deg, (ρ ^ k) • comp k s C x
        = mehler ρ (Submission.GaussianChaos.hermSum s C) x := by
    intro ρ hρ x
    rw [mehler_hermSum s C ρ hρ x, hermSum_damped s C ρ x]
  by_cases hAz : A = 0
  · have h1 := hiii 1
    rw [hAz, mul_zero] at h1
    refine le_trans h1 ?_
    rw [hAz]
    positivity
  · have hApos : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hAz)
    have hsqrtpos : 0 < Real.sqrt A := Real.sqrt_pos.mpr hApos
    haveI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
    let y : ℕ → Lp ℝ 2 (Submission.GaussianChaos.μ N) :=
      fun k => (hfmem k).toLp (fun x => inner ℝ (Ψ x) (comp k s C x))
    have hy_norm : ∀ k, ‖y k‖ = Real.sqrt (∫ x, (inner ℝ (Ψ x) (comp k s C x)) ^ 2
        ∂Submission.GaussianChaos.μ N) := fun k => norm_toLp_sqrt (hfmem k)
    have hy_zero : ∀ k : ℕ, k ∉ s.image deg → y k = 0 := by
      intro k hk
      have hzero : ∀ x : EuclideanSpace ℝ (Fin N), inner ℝ (Ψ x) (comp k s C x) = 0 := by
        intro x
        rw [hcomp_zero k hk]
        simp
      have h0 : MemLp (0 : EuclideanSpace ℝ (Fin N) → ℝ) 2 (Submission.GaussianChaos.μ N) :=
        memLp_const (c := (0 : ℝ))
      exact (MemLp.toLp_congr (hfmem k) h0 (Filter.Eventually.of_forall hzero)).trans
        (MemLp.toLp_zero h0)
    -- (i) the normalised sequence has norms bounded by `d`
    have hc : ∀ k, ‖(Real.sqrt A)⁻¹ • y k‖ ≤ d := by
      intro k
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsqrtpos), hy_norm k]
      calc (Real.sqrt A)⁻¹ * Real.sqrt (∫ x, (inner ℝ (Ψ x) (comp k s C x)) ^ 2
            ∂Submission.GaussianChaos.μ N)
          ≤ (Real.sqrt A)⁻¹ * Real.sqrt (d ^ 2 * A) :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hiii k)) (by positivity)
        _ = d := by
            rw [Real.sqrt_mul (sq_nonneg d), Real.sqrt_sq (le_trans zero_le_one hd)]
            rw [mul_comm d (Real.sqrt A), ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hsqrtpos),
              one_mul]
    -- (ii) the power series is bounded by 1
    have hsup : ∀ ρ : ℝ, |ρ| ≤ 1 / 2 →
        ‖∑' k : ℕ, ρ ^ k • ((Real.sqrt A)⁻¹ • y k)‖ ≤ 1 := by
      intro ρ hρ
      have hρ1 : |ρ| < 1 := lt_of_le_of_lt hρ (by norm_num)
      have hρ2 : ρ ^ 2 < 1 := by nlinarith [sq_abs ρ, abs_nonneg ρ, hρ1]
      have hfin : (∑' k : ℕ, ρ ^ k • ((Real.sqrt A)⁻¹ • y k))
          = ∑ k ∈ s.image deg, ρ ^ k • ((Real.sqrt A)⁻¹ • y k) :=
        tsum_eq_sum (s := s.image deg) fun k hk => by
          have hz : (ρ ^ k) • ((Real.sqrt A)⁻¹ • (0 : Lp ℝ 2 (Submission.GaussianChaos.μ N))) = 0 := by
            rw [smul_zero, smul_zero]
          rw [hy_zero k hk]
          exact hz
      rw [hfin]
      rw [show ∑ k ∈ s.image deg, ρ ^ k • ((Real.sqrt A)⁻¹ • y k)
          = ∑ k ∈ s.image deg, (Real.sqrt A)⁻¹ • (ρ ^ k • y k) from
        Finset.sum_congr rfl fun k _ => smul_comm _ _ _]
      rw [← Finset.smul_sum]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsqrtpos)]
      -- compute the norm of the `Lp` sum
      have hnorm : ‖∑ k ∈ s.image deg, ρ ^ k • y k‖
          = Real.sqrt (∫ x, (inner ℝ (Ψ x)
              (mehler ρ (Submission.GaussianChaos.hermSum s C) x)) ^ 2
              ∂Submission.GaussianChaos.μ N) := by
        refine norm_finsetSum_toLp (s.image deg) (fun k => ρ ^ k)
          (fun k x => inner ℝ (Ψ x) (comp k s C x)) hfmem
          (fun x => inner ℝ (Ψ x) (mehler ρ (Submission.GaussianChaos.hermSum s C) x)) ?_ ?_
        · have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin N) =>
              ∑ k ∈ s.image deg, (ρ ^ k) • comp k s C x) := by
            refine continuous_finsetSum _ fun k _ => ?_
            have hcomp : Continuous (fun x : EuclideanSpace ℝ (Fin N) => comp k s C x) :=
              continuous_hermSum (s.filter (fun α => deg α = k)) C
            fun_prop
          have heq : (fun x : EuclideanSpace ℝ (Fin N) =>
                mehler ρ (Submission.GaussianChaos.hermSum s C) x)
              = fun x => ∑ k ∈ s.image deg, (ρ ^ k) • comp k s C x := by
            funext x
            exact (hmehler ρ hρ2 x).symm
          rw [show (fun x => inner ℝ (Ψ x) (mehler ρ (Submission.GaussianChaos.hermSum s C) x))
              = (fun x => inner ℝ (Ψ x) (∑ k ∈ s.image deg, (ρ ^ k) • comp k s C x)) from by
            funext x
            rw [congrFun heq x]]
          exact hΨm.inner hcont.aestronglyMeasurable
        · filter_upwards with x
          rw [← hmehler ρ hρ2 x, inner_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [inner_smul_right, mul_comm]
      rw [hnorm]
      -- the integral bound
      have hIntR : Integrable (fun x => (∫ y, mehlerK ρ x y *
          gauge K (Submission.GaussianChaos.hermSum s C y) ∂volume) ^ 2)
          (Submission.GaussianChaos.μ N) := by
        have h := Commons.Analysis.GaussianMeasure.integrable_mehler_sq K hcvx (interior_subset h0)
          habs hbdd hbal ρ hρ2 s C
        rw [Submission.GaussianChaos.μ]
        rw [MeasureTheory.integrable_withDensity_iff_integrable_smul'
          (f := fun x : EuclideanSpace ℝ (Fin N) => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2 / 2)))
          (by fun_prop) (by simp)]
        rw [show (fun x : EuclideanSpace ℝ (Fin N) =>
              (ENNReal.ofReal (Real.exp (-‖x‖ ^ 2 / 2))).toReal •
                (∫ y : EuclideanSpace ℝ (Fin N), mehlerK ρ x y * gauge K (Submission.GaussianChaos.hermSum s C y) ∂volume) ^ 2)
            = (fun x => (∫ y, mehlerK ρ x y *
                gauge K (Submission.GaussianChaos.hermSum s C y) ∂volume) ^ 2 *
                Real.exp (-‖x‖ ^ 2 / 2)) from by
          funext x
          rw [smul_eq_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
          ring]
        exact h
      have hmehlerint :
          ∫ x, (inner ℝ (Ψ x) (mehler ρ (Submission.GaussianChaos.hermSum s C) x)) ^ 2
            ∂Submission.GaussianChaos.μ N ≤ A := by
        have hint := Commons.Analysis.GaussianMeasure.integrable_mehler_data K hcvx
          (interior_subset h0) habs hbdd hbal ρ hρ2 s C
        have hbound : ∀ x, (inner ℝ (Ψ x) (mehler ρ (Submission.GaussianChaos.hermSum s C) x)) ^ 2
            ≤ (∫ y, mehlerK ρ x y * gauge K (Submission.GaussianChaos.hermSum s C y)
                ∂volume) ^ 2 := by
          intro x
          have hJ := mehler_gauge_le_normalized K hcvx (interior_subset h0) habs hbdd hbal ρ hρ2 x
            (Submission.GaussianChaos.hermSum s C)
            (by simpa [Submission.GaussianChaos.hermSum, Submission.GaussianChaos.herm] using hint.1 x)
            (by simpa [Submission.GaussianChaos.hermSum, Submission.GaussianChaos.herm] using hint.2 x)
          have h3 : |inner ℝ (Ψ x) (mehler ρ (Submission.GaussianChaos.hermSum s C) x)|
              ≤ ∫ y : EuclideanSpace ℝ (Fin N), mehlerK ρ x y *
                gauge K (Submission.GaussianChaos.hermSum s C y) ∂volume := by
            refine le_trans (abs_inner_le_gauge_polar K hcvx hcpt habs hbdd h0 hKsymm _ _) ?_
            have h2 : gauge (polar K) (Ψ x) * gauge K (mehler ρ (Submission.GaussianChaos.hermSum s C) x)
                ≤ 1 * gauge K (mehler ρ (Submission.GaussianChaos.hermSum s C) x) :=
              mul_le_mul_of_nonneg_right (hΨ x) (gauge_nonneg _)
            rw [one_mul] at h2
            exact le_trans h2 hJ
          rw [← sq_abs (inner ℝ (Ψ x) (mehler ρ (Submission.GaussianChaos.hermSum s C) x))]
          exact pow_le_pow_left₀ (abs_nonneg _) h3 2
        calc ∫ x, (inner ℝ (Ψ x) (mehler ρ (Submission.GaussianChaos.hermSum s C) x)) ^ 2
              ∂Submission.GaussianChaos.μ N
            ≤ ∫ x, (∫ y, mehlerK ρ x y *
                gauge K (Submission.GaussianChaos.hermSum s C y) ∂volume) ^ 2
                ∂Submission.GaussianChaos.μ N :=
              integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _) hIntR
                (Filter.Eventually.of_forall hbound)
          _ ≤ A := by
              rw [hA]
              exact mehler_scalar_contraction K hcvx (interior_subset h0) habs hbdd hbal ρ hρ2 s C
      calc (Real.sqrt A)⁻¹ * Real.sqrt (∫ x, (inner ℝ (Ψ x)
              (mehler ρ (Submission.GaussianChaos.hermSum s C) x)) ^ 2
              ∂Submission.GaussianChaos.μ N)
          ≤ (Real.sqrt A)⁻¹ * Real.sqrt A :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmehlerint) (by positivity)
        _ = 1 := by field_simp
    have hmain := Commons.Analysis.Normed.analytic_coeff_bound
      (x := fun k => (Real.sqrt A)⁻¹ • y k) d hd hc hsup
    -- transfer the bound back
    have hnorm1 : ‖(Real.sqrt A)⁻¹ • y 1‖
        = (Real.sqrt A)⁻¹ * Real.sqrt (∫ x, (inner ℝ (Ψ x) (comp 1 s C x)) ^ 2
            ∂Submission.GaussianChaos.μ N) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hsqrtpos), hy_norm 1]
    rw [hnorm1] at hmain
    have hfinal : Real.sqrt (∫ x, (inner ℝ (Ψ x) (comp 1 s C x)) ^ 2
        ∂Submission.GaussianChaos.μ N)
        ≤ (4 * (1 + Real.log d / Real.log 2)) * Real.sqrt A := by
      have h := mul_le_mul_of_nonneg_left hmain hsqrtpos.le
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hsqrtpos), one_mul] at h
      rwa [mul_comm] at h
    calc ∫ x, (inner ℝ (Ψ x) (comp 1 s C x)) ^ 2 ∂Submission.GaussianChaos.μ N
        = (Real.sqrt (∫ x, (inner ℝ (Ψ x) (comp 1 s C x)) ^ 2
            ∂Submission.GaussianChaos.μ N)) ^ 2 :=
          (Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)).symm
      _ ≤ ((4 * (1 + Real.log d / Real.log 2)) * Real.sqrt A) ^ 2 :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) hfinal 2
      _ = (4 * (1 + Real.log d / Real.log 2)) ^ 2 * A := by
          rw [mul_pow, Real.sq_sqrt hA0]

end ScalarBound

end Submission.KConvex
