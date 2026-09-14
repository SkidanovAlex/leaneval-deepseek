import Mathlib
import Submission.KConvexL2
import Submission.Commons.GeometryOfNumbers.EllNorm.sSup_inner_image_eq_gauge_polar
import Submission.Commons.Topology.exists_seq_denseRange_of_isCompact
import Submission.Commons.MeasureTheory.measurable_argmax_select
import Submission.Commons.GeometryOfNumbers.EllNorm.lewis_ellNorm_max
import Submission.Commons.GeometryOfNumbers.Lattice.exists_gauge_euclidean_comparison
import Submission.Commons.Analysis.GaussianMeasure.integral_gauge_sq_exp_pi_eq

/-!
# The `ℓℓ*` theorem (Figiel–Tomczak-Jaegermann / Lewis / Pisier) and its assembly

This file proves the sharp `ℓℓ*` inequality

`inf_{det A = 1} ℓ_K(A) · ℓ_{K°}((Aᵀ)⁻¹) ≤ m (log₂ m + 2) / π`

for a symmetric convex body `K ⊆ ℝᵐ` of volume one, in the normalization
`ℓ_K(A)² = ∫ (gauge K (A x))² e^{-π‖x‖²} dx` used in Regev–Stephens-Davidowitz §4.3.  This is the
last external input of the development.

The proof follows Pisier's book (*The volume of convex bodies and Banach space geometry*, CUP
1989):

* Lewis's theorem (`Commons.GeometryOfNumbers.EllNorm.lewis_ellNorm_max`) gives `A₀` maximizing the
  determinant on the Gaussian `ℓ`-ball, with `ℓ_K(A₀) ≤ 1` and `ℓ*_K(A₀⁻¹) ≤ m`.
* Pisier's Lemma 3.10 (`ell_ell_star_aux` below) turns the `ℓ*`-bound into
  `ℓ_{K°}((A₀ᵀ)⁻¹) ≤ K(X) · m`, where `K(X)` is the K-convexity constant of `X = (ℝᵐ, ‖·‖_K)`.
* Pisier's Theorem 2.5 with the explicit constant `4` (the analytic heart, proved in
  `Submission.KConvex.lean`, `Submission.KConvexGauge.lean` and `Submission.KConvexL2.lean`)
  gives `K(X) ≤ 4 (1 + log₂ d(X, ℓ₂ᵐ)) ≤ 4 (1 + ½ log₂ m)` by John's theorem
  (`Commons.GeometryOfNumbers.Lattice.exists_gauge_euclidean_comparison`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open MeasureTheory Matrix Filter Set
open scoped BigOperators ENNReal Topology Real Pointwise

namespace Submission.EllEllStar

open Submission.KConvex Submission.GaussianChaos Submission.KConvexL2 Submission.KConvexGauge
  Submission.LEllStar

variable {m : ℕ}
noncomputable section

/-! ## Coordinate bookkeeping for vector-valued Gaussian integrals -/

/-- Coordinate functionals commute with the Bochner integral on `ℝᵐ`. -/
theorem integral_ofLp_coord (Φ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hΦ : Integrable Φ (μ m)) (j : Fin m) :
    ∫ x, (Φ x).ofLp j ∂μ m = (∫ x, Φ x ∂μ m).ofLp j :=
  ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj j) hΦ

theorem smul_ofLp (c : ℝ) (y : EuclideanSpace ℝ (Fin m)) (j : Fin m) :
    (c • y).ofLp j = c * y.ofLp j := by simp

theorem ofLp_toLpLin_transpose (v : Matrix (Fin m) (Fin m) ℝ) (x : EuclideanSpace ℝ (Fin m))
    (j : Fin m) :
    (Matrix.toLpLin 2 2 vᵀ x).ofLp j = ∑ i, v i j * x.ofLp i := by
  rw [Matrix.toLpLin_apply, WithLp.ofLp_toLp, Matrix.mulVec_apply]
  simp only [dotProduct, Matrix.row, Matrix.transpose_apply]

theorem inner_toLpLin_expand (v : Matrix (Fin m) (Fin m) ℝ)
    (Ψ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (Ψ x) (Matrix.toLpLin 2 2 vᵀ x)
      = ∑ j, ∑ i, v i j * ((x.ofLp i) • Ψ x).ofLp j := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Real.inner_apply, ofLp_toLpLin_transpose, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_ofLp]
  ring

/-- The Bochner inner product `∫ ⟪Ψ x, vᵀ x⟫` of a vector-valued function with the linear map
`vᵀ` is `gaussZ m` times the matrix trace `tr (v · X)`, where `X` collects the first chaos
coefficients of `Ψ`. -/
theorem integral_inner_toLpLin_eq_trace
    (v : Matrix (Fin m) (Fin m) ℝ) (Ψ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hΨ : ∀ i : Fin m, Integrable (fun x => (x.ofLp i) • Ψ x) (μ m)) :
    ∫ x, inner ℝ (Ψ x) (Matrix.toLpLin 2 2 vᵀ x) ∂μ m
      = gaussZ m * Matrix.trace (v * Matrix.of (fun i j =>
          ((gaussZ m)⁻¹ • ∫ x, (x.ofLp j) • Ψ x ∂μ m).ofLp i)) := by
  classical
  set W : Fin m → EuclideanSpace ℝ (Fin m) :=
    fun i => ∫ x, (x.ofLp i) • Ψ x ∂μ m with hWdef
  set c : Fin m → EuclideanSpace ℝ (Fin m) := fun j => (gaussZ m)⁻¹ • W j with hcdef
  set X : Matrix (Fin m) (Fin m) ℝ := Matrix.of (fun i j => (c j).ofLp i) with hXdef
  have hpoint : ∀ x, inner ℝ (Ψ x) (Matrix.toLpLin 2 2 vᵀ x)
      = ∑ j, ∑ i, v i j * ((x.ofLp i) • Ψ x).ofLp j := fun x => inner_toLpLin_expand v Ψ x
  rw [show (∫ x, inner ℝ (Ψ x) (Matrix.toLpLin 2 2 vᵀ x) ∂μ m)
      = ∫ x, ∑ j, ∑ i, v i j * ((x.ofLp i) • Ψ x).ofLp j ∂μ m from
        integral_congr_ae (Eventually.of_forall hpoint)]
  have hInt2 : ∀ j i : Fin m,
      Integrable (fun x => v i j * ((x.ofLp i) • Ψ x).ofLp j) (μ m) := by
    intro j i
    have h : Integrable (fun x => (EuclideanSpace.proj j) ((x.ofLp i) • Ψ x)) (μ m) := by
      fun_prop
    refine (h.const_mul (v i j)).congr (Eventually.of_forall fun x => ?_)
    simp only [PiLp.proj_apply]
  have hInt1 : ∀ j : Fin m,
      Integrable (fun x => ∑ i, v i j * ((x.ofLp i) • Ψ x).ofLp j) (μ m) :=
    fun j => integrable_finsetSum Finset.univ (fun i _ => hInt2 j i)
  rw [integral_finsetSum Finset.univ (fun j _ => hInt1 j)]
  have hinner : ∀ j : Fin m, (∫ x, ∑ i, v i j * ((x.ofLp i) • Ψ x).ofLp j ∂μ m)
      = ∑ i, v i j * (W i).ofLp j := by
    intro j
    rw [integral_finsetSum Finset.univ (fun i _ => hInt2 j i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul]
    congr 1
    exact integral_ofLp_coord (fun x => (x.ofLp i) • Ψ x) (hΨ i) j
  rw [Finset.sum_congr rfl (fun j _ => hinner j)]
  have hWsmul : ∀ i : Fin m, W i = gaussZ m • c i := by
    intro i
    have h1 : c i = (gaussZ m)⁻¹ • W i := congrFun hcdef i
    rw [h1, smul_smul, mul_inv_cancel₀ (gaussZ_ne_zero m), one_smul]
  have htr : Matrix.trace (v * X) = ∑ j, ∑ i, v j i * (c j).ofLp i := by
    rw [Matrix.trace]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hXdef, Matrix.of_apply]
  rw [htr]
  rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hWsmul, smul_ofLp]
  ring



theorem ofLp_toLpLin_apply (M : Matrix (Fin m) (Fin m) ℝ)
    (x : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    (Matrix.toLpLin 2 2 M x).ofLp i = ∑ j, M i j * x.ofLp j := by
  rw [Matrix.toLpLin_apply, WithLp.ofLp_toLp, Matrix.mulVec_apply, Matrix.row]
  simp only [dotProduct]

/-- The adjoint relation `⟪p, M x⟫ = ⟪Mᵀ p, x⟫` for the Euclidean inner product. -/
theorem inner_toLpLin_comm (M : Matrix (Fin m) (Fin m) ℝ)
    (p x : EuclideanSpace ℝ (Fin m)) :
    inner ℝ p (Matrix.toLpLin 2 2 M x) = inner ℝ (Matrix.toLpLin 2 2 Mᵀ p) x := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [Real.inner_apply, ofLp_toLpLin_apply]
  have h1 : ∀ i : Fin m, p.ofLp i * (∑ j, M i j * x.ofLp j)
      = ∑ j, (M i j * p.ofLp i) * x.ofLp j := by
    intro i
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : ∀ i : Fin m, (∑ j, Mᵀ i j * p.ofLp j) * x.ofLp i
      = ∑ j, (M j i * p.ofLp j) * x.ofLp i := by
    intro i
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [Matrix.transpose_apply]
  rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_congr rfl (fun i _ => h2 i),
    Finset.sum_comm]

/-- The sup-representation of the polar gauge in the form used by the `ℓℓ*` statement:
`sup{⟪y,x⟫ : y ∈ B '' K} = gauge K° (Bᵀ x)`. -/
theorem sSup_inner_image_mul_eq (K : Set (EuclideanSpace ℝ (Fin m)))
    (hsym : ∀ z ∈ K, -z ∈ K) (hbdd : Bornology.IsBounded K)
    (B : Matrix (Fin m) (Fin m) ℝ) (x : EuclideanSpace ℝ (Fin m)) :
    sSup ((fun y => inner ℝ y x) ''
        (Set.image (fun v => Matrix.toLpLin 2 2 B v) K))
      = gauge (polar K) (Matrix.toLpLin 2 2 Bᵀ x) := by
  have key : ∀ v : EuclideanSpace ℝ (Fin m),
      inner ℝ (Matrix.toLpLin 2 2 B v) x = inner ℝ v (Matrix.toLpLin 2 2 Bᵀ x) := by
    intro v
    rw [inner_toLpLin_comm Bᵀ v x, Matrix.transpose_transpose]
  have hset : Set.image (fun y => inner ℝ y x)
        (Set.image (fun v => Matrix.toLpLin 2 2 B v) K)
      = (fun z => inner ℝ z (Matrix.toLpLin 2 2 Bᵀ x)) '' K := by
    ext a
    constructor
    · rintro ⟨y, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨v, hv, by simp only [key v]⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨Matrix.toLpLin 2 2 B v, ⟨v, hv, rfl⟩, by simp only [key v]⟩
  rw [hset]
  exact Commons.GeometryOfNumbers.EllNorm.sSup_inner_image_eq_gauge_polar K hsym hbdd
    (Matrix.toLpLin 2 2 Bᵀ x)

/-- **Normalisation change for Gaussian integrals of squared gauges.**  The `e^{-π‖x‖²}`
normalisation used by Regev–Stephens-Davidowitz differs from the `e^{-‖x‖²/2}` normalisation by
the factor `gaussZ m · 2π`. -/
theorem integral_gauge_sq_exp_pi (K : Set (EuclideanSpace ℝ (Fin m)))
    (A : Matrix (Fin m) (Fin m) ℝ) :
    ∫ x : EuclideanSpace ℝ (Fin m),
        (gauge K (Matrix.toLpLin 2 2 A x)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)
      = (gaussZ m * (2 * Real.pi))⁻¹ *
        ∫ x : EuclideanSpace ℝ (Fin m),
          (gauge K (Matrix.toLpLin 2 2 A x)) ^ 2 * Real.exp (-‖x‖ ^ 2 / 2) := by
  set R : ℝ := Real.sqrt (2 * Real.pi) with hRdef
  have hRnn : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
  have hpow : R ^ m = gaussZ m := by rw [gaussZ, hRdef]
  set F : EuclideanSpace ℝ (Fin m) → ℝ :=
    fun x => (gauge K (Matrix.toLpLin 2 2 A x)) ^ 2 * Real.exp (-‖x‖ ^ 2 / 2) with hF
  set G : EuclideanSpace ℝ (Fin m) → ℝ :=
    fun x => (gauge K (Matrix.toLpLin 2 2 A x)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2) with hG
  have key : ∀ x : EuclideanSpace ℝ (Fin m), F (R • x) = (2 * Real.pi) * G x := by
    intro x
    have hg : gauge K (Matrix.toLpLin 2 2 A (R • x))
        = R * gauge K (Matrix.toLpLin 2 2 A x) := by
      rw [LinearMap.map_smul, gauge_smul_of_nonneg hRnn, smul_eq_mul]
    have hn : ‖R • x‖ ^ 2 = (2 * Real.pi) * ‖x‖ ^ 2 := by
      rw [norm_smul, Real.norm_of_nonneg hRnn, mul_pow, hR2]
    have he : (-‖R • x‖ ^ 2 / 2 : ℝ) = -Real.pi * ‖x‖ ^ 2 := by rw [hn]; ring
    simp only [hF, hG]
    rw [hg, he, mul_pow, hR2]
    ring
  have hInt := MeasureTheory.Measure.integral_comp_smul_of_nonneg (μ := volume) F R (hR := hRnn)
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m := by simp [EuclideanSpace, PiLp]
  have hLHS : (∫ x, F (R • x)) = (2 * Real.pi) * ∫ x, G x := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall key)
  have hmain : (2 * Real.pi) * (∫ x, G x) = (R ^ m)⁻¹ * (∫ x, F x) := by
    rw [hfin] at hInt
    rw [hLHS] at hInt
    simpa [smul_eq_mul] using hInt
  have hne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  calc ∫ x, G x = (2 * Real.pi)⁻¹ * ((2 * Real.pi) * ∫ x, G x) := by
        rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    _ = (2 * Real.pi)⁻¹ * ((R ^ m)⁻¹ * ∫ x, F x) := by rw [hmain]
    _ = ((2 * Real.pi) * R ^ m)⁻¹ * (∫ x, F x) := by rw [← mul_assoc, ← mul_inv]
    _ = (gaussZ m * (2 * Real.pi))⁻¹ * (∫ x, F x) := by rw [hpow, mul_comm (2 * Real.pi) (gaussZ m)]

/-- The first-chaos coefficient matrix `Matrix.of (fun i j => (c j) i)` acts by `Q1`. -/
theorem toLpLin_matrixOf_eq (c : Fin m → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin m)) :
    Matrix.toLpLin 2 2 (Matrix.of (fun i j => (c j).ofLp i)) x
      = ∑ j : Fin m, (x.ofLp j) • c j := by
  rw [Matrix.toLpLin_apply]
  apply WithLp.ofLp_injective
  rw [WithLp.ofLp_toLp, WithLp.ofLp_sum]
  funext i
  rw [Finset.sum_apply, Matrix.mulVec_apply, Matrix.row]
  simp only [dotProduct, Matrix.of_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [smul_ofLp]; ring

/-! ## Pisier's Lemma 3.10 -/

/-- **Pisier's Lemma 3.10 (ℓ-position comparison).**  For a symmetric convex body `K ⊆ ℝᵐ`
whose gauge is `d`-equivalent to a Euclidean norm, and any matrix `v` whose trace pairing with
the `ℓ`-unit ball is bounded by `L`, the dual `ℓ`-norm of `v` is at most
`gaussZ m · 4(1 + log₂ d) · L`.

Equivalently `ℓ_{K°}(vᵀ) ≤ K(X) · ℓ*_K(v)` — the analytic content of Pisier's comparison
between the ℓ-position and the ℓ*-position. -/
theorem ell_ell_star_aux (K : Set (EuclideanSpace ℝ (Fin m)))
    (hcvx : Convex ℝ K) (habs : Absorbent ℝ K) (hbdd : Bornology.IsVonNBounded ℝ K)
    (hbal : Balanced ℝ K) (hcpt : IsCompact K)
    (h0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior K)
    (hKsymm : (-K : Set (EuclideanSpace ℝ (Fin m))) = K)
    {d : ℝ} (hd : 1 ≤ d) (T : EuclideanSpace ℝ (Fin m) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (hT1 : ∀ x, ‖T x‖ ≤ gauge K x) (hT2 : ∀ x, gauge K x ≤ d * ‖T x‖)
    (v : Matrix (Fin m) (Fin m) ℝ) (L : ℝ) (hLnn : 0 ≤ L)
    (hL : ∀ X : Matrix (Fin m) (Fin m) ℝ, ellSq K X ≤ 1 → Matrix.trace (v * X) ≤ L) :
    ellSq (polar K) vᵀ ≤ (gaussZ m * (4 * (1 + Real.log d / Real.log 2)) * L) ^ 2 := by
  classical
  set C0 : ℝ := 4 * (1 + Real.log d / Real.log 2) with hC0
  have hd0 : 0 ≤ d := le_trans zero_le_one hd
  have hC0nn : 0 ≤ C0 := by rw [hC0]; have := Real.log_nonneg hd; positivity
  have hKbdd : Bornology.IsBounded K := hcpt.isBounded
  have hsym : ∀ z ∈ K, -z ∈ K := fun z hz => by
    rw [← hKsymm] at hz
    exact Set.mem_neg.mp hz
  obtain ⟨R, hR⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace ℝ (Fin m))).mp hKbdd
  have hRmem : ∀ z ∈ K, ‖z‖ ≤ R := fun z hz => by
    have h := hR hz
    rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
  have hRnn : 0 ≤ R := le_trans (norm_nonneg (0 : EuclideanSpace ℝ (Fin m)))
    (hRmem 0 (interior_subset h0))
  set Y : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) :=
    fun x => Matrix.toLpLin 2 2 vᵀ x with hY
  have hYcont : Continuous Y := by rw [hY]; fun_prop
  have hYmeas : Measurable Y := hYcont.measurable
  have hgsSup : ∀ w, gauge (polar K) w
      = sSup ((fun z : EuclideanSpace ℝ (Fin m) => inner ℝ z w) '' K) := fun w =>
    (Commons.GeometryOfNumbers.EllNorm.sSup_inner_image_eq_gauge_polar K hsym hKbdd w).symm
  have hinner_le : ∀ z ∈ K, ∀ w, inner ℝ z w ≤ R * ‖w‖ := fun z hz w =>
    calc inner ℝ z w ≤ ‖inner ℝ z w‖ := le_abs_self _
      _ ≤ ‖z‖ * ‖w‖ := norm_inner_le_norm z w
      _ ≤ R * ‖w‖ := mul_le_mul_of_nonneg_right (hRmem z hz) (norm_nonneg w)
  have hbddAbove : ∀ w, BddAbove ((fun z : EuclideanSpace ℝ (Fin m) => inner ℝ z w) '' K) :=
    fun w => ⟨R * ‖w‖, by rintro a ⟨z, hz, rfl⟩; exact hinner_le z hz w⟩
  have hgle : ∀ w, gauge (polar K) w ≤ R * ‖w‖ := fun w => by
    rw [hgsSup w]
    exact csSup_le ⟨inner ℝ 0 w, ⟨0, interior_subset h0, rfl⟩⟩
      (by rintro a ⟨z, hz, rfl⟩; exact hinner_le z hz w)
  obtain ⟨ψ, hψK, hψdense⟩ :=
    Commons.Topology.exists_seq_denseRange_of_isCompact K ⟨0, interior_subset h0⟩
  have hsupseq : ∀ x, sSup (Set.range (fun n => inner ℝ (ψ n) (Y x))) = gauge (polar K) (Y x) :=
    fun x => (sSup_image_eq_sSup_range hKbdd hψK hψdense (Y x)).symm.trans (hgsSup (Y x)).symm
  choose g hgm hgset hgmax using fun M : ℕ =>
    Commons.MeasureTheory.measurable_argmax_select ψ Y
      (fun m => (continuous_const.inner hYcont).measurable) M
  set u : ℕ → EuclideanSpace ℝ (Fin m) → ℝ := fun M x => inner ℝ (g M x) (Y x) with hu
  have humeas : ∀ M, Measurable (u M) := fun M => (hgm M).inner hYmeas
  have hugK : ∀ M x, g M x ∈ K := fun M x => by
    obtain ⟨m, _, hm⟩ := hgset M x
    rw [hm]; exact hψK m
  have hubound : ∀ M x, u M x ≤ gauge (polar K) (Y x) := fun M x => by
    rw [hgsSup (Y x)]
    exact le_csSup (hbddAbove (Y x)) ⟨g M x, hugK M x, rfl⟩
  have huneg : ∀ M x, -u M x ≤ gauge (polar K) (Y x) := fun M x => by
    rw [hgsSup (Y x)]
    have h : -u M x = inner ℝ (-(g M x)) (Y x) := by
      simp only [hu, inner_neg_left]
    rw [h]
    exact le_csSup (hbddAbove (Y x)) ⟨-(g M x), hsym (g M x) (hugK M x), rfl⟩
  have huabs : ∀ M x, |u M x| ≤ gauge (polar K) (Y x) := fun M x =>
    abs_le'.mpr ⟨hubound M x, huneg M x⟩
  have hu_mono : ∀ x, Monotone (fun M => u M x) := by
    intro x M M' hMM'
    change u M x ≤ u M' x
    obtain ⟨m₀, hm₀, heq⟩ := hgset M x
    have h2 : u M x = inner ℝ (ψ m₀) (Y x) := by
      simp only [hu]
      rw [heq]
    rw [h2]
    exact hgmax M' x m₀ (le_trans hm₀ hMM')
  have hu_bdd : ∀ x, BddAbove (Set.range (fun M => u M x)) := fun x =>
    ⟨gauge (polar K) (Y x), by rintro a ⟨M, rfl⟩; exact hubound M x⟩
  have hu_sup : ∀ x, (⨆ M, u M x) = gauge (polar K) (Y x) := by
    intro x
    refine le_antisymm (ciSup_le (fun M => hubound M x)) ?_
    rw [← hsupseq x]
    refine csSup_le ⟨inner ℝ (ψ 0) (Y x), ⟨0, rfl⟩⟩ (fun b hb => ?_)
    obtain ⟨m, rfl⟩ := hb
    exact le_trans (hgmax m x m le_rfl) (le_ciSup (hu_bdd x) m)
  have hu_lim : ∀ x, Tendsto (fun M => u M x) atTop (𝓝 (gauge (polar K) (Y x))) := by
    intro x
    rw [← hu_sup x]
    exact tendsto_atTop_ciSup (hu_mono x) (hu_bdd x)
  have hYint : Integrable (fun x => ‖Y x‖ ^ 2) (μ m) := by
    simpa only [hY] using integrable_norm_sq_act vᵀ
  have hYmem : MemLp Y 2 (μ m) :=
    (memLp_two_iff_integrable_sq_norm hYmeas.aestronglyMeasurable).mpr hYint
  have hGmeas : Measurable (fun x => gauge (polar K) (Y x)) := by
    have h : Measurable (fun x : EuclideanSpace ℝ (Fin m) => ⨆ M : ℕ, u M x) :=
      Measurable.iSup humeas
    rwa [show (fun x => (⨆ M, u M x)) = fun x => gauge (polar K) (Y x) from
      funext fun x => hu_sup x] at h
  have hintf : Integrable (fun x => (gauge (polar K) (Y x)) ^ 2) (μ m) := by
    refine Integrable.mono' (g := fun x => R ^ 2 * ‖Y x‖ ^ 2) ?_ ?_ ?_
    · exact hYint.const_mul (R ^ 2)
    · exact (hGmeas.pow_const 2).aestronglyMeasurable
    · refine Eventually.of_forall fun x => ?_
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have h1 : gauge (polar K) (Y x) ≤ R * ‖Y x‖ := hgle (Y x)
      have h2 : 0 ≤ gauge (polar K) (Y x) := gauge_nonneg _
      calc (gauge (polar K) (Y x)) ^ 2 ≤ (R * ‖Y x‖) ^ 2 := pow_le_pow_left₀ h2 h1 2
        _ = R ^ 2 * ‖Y x‖ ^ 2 := by ring
  have hmean : Tendsto (fun M => ∫ x, (u M x) ^ 2 ∂μ m) atTop
      (𝓝 (∫ x, (gauge (polar K) (Y x)) ^ 2 ∂μ m)) := by
    refine tendsto_integral_of_dominated_convergence
      (μ := μ m) (F := fun M x => (u M x) ^ 2) (f := fun x => (gauge (polar K) (Y x)) ^ 2)
      (fun x => (gauge (polar K) (Y x)) ^ 2)
      (fun M => ((humeas M).pow_const 2).aestronglyMeasurable) hintf ?_ ?_
    · intro M
      exact Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (huabs M x) 2
    · exact Eventually.of_forall fun x => (hu_lim x).pow 2
  have hterm : ∀ M, ∫ x, (u M x) ^ 2 ∂μ m ≤ (gaussZ m * C0 * L) ^ 2 := by
    intro M
    set Ψ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) := fun x => u M x • g M x
      with hΨ
    have hΨmeas : Measurable Ψ := by
      rw [hΨ]; exact (humeas M).smul (hgm M)
    have hΨbound : ∀ x, ‖Ψ x‖ ≤ R ^ 2 * ‖Y x‖ := by
      intro x
      have h1 : ‖Ψ x‖ = |u M x| * ‖g M x‖ := by
        rw [hΨ]; simp [norm_smul, Real.norm_eq_abs]
      rw [h1]
      have h2 : |u M x| ≤ R * ‖Y x‖ := le_trans (huabs M x) (hgle (Y x))
      have h3 : ‖g M x‖ ≤ R := hRmem _ (hugK M x)
      calc |u M x| * ‖g M x‖ ≤ (R * ‖Y x‖) * R :=
            mul_le_mul h2 h3 (norm_nonneg _) (mul_nonneg hRnn (norm_nonneg _))
        _ = R ^ 2 * ‖Y x‖ := by ring
    have hΨmem : MemLp Ψ 2 (μ m) :=
      MemLp.of_le_mul (f := Ψ) (g := Y) (c := R ^ 2) hYmem
        hΨmeas.aestronglyMeasurable (Eventually.of_forall hΨbound)
    have hΨgmem : MemLp (fun x => gauge K (Ψ x)) 2 (μ m) := by
      refine MemLp.of_le_mul (f := fun x => gauge K (Ψ x)) (g := Y) (c := R) hYmem ?_ ?_
      · exact (continuous_gauge hcvx (mem_interior_iff_mem_nhds.mp h0)).comp_aestronglyMeasurable
          hΨmeas.aestronglyMeasurable
      · refine Eventually.of_forall fun x => ?_
        have h1 : gauge K (Ψ x) = |u M x| * gauge K (g M x) := by
          rw [hΨ, gauge_smul hbal, Real.norm_eq_abs]
        rw [h1, Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (gauge_nonneg _))]
        calc |u M x| * gauge K (g M x) ≤ |u M x| * 1 :=
              mul_le_mul_of_nonneg_left (gauge_le_one_of_mem (hugK M x)) (abs_nonneg _)
          _ = |u M x| := mul_one _
          _ ≤ R * ‖Y x‖ := le_trans (huabs M x) (hgle (Y x))
    have hQ1 : ∫ x, (gauge K (Q1 Ψ x)) ^ 2 ∂μ m
        ≤ C0 ^ 2 * ∫ x, (gauge K (Ψ x)) ^ 2 ∂μ m := by
      have h := kconvex_l2 K hcvx habs hbdd hbal hcpt h0 hKsymm hd T hT1 hT2 Ψ hΨmem hΨgmem
      rw [← hC0] at h
      exact h
    have hu2int : Integrable (fun x => (u M x) ^ 2) (μ m) := by
      refine Integrable.mono' (g := fun x => R ^ 2 * ‖Y x‖ ^ 2) (hYint.const_mul (R ^ 2))
        ((humeas M).pow_const 2).aestronglyMeasurable ?_
      refine Eventually.of_forall fun x => ?_
      rw [Real.norm_of_nonneg (sq_nonneg _), ← sq_abs]
      have h2 : |u M x| ≤ R * ‖Y x‖ := le_trans (huabs M x) (hgle (Y x))
      calc |u M x| ^ 2 ≤ (R * ‖Y x‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
        _ = R ^ 2 * ‖Y x‖ ^ 2 := by ring
    have hΨgcont : AEStronglyMeasurable (fun x => gauge K (Ψ x)) (μ m) :=
      (continuous_gauge hcvx (mem_interior_iff_mem_nhds.mp h0)).comp_aestronglyMeasurable
        hΨmeas.aestronglyMeasurable
    have hΨgint : Integrable (fun x => (gauge K (Ψ x)) ^ 2) (μ m) :=
      ((memLp_two_iff_integrable_sq_norm hΨgcont).mp hΨgmem).congr
        (Eventually.of_forall fun x => by simp only [Real.norm_eq_abs, sq_abs])
    have hgl : ∫ x, (gauge K (Ψ x)) ^ 2 ∂μ m ≤ ∫ x, (u M x) ^ 2 ∂μ m := by
      refine integral_mono hΨgint hu2int (fun x => ?_)
      have h1 : gauge K (Ψ x) ≤ |u M x| := by
        have h1' : gauge K (Ψ x) = |u M x| * gauge K (g M x) := by
          rw [hΨ, gauge_smul hbal, Real.norm_eq_abs]
        calc gauge K (Ψ x) = |u M x| * gauge K (g M x) := h1'
          _ ≤ |u M x| * 1 :=
              mul_le_mul_of_nonneg_left (gauge_le_one_of_mem (hugK M x)) (abs_nonneg _)
          _ = |u M x| := mul_one _
      calc (gauge K (Ψ x)) ^ 2 ≤ |u M x| ^ 2 := pow_le_pow_left₀ (gauge_nonneg _) h1 2
        _ = (u M x) ^ 2 := sq_abs _
    have hpointΨ : ∀ x, (u M x) ^ 2 = inner ℝ (Ψ x) (Y x) := by
      intro x
      have h2 : inner ℝ (g M x) (Y x) = u M x := by simp only [hu]
      have h1 : inner ℝ (Ψ x) (Y x) = u M x * inner ℝ (g M x) (Y x) := by
        rw [hΨ]; exact real_inner_smul_left _ _ _
      rw [h1, h2, sq]
    set XM : Matrix (Fin m) (Fin m) ℝ := Matrix.of (fun i j =>
      ((gaussZ m)⁻¹ • ∫ x, (x.ofLp j) • Ψ x ∂μ m).ofLp i) with hXM
    have htrace : ∫ x, inner ℝ (Ψ x) (Y x) ∂μ m = gaussZ m * Matrix.trace (v * XM) := by
      have h := integral_inner_toLpLin_eq_trace v Ψ (fun i => integrable_coord_smul hΨmem i)
      rw [hXM]
      simpa only [hY] using h
    have hAeq : ∫ x, (u M x) ^ 2 ∂μ m = gaussZ m * Matrix.trace (v * XM) := by
      rw [show (∫ x, (u M x) ^ 2 ∂μ m) = ∫ x, inner ℝ (Ψ x) (Y x) ∂μ m from
        integral_congr_ae (Eventually.of_forall hpointΨ)]
      exact htrace
    have hQ1eq : ellSq K XM = ∫ x, (gauge K (Q1 Ψ x)) ^ 2 ∂μ m := by
      have key : (fun x => gauge K (Matrix.toLpLin 2 2 XM x) ^ 2)
          = fun x => gauge K (Q1 Ψ x) ^ 2 := by
        funext x
        have h1 : Matrix.toLpLin 2 2 XM x = Q1 Ψ x := by
          rw [hXM]
          show Matrix.toLpLin 2 2 (Matrix.of (fun i j =>
              ((gaussZ m)⁻¹ • ∫ y, (y.ofLp j) • Ψ y ∂μ m).ofLp i)) x
            = ∑ j : Fin m,
                (x.ofLp j) • ((gaussZ m)⁻¹ • ∫ y, (y.ofLp j) • Ψ y ∂μ m)
          exact toLpLin_matrixOf_eq _ x
        rw [h1]
      rw [ellSq, key]
    have hA0 : 0 ≤ ∫ x, (u M x) ^ 2 ∂μ m := integral_nonneg fun x => sq_nonneg _
    have hstep1 : ∫ x, (u M x) ^ 2 ∂μ m ≤ gaussZ m * (L * Real.sqrt (ellSq K XM)) := by
      rw [hAeq]
      exact mul_le_mul_of_nonneg_left (trace_le_mul_sqrt_ellSq K hbal hLnn hL XM)
        (gaussZ_pos m).le
    have hellsq_bound : Real.sqrt (ellSq K XM) ≤ C0 * Real.sqrt (∫ x, (u M x) ^ 2 ∂μ m) := by
      have h1 : ellSq K XM ≤ C0 ^ 2 * ∫ x, (u M x) ^ 2 ∂μ m := by
        rw [hQ1eq]
        exact le_trans hQ1 (mul_le_mul_of_nonneg_left hgl (sq_nonneg C0))
      calc Real.sqrt (ellSq K XM) ≤ Real.sqrt (C0 ^ 2 * ∫ x, (u M x) ^ 2 ∂μ m) :=
            Real.sqrt_le_sqrt h1
        _ = C0 * Real.sqrt (∫ x, (u M x) ^ 2 ∂μ m) := by
            rw [Real.sqrt_mul (sq_nonneg C0), Real.sqrt_sq hC0nn]
    have hkey : ∫ x, (u M x) ^ 2 ∂μ m
        ≤ gaussZ m * L * C0 * Real.sqrt (∫ x, (u M x) ^ 2 ∂μ m) := by
      calc ∫ x, (u M x) ^ 2 ∂μ m ≤ gaussZ m * (L * Real.sqrt (ellSq K XM)) := hstep1
        _ ≤ gaussZ m * (L * (C0 * Real.sqrt (∫ x, (u M x) ^ 2 ∂μ m))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hellsq_bound hLnn) (gaussZ_pos m).le
        _ = gaussZ m * L * C0 * Real.sqrt (∫ x, (u M x) ^ 2 ∂μ m) := by ring
    have hsq_le : Real.sqrt (∫ x, (u M x) ^ 2 ∂μ m) ≤ gaussZ m * L * C0 := by
      rcases eq_or_lt_of_le (Real.sqrt_nonneg (∫ x, (u M x) ^ 2 ∂μ m)) with h | h
      · rw [← h]
        exact mul_nonneg (mul_nonneg (gaussZ_pos m).le hLnn) hC0nn
      · have hsq : Real.sqrt (∫ x, (u M x) ^ 2 ∂μ m) * Real.sqrt (∫ x, (u M x) ^ 2 ∂μ m)
            = ∫ x, (u M x) ^ 2 ∂μ m := Real.mul_self_sqrt hA0
        have h2 : Real.sqrt (∫ x, (u M x) ^ 2 ∂μ m) * Real.sqrt (∫ x, (u M x) ^ 2 ∂μ m)
            ≤ gaussZ m * L * C0 * Real.sqrt (∫ x, (u M x) ^ 2 ∂μ m) := by
          rw [hsq]; exact hkey
        exact le_of_mul_le_mul_right h2 h
    calc ∫ x, (u M x) ^ 2 ∂μ m = (Real.sqrt (∫ x, (u M x) ^ 2 ∂μ m)) ^ 2 :=
          (Real.sq_sqrt hA0).symm
      _ ≤ (gaussZ m * L * C0) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq_le 2
      _ = (gaussZ m * C0 * L) ^ 2 := by ring
  have hfin := le_of_tendsto' hmean hterm
  have hgoal_eq : ellSq (polar K) vᵀ
      = ∫ x, (gauge (polar K) (Y x)) ^ 2 ∂μ m := by
    simp only [ellSq, hY]
  rw [hgoal_eq]
  exact hfin


/-- Homogeneity of `ellSq` under a nonnegative scalar (no `Balanced` hypothesis needed). -/
theorem ellSq_smul_of_nonneg (K : Set (EuclideanSpace ℝ (Fin m))) {t : ℝ} (ht : 0 ≤ t)
    (X : Matrix (Fin m) (Fin m) ℝ) : ellSq K (t • X) = t ^ 2 * ellSq K X := by
  rw [ellSq, ellSq]
  have hpt : ∀ x : EuclideanSpace ℝ (Fin m),
      (gauge K (Matrix.toLpLin 2 2 (t • X) x)) ^ 2
        = t ^ 2 * (gauge K (Matrix.toLpLin 2 2 X x)) ^ 2 := by
    intro x
    rw [toLpLin_smul_apply, gauge_smul_of_nonneg ht, smul_eq_mul, mul_pow]
  rw [show (fun x : EuclideanSpace ℝ (Fin m) =>
        (gauge K (Matrix.toLpLin 2 2 (t • X) x)) ^ 2)
      = fun x => t ^ 2 * (gauge K (Matrix.toLpLin 2 2 X x)) ^ 2 from funext hpt]
  rw [integral_const_mul]

/-- The Gaussian integral of the squared support function of `B '' K` is the squared
`ℓ`-norm of the polar in the `e^{-π‖x‖²}` normalisation. -/
theorem integral_sSup_inner_eq (K : Set (EuclideanSpace ℝ (Fin m)))
    (hsym : ∀ z ∈ K, -z ∈ K) (hbdd : Bornology.IsBounded K)
    (B : Matrix (Fin m) (Fin m) ℝ) :
    ∫ x : EuclideanSpace ℝ (Fin m),
        (sSup ((fun y => inner ℝ y x) ''
          (Set.image (fun v => Matrix.toLpLin 2 2 B v) K))) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)
      = (gaussZ m * (2 * Real.pi))⁻¹ * ellSq (polar K) Bᵀ := by
  rw [show (fun x : EuclideanSpace ℝ (Fin m) =>
        (sSup ((fun y => inner ℝ y x) ''
          (Set.image (fun v => Matrix.toLpLin 2 2 B v) K))) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))
      = fun x => (gauge (polar K) (Matrix.toLpLin 2 2 Bᵀ x)) ^ 2
          * Real.exp (-Real.pi * ‖x‖ ^ 2) from
    funext fun x => by rw [sSup_inner_image_mul_eq K hsym hbdd B x]]
  rw [integral_gauge_sq_exp_pi (polar K) Bᵀ, ellSq, Submission.GaussianChaos.integral_μ]

/-- **The `ℓℓ*` inequality** (Figiel–Tomczak-Jaegermann 1979, Lewis 1979, Pisier 1982) in the
normalization used in Regev–Stephens-Davidowitz §4.3.

With `ℓ_K(A)² := ∫ (gauge K (A x))² e^{-π‖x‖²} dx` and the dual side written as
`ℓ_{K°}((Aᵀ)^{-1})² = ∫ (sup_{y ∈ K} ⟨y, (Aᵀ)^{-1} x⟩)² e^{-π‖x‖²} dx`, it says: for every
symmetric convex body `K` of volume one in `ℝᵐ` with `m ≥ 1` there is `A` with `det A = 1` and
`ℓ_K(A) · ℓ_{K°}((Aᵀ)^{-1}) ≤ m (log₂ m + 2)/π`.

This is the *only* external input of the development; it is proved here from Pisier's book
(Lewis's theorem + the K-convexity bound of `Submission.KConvex.lean` / `KConvexGauge.lean` /
`KConvexL2.lean` + John's theorem). -/
def EllEllStarHyp : Prop :=
  ∀ {m : ℕ}, 1 ≤ m → ∀ (K : Set (EuclideanSpace ℝ (Fin m))), Convex ℝ K → IsCompact K →
    (-K : Set (EuclideanSpace ℝ (Fin m))) = K → MeasureTheory.volume.real K = 1 →
    ∃ A : Matrix (Fin m) (Fin m) ℝ, A.det = 1 ∧
      (∫ x : EuclideanSpace ℝ (Fin m),
          (gauge K (Matrix.toLpLin 2 2 A x)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))
        * (∫ x : EuclideanSpace ℝ (Fin m),
            (sSup ((fun y => inner ℝ y x) ''
              (Set.image (fun v : EuclideanSpace ℝ (Fin m) =>
                Matrix.toLpLin 2 2 A⁻¹ v) K))) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))
        ≤ ((m : ℝ) * (Real.log (m : ℝ) / Real.log 2 + 2) / Real.pi) ^ 2

/-- **The `ℓℓ*` inequality holds.** -/
theorem ell_ell_star_hyp : EllEllStarHyp := by
  intro m' hm' K hKcvx hKcpt hKsymm hKvol
  classical
  have hmem_neg : ∀ z : EuclideanSpace ℝ (Fin m'), z ∈ K ↔ -z ∈ K := fun z =>
    ⟨fun hz => by rw [← hKsymm] at hz; exact Set.mem_neg.mp hz,
     fun hz => by
       rw [← hKsymm] at hz
       simpa using Set.mem_neg.mp hz⟩
  have hne : K.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have h0 : MeasureTheory.volume.real K = 0 := by rw [h]; simp
    rw [h0] at hKvol
    norm_num at hKvol
  obtain ⟨x₀, hx₀⟩ := hne
  have h0K : (0 : EuclideanSpace ℝ (Fin m')) ∈ K := by
    have hneg : -x₀ ∈ K := (hmem_neg x₀).mp hx₀
    have h := hKcvx hx₀ hneg (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) + 1/2 = 1)
    simpa using h
  have hvol_ne : MeasureTheory.volume K ≠ 0 := by
    intro hv
    have h0 : MeasureTheory.volume.real K = 0 := by
      rw [MeasureTheory.Measure.real, hv, ENNReal.toReal_zero]
    rw [h0] at hKvol
    norm_num at hKvol
  have hInt : (interior K).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hfr : K = frontier K := by
      conv_lhs => rw [← hKcpt.isClosed.closure_eq, closure_eq_interior_union_frontier, h,
        Set.empty_union]
    have hz : MeasureTheory.volume K = 0 := by
      rw [hfr]
      exact hKcvx.addHaar_frontier volume
    exact hvol_ne hz
  have h0int : (0 : EuclideanSpace ℝ (Fin m')) ∈ interior K := by
    obtain ⟨y, hy⟩ := hInt
    have hneg : -y ∈ K := (hmem_neg y).mp (interior_subset hy)
    have h := hKcvx.combo_interior_self_mem_interior hy hneg
      (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num : (1/2:ℝ) + 1/2 = 1)
    simpa using h
  have hbal : Balanced ℝ K := by
    intro a ha
    rintro z hz
    obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hz
    have ha1 : |a| ≤ 1 := by rwa [Real.norm_eq_abs] at ha
    have h1 : 0 ≤ (1 + a) / 2 := by have := (abs_le.mp ha1).1; linarith
    have h2 : 0 ≤ (1 - a) / 2 := by have := (abs_le.mp ha1).2; linarith
    have h3 : (1 + a) / 2 + (1 - a) / 2 = 1 := by ring
    have h := hKcvx hy ((hmem_neg y).mp hy) h1 h2 h3
    have heq : ((1 + a) / 2) • y + ((1 - a) / 2) • (-y) = a • y := by
      rw [smul_neg, ← sub_eq_add_neg, ← sub_smul]
      congr 1
      ring
    rwa [heq] at h
  have habs : Absorbent ℝ K := absorbent_nhds_zero (mem_interior_iff_mem_nhds.mp h0int)
  have hbdd : Bornology.IsVonNBounded ℝ K :=
    NormedSpace.isVonNBounded_of_isBounded ℝ hKcpt.isBounded
  obtain ⟨T, hT1, hT2⟩ :=
    Commons.GeometryOfNumbers.Lattice.exists_gauge_euclidean_comparison K hKcvx hKcpt hmem_neg hInt
  obtain ⟨A₀, hdet₀, hJ₀, hmax₀, htr₀, htrace₀⟩ :=
    Commons.GeometryOfNumbers.EllNorm.lewis_ellNorm_max K hKcvx hKsymm hKcpt h0int
  have hEllK : ellSq K A₀ ≤ 1 := by
    rw [ellSq, Submission.GaussianChaos.integral_μ]
    exact hJ₀
  have hL : ∀ X : Matrix (Fin m') (Fin m') ℝ, ellSq K X ≤ 1 →
      Matrix.trace (A₀⁻¹ * X) ≤ (m' : ℝ) := by
    intro X hX
    refine htr₀ X ?_
    rw [← Submission.GaussianChaos.integral_μ]
    exact hX
  have hsqrt1 : 1 ≤ Real.sqrt (m' : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hm')
  have hC0eq : 4 * (1 + Real.log (Real.sqrt (m' : ℝ)) / Real.log 2)
      = 2 * (2 + Real.log (m' : ℝ) / Real.log 2) := by
    rw [Real.log_sqrt (by positivity : (0:ℝ) ≤ (m':ℝ))]
    ring
  have hbnd : ellSq (polar K) (A₀⁻¹)ᵀ
      ≤ (gaussZ m' * (2 * (2 + Real.log (m' : ℝ) / Real.log 2)) * (m' : ℝ)) ^ 2 := by
    have h := ell_ell_star_aux K hKcvx habs hbdd hbal hKcpt h0int hKsymm hsqrt1 T hT1 hT2
      (A₀⁻¹) (m' : ℝ) (Nat.cast_nonneg m') hL
    rwa [hC0eq] at h
  set t : ℝ := (A₀.det) ^ (-(1 / (m' : ℝ))) with ht
  have htpos : 0 < t := Real.rpow_pos_of_pos hdet₀ _
  have htne : t ≠ 0 := ne_of_gt htpos
  have htm : t ^ m' = (A₀.det)⁻¹ := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hdet₀.le]
    rw [show (-(1 / (m' : ℝ))) * (m' : ℝ) = -1 by field_simp]
    rw [Real.rpow_neg_one]
  have hdet1 : (t • A₀).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, htm, inv_mul_cancel₀ (ne_of_gt hdet₀)]
  have hinv : (t • A₀)⁻¹ = t⁻¹ • A₀⁻¹ := by
    refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_nonsing_inv A₀ (isUnit_iff_ne_zero.mpr (ne_of_gt hdet₀)), smul_smul,
      mul_inv_cancel₀ htne, one_smul]
  have hP : (∫ x : EuclideanSpace ℝ (Fin m'),
        (gauge K (Matrix.toLpLin 2 2 (t • A₀) x)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))
      = (gaussZ m' * (2 * Real.pi))⁻¹ * ellSq K (t • A₀) := by
    rw [integral_gauge_sq_exp_pi, ellSq, Submission.GaussianChaos.integral_μ]
  have hQ : (∫ x : EuclideanSpace ℝ (Fin m'),
        (sSup ((fun y => inner ℝ y x) ''
          (Set.image (fun v : EuclideanSpace ℝ (Fin m') =>
            Matrix.toLpLin 2 2 (t • A₀)⁻¹ v) K))) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2))
      = (gaussZ m' * (2 * Real.pi))⁻¹ * ellSq (polar K) ((t • A₀)⁻¹)ᵀ :=
    integral_sSup_inner_eq K (fun z hz => (hmem_neg z).mp hz) hKcpt.isBounded ((t • A₀)⁻¹)
  refine ⟨t • A₀, hdet1, ?_⟩
  rw [hP, hQ]
  have hPbound : ellSq K (t • A₀) ≤ t ^ 2 := by
    rw [ellSq_smul_of_nonneg K htpos.le]
    exact mul_le_of_le_one_right (sq_nonneg t) hEllK
  have hQbound : ellSq (polar K) ((t • A₀)⁻¹)ᵀ
      ≤ (t⁻¹) ^ 2 * (gaussZ m' * (2 * (2 + Real.log (m' : ℝ) / Real.log 2)) * (m' : ℝ)) ^ 2 := by
    rw [hinv, Matrix.transpose_smul, ellSq_smul_of_nonneg (polar K) (inv_nonneg.mpr htpos.le)]
    exact mul_le_mul_of_nonneg_left hbnd (sq_nonneg t⁻¹)
  have hA0 : 0 ≤ (gaussZ m' * (2 * Real.pi))⁻¹ :=
    inv_nonneg.mpr (mul_nonneg (gaussZ_pos m').le (by positivity))
  have h1 : (gaussZ m' * (2 * Real.pi))⁻¹ * ellSq K (t • A₀)
      ≤ (gaussZ m' * (2 * Real.pi))⁻¹ * t ^ 2 :=
    mul_le_mul_of_nonneg_left hPbound hA0
  have h2 : (gaussZ m' * (2 * Real.pi))⁻¹ * ellSq (polar K) ((t • A₀)⁻¹)ᵀ
      ≤ (gaussZ m' * (2 * Real.pi))⁻¹
        * ((t⁻¹) ^ 2 * (gaussZ m' * (2 * (2 + Real.log (m' : ℝ) / Real.log 2)) * (m' : ℝ)) ^ 2) :=
    mul_le_mul_of_nonneg_left hQbound hA0
  have h3 : 0 ≤ (gaussZ m' * (2 * Real.pi))⁻¹ * ellSq (polar K) ((t • A₀)⁻¹)ᵀ :=
    mul_nonneg hA0 (ellSq_nonneg _ _)
  have h4 : 0 ≤ (gaussZ m' * (2 * Real.pi))⁻¹ * t ^ 2 := mul_nonneg hA0 (sq_nonneg _)
  refine le_trans (mul_le_mul h1 h2 h3 h4) ?_
  have ht2 : (t⁻¹) ^ 2 = (t ^ 2)⁻¹ := by rw [inv_pow]
  have key : (gaussZ m' * (2 * Real.pi))⁻¹ * t ^ 2
        * ((gaussZ m' * (2 * Real.pi))⁻¹
            * ((t⁻¹) ^ 2 * (gaussZ m' * (2 * (2 + Real.log (m' : ℝ) / Real.log 2))
              * (m' : ℝ)) ^ 2))
      = ((m' : ℝ) * (Real.log (m' : ℝ) / Real.log 2 + 2) / Real.pi) ^ 2 := by
    rw [ht2]
    have hG : gaussZ m' ≠ 0 := gaussZ_ne_zero m'
    have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  rw [key]

end
end Submission.EllEllStar
