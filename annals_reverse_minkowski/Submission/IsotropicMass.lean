import Mathlib
import Submission.MainStable
import Submission.ShapeDeriv
import Submission.Isotropic
import Submission.LatticeParam
import Submission.Commons.GeometryOfNumbers.gauge_le_iff
import Submission.BConjDiagonal
import Submission.Commons.Analysis.GaussianMeasure.bobkov_maximum_mass_of_B_conjecture
import Submission.Commons.GeometryOfNumbers.polar_lower_det_one
import Submission.Commons.Analysis.SpecialFunctions.ball_volume_le
import Submission.EllEllStar

open Module Real Matrix MeasureTheory
open scoped Real BigOperators Pointwise
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

/-!
# Paper Theorem 4.2 (`thm:isotropic_mass`): the Gaussian mass in isotropic position

This module contains the second half of the paper's `minima_have_mass`
(Theorem 6.3), namely Theorem 4.2 of Regev–Stephens-Davidowitz:

> For any symmetric convex body `K ⊆ E` with `vol(K) ≥ 1`, if `K` is in *isotropic
> Gaussian position for parameter* `0 < s ≤ 1/t` (where `t = 10(log m + 2)`), i.e.
> `∫_{K/s} e^{-π‖x‖²} xᵢ xⱼ dx = α δᵢⱼ`, then `γ_s(K) ≥ 2/3`.

It is consumed by `Submission.MainStable.interior_minimizer_gamma_of_stable`
(the interior branch of paper Prop. 7.2), which supplies `K := V(ℳ)` together with
the isotropy conclusion of `Submission.Isotropic.secondMoment_scalar_of_local_min_scaled`.

## Status

The theorems `bobkov_maximum_mass` (paper Prop. 4.3, Bobkov) and `ell_position_mass`
(paper Thm. 4.6) are the two remaining deep inputs; `isotropic_mass` is derived from
them.  See the module body for the precise statements and proof routes.
-/

namespace Submission.IsotropicMass

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "Mx" => Matrix (Fin m) (Fin m) ℝ

/-! ## Matrix generators of `latticeOfMatrix` and perturbation facts -/

/-- The list of generators whose `ℤ`-span is `latticeOfMatrix A` (column `i` of `A`). -/
def gen (A : Mx) : Fin m → E := fun i => WithLp.toLp 2 (fun row : Fin m => A row i)

lemma latticeOfMatrix_eq_span_gen (A : Mx) :
    Submission.LatticeParam.latticeOfMatrix A = Submodule.span ℤ (Set.range (gen A)) := rfl

lemma gen_mul (C B : Mx) (i : Fin m) :
    gen (C * B) i = Submission.ShapeDeriv.mvec C (gen B i) := by
  apply WithLp.ofLp_injective (p := 2)
  funext j
  rw [Submission.ShapeDeriv.mvec_coord_sum]
  simp [gen, Matrix.mul_apply]

/-- Multiplying the matrix of a lattice by `C` corresponds to applying `mvec C`. -/
lemma latticeOfMatrix_mul (C B : Mx) :
    Submission.LatticeParam.latticeOfMatrix (C * B) =
      (Submission.LatticeParam.latticeOfMatrix B).map
        ((Submission.ShapeDeriv.mvec C).restrictScalars ℤ) := by
  rw [latticeOfMatrix_eq_span_gen, latticeOfMatrix_eq_span_gen]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact Submodule.mem_map.mpr ⟨gen B i, Submodule.subset_span ⟨i, rfl⟩, (gen_mul C B i).symm⟩
  · rw [Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro x ⟨y, ⟨i, rfl⟩, rfl⟩
    exact Submodule.subset_span (s := Set.range (gen (C * B))) ⟨i, gen_mul C B i⟩

/-- **Matrix perturbation.** Matrices `C` entrywise close to the identity produce
matrices `C * B₀` entrywise close to `B₀`. -/
lemma mat_mul_near (B₀ : Mx) (δ₀ : ℝ) (hδ₀ : 0 < δ₀) :
    ∃ δ, 0 < δ ∧ ∀ C : Mx, (∀ j i, |C j i - (1 : Mx) j i| < δ) →
      ∀ j i, |(C * B₀) j i - B₀ j i| < δ₀ := by
  let S : ℝ := ∑ k : Fin m, ∑ i : Fin m, |B₀ k i|
  have hS0 : 0 ≤ S := by dsimp [S]; positivity
  refine ⟨δ₀ / (S + 1), by positivity, ?_⟩
  intro C hC j i
  have hkey : (C * B₀) j i - B₀ j i = ∑ k : Fin m, (C j k - (1 : Mx) j k) * B₀ k i := by
    rw [Matrix.mul_apply]
    have h1 : B₀ j i = ∑ k : Fin m, (1 : Mx) j k * B₀ k i := by
      rw [← Matrix.mul_apply, Matrix.one_mul]
    rw [h1, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hkey]
  calc |∑ k : Fin m, (C j k - (1 : Mx) j k) * B₀ k i|
      ≤ ∑ k : Fin m, |(C j k - (1 : Mx) j k) * B₀ k i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin m, |C j k - (1 : Mx) j k| * |B₀ k i| := by
        apply Finset.sum_congr rfl; intro k _; rw [abs_mul]
    _ ≤ ∑ k : Fin m, (δ₀ / (S + 1)) * |B₀ k i| := by
        apply Finset.sum_le_sum; intro k _
        exact mul_le_mul_of_nonneg_right (le_of_lt (hC j k)) (abs_nonneg _)
    _ = (δ₀ / (S + 1)) * ∑ k : Fin m, |B₀ k i| := by rw [Finset.mul_sum]
    _ ≤ (δ₀ / (S + 1)) * S := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        dsimp [S]
        apply Finset.sum_le_sum
        intro k _
        exact Finset.single_le_sum (f := fun i' => |B₀ k i'|) (fun i' _ => abs_nonneg _)
          (Finset.mem_univ i)
    _ < δ₀ := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [hS0, hδ₀]

/-! ## Paper Theorem 4.2 (`thm:isotropic_mass`): assembly from its two deep inputs -/

/-- Images of scalar multiples under the linear map `mvec A`. -/
lemma mvec_image_smul (A : Mx) (c : ℝ) (K : Set E) :
    Submission.ShapeDeriv.mvec A '' (c • K) = c • (Submission.ShapeDeriv.mvec A '' K) := by
  ext x
  simp only [Set.mem_image, Set.mem_smul_set]
  constructor
  · rintro ⟨y, ⟨z, hz, hyz⟩, hxy⟩
    refine ⟨Submission.ShapeDeriv.mvec A z, ⟨z, hz, rfl⟩, ?_⟩
    rw [← hxy, ← hyz, map_smul]
  · rintro ⟨z, ⟨y, hy, hyz⟩, hxz⟩
    refine ⟨c • y, ⟨y, hy, rfl⟩, ?_⟩
    rw [← hxz, ← hyz, map_smul]

/-- **Monotonicity of `γ_s` in `s`** for a convex set containing `0`: `s ≤ s'` gives
`γ_{s'}(K) ≤ γ_s(K)` (smaller parameter = larger blow-up of `K`). -/
lemma gammaMass_mono_param {s s' : ℝ} (hs : 0 < s) (h : s ≤ s') {K : Set E}
    (hKconv : Convex ℝ K) (h0 : (0 : E) ∈ K) :
    Submission.GaussianMeasure.gammaMass s' K ≤ Submission.GaussianMeasure.gammaMass s K := by
  have hs' : 0 < s' := lt_of_lt_of_le hs h
  have hsub : {y : E | s' • y ∈ K} ⊆ {y : E | s • y ∈ K} := by
    intro y hy
    have ht0 : (0 : ℝ) ≤ s / s' := div_nonneg (le_of_lt hs) (le_of_lt hs')
    have ht1 : s / s' ≤ 1 := by rw [div_le_one hs']; exact h
    have := hKconv.smul_mem_of_zero_mem h0 hy ⟨ht0, ht1⟩
    rwa [smul_smul, div_mul_cancel₀ _ (ne_of_gt hs')] at this
  dsimp [Submission.GaussianMeasure.gammaMass]
  refine MeasureTheory.setIntegral_mono_set
    Submission.GaussianMeasure.gaussian_density_integrable.integrableOn
    (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
    (Filter.Eventually.of_forall fun x hx => hsub hx)

/-- **Paper Proposition 4.3 (Bobkov).**  A symmetric convex body `K` in isotropic
Gaussian position for parameter `s` *maximizes* the Gaussian mass `γ_s` over its
determinant-one positions `A K`, `A ∈ SL_m`.

PROOF ROUTE (paper §4.2), with the exact decomposition to implement:

**(a) Spectral reduction to diagonal.**  `AᵀA` is positive semidefinite, so
`Commons.LinearAlgebra.Matrix.posSemidef_spectral` gives an orthogonal `V`
(`Vᵀ V = 1`) and `d ≥ 0` with `AᵀA = Vᵀ diag(d) V`; since `det A = 1`, `det AᵀA = 1`, and
with `D := diag(√d)` (`det D = 1`, diagonal, positive entries) one has
`‖A x‖² = xᵀAᵀAx = ‖D (V x)‖²`.  Hence (change of variables with `|det A| = |det V| = 1`)
`γ_s(A K) = γ_s(D·(V K))`, and `Commons.Analysis.GaussianMeasure.integral_orthogonal_image`
gives `γ_s(V K) = γ_s(K)`; finally `V K` is again isotropic-for-`s` (the Gaussian measure
is rotation invariant).  So it suffices to prove the **diagonal case**
`γ_s(D K) ≤ γ_s(K)` for diagonal `D ∈ SL_m`.

**(b) Diagonal case via CFM04 + the gradient fact.**  Write `D = e^{M}`, `M := diag(log d_i)`
diagonal with `tr M = log det D = 0`.  Then
`γ_s(D K) = γ_s(e^M K)`, and by
`Commons.Analysis.GaussianMeasure.B_conjecture_diagonal` (the CFM04 (B)-conjecture) the
function `M ↦ γ_s(e^M K)` is log-concave.  Its one-parameter restriction
`φ(t) := γ_s(e^{tM} K)` is therefore log-concave, and
`Commons.Analysis.GaussianMeasure.deriv_diagonal_exp_integral` computes
`φ'(0) = -2π Σ_i M_ii ∫_{K/s} x_i² e^{-π‖x‖²} dx = -2π tr(M)·α = 0`
(the second equality is the isotropic hypothesis `secondMoment ((1/s)•K) = α·δ`).
`Commons.Analysis.Convex.isMax_of_logConcave_deriv_zero` then gives `φ(1) ≤ φ(0)`, i.e.
`γ_s(e^M K) ≤ γ_s(K)`. -/
theorem bobkov_maximum_mass (K : Set E) (hKcvx : Convex ℝ K) (hKcpt : IsCompact K)
    (hKsymm : (-K : Set E) = K) (hInt : (0 : E) ∈ interior K) (s : ℝ) (hs : 0 < s)
    (hIso : ∃ α : ℝ, ∀ i j : Fin m,
      Submission.ShapeDeriv.secondMoment ((1 / s) • K) i j = α * (if i = j then 1 else 0))
    (A : Mx) (hA : A.det = 1) :
    Submission.GaussianMeasure.gammaMass s (Submission.ShapeDeriv.mvec A '' K)
      ≤ Submission.GaussianMeasure.gammaMass s K := by
  -- Bridge the local normalizations (`secondMoment`, `gammaMass`, `(1/s)•K`) to the explicit
  -- integral form used by the commons theorem `bobkov_maximum_mass_of_B_conjecture`.
  have himg : (1 / s) • K = Set.image (fun k : E => s⁻¹ • k) K := by rw [one_div]; rfl
  have hset : ∀ S : Set E, {y : E | s • y ∈ S} = Set.image (fun k : E => s⁻¹ • k) S := by
    intro S
    ext y
    constructor
    · intro hy
      exact ⟨s • y, hy, by
        change s⁻¹ • (s • y) = y
        rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hs), one_smul]⟩
    · rintro ⟨k, hk, rfl⟩
      change s • (s⁻¹ • k) ∈ S
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hs), one_smul]
      exact hk
  have hIso' : ∃ α : ℝ, ∀ i j : Fin m,
      (∫ y in Set.image (fun k : E => s⁻¹ • k) K,
        rexp (-Real.pi * ‖y‖ ^ 2) * y i * y j) = α * (if i = j then 1 else 0) := by
    obtain ⟨α, hα⟩ := hIso
    refine ⟨α, fun i j => ?_⟩
    have h0 : (∫ y in (1 / s) • K, rexp (-Real.pi * ‖y‖ ^ 2) * y i * y j)
        = α * (if i = j then 1 else 0) := hα i j
    rwa [himg] at h0
  have hmain := Commons.Analysis.GaussianMeasure.bobkov_maximum_mass_of_B_conjecture
    Commons.Analysis.GaussianMeasure.B_conjecture_diagonal
    K hKcvx hKcpt hKsymm hInt s hs hIso' A hA
  dsimp only [Submission.GaussianMeasure.gammaMass]
  rw [hset (Submission.ShapeDeriv.mvec A '' K), hset K]
  exact hmain

/-! ### The wall, isolated: `ℓℓ*` ⟹ `ell_position_core`

`ell_position_core` (paper Cor. 4.5) is the only remaining `sorry` of the project.  Its unique
known route is the sharp `ℓℓ*` inequality of Figiel–Tomczak-Jaegermann / Lewis / Pisier; the two
other ingredients are already in the commons
(`Commons.GeometryOfNumbers.polar_lower_det_one` for the lower bound on `ℓ_{K°}`, and
`Commons.Analysis.SpecialFunctions.ball_volume_le` for the ball-volume estimate).  We record the
reduction here, so that the project reduces to the single named hypothesis `EllEllStarHyp`. -/

/-- **`ℓℓ*` implies paper Corollary 4.5** (`ell_position_core`). -/
theorem ell_position_core_of_ell_ell_star (hm : 1 ≤ m)
    (hell : Submission.EllEllStar.EllEllStarHyp)
    (K : Set E) (hKcvx : Convex ℝ K) (hKcpt : IsCompact K)
    (hKsymm : (-K : Set E) = K) (hKvol : volume.real K = 1) :
    ∃ A : Mx, A.det = 1 ∧
      ∫ x, (gauge K (Submission.ShapeDeriv.mvec A x)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)
        ≤ (2 * Real.sqrt (Real.exp 1) * (Real.log (m : ℝ) / Real.log 2 + 2)) ^ 2 := by
  classical
  obtain ⟨A, hAdet, hprod⟩ := hell hm K hKcvx hKcpt hKsymm hKvol
  refine ⟨A, hAdet, ?_⟩
  set L : ℝ := Real.log (m : ℝ) / Real.log 2 + 2 with hLdef
  set V : ℝ := volume.real (Metric.ball (0 : E) 1) with hVdef
  set P : ℝ := ∫ x, (gauge K (Submission.ShapeDeriv.mvec A x)) ^ 2
      * Real.exp (-Real.pi * ‖x‖ ^ 2) with hPdef
  set Q : ℝ := ∫ x, (sSup ((fun y : E => inner ℝ y x) ''
      (Set.image (fun v : E => Submission.ShapeDeriv.mvec A⁻¹ v) K))) ^ 2
      * Real.exp (-Real.pi * ‖x‖ ^ 2) with hQdef
  have hprod' : P * Q ≤ ((m : ℝ) * L / Real.pi) ^ 2 := by
    rw [hPdef, hQdef, hLdef]
    exact hprod
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hLpos : 0 < L := by
    rw [hLdef]
    have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
    have h2log : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hP0 : 0 ≤ P := by
    rw [hPdef]
    exact integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
  have hVpos : 0 < V := by
    rw [hVdef]
    have h1 : 0 < volume (Metric.ball (0 : E) 1) := Metric.measure_ball_pos volume 0 one_pos
    have h2 : volume (Metric.ball (0 : E) 1) ≠ ⊤ := (Metric.isBounded_ball.measure_lt_top).ne
    exact ENNReal.toReal_pos h1.ne' h2
  have hQlow : V ^ (-(2 / (m : ℝ))) * (m : ℝ) / (2 * Real.pi) ≤ Q := by
    rw [hQdef, hVdef]
    exact Commons.GeometryOfNumbers.polar_lower_det_one hm K hKcvx hKcpt hKsymm hKvol A hAdet
  have hQ0 : 0 < V ^ (-(2 / (m : ℝ))) * (m : ℝ) / (2 * Real.pi) :=
    div_pos (mul_pos (Real.rpow_pos_of_pos hVpos _) hm0) (by positivity)
  have hPbound : P ≤ ((m : ℝ) * L / Real.pi) ^ 2 / (V ^ (-(2 / (m : ℝ))) * (m : ℝ) / (2 * Real.pi)) := by
    rw [le_div_iff₀ hQ0]
    exact le_trans (mul_le_mul_of_nonneg_left hQlow hP0) hprod'
  -- the ball-volume estimate
  have hvol : V ≤ (2 * Real.pi * Real.exp 1 / (m : ℝ)) ^ ((m : ℝ) / 2) := by
    rw [hVdef]
    exact Commons.Analysis.SpecialFunctions.ball_volume_le m hm
  have hVpow : V ^ (2 / (m : ℝ)) ≤ 2 * Real.pi * Real.exp 1 / (m : ℝ) := by
    have h1 := Real.rpow_le_rpow hVpos.le hvol (by positivity : (0 : ℝ) ≤ 2 / (m : ℝ))
    have h2 : ((2 * Real.pi * Real.exp 1 / (m : ℝ)) ^ ((m : ℝ) / 2)) ^ (2 / (m : ℝ))
        = 2 * Real.pi * Real.exp 1 / (m : ℝ) := by
      rw [← Real.rpow_mul (by positivity)]
      rw [show ((m : ℝ) / 2) * (2 / (m : ℝ)) = 1 by field_simp, Real.rpow_one]
    rwa [h2] at h1
  -- algebra
  have hVpow_pos : 0 < V ^ (2 / (m : ℝ)) := Real.rpow_pos_of_pos hVpos _
  have hsimp : ((m : ℝ) * L / Real.pi) ^ 2 / (V ^ (-(2 / (m : ℝ))) * (m : ℝ) / (2 * Real.pi))
      = (2 * (m : ℝ) * L ^ 2 / Real.pi) * V ^ (2 / (m : ℝ)) := by
    rw [Real.rpow_neg hVpos.le]
    have hne : V ^ (2 / (m : ℝ)) ≠ 0 := ne_of_gt hVpow_pos
    field_simp
  have hstep : (2 * (m : ℝ) * L ^ 2 / Real.pi) * V ^ (2 / (m : ℝ))
      ≤ (2 * (m : ℝ) * L ^ 2 / Real.pi) * (2 * Real.pi * Real.exp 1 / (m : ℝ)) :=
    mul_le_mul_of_nonneg_left hVpow (by positivity)
  have hfinal : (2 * (m : ℝ) * L ^ 2 / Real.pi) * (2 * Real.pi * Real.exp 1 / (m : ℝ))
      = (2 * Real.sqrt (Real.exp 1) * L) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (Real.exp_pos 1).le]
    field_simp
  calc P ≤ ((m : ℝ) * L / Real.pi) ^ 2 / (V ^ (-(2 / (m : ℝ))) * (m : ℝ) / (2 * Real.pi)) :=
        hPbound
    _ = (2 * (m : ℝ) * L ^ 2 / Real.pi) * V ^ (2 / (m : ℝ)) := hsimp
    _ ≤ (2 * (m : ℝ) * L ^ 2 / Real.pi) * (2 * Real.pi * Real.exp 1 / (m : ℝ)) := hstep
    _ = (2 * Real.sqrt (Real.exp 1) * L) ^ 2 := hfinal


/-- **Paper Corollary 4.5 (`cor:ell_position`).**  A volume-one symmetric convex body `K ⊆ ℝᵐ`
admits a determinant-one position `A` with `ℓ_K(A) ≤ 2√e(log₂ m + 2)`, i.e.
`∫ (gauge K (A x))² e^{−π‖x‖²} dx ≤ (2√e(log₂ m + 2))²`, where `gauge K` is Mathlib's
Minkowski functional.

Proved from the `ℓℓ*` inequality `Submission.EllEllStar.ell_ell_star_hyp` via
`ell_position_core_of_ell_ell_star`. -/
theorem ell_position_core (hm : 1 ≤ m) (K : Set E) (hKcvx : Convex ℝ K) (hKcpt : IsCompact K)
    (hKsymm : (-K : Set E) = K) (hKvol : volume.real K = 1) :
    ∃ A : Mx, A.det = 1 ∧
      ∫ x, (gauge K (Submission.ShapeDeriv.mvec A x)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)
        ≤ (2 * Real.sqrt (Real.exp 1) * (Real.log (m : ℝ) / Real.log 2 + 2)) ^ 2 :=
  ell_position_core_of_ell_ell_star hm Submission.EllEllStar.ell_ell_star_hyp K hKcvx hKcpt
    hKsymm hKvol

/-! ### Gauge / Markov glue: `ell_position_core` ⟹ `ell_position_mass` -/

lemma mvec_inv_comp (A : Mx) (hA : A.det = 1) (w : E) :
    Submission.ShapeDeriv.mvec A (Submission.ShapeDeriv.mvec A⁻¹ w) = w := by
  have hunit : IsUnit A.det := by rw [hA]; exact isUnit_one
  have hmul : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hunit
  have hcomp : Submission.ShapeDeriv.mvec A ∘ₗ Submission.ShapeDeriv.mvec A⁻¹
      = LinearMap.id := by
    simp only [Submission.ShapeDeriv.mvec]
    rw [← Matrix.toLpLin_mul (2) (2) (2) (A) (A⁻¹), hmul, Matrix.toLpLin_one]
  simpa using LinearMap.congr_fun hcomp w

lemma mvec_inv_comp' (A : Mx) (hA : A.det = 1) (w : E) :
    Submission.ShapeDeriv.mvec A⁻¹ (Submission.ShapeDeriv.mvec A w) = w := by
  have hunit : IsUnit A.det := by rw [hA]; exact isUnit_one
  have hmul : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A hunit
  have hcomp : Submission.ShapeDeriv.mvec A⁻¹ ∘ₗ Submission.ShapeDeriv.mvec A
      = LinearMap.id := by
    simp only [Submission.ShapeDeriv.mvec]
    rw [← Matrix.toLpLin_mul (2) (2) (2) (A⁻¹) (A), hmul, Matrix.toLpLin_one]
  simpa using LinearMap.congr_fun hcomp w

lemma gauge_le_iff_mem {K : Set E} (hCvx : Convex ℝ K) (hKc : IsCompact K)
    (h0K : (0 : E) ∈ K) (hInt : (0 : E) ∈ interior K) (y : E) {t : ℝ} (ht : 0 ≤ t) :
    gauge K y ≤ t ↔ y ∈ Set.image (fun x : E => t • x) K := by
  constructor
  · intro h
    have hAbs : Absorbent ℝ K := absorbent_nhds_zero (mem_interior_iff_mem_nhds.mp hInt)
    refine Commons.GeometryOfNumbers.mem_smul_of_forall_lt hKc h0K ht ?_
    intro r hr
    have hlt : gauge K y < r := lt_of_le_of_lt h hr
    have hmem : y ∈ ⋃ r' ∈ Set.Ioo (0 : ℝ) r, r' • K := by
      have h1 : y ∈ ({x : E | gauge K x < r}) := hlt
      rw [setOfPred_gauge_lt_eq hAbs r] at h1
      exact h1
    rcases Set.mem_iUnion.mp hmem with ⟨r', hmem2⟩
    rcases Set.mem_iUnion.mp hmem2 with ⟨hr', hyr'⟩
    exact Commons.GeometryOfNumbers.mem_smul_of_mem_smul_of_le hCvx h0K hr'.1.le (le_of_lt hr'.2) hyr'
  · intro hy
    exact gauge_le_of_mem ht hy

lemma smul_mvec_inv_image (A : Mx) (hA : A.det = 1) {K : Set E} (hCvx : Convex ℝ K)
    (hKc : IsCompact K) (h0K : (0 : E) ∈ K) (hInt : (0 : E) ∈ interior K) {t : ℝ} (ht : 0 ≤ t) :
    t • (Submission.ShapeDeriv.mvec A⁻¹ '' K)
      = {y : E | gauge K (Submission.ShapeDeriv.mvec A y) ≤ t} := by
  ext y
  rw [Set.mem_setOf_eq]
  constructor
  · intro hy
    rw [Set.mem_smul_set] at hy
    rcases hy with ⟨z, hz, hzy⟩
    rw [Set.mem_image] at hz
    rcases hz with ⟨k, hk, hkz⟩
    have hAy : Submission.ShapeDeriv.mvec A y = t • k := by
      rw [← hzy, map_smul, ← hkz, mvec_inv_comp A hA]
    rw [hAy]
    exact gauge_le_of_mem ht ⟨k, hk, rfl⟩
  · intro hy
    rw [Set.mem_smul_set]
    have hAyk : Submission.ShapeDeriv.mvec A y ∈ t • K :=
      (gauge_le_iff_mem hCvx hKc h0K hInt (Submission.ShapeDeriv.mvec A y) ht).mp hy
    rw [Set.mem_smul_set] at hAyk
    rcases hAyk with ⟨k, hk, hky⟩
    refine ⟨Submission.ShapeDeriv.mvec A⁻¹ k, ?_, ?_⟩
    · rw [Set.mem_image]; exact ⟨k, hk, rfl⟩
    · rw [← map_smul, hky, mvec_inv_comp' A hA]

lemma gauge_bound {K : Set E} (hInt : (0 : E) ∈ interior K) :
    ∃ r : ℝ, 0 < r ∧ (∀ x : E, gauge K x ≤ ‖x‖ / r) := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hInt)
  refine ⟨ε / 2, by positivity, fun x => ?_⟩
  have hcb : Metric.closedBall (0 : E) (ε / 2) ⊆ K := by
    intro z hz
    apply hball
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  rcases eq_or_ne x 0 with rfl | hx
  · rw [gauge_zero]; positivity
  · have hnorm : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
    have hmem : x ∈ (‖x‖ / (ε / 2)) • K := by
      rw [Set.mem_smul_set]
      refine ⟨((ε / 2) / ‖x‖) • x, hcb ?_, ?_⟩
      · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos (by positivity), div_mul_cancel₀ _ (ne_of_gt hnorm)]
      · show (‖x‖ / (ε / 2)) • (((ε / 2) / ‖x‖) • x) = x
        rw [smul_smul]
        have hcoef : ‖x‖ / (ε / 2) * ((ε / 2) / ‖x‖) = 1 := by
          field_simp
        rw [hcoef, one_smul]
    exact gauge_le_of_mem (by positivity) hmem


lemma integrable_norm_sq_gaussian :
    Integrable (fun y : E => ‖y‖ ^ 2 * Real.exp (-Real.pi * ‖y‖ ^ 2)) := by
  have hbase : Integrable (fun y : E => Real.exp (-(Real.pi / 2) * ‖y‖ ^ 2)) :=
    Submission.ShapeDeriv.gaussian_b_integrable (Real.pi / 2) (by positivity)
  refine Integrable.mono' hbase ?_ ?_
  · have hcont : Continuous (fun y : E => ‖y‖ ^ 2 * Real.exp (-Real.pi * ‖y‖ ^ 2)) :=
      (continuous_norm.pow 2).mul (Real.continuous_exp.comp
        (continuous_const.mul (continuous_norm.pow 2)))
    exact hcont.aestronglyMeasurable
  · filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hsplit : Real.exp (-Real.pi * ‖y‖ ^ 2)
        = Real.exp (-(Real.pi / 2) * ‖y‖ ^ 2) * Real.exp (-(Real.pi / 2) * ‖y‖ ^ 2) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hsplit]
    calc ‖y‖ ^ 2 * (Real.exp (-(Real.pi / 2) * ‖y‖ ^ 2) * Real.exp (-(Real.pi / 2) * ‖y‖ ^ 2))
        = (‖y‖ ^ 2 * Real.exp (-(Real.pi / 2) * ‖y‖ ^ 2))
            * Real.exp (-(Real.pi / 2) * ‖y‖ ^ 2) := by ring
      _ ≤ 1 * Real.exp (-(Real.pi / 2) * ‖y‖ ^ 2) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
          have h := Submission.ShapeDeriv.norm_sq_exp_half y
          have hp : (2 : ℝ) / Real.pi ≤ 1 := by
            rw [div_le_one (by positivity)]; linarith [Real.pi_gt_three]
          linarith [h, hp]
      _ = Real.exp (-(Real.pi / 2) * ‖y‖ ^ 2) := one_mul _

lemma integrable_gauge_sq_image (A : Mx) {K : Set E} (hCvx : Convex ℝ K)
    (hInt : (0 : E) ∈ interior K) :
    Integrable (fun y : E =>
      (gauge K (Submission.ShapeDeriv.mvec A y)) ^ 2 * Real.exp (-Real.pi * ‖y‖ ^ 2)) := by
  rcases gauge_bound hInt with ⟨r, hr, hbound⟩
  rcases Submission.ShapeDeriv.mvec_bound A with ⟨L, hL, hLb⟩
  have hC0 : 0 ≤ L ^ 2 / r ^ 2 := by positivity
  have hdom : Integrable (fun y : E =>
      (L ^ 2 / r ^ 2) * (‖y‖ ^ 2 * Real.exp (-Real.pi * ‖y‖ ^ 2))) :=
    integrable_norm_sq_gaussian.const_mul _
  refine Integrable.mono' hdom ?_ ?_
  · have hnhds : K ∈ nhds (0 : E) := mem_interior_iff_mem_nhds.mp hInt
    have hgc : Continuous (fun y : E => gauge K (Submission.ShapeDeriv.mvec A y)) :=
      (continuous_gauge hCvx hnhds).comp
        (LinearMap.continuous_of_finiteDimensional (Submission.ShapeDeriv.mvec A))
    exact (((hgc.pow 2).mul (Real.continuous_exp.comp
      (continuous_const.mul (continuous_norm.pow 2))))).aestronglyMeasurable
  · filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hg0 : 0 ≤ gauge K (Submission.ShapeDeriv.mvec A y) := gauge_nonneg _
    have h1 : gauge K (Submission.ShapeDeriv.mvec A y) ≤ ‖Submission.ShapeDeriv.mvec A y‖ / r :=
      hbound _
    have h2 : ‖Submission.ShapeDeriv.mvec A y‖ ≤ L * ‖y‖ := hLb y
    have h3 : gauge K (Submission.ShapeDeriv.mvec A y) ≤ (L / r) * ‖y‖ := by
      calc gauge K (Submission.ShapeDeriv.mvec A y) ≤ ‖Submission.ShapeDeriv.mvec A y‖ / r := h1
        _ ≤ (L * ‖y‖) / r := by
            exact div_le_div_of_nonneg_right h2 (le_of_lt hr)
        _ = (L / r) * ‖y‖ := by ring
    have hLr : 0 ≤ L / r := div_nonneg (le_of_lt hL) (le_of_lt hr)
    have hsq : (gauge K (Submission.ShapeDeriv.mvec A y)) ^ 2 ≤ ((L / r) * ‖y‖) ^ 2 :=
      pow_le_pow_left₀ hg0 h3 2
    calc (gauge K (Submission.ShapeDeriv.mvec A y)) ^ 2 * Real.exp (-Real.pi * ‖y‖ ^ 2)
        ≤ ((L / r) * ‖y‖) ^ 2 * Real.exp (-Real.pi * ‖y‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hsq (Real.exp_nonneg _)
      _ = (L ^ 2 / r ^ 2) * (‖y‖ ^ 2 * Real.exp (-Real.pi * ‖y‖ ^ 2)) := by ring


lemma markov_gauge (A : Mx) {K : Set E} (hCvx : Convex ℝ K) (hKc : IsCompact K)
    (hInt : (0 : E) ∈ interior K) {t : ℝ} (ht : 0 < t) :
    ∫ y in {y : E | t < gauge K (Submission.ShapeDeriv.mvec A y)}, Real.exp (-Real.pi * ‖y‖ ^ 2)
      ≤ (1 / t ^ 2) * ∫ y, (gauge K (Submission.ShapeDeriv.mvec A y)) ^ 2
          * Real.exp (-Real.pi * ‖y‖ ^ 2) := by
  have hnhds : K ∈ nhds (0 : E) := mem_interior_iff_mem_nhds.mp hInt
  have hgc : Continuous (fun y : E => gauge K (Submission.ShapeDeriv.mvec A y)) :=
    (continuous_gauge hCvx hnhds).comp
      (LinearMap.continuous_of_finiteDimensional (Submission.ShapeDeriv.mvec A))
  have hmeas : MeasurableSet {y : E | t < gauge K (Submission.ShapeDeriv.mvec A y)} :=
    (IsOpen.preimage hgc isOpen_Ioi).measurableSet
  have hfint : Integrable (fun y : E => Real.exp (-Real.pi * ‖y‖ ^ 2)) :=
    Submission.ShapeDeriv.gaussian_b_integrable Real.pi (by positivity)
  have hgint : Integrable (fun y : E =>
      (gauge K (Submission.ShapeDeriv.mvec A y)) ^ 2 * Real.exp (-Real.pi * ‖y‖ ^ 2)) :=
    integrable_gauge_sq_image A hCvx hInt
  have hcint : Integrable (fun y : E =>
      (1 / t ^ 2) * ((gauge K (Submission.ShapeDeriv.mvec A y)) ^ 2
        * Real.exp (-Real.pi * ‖y‖ ^ 2))) := hgint.const_mul _
  have hpoint : ∀ y, t < gauge K (Submission.ShapeDeriv.mvec A y) →
      Real.exp (-Real.pi * ‖y‖ ^ 2) ≤ (1 / t ^ 2)
        * ((gauge K (Submission.ShapeDeriv.mvec A y)) ^ 2 * Real.exp (-Real.pi * ‖y‖ ^ 2)) := by
    intro y hy
    have hone : (1 : ℝ) ≤ (1 / t ^ 2) * (gauge K (Submission.ShapeDeriv.mvec A y)) ^ 2 := by
      rw [div_mul_eq_mul_div, one_le_div (by positivity)]
      nlinarith [hy, ht]
    calc Real.exp (-Real.pi * ‖y‖ ^ 2)
        = (1 : ℝ) * Real.exp (-Real.pi * ‖y‖ ^ 2) := (one_mul _).symm
      _ ≤ ((1 / t ^ 2) * (gauge K (Submission.ShapeDeriv.mvec A y)) ^ 2)
            * Real.exp (-Real.pi * ‖y‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hone (Real.exp_nonneg _)
      _ = (1 / t ^ 2) * ((gauge K (Submission.ShapeDeriv.mvec A y)) ^ 2
            * Real.exp (-Real.pi * ‖y‖ ^ 2)) := by ring
  calc ∫ y in {y : E | t < gauge K (Submission.ShapeDeriv.mvec A y)}, Real.exp (-Real.pi * ‖y‖ ^ 2)
      ≤ ∫ y in {y : E | t < gauge K (Submission.ShapeDeriv.mvec A y)},
          (1 / t ^ 2) * ((gauge K (Submission.ShapeDeriv.mvec A y)) ^ 2
            * Real.exp (-Real.pi * ‖y‖ ^ 2)) := by
        refine integral_mono_ae hfint.integrableOn hcint.integrableOn ?_
        filter_upwards [MeasureTheory.ae_restrict_mem hmeas] with y hy
        exact hpoint y hy
    _ ≤ ∫ y, (1 / t ^ 2) * ((gauge K (Submission.ShapeDeriv.mvec A y)) ^ 2
            * Real.exp (-Real.pi * ‖y‖ ^ 2)) :=
        setIntegral_le_integral hcint (Filter.Eventually.of_forall fun y => by positivity)
    _ = (1 / t ^ 2) * ∫ y, (gauge K (Submission.ShapeDeriv.mvec A y)) ^ 2
            * Real.exp (-Real.pi * ‖y‖ ^ 2) := by
        rw [MeasureTheory.integral_const_mul]

lemma paper_t_le :
    2 * Real.sqrt (3 * Real.exp 1) * (Real.log (m : ℝ) / Real.log 2 + 2)
      ≤ Submission.MainStable.t m := by
  have hlog2 : (2 : ℝ) / 3 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hlog2pos : 0 < Real.log 2 := by linarith
  have hlogm : 0 ≤ Real.log (m : ℝ) := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp
    · exact Real.log_nonneg (by exact_mod_cast h)
  have h1 : Real.log (m : ℝ) / Real.log 2 ≤ (3 / 2) * Real.log (m : ℝ) := by
    rw [div_le_iff₀ hlog2pos]
    nlinarith [hlogm, hlog2]
  have h2 : Real.sqrt (3 * Real.exp 1) ≤ 3 := by
    rw [Real.sqrt_le_left (by norm_num)]
    have := Real.exp_one_lt_three
    nlinarith
  have h3 : (0:ℝ) ≤ Real.sqrt (3 * Real.exp 1) := Real.sqrt_nonneg _
  rw [Submission.MainStable.t]
  nlinarith [h1, h2, h3, hlogm, Real.exp_pos 1]


theorem ell_position_mass_of_core (K : Set E) (hKcvx : Convex ℝ K) (hKcpt : IsCompact K)
    (hKsymm : (-K : Set E) = K) (h0K : (0 : E) ∈ K) (hInt : (0 : E) ∈ interior K)
    (core : ∃ A : Mx, A.det = 1 ∧
      ∫ x, (gauge K (Submission.ShapeDeriv.mvec A x)) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)
        ≤ (2 * Real.sqrt (Real.exp 1) * (Real.log (m : ℝ) / Real.log 2 + 2)) ^ 2) :
    ∃ A : Mx, A.det = 1 ∧ (2 : ℝ) / 3 ≤
      Submission.GaussianMeasure.gammaMass (1 / Submission.MainStable.t m)
        (Submission.ShapeDeriv.mvec A '' K) := by
  rcases core with ⟨A, hAdet, hcore⟩
  refine ⟨A⁻¹, ?_, ?_⟩
  · rw [Matrix.det_nonsing_inv, hAdet]; norm_num
  · set tm : ℝ := Submission.MainStable.t m with htm
    have htmpos : 0 < tm := by rw [htm]; exact Submission.MainStable.t_pos m
    rw [Submission.GaussianMeasure.gammaMass_inv_smul_set tm (ne_of_gt htmpos)
      (Submission.ShapeDeriv.mvec A⁻¹ '' K)]
    rw [smul_mvec_inv_image A hAdet hKcvx hKcpt h0K hInt (le_of_lt htmpos)]
    set S : Set E := {y : E | gauge K (Submission.ShapeDeriv.mvec A y) ≤ tm} with hS
    have hnhds : K ∈ nhds (0 : E) := mem_interior_iff_mem_nhds.mp hInt
    have hgc : Continuous (fun y : E => gauge K (Submission.ShapeDeriv.mvec A y)) :=
      (continuous_gauge hKcvx hnhds).comp
        (LinearMap.continuous_of_finiteDimensional (Submission.ShapeDeriv.mvec A))
    have hmeas : MeasurableSet S := by
      rw [hS]
      exact (isClosed_le hgc continuous_const).measurableSet
    have hScompl : Sᶜ = {y : E | tm < gauge K (Submission.ShapeDeriv.mvec A y)} := by
      rw [hS]; ext y; simp [not_le]
    have hfint : Integrable (fun y : E => Real.exp (-Real.pi * ‖y‖ ^ 2)) :=
      Submission.ShapeDeriv.gaussian_b_integrable Real.pi (by positivity)
    have hone : ∫ y : E, Real.exp (-Real.pi * ‖y‖ ^ 2) = 1 := by
      have h := Submission.GaussianMeasure.gammaMass_univ (n := m) (1 : ℝ) (by norm_num)
      rw [Submission.GaussianMeasure.gammaMass_one, MeasureTheory.setIntegral_univ] at h
      exact h
    have hsplit : ∫ y in S, Real.exp (-Real.pi * ‖y‖ ^ 2)
        = 1 - ∫ y in Sᶜ, Real.exp (-Real.pi * ‖y‖ ^ 2) := by
      have h := integral_add_compl hmeas hfint
      rw [hone] at h
      linarith
    have hbnd : ∫ y in Sᶜ, Real.exp (-Real.pi * ‖y‖ ^ 2) ≤ 1 / 3 := by
      rw [hScompl]
      refine le_trans (markov_gauge A hKcvx hKcpt hInt htmpos (t := tm)) ?_
      set L : ℝ := Real.log (m : ℝ) / Real.log 2 + 2 with hLdef
      have hCsq : 3 * (2 * Real.sqrt (Real.exp 1) * L) ^ 2 ≤ tm ^ 2 := by
        have hL0 : 0 ≤ L := by
          have hlog2pos : 0 < Real.log 2 := by
            have := Real.log_two_gt_d9; linarith
          rcases Nat.eq_zero_or_pos m with h | h
          · subst h; simp [hLdef]
          · rw [hLdef]; positivity
        have key : Real.sqrt 3 * (2 * Real.sqrt (Real.exp 1) * L)
            = 2 * Real.sqrt (3 * Real.exp 1) * L := by
          have hsm : Real.sqrt (3 * Real.exp 1) = Real.sqrt 3 * Real.sqrt (Real.exp 1) :=
            Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3) (Real.exp 1)
          rw [hsm]; ring
        have h3C : (Real.sqrt 3 * (2 * Real.sqrt (Real.exp 1) * L)) ^ 2
            = 3 * (2 * Real.sqrt (Real.exp 1) * L) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
        rw [← h3C, key]
        exact pow_le_pow_left₀ (by positivity) paper_t_le 2
      calc (1 / tm ^ 2) * ∫ y, (gauge K (Submission.ShapeDeriv.mvec A y)) ^ 2
              * Real.exp (-Real.pi * ‖y‖ ^ 2)
          = (1 / tm ^ 2) * (∫ y, (gauge K (Submission.ShapeDeriv.mvec A y)) ^ 2
              * Real.exp (-Real.pi * ‖y‖ ^ 2)) := by ring
        _ ≤ (1 / tm ^ 2) * (2 * Real.sqrt (Real.exp 1) * L) ^ 2 := by
            have := hcore
            rw [hLdef] at this ⊢
            exact mul_le_mul_of_nonneg_left this (by positivity)
        _ ≤ 1 / 3 := by
            have hEq : (1 / tm ^ 2) * (2 * Real.sqrt (Real.exp 1) * L) ^ 2
                = (2 * Real.sqrt (Real.exp 1) * L) ^ 2 / tm ^ 2 := by ring
            rw [hEq, div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 3)]
            nlinarith [hCsq]
    rw [hsplit]
    linarith


/-- **Paper Theorem 4.6 (`thm:ell_position_mass`).**  A symmetric convex body `K` of
volume one has a determinant-one position `A K` with `γ_{1/t}(A K) ≥ 2/3`, where
`t = 10(log m + 2)`.

Obtained from `ell_position_core` (paper Cor. 4.5) by Markov's inequality: for `A` with
`ℓ_K(A)² ≤ C²`, the body `A⁻¹K` satisfies
`γ_{1/t}(A⁻¹ K) = ∫_{gauge K (Ax) ≤ t} e^{−π‖x‖²} dx ≥ 1 − C²/t² ≥ 2/3`
(`t = t(m)` and `paper_t_le`). -/
theorem ell_position_mass (hm : 1 ≤ m) (K : Set E) (hKcvx : Convex ℝ K) (hKcpt : IsCompact K)
    (hKsymm : (-K : Set E) = K) (hInt : (0 : E) ∈ interior K) (hKvol : volume.real K = 1) :
    ∃ A : Mx, A.det = 1 ∧ (2 : ℝ) / 3 ≤
      Submission.GaussianMeasure.gammaMass (1 / Submission.MainStable.t m)
        (Submission.ShapeDeriv.mvec A '' K) :=
  ell_position_mass_of_core K hKcvx hKcpt hKsymm (interior_subset hInt) hInt
    (ell_position_core hm K hKcvx hKcpt hKsymm hKvol)

/-- **Paper Theorem 4.2 (`thm:isotropic_mass`).** A symmetric convex body `K` of volume
one in isotropic Gaussian position for some parameter `0 < s ≤ 1/t` has `γ_s(K) ≥ 2/3`,
where `t = 10(log m + 2)`.

Assembly: `ell_position_mass` gives `A ∈ SL_m` with `γ_{1/t}(A K) ≥ 2/3`; monotonicity
of `γ_s` in `s` upgrades it to `γ_s(A K) ≥ 2/3`; `bobkov_maximum_mass` upgrades
`γ_s(A K) ≤ γ_s(K)`.  (The paper states the theorem for `vol(K) ≥ 1`; only the
`vol(K) = 1` case is used below, for `K = V(ℳ)`.) -/
theorem isotropic_mass (hm : 1 ≤ m) (K : Set E) (hKcvx : Convex ℝ K) (hKcpt : IsCompact K)
    (hKsymm : (-K : Set E) = K) (h0K : (0 : E) ∈ K) (hInt : (0 : E) ∈ interior K)
    (hKvol : volume.real K = 1)
    (s : ℝ) (hs : 0 < s) (hst : s ≤ 1 / Submission.MainStable.t m)
    (hIso : ∃ α : ℝ, ∀ i j : Fin m,
      Submission.ShapeDeriv.secondMoment ((1 / s) • K) i j
        = α * (if i = j then 1 else 0)) :
    (2 : ℝ) / 3 ≤ Submission.GaussianMeasure.gammaMass s K := by
  rcases ell_position_mass hm K hKcvx hKcpt hKsymm hInt hKvol with ⟨A, hAdet, hmass⟩
  have hconvA : Convex ℝ (Submission.ShapeDeriv.mvec A '' K) :=
    hKcvx.linear_image (Submission.ShapeDeriv.mvec A)
  have h0A : (0 : E) ∈ Submission.ShapeDeriv.mvec A '' K := ⟨0, h0K, by simp⟩
  have h1 : Submission.GaussianMeasure.gammaMass (1 / Submission.MainStable.t m)
      (Submission.ShapeDeriv.mvec A '' K)
      ≤ Submission.GaussianMeasure.gammaMass s (Submission.ShapeDeriv.mvec A '' K) :=
    gammaMass_mono_param hs hst hconvA h0A
  have h2 : Submission.GaussianMeasure.gammaMass s (Submission.ShapeDeriv.mvec A '' K)
      ≤ Submission.GaussianMeasure.gammaMass s K :=
    bobkov_maximum_mass K hKcvx hKcpt hKsymm hInt s hs hIso A hAdet
  linarith

end Submission.IsotropicMass
