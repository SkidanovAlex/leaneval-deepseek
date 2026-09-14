import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Submission.Commons.Analysis.GaussianMeasure.integral_spectral_diagonal_image
import Submission.Commons.Analysis.GaussianMeasure.norm_sq_eq_sum_diagonal_spectral
import Submission.Commons.Analysis.GaussianMeasure.integral_orthogonal_image
import Submission.Commons.Analysis.GaussianMeasure.deriv_diagonal_exp_integral
import Submission.Commons.Analysis.GaussianMeasure.integral_diag_image
import Submission.Commons.Analysis.Convex.le_of_logConcaveOn_Icc_deriv_zero
import Submission.Commons.LinearAlgebra.Matrix.posSemidef_spectral
import Submission.Commons.LinearAlgebra.Matrix.posSemidef_transpose_mul_self

open Module Real Matrix MeasureTheory
open scoped Real BigOperators Pointwise
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

namespace Commons.Analysis.GaussianMeasure

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "Mx" => Matrix (Fin m) (Fin m) ℝ

/-! ## Local inlinings of the workspace definitions

The proof below is ported from `Submission/Work/Analysis/IsotropicDirect/bobkov_final.lean`, where
it was phrased with the workspace definitions `Submission.ShapeDeriv.mvec`,
`Submission.ShapeDeriv.secondMoment` and `Submission.GaussianMeasure.gammaMass`.  Those are inlined
here (as `private` definitions) so that this file imports only Mathlib and the shared commons. -/

/-- The matrix `M` as an endomorphism of Euclidean space (`= Matrix.toLpLin 2 2 M`). -/
private noncomputable def mvec (M : Mx) : E →ₗ[ℝ] E := Matrix.toLpLin 2 2 M

/-- The second-moment (isotropy) matrix of the Gaussian-weighted set `K`. -/
private noncomputable def secondMoment (K : Set E) (i j : Fin m) : ℝ :=
  ∫ y in K, rexp (-Real.pi * ‖y‖ ^ 2) * y i * y j

/-- Gaussian mass `γ_s(S) = ∫_{s⁻¹S} e^{-π‖x‖²} dx`. -/
private noncomputable def gammaMass (s : ℝ) (S : Set E) : ℝ :=
  ∫ x in {y : E | s • y ∈ S}, rexp (-Real.pi * ‖x‖ ^ 2)

/-- The exact statement of the CFM04 diagonal (B)-conjecture, as a hypothesis. -/
private def BconjHyp : Prop :=
  ∀ {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))), Convex ℝ K →
    (-K : Set (EuclideanSpace ℝ (Fin n))) = K →
    ∀ (a b : Fin n → ℝ) (lam : ℝ), 0 ≤ lam → lam ≤ 1 →
    (∫ x in (fun x : EuclideanSpace ℝ (Fin n) =>
        WithLp.toLp 2 (fun i => Real.exp (a i) * x i)) '' K,
        Real.exp (-Real.pi * ‖x‖ ^ 2)) ^ lam
      * (∫ x in (fun x : EuclideanSpace ℝ (Fin n) =>
        WithLp.toLp 2 (fun i => Real.exp (b i) * x i)) '' K,
        Real.exp (-Real.pi * ‖x‖ ^ 2)) ^ (1 - lam)
      ≤ ∫ x in (fun x : EuclideanSpace ℝ (Fin n) =>
        WithLp.toLp 2 (fun i => Real.exp (lam * a i + (1 - lam) * b i) * x i)) '' K,
        Real.exp (-Real.pi * ‖x‖ ^ 2)

/-! ## Coordinates of the matrix action -/

private noncomputable def co (y : E) : Fin m → ℝ := WithLp.ofLp (p := 2) y

private lemma coord_apply (y : E) (i : Fin m) : co y i = y i := rfl

private lemma co_mvec (M : Mx) (y : E) : co (mvec M y) = M *ᵥ co y := by
  dsimp [co, mvec]

private lemma mvec_coord_sum (M : Mx) (y : E) (i : Fin m) :
    (mvec M y) i = ∑ j : Fin m, M i j * y j := by
  have hc0 : (mvec M y) i = co (mvec M y) i := (coord_apply (mvec M y) i).symm
  rw [hc0, co_mvec]
  simp [Matrix.mulVec, dotProduct, co]

/-! ## Integrability of the coordinate-pair weight -/

private lemma gaussian_b_integrable (b : ℝ) (hb : 0 < b) :
    Integrable (fun y : E => rexp (-b * ‖y‖ ^ 2)) (volume : Measure E) := by
  refine Integrable.of_integral_ne_zero ?_
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := E) (b := b) hb
  rw [h]
  have hfin : Module.finrank ℝ E = m := by simp
  rw [hfin]
  positivity

private lemma mul_exp_neg_le_one {u : ℝ} : u * rexp (-u) ≤ 1 := by
  calc
    u * rexp (-u) ≤ rexp (-1) := mul_exp_neg_le_exp_neg_one u
    _ ≤ 1 := by exact (Real.exp_le_one_iff).2 (by norm_num)
/-- ‖y‖²·e^{-(π/2)‖y‖²} ≤ 2/π. -/
private lemma norm_sq_exp_half (y : E) : ‖y‖ ^ 2 * rexp (-(Real.pi / 2) * ‖y‖ ^ 2) ≤ 2 / Real.pi := by
  have hm := mul_exp_neg_le_one (u := (Real.pi / 2) * ‖y‖ ^ 2)
  have hstep1 : ‖y‖ ^ 2 * rexp (-(Real.pi / 2) * ‖y‖ ^ 2) =
      (2 / Real.pi) * (((Real.pi / 2) * ‖y‖ ^ 2) * rexp (-((Real.pi / 2) * ‖y‖ ^ 2))) := by
    field_simp [Real.pi_ne_zero]
  rw [hstep1]
  calc
    (2 / Real.pi) * (((Real.pi / 2) * ‖y‖ ^ 2) * rexp (-((Real.pi / 2) * ‖y‖ ^ 2))) ≤ (2 / Real.pi) * 1 := by
      exact mul_le_mul_of_nonneg_left hm (by positivity)
    _ = 2 / Real.pi := by ring

/-- ‖y‖²·e^{-π‖y‖²} ≤ (2/π)·e^{-(π/2)‖y‖²}. -/
private lemma norm_sq_exp_full_le (y : E) :
    ‖y‖ ^ 2 * rexp (-Real.pi * ‖y‖ ^ 2) ≤ (2 / Real.pi) * rexp (-(Real.pi / 2) * ‖y‖ ^ 2) := by
  have h := norm_sq_exp_half y
  have hsplit : -Real.pi * ‖y‖ ^ 2 = (-(Real.pi / 2)) * ‖y‖ ^ 2 + (-(Real.pi / 2)) * ‖y‖ ^ 2 := by ring
  calc
    ‖y‖ ^ 2 * rexp (-Real.pi * ‖y‖ ^ 2)
        = ‖y‖ ^ 2 * rexp ((-(Real.pi / 2)) * ‖y‖ ^ 2 + (-(Real.pi / 2)) * ‖y‖ ^ 2) := by rw [hsplit]
    _ = ‖y‖ ^ 2 * (rexp ((-(Real.pi / 2)) * ‖y‖ ^ 2) * rexp ((-(Real.pi / 2)) * ‖y‖ ^ 2)) := by
          rw [Real.exp_add]
    _ = (‖y‖ ^ 2 * rexp ((-(Real.pi / 2)) * ‖y‖ ^ 2)) * rexp ((-(Real.pi / 2)) * ‖y‖ ^ 2) := by ring
    _ ≤ (2 / Real.pi) * rexp ((-(Real.pi / 2)) * ‖y‖ ^ 2) := by
          exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le

/-- coordinate product × Gaussian bounded by a decaying Gaussian. -/
private lemma coordPair_norm_le (y : E) (i j : Fin m) :
    |rexp (-Real.pi * ‖y‖ ^ 2) * y i * y j| ≤ (2 / Real.pi) * rexp (-(Real.pi / 2) * ‖y‖ ^ 2) := by
  have h1 : |y i| ≤ ‖y‖ := by
    have h := PiLp.norm_apply_le (p := 2) (β := fun _ : Fin m => ℝ) y i
    simpa [Real.norm_eq_abs] using h
  have h2 : |y j| ≤ ‖y‖ := by
    have h := PiLp.norm_apply_le (p := 2) (β := fun _ : Fin m => ℝ) y j
    simpa [Real.norm_eq_abs] using h
  calc
    |rexp (-Real.pi * ‖y‖ ^ 2) * y i * y j|
        = rexp (-Real.pi * ‖y‖ ^ 2) * |y i| * |y j| := by
          rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ rexp (-Real.pi * ‖y‖ ^ 2) * ‖y‖ * ‖y‖ := by
          gcongr
    _ = ‖y‖ ^ 2 * rexp (-Real.pi * ‖y‖ ^ 2) := by ring
    _ ≤ (2 / Real.pi) * rexp (-(Real.pi / 2) * ‖y‖ ^ 2) := norm_sq_exp_full_le y

/-- coordinate-pair Gaussian integrable on any measurable-restricted set (decay domination). -/
private lemma coordPair_integrableOn (K : Set E) (i j : Fin m) :
    Integrable (fun y : E => rexp (-Real.pi * ‖y‖ ^ 2) * y i * y j) (volume.restrict K) := by
  let bnd : E → ℝ := fun y => (2 / Real.pi) * rexp (-(Real.pi / 2) * ‖y‖ ^ 2)
  have hbE : Integrable bnd (volume : Measure E) := by
    have hg : Integrable (fun y : E => rexp (-(Real.pi / 2) * ‖y‖ ^ 2)) (volume : Measure E) :=
      gaussian_b_integrable (Real.pi / 2) (by positivity)
    simpa [bnd] using hg.const_mul (2 / Real.pi)
  have hb : Integrable bnd (volume.restrict K) := by
    simpa [MeasureTheory.IntegrableOn] using hbE.integrableOn (s := K)
  have hcont : Continuous (fun y : E => rexp (-Real.pi * ‖y‖ ^ 2) * y i * y j) := by
    fun_prop
  refine Integrable.mono' hb ?meas ?ae
  · exact hcont.stronglyMeasurable.aestronglyMeasurable
  · refine Filter.Eventually.of_forall ?_
    intro y
    have hn := coordPair_norm_le y i j
    calc
      ‖rexp (-Real.pi * ‖y‖ ^ 2) * y i * y j‖ = |rexp (-Real.pi * ‖y‖ ^ 2) * y i * y j| := by
        rw [Real.norm_eq_abs]
      _ ≤ (2 / Real.pi) * rexp (-(Real.pi / 2) * ‖y‖ ^ 2) := hn

/-! ## Isotropy transfer along an orthogonal map -/

/-- Integrating a coordinate pair against the Gaussian over the orthogonal image `V '' U`. -/
private lemma integral_image_orthogonal_coordPair (V : Mx) (hV : V.transpose * V = 1)
    (U : Set E) (i j : Fin m) :
    ∫ y in (Matrix.toLpLin 2 2 V) '' U, rexp (-Real.pi * ‖y‖ ^ 2) * y i * y j
      = ∑ k : Fin m, ∑ l : Fin m, V i k * V j l *
          ∫ y in U, rexp (-Real.pi * ‖y‖ ^ 2) * y k * y l := by
  have hT : |LinearMap.det (Matrix.toLpLin 2 2 V)| = 1 :=
    Commons.Analysis.GaussianMeasure.abs_det_toLpLin_of_orthogonal V hV
  have hnorm : ∀ x : E, ‖(Matrix.toLpLin 2 2 V) x‖ = ‖x‖ :=
    Commons.Analysis.GaussianMeasure.norm_toLpLin_of_transpose_mul_eq_one V hV
  have hcoord : ∀ (y : E) (i : Fin m),
      ((Matrix.toLpLin 2 2 V) y) i = ∑ k : Fin m, V i k * y k := by
    intro y i
    exact mvec_coord_sum V y i
  have hfun : ∀ y : E,
      rexp (-Real.pi * ‖(Matrix.toLpLin 2 2 V) y‖ ^ 2)
        * ((Matrix.toLpLin 2 2 V) y) i * ((Matrix.toLpLin 2 2 V) y) j
      = ∑ k : Fin m, ∑ l : Fin m,
          (V i k * V j l) * (rexp (-Real.pi * ‖y‖ ^ 2) * y k * y l) := by
    intro y
    rw [hnorm y, hcoord y i, hcoord y j, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro l _
    ring
  rw [Commons.Analysis.GaussianMeasure.integral_image_linearMap_det_abs_one volume
      (Matrix.toLpLin 2 2 V) hT U (fun y => rexp (-Real.pi * ‖y‖ ^ 2) * y i * y j)]
  simp only [hfun]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl; intro k _
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl; intro l _
      rw [MeasureTheory.integral_const_mul]
    · intro l _
      exact (coordPair_integrableOn U k l).const_mul (V i k * V j l)
  · intro k _
    exact integrable_finsetSum Finset.univ
      (fun l _ => (coordPair_integrableOn U k l).const_mul (V i k * V j l))

/-- **Isotropy transfers along an orthogonal map.** -/
private lemma secondMoment_image_orthogonal (V : Mx) (hV : V.transpose * V = 1)
    (U : Set E) (i j : Fin m) :
    secondMoment (mvec V '' U) i j
      = ∑ k : Fin m, ∑ l : Fin m, V i k * V j l *
          secondMoment U k l := by
  have h := integral_image_orthogonal_coordPair V hV U i j
  simpa [secondMoment, mvec] using h

/-- Isotropy is preserved by an orthogonal map. -/
private lemma isotropic_image_orthogonal (V : Mx) (hV : V.transpose * V = 1)
    (hVt : V * V.transpose = 1) (U : Set E) (α : ℝ)
    (hα : ∀ i j : Fin m, secondMoment U i j
      = α * (if i = j then 1 else 0)) (i j : Fin m) :
    secondMoment (mvec V '' U) i j
      = α * (if i = j then 1 else 0) := by
  rw [secondMoment_image_orthogonal V hV U i j]
  have hinner : ∀ k : Fin m, (∑ l : Fin m, V j l * (α * (if k = l then 1 else 0)))
      = α * V j k := by
    intro k
    rw [Finset.sum_eq_single k]
    · rw [if_pos rfl, mul_one]; ring
    · intro l _ hl; rw [if_neg (Ne.symm hl), mul_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ k) h
  have hsum : (∑ k : Fin m, V i k * V j k) = (V * V.transpose) i j := by
    simp [Matrix.mul_apply, Matrix.transpose_apply]
  calc ∑ k : Fin m, ∑ l : Fin m, V i k * V j l * secondMoment U k l
      = ∑ k : Fin m, ∑ l : Fin m, V i k * (V j l * (α * (if k = l then 1 else 0))) := by
        apply Finset.sum_congr rfl; intro k _
        apply Finset.sum_congr rfl; intro l _
        rw [hα k l]; ring
    _ = ∑ k : Fin m, V i k * (α * V j k) := by
        apply Finset.sum_congr rfl; intro k _
        rw [← Finset.mul_sum, hinner k]
    _ = α * ∑ k : Fin m, V i k * V j k := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
    _ = α * (V * V.transpose) i j := by rw [hsum]
    _ = α * (if i = j then 1 else 0) := by
        rw [hVt]; simp [Matrix.one_apply]

/-! ## Auxiliary rewrites -/

/-- `γ_s(T K) = ∫_{T '' ((1/s) • K)} e^{-π‖x‖²}`. -/
private lemma gammaMass_image_linearMap (T : E →ₗ[ℝ] E) (s : ℝ) (hs : s ≠ 0) (K : Set E) :
    gammaMass s (T '' K)
      = ∫ x in T '' ((1 / s) • K), rexp (-Real.pi * ‖x‖ ^ 2) := by
  have hset : {y : E | s • y ∈ T '' K} = T '' ((1 / s) • K) := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_smul_set]
    constructor
    · rintro ⟨k, hk, hk'⟩
      refine ⟨(1 / s) • k, ⟨k, hk, rfl⟩, ?_⟩
      rw [map_smul, hk', smul_smul, one_div, inv_mul_cancel₀ hs, one_smul]
    · rintro ⟨j, hjK, hjy⟩
      obtain ⟨k', hk', rfl⟩ := hjK
      refine ⟨k', hk', ?_⟩
      rw [← hjy, map_smul, smul_smul, one_div, mul_inv_cancel₀ hs, one_smul]
  dsimp [gammaMass]
  rw [hset]

/-- The diagonal matrix map as an explicit coordinate scaling. -/
private lemma mvec_diagonal' (f : Fin m → ℝ) (x : E) :
    mvec (Matrix.diagonal f) x = WithLp.toLp 2 (fun i => f i * x i) := by
  apply WithLp.ofLp_injective (p := 2)
  funext i
  rw [mvec_coord_sum]
  simp [Matrix.diagonal]


/-! ## Bobkov's maximum-mass property, assuming the diagonal (B)-conjecture -/


/-! ## The Gaussian mass from the `s⁻¹`-image form -/

private lemma gammaMass_eq_setImage (s : ℝ) (hs : s ≠ 0) (S : Set E) :
    gammaMass s S
      = ∫ x in Set.image (fun k : E => s⁻¹ • k) S, rexp (-Real.pi * ‖x‖ ^ 2) := by
  have hset : {y : E | s • y ∈ S} = Set.image (fun k : E => s⁻¹ • k) S := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · intro hy
      exact ⟨s • y, hy, by rw [smul_smul, inv_mul_cancel₀ hs, one_smul]⟩
    · rintro ⟨k, hk, hky⟩
      rw [← hky, smul_smul, mul_inv_cancel₀ hs, one_smul]
      exact hk
  dsimp [gammaMass]
  rw [hset]
  rfl

/-! ## Bobkov's maximum-mass property, assuming the diagonal (B)-conjecture -/

private theorem bobkov_core
    (Bconj : BconjHyp)
    (K : Set E) (hKcvx : Convex ℝ K) (hKcpt : IsCompact K)
    (hKsymm : (-K : Set E) = K) (hInt : (0 : E) ∈ interior K)
    (s : ℝ) (hs : 0 < s)
    (hIso : ∃ α : ℝ, ∀ i j : Fin m,
      (∫ y in Set.image (fun k : E => s⁻¹ • k) K,
        rexp (-Real.pi * ‖y‖ ^ 2) * y i * y j) = α * (if i = j then 1 else 0))
    (A : Mx) (hA : A.det = 1) :
    gammaMass s (mvec A '' K) ≤ gammaMass s K := by
  classical
  obtain ⟨α, hα₀⟩ := hIso
  -- ------------------------------------------------------------------ setup
  set U : Set E := Set.image (fun k : E => s⁻¹ • k) K with hUdef
  have hUeq : U = (1 / s) • K := by
    rw [hUdef]
    ext x
    simp only [Set.mem_image, Set.mem_smul_set]
    constructor
    · rintro ⟨k, hk, hkx⟩; exact ⟨k, hk, by simpa [one_div] using hkx⟩
    · rintro ⟨k, hk, hkx⟩; exact ⟨k, hk, by simpa [one_div] using hkx⟩
  have hαU : ∀ i j : Fin m, secondMoment U i j
      = α * (if i = j then 1 else 0) := by
    intro i j; rw [hUdef]; exact hα₀ i j
  -- ------------------------------------------------------------------ SVD
  obtain ⟨V, d, hV, hdnn, hM⟩ :=
    Commons.LinearAlgebra.Matrix.posSemidef_spectral (A.transpose * A)
      (Commons.LinearAlgebra.Matrix.posSemidef_transpose_mul_self A)
  have hVt : V * V.transpose = 1 := mul_eq_one_comm.mp hV
  have hprodd : ∏ i, d i = 1 := by
    have h : (A.transpose * A).det = 1 := by
      rw [Matrix.det_mul, Matrix.det_transpose, hA, mul_one]
    rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
      Matrix.det_diagonal] at h
    have hVdet : V.det * V.det = 1 := by
      have h2 := congrArg Matrix.det hV
      rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h2
      linarith
    nlinarith [h, hVdet]
  have hdpos : ∀ i, 0 < d i := by
    intro i
    rcases lt_or_eq_of_le (hdnn i) with h | h
    · exact h
    · exfalso
      have hz : ∏ j, d j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) h.symm
      rw [hprodd] at hz
      exact one_ne_zero hz
  set u : Fin m → ℝ := fun i => (1 / 2) * Real.log (d i) with hu
  have hexp_u : ∀ i, Real.exp (2 * u i) = d i := by
    intro i
    have h2 : 2 * u i = Real.log (d i) := by rw [hu]; simp only; ring
    rw [h2, Real.exp_log (hdpos i)]
  have hsumu : ∑ i, u i = 0 := by
    have h2 : (2 : ℝ) * ∑ i, u i = 0 := by
      rw [Finset.mul_sum]
      have h3 : ∑ i : Fin m, 2 * u i = ∑ i : Fin m, Real.log (d i) := by
        apply Finset.sum_congr rfl; intro i _; rw [hu]; simp only; ring
      rw [h3, ← Real.log_prod (fun i _ => ne_of_gt (hdpos i)), hprodd, Real.log_one]
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  have hexp_sq : ∀ a : ℝ, Real.exp a ^ 2 = Real.exp (2 * a) := by
    intro a
    rw [sq, ← Real.exp_add, show a + a = 2 * a by ring]
  -- ------------------------------------------------------------ the bodies
  set U1 : Set E := Set.image (fun x : E => (Matrix.toLpLin 2 2 V) x) U with hU1def
  have hU1eq : U1 = mvec V '' U := rfl
  have hUcpt : IsCompact U := by
    rw [hUdef]
    exact hKcpt.image (continuous_const_smul (s⁻¹))
  have hU1cpt : IsCompact U1 := by
    rw [hU1def]
    exact hUcpt.image (LinearMap.continuous_of_finiteDimensional (Matrix.toLpLin 2 2 V))
  have hU1meas : MeasurableSet U1 := hU1cpt.isClosed.measurableSet
  have hUcvx : Convex ℝ U := by
    have h := hKcvx.linear_image (((s⁻¹ : ℝ)) • (1 : E →ₗ[ℝ] E))
    have himg : (((s⁻¹ : ℝ)) • (1 : E →ₗ[ℝ] E)) '' K = U := by
      rw [hUdef]
      congr 1
    rwa [himg] at h
  have hnegK : ∀ k : E, k ∈ K → -k ∈ K := by
    intro k hk
    have h2 : -k ∈ -K := by rw [Set.mem_neg]; simpa using hk
    rwa [hKsymm] at h2
  have hUsymm : -U = U := by
    rw [hUdef]
    ext x
    simp only [Set.mem_neg, Set.mem_image]
    constructor
    · rintro ⟨k, hk, hkx⟩
      exact ⟨-k, hnegK k hk, by rw [smul_neg, hkx, neg_neg]⟩
    · rintro ⟨k, hk, hkx⟩
      exact ⟨-k, hnegK k hk, by rw [smul_neg, hkx]⟩
  have hnegU : ∀ k : E, k ∈ U → -k ∈ U := by
    intro k hk
    have h2 : -k ∈ -U := by rw [Set.mem_neg]; simpa using hk
    rwa [hUsymm] at h2
  have hU1cvx : Convex ℝ U1 := by
    rw [hU1def]
    exact hUcvx.linear_image (Matrix.toLpLin 2 2 V)
  have hU1symm : -U1 = U1 := by
    rw [hU1def]
    ext x
    simp only [Set.mem_neg, Set.mem_image]
    constructor
    · rintro ⟨y, hy, hyx⟩
      exact ⟨-y, hnegU y hy, by rw [map_neg, hyx, neg_neg]⟩
    · rintro ⟨y, hy, hyx⟩
      exact ⟨-y, hnegU y hy, by rw [map_neg, hyx]⟩
  have hαU1 : ∀ i j : Fin m, secondMoment U1 i j
      = α * (if i = j then 1 else 0) := by
    intro i j
    rw [hU1eq]
    exact isotropic_image_orthogonal V hV hVt U α hαU i j
  -- --------------------------------------------------------------- the path
  let φ : ℝ → ℝ :=
    fun t => ∫ y in U1, rexp (-Real.pi * ∑ i : Fin m, Real.exp (2 * t * u i) * (y i) ^ 2)
  -- positivity of the base ball
  obtain ⟨r, hr, hballK⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hInt)
  set ρ : ℝ := r / s with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; positivity
  have hballU1 : Metric.ball (0 : E) ρ ⊆ U1 := by
    intro y hy
    rw [hU1def]
    refine ⟨(Matrix.toLpLin 2 2 V.transpose) y, ?_, ?_⟩
    · rw [hUeq, Set.mem_smul_set]
      refine ⟨s • ((Matrix.toLpLin 2 2 V.transpose) y), ?_, ?_⟩
      · apply hballK
        rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hs,
          Commons.Analysis.GaussianMeasure.norm_toLpLin_of_transpose_mul_eq_one V.transpose hVt]
        have hy' : ‖y‖ < ρ := by
          rw [Metric.mem_ball, dist_zero_right] at hy
          exact hy
        rw [hρdef, lt_div_iff₀ hs] at hy'
        linarith
      · rw [smul_smul, one_div, inv_mul_cancel₀ (ne_of_gt hs), one_smul]
    · have hcomp : (Matrix.toLpLin 2 2 V).comp (Matrix.toLpLin 2 2 V.transpose)
          = LinearMap.id := by
        rw [← Matrix.toLpLin_mul (p := 2) (q := 2) (r := 2), hVt, Matrix.toLpLin_one]
      exact LinearMap.congr_fun hcomp y
  have hvolU1 : 0 < volume U1 := by
    have hb : 0 < volume (Metric.ball (0 : E) ρ) := Metric.measure_ball_pos (volume : Measure E) (0 : E) hρpos
    exact lt_of_lt_of_le hb (measure_mono hballU1)
  have hpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < φ t := by
    intro t _
    have hsupp : Function.support
        (fun y : E => rexp (-Real.pi * ∑ i : Fin m, Real.exp (2 * t * u i) * (y i) ^ 2))
        = Set.univ := by
      ext y
      simp [Function.mem_support, Real.exp_ne_zero]
    have hcont : Continuous
        (fun y : E => rexp (-Real.pi * ∑ i : Fin m, Real.exp (2 * t * u i) * (y i) ^ 2)) := by
      fun_prop
    have hint : IntegrableOn
        (fun y : E => rexp (-Real.pi * ∑ i : Fin m, Real.exp (2 * t * u i) * (y i) ^ 2)) U1 :=
      hcont.continuousOn.integrableOn_compact hU1cpt
    have h := (MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall fun y => (Real.exp_pos _).le) hint).mpr
    have := h (by rw [hsupp, Set.univ_inter]; exact hvolU1)
    simpa only [φ] using this
  -- the diagonal (B)-conjecture gives pointwise log-concavity along the segment
  have hψ : ∀ t : ℝ, (∫ x in (fun x : E =>
        WithLp.toLp 2 (fun i => Real.exp (t * u i) * x i)) '' U1, rexp (-Real.pi * ‖x‖ ^ 2))
      = φ t := by
    intro t
    have hdiag := Commons.Analysis.GaussianMeasure.integral_diag_image U1 hU1meas
      (fun i : Fin m => t * u i)
    have hsum0 : Real.exp (∑ i : Fin m, t * u i) = 1 := by
      have : ∑ i : Fin m, t * u i = 0 := by
        rw [← Finset.mul_sum, hsumu, mul_zero]
      rw [this, Real.exp_zero]
    rw [hdiag, hsum0]
    simp only [one_mul]
    change (∫ y in U1, rexp (-Real.pi * ∑ i : Fin m, (Real.exp (t * u i) * y i) ^ 2))
      = ∫ y in U1, rexp (-Real.pi * ∑ i : Fin m, Real.exp (2 * t * u i) * (y i) ^ 2)
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    rw [show (∑ i : Fin m, (Real.exp (t * u i) * y i) ^ 2)
        = ∑ i : Fin m, Real.exp (2 * t * u i) * (y i) ^ 2 from by
      apply Finset.sum_congr rfl; intro i _
      rw [mul_pow, hexp_sq, show (2 : ℝ) * (t * u i) = 2 * t * u i by ring]]
  have hpoint : ∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) 1 → b ∈ Set.Icc (0 : ℝ) 1 →
      ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 →
      φ a ^ lam * φ b ^ (1 - lam) ≤ φ (lam * a + (1 - lam) * b) := by
    intro a b ha hb lam h0 h1
    have h := Bconj U1 hU1cvx hU1symm (fun i => a * u i) (fun i => b * u i) lam h0 h1
    have hset : (fun x : E => WithLp.toLp 2 (fun i =>
          Real.exp (lam * (a * u i) + (1 - lam) * (b * u i)) * x i)) '' U1
        = (fun x : E => WithLp.toLp 2 (fun i =>
          Real.exp ((lam * a + (1 - lam) * b) * u i) * x i)) '' U1 := by
      congr 1
      funext x
      congr 1
      funext i
      rw [show lam * (a * u i) + (1 - lam) * (b * u i) = (lam * a + (1 - lam) * b) * u i by ring]
    rw [hset] at h
    rw [← hψ a, ← hψ b, ← hψ (lam * a + (1 - lam) * b)]
    exact h
  have hconcave : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (fun t => Real.log (φ t)) := by
    refine ⟨convex_Icc 0 1, ?_⟩
    intro x hx y hy a b ha hb hab
    have hb1 : b = 1 - a := by linarith
    have hmain := hpoint x y hx hy a ha (by linarith)
    have hxpos : 0 < φ x := hpos x hx
    have hypos : 0 < φ y := hpos y hy
    have harg : a • x + b • y = a * x + (1 - a) * y := by
      rw [hb1]; simp [smul_eq_mul]
    rw [harg]
    calc a • Real.log (φ x) + b • Real.log (φ y)
        = a * Real.log (φ x) + (1 - a) * Real.log (φ y) := by
          rw [hb1]; simp [smul_eq_mul]
      _ = Real.log (φ x ^ a) + Real.log (φ y ^ (1 - a)) := by
          rw [Real.log_rpow hxpos, Real.log_rpow hypos]
      _ = Real.log (φ x ^ a * φ y ^ (1 - a)) := by
          rw [Real.log_mul (by positivity) (by positivity)]
      _ ≤ Real.log (φ (a * x + (1 - a) * y)) := by
          apply Real.log_le_log (by positivity)
          exact hmain
  have hderiv : HasDerivAt φ 0 0 := by
    have hraw := Commons.Analysis.GaussianMeasure.deriv_diagonal_exp_integral U1
      hU1cpt.isBounded u
    have hinv : ∀ i : Fin m, (∫ x in U1, (x i) ^ 2 * rexp (-Real.pi * ‖x‖ ^ 2)) = α := by
      intro i
      have h := hαU1 i i
      rw [if_pos rfl, mul_one] at h
      rw [← h]
      dsimp only [secondMoment]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      ring
    have hzero : (-2 * Real.pi * ∑ i : Fin m, u i *
        ∫ x in U1, (x i) ^ 2 * rexp (-Real.pi * ‖x‖ ^ 2)) = 0 := by
      have hsum : (∑ i : Fin m, u i * ∫ x in U1, (x i) ^ 2 * rexp (-Real.pi * ‖x‖ ^ 2))
          = ∑ i : Fin m, u i * α := by
        apply Finset.sum_congr rfl; intro i _; rw [hinv i]
      rw [hsum, ← Finset.sum_mul, hsumu, zero_mul, mul_zero]
    simpa only [φ] using hraw.congr_deriv hzero
  -- ---------------------------------------------------------- the two ends
  have hφ1 : φ 1 = gammaMass s
      (mvec A '' K) := by
    have hspec := Commons.Analysis.GaussianMeasure.integral_spectral_diagonal_image
      A V d hV hA hM s hs K
    rw [← hUdef] at hspec
    rw [gammaMass_image_linearMap (mvec A) s (ne_of_gt hs) K,
      show ((1 / s) • K) = U from hUeq.symm]
    change φ 1 = ∫ x in (Matrix.toLpLin 2 2 A) '' U, rexp (-Real.pi * ‖x‖ ^ 2)
    rw [hspec]
    change (∫ y in U1, rexp (-Real.pi * ∑ i : Fin m, Real.exp (2 * 1 * u i) * (y i) ^ 2))
      = ∫ y in U1, rexp (-Real.pi * ∑ i : Fin m, d i * (y i) ^ 2)
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    rw [show (∑ i : Fin m, Real.exp (2 * 1 * u i) * (y i) ^ 2)
        = ∑ i : Fin m, d i * (y i) ^ 2 from by
      apply Finset.sum_congr rfl; intro i _
      rw [show (2 : ℝ) * 1 * u i = 2 * u i by ring, hexp_u i]]
  have hφ0 : φ 0 = gammaMass s K := by
    have horth := Commons.Analysis.GaussianMeasure.integral_orthogonal_image V hV U
    have hset : U = {y : E | s • y ∈ K} := by
      rw [hUeq]
      ext y
      simp only [Set.mem_smul_set, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨k, hk, hky⟩
        rw [← hky, smul_smul, one_div, mul_inv_cancel₀ (ne_of_gt hs), one_smul]
        exact hk
      · intro hy
        exact ⟨s • y, hy, by rw [smul_smul, one_div, inv_mul_cancel₀ (ne_of_gt hs), one_smul]⟩
    have hgm : (∫ x in U, rexp (-Real.pi * ‖x‖ ^ 2))
        = gammaMass s K := by
      rw [hset]
      rfl
    have hpt : (fun y : E => rexp (-Real.pi * ∑ i : Fin m, Real.exp (2 * 0 * u i) * (y i) ^ 2))
        = fun y : E => rexp (-Real.pi * ‖y‖ ^ 2) := by
      funext y
      have h1 : ∀ i : Fin m, Real.exp (2 * 0 * u i) * (y i) ^ 2 = (y i) ^ 2 := by
        intro i
        rw [show (2 : ℝ) * 0 * u i = 0 by ring, Real.exp_zero, one_mul]
      rw [Finset.sum_congr rfl (fun i _ => h1 i), EuclideanSpace.real_norm_sq_eq]
    have hstep : φ 0 = ∫ x in U, rexp (-Real.pi * ‖x‖ ^ 2) := by
      change (∫ y in U1, rexp (-Real.pi * ∑ i : Fin m, Real.exp (2 * 0 * u i) * (y i) ^ 2)) = _
      rw [hpt, hU1def, ← horth]
    rw [hstep, hgm]
  calc gammaMass s (mvec A '' K)
      = φ 1 := hφ1.symm
    _ ≤ φ 0 :=
      Commons.Analysis.Convex.le_of_logConcaveOn_Icc_deriv_zero hpos hconcave hderiv
    _ = gammaMass s K := hφ0

/-- **Bobkov's maximum-mass property for isotropic Gaussian positions** (Bobkov 2011, Prop. 3.1;
Regev–Stephens-Davidowitz, Prop. 4.3), *conditional on the CFM04 diagonal (B)-conjecture*
`Bconj`, which is the only external input.

If `K` is a symmetric convex body with `0 ∈ interior K` in isotropic Gaussian position for the
parameter `s > 0` (i.e. `∫_{(1/s)•K} e^{-π‖y‖²} yᵢ yⱼ = α δᵢⱼ`), then `γ_s` is maximized at `K`
among the determinant-one positions: `γ_s (A K) ≤ γ_s K` for every `A` with `det A = 1`.

Here `γ_s (S) = ∫_{s⁻¹ S} e^{-π‖x‖²} dx`, and the positions `A K` are with respect to
`Matrix.toLpLin 2 2 A` (the matrix as an endomorphism of Euclidean space).

PROOF SOURCE: a complete, verified proof of this result (modulo naming `Bconj` as a hypothesis)
already exists in this workspace in `Submission/Work/Analysis/IsotropicDirect/bobkov_final.lean`
(declaration `bobkov_maximum_mass_of_Bconj`, 0 sorries, `lake env lean` rc=0).  That file phrases
everything with the local definitions `Submission.ShapeDeriv.mvec = Matrix.toLpLin 2 2`,
`Submission.ShapeDeriv.secondMoment U i j = ∫_{y∈U} e^{-π‖y‖²} yᵢ yⱼ` and
`Submission.GaussianMeasure.gammaMass s K = ∫_{s⁻¹K} e^{-π‖x‖²}`, so the port is purely
mechanical (inline those definitions; the (B)-conjecture hypothesis is literally the same
statement as `Bconj` here).  Proof structure: spectral decomposition `AᵀA = Vᵀ diag(d) V`,
`∏ dᵢ = 1`, `dᵢ > 0`, `u := ½ log ∘ d` with `Σ uᵢ = 0`, the orthogonal image `V '' ((1/s)•K)`
(still isotropic), the one-parameter function `φ t := ∫ e^{-π Σᵢ exp(2 t uᵢ) yᵢ²}` with
`φ 1 = γ_s(AK)`, `φ 0 = γ_s K`, `φ'(0) = 0` by isotropy, `log ∘ φ` concave on `[0,1]` by `Bconj`,
`φ > 0` on `[0,1]`, and `le_of_logConcaveOn_Icc_deriv_zero`. -/
theorem bobkov_maximum_mass_of_B_conjecture
    (Bconj : ∀ {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))), Convex ℝ K →
      (-K : Set (EuclideanSpace ℝ (Fin n))) = K →
      ∀ (a b : Fin n → ℝ) (lam : ℝ), 0 ≤ lam → lam ≤ 1 →
      (∫ x in (fun x : EuclideanSpace ℝ (Fin n) =>
          WithLp.toLp 2 (fun i => Real.exp (a i) * x i)) '' K,
          Real.exp (-Real.pi * ‖x‖ ^ 2)) ^ lam
        * (∫ x in (fun x : EuclideanSpace ℝ (Fin n) =>
          WithLp.toLp 2 (fun i => Real.exp (b i) * x i)) '' K,
          Real.exp (-Real.pi * ‖x‖ ^ 2)) ^ (1 - lam)
        ≤ ∫ x in (fun x : EuclideanSpace ℝ (Fin n) =>
          WithLp.toLp 2 (fun i => Real.exp (lam * a i + (1 - lam) * b i) * x i)) '' K,
          Real.exp (-Real.pi * ‖x‖ ^ 2))
    {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin m)))
    (hKcvx : Convex ℝ K) (hKcpt : IsCompact K)
    (hKsymm : (-K : Set (EuclideanSpace ℝ (Fin m))) = K)
    (hInt : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior K)
    (s : ℝ) (hs : 0 < s)
    (hIso : ∃ α : ℝ, ∀ i j : Fin m,
      (∫ y in Set.image (fun k : EuclideanSpace ℝ (Fin m) => s⁻¹ • k) K,
        Real.exp (-Real.pi * ‖y‖ ^ 2) * y i * y j) = α * (if i = j then 1 else 0))
    (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.det = 1) :
    (∫ x in Set.image (fun k : EuclideanSpace ℝ (Fin m) => s⁻¹ • k)
        ((Matrix.toLpLin 2 2 A) '' K), Real.exp (-Real.pi * ‖x‖ ^ 2))
      ≤ (∫ x in Set.image (fun k : EuclideanSpace ℝ (Fin m) => s⁻¹ • k) K,
          Real.exp (-Real.pi * ‖x‖ ^ 2)) := by
  have hcore := bobkov_core (show BconjHyp from Bconj) K hKcvx hKcpt hKsymm hInt s hs hIso A hA
  rw [gammaMass_eq_setImage s (ne_of_gt hs) (mvec A '' K),
      gammaMass_eq_setImage s (ne_of_gt hs) K] at hcore
  exact hcore

end Commons.Analysis.GaussianMeasure