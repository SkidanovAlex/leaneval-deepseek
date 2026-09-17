import Mathlib
import Submission.MatSpace
import Submission.MatBridge
import Submission.Commons.Probability.Gaussian.integral_inner_mul_inner_stdGaussian
import Submission.Commons.LinearAlgebra.Matrix.log_det_add_smul_le
import Submission.Commons.Probability.Gaussian.integral_norm_cube_stdGaussian_le
import Submission.Commons.LinearAlgebra.Matrix.trace_inv_mul_inv_mul_le
import Submission.Commons.LinearAlgebra.Matrix.trace_mul_transpose_eq_sum_sq

set_option synthInstance.maxHeartbeats 1000000

/-!
# The one-step drift of the exploration process

This file starts the estimate `E log det A_{k+1} ≤ E log det A_k - (ε²/2) N_k/c_k² + ...` of
`Submission/PLAN_V7.md` §2.  What is proved here is the *second-moment* part: for a fixed
matrix `M` and a fixed constraint space `F` (a submodule of the symmetric matrices), the
`M`-weighted second moment of the projected standard Gaussian is the sum over an orthonormal
basis of `F`,

    ∫ ξ, (M * P ξ * M * P ξ).trace dN = ∑ i, (M * m i * M * m i).trace ,

where `P` is the orthogonal projection onto `F` and `m` an orthonormal basis of `F`.  This is
the `-（ε²/2) Σ_i tr(A⁻¹ m_i A⁻¹ m_i)` term of the Taylor expansion of `log det`.
-/

namespace Submission.DriftStep

open Matrix MeasureTheory ProbabilityTheory
open Submission.MatSpace
open Submission.MatBridge

noncomputable section

variable {d : ℕ}

/-- The orthonormal basis of a constraint space, transported to the matrix world. -/
def orthMat (F : Submodule ℝ (MatV d)) (i : Fin (Module.finrank ℝ ↥F)) :
    Matrix (Fin d) (Fin d) ℝ :=
  matOf d (((stdOrthonormalBasis ℝ ↥F) i : ↥F) : MatV d)

/-- The coefficient of `ξ` in the orthonormal basis. -/
def coeff (F : Submodule ℝ (MatV d)) (ξ : MatV d) (i : Fin (Module.finrank ℝ ↥F)) : ℝ :=
  inner ℝ (((stdOrthonormalBasis ℝ ↥F) i : ↥F) : MatV d) ξ

lemma orthMat_isSymm (F : Submodule ℝ (MatV d)) (hF : F ≤ symV d)
    (i : Fin (Module.finrank ℝ ↥F)) : (orthMat F i).IsSymm :=
  isSymm_orthonormalBasis F hF i

lemma orthMat_trace_mul (F : Submodule ℝ (MatV d)) (hF : F ≤ symV d)
    (i j : Fin (Module.finrank ℝ ↥F)) :
    (orthMat F i * orthMat F j).trace = if i = j then 1 else 0 :=
  orthonormalBasis_trace_mul F hF i j

/-- The projection expands in the orthonormal basis. -/
lemma matOf_starProjection_eq (F : Submodule ℝ (MatV d)) (ξ : MatV d) :
    matOf d (F.starProjection ξ) = ∑ i, coeff F ξ i • orthMat F i := by
  rw [matOf_starProjection_eq_sum]
  rfl

lemma coeff_memLp (F : Submodule ℝ (MatV d)) (i : Fin (Module.finrank ℝ ↥F)) :
    MemLp (fun ξ : MatV d => coeff F ξ i) 2 (ProbabilityTheory.stdGaussian (MatV d)) := by
  have h1 : (fun ξ : MatV d => coeff F ξ i)
      = fun ξ => (innerSL ℝ (((stdOrthonormalBasis ℝ ↥F) i : ↥F) : MatV d)) ξ := rfl
  rw [h1]
  exact ProbabilityTheory.IsGaussian.memLp_dual _ _ 2 (by norm_num)

lemma coeff_integrable (F : Submodule ℝ (MatV d)) (i : Fin (Module.finrank ℝ ↥F)) :
    Integrable (fun ξ : MatV d => coeff F ξ i) (ProbabilityTheory.stdGaussian (MatV d)) :=
  (coeff_memLp F i).integrable (by norm_num)

lemma coeff_mul_coeff_integrable (F : Submodule ℝ (MatV d))
    (i j : Fin (Module.finrank ℝ ↥F)) :
    Integrable (fun ξ : MatV d => coeff F ξ i * coeff F ξ j)
      (ProbabilityTheory.stdGaussian (MatV d)) := by
  have h := MeasureTheory.MemLp.integrable_mul (coeff_memLp F i) (coeff_memLp F j)
  convert h using 1

/-- Orthonormality of the coefficients under the standard Gaussian. -/
lemma integral_coeff_mul_coeff (F : Submodule ℝ (MatV d))
    (i j : Fin (Module.finrank ℝ ↥F)) :
    ∫ ξ, coeff F ξ i * coeff F ξ j ∂(ProbabilityTheory.stdGaussian (MatV d))
      = if i = j then 1 else 0 := by
  rw [show (∫ ξ, coeff F ξ i * coeff F ξ j ∂(ProbabilityTheory.stdGaussian (MatV d)))
      = inner ℝ (((stdOrthonormalBasis ℝ ↥F) i : ↥F) : MatV d)
          (((stdOrthonormalBasis ℝ ↥F) j : ↥F) : MatV d) from
    Commons.Probability.Gaussian.integral_inner_mul_inner_stdGaussian _ _]
  have h := (stdOrthonormalBasis ℝ ↥F).orthonormal
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, real_inner_self_eq_norm_sq, ← Submodule.coe_norm, h.1 i]
    norm_num
  · rw [if_neg hij, ← Submodule.coe_inner F ((stdOrthonormalBasis ℝ ↥F) i)
      ((stdOrthonormalBasis ℝ ↥F) j)]
    exact h.2 hij

/-- The matrix-algebra core of the second-moment computation. -/
lemma trace_mul_proj_eq_sum (F : Submodule ℝ (MatV d)) (M : Matrix (Fin d) (Fin d) ℝ)
    (ξ : MatV d) :
    (M * matOf d (F.starProjection ξ) * M * matOf d (F.starProjection ξ)).trace
      = ∑ i, ∑ j, (coeff F ξ i * coeff F ξ j) *
          (M * orthMat F j * M * orthMat F i).trace := by
  rw [matOf_starProjection_eq F ξ]
  simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul_sum, Matrix.trace_sum,
    Matrix.trace_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul]
  ring

/-- **The second moment of the projected Gaussian.**  For a fixed matrix `M` and constraint
space `F`, the `M`-weighted second moment of `P ξ` is the sum over an orthonormal basis of
`F`. -/
theorem integral_trace_second_moment (F : Submodule ℝ (MatV d)) (M : Matrix (Fin d) (Fin d) ℝ) :
    (∫ ξ : MatV d,
        (M * matOf d (F.starProjection ξ) * M * matOf d (F.starProjection ξ)).trace
        ∂(ProbabilityTheory.stdGaussian (MatV d)))
      = ∑ i, (M * orthMat F i * M * orthMat F i).trace := by
  have hξ : ∀ ξ : MatV d,
      (M * matOf d (F.starProjection ξ) * M * matOf d (F.starProjection ξ)).trace
        = ∑ i, ∑ j, (coeff F ξ i * coeff F ξ j) *
            (M * orthMat F j * M * orthMat F i).trace := fun ξ =>
    trace_mul_proj_eq_sum F M ξ
  simp only [hξ]
  have hinner : ∀ i : Fin (Module.finrank ℝ ↥F),
      Integrable (fun ξ : MatV d => ∑ j, (coeff F ξ i * coeff F ξ j) *
        (M * orthMat F j * M * orthMat F i).trace) (ProbabilityTheory.stdGaussian (MatV d)) := by
    intro i
    refine integrable_finsetSum Finset.univ fun j _ => ?_
    exact (coeff_mul_coeff_integrable F i j).mul_const _
  have hout : (∫ ξ : MatV d, ∑ i, ∑ j, (coeff F ξ i * coeff F ξ j) *
        (M * orthMat F j * M * orthMat F i).trace ∂(ProbabilityTheory.stdGaussian (MatV d)))
      = ∑ i, ∫ ξ : MatV d, ∑ j, (coeff F ξ i * coeff F ξ j) *
        (M * orthMat F j * M * orthMat F i).trace ∂(ProbabilityTheory.stdGaussian (MatV d)) :=
    MeasureTheory.integral_finsetSum (μ := ProbabilityTheory.stdGaussian (MatV d))
      (ι := Fin (Module.finrank ℝ ↥F)) (s := Finset.univ)
      (f := fun i ξ => ∑ j, (coeff F ξ i * coeff F ξ j) *
        (M * orthMat F j * M * orthMat F i).trace)
      (fun i _ => hinner i)
  rw [hout]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hin : (∫ ξ : MatV d, ∑ j, (coeff F ξ i * coeff F ξ j) *
        (M * orthMat F j * M * orthMat F i).trace ∂(ProbabilityTheory.stdGaussian (MatV d)))
      = ∑ j, ∫ ξ : MatV d, (coeff F ξ i * coeff F ξ j) *
        (M * orthMat F j * M * orthMat F i).trace ∂(ProbabilityTheory.stdGaussian (MatV d)) :=
    MeasureTheory.integral_finsetSum (μ := ProbabilityTheory.stdGaussian (MatV d))
      (ι := Fin (Module.finrank ℝ ↥F)) (s := Finset.univ)
      (f := fun j ξ => (coeff F ξ i * coeff F ξ j) *
        (M * orthMat F j * M * orthMat F i).trace)
      (fun j _ => (coeff_mul_coeff_integrable F i j).mul_const _)
  rw [hin]
  have hsingle : ∀ j, (∫ ξ : MatV d, (coeff F ξ i * coeff F ξ j) *
        (M * orthMat F j * M * orthMat F i).trace ∂(ProbabilityTheory.stdGaussian (MatV d)))
      = (if i = j then 1 else 0) * (M * orthMat F j * M * orthMat F i).trace := by
    intro j
    rw [MeasureTheory.integral_mul_const, integral_coeff_mul_coeff]
  simp only [hsingle]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hjne
    rw [if_neg (Ne.symm hjne), zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-! ## The first moment vanishes -/

lemma integral_coeff_zero (F : Submodule ℝ (MatV d))
    (i : Fin (Module.finrank ℝ ↥F)) :
    (∫ ξ : MatV d, coeff F ξ i ∂(ProbabilityTheory.stdGaussian (MatV d))) = 0 := by
  have h : (fun ξ : MatV d => coeff F ξ i)
      = fun ξ => (innerSL ℝ (((stdOrthonormalBasis ℝ ↥F) i : ↥F) : MatV d)) ξ := rfl
  rw [h]
  exact ProbabilityTheory.integral_strongDual_stdGaussian _

/-- The linear term of the Taylor expansion has zero mean. -/
theorem integral_trace_first_moment (F : Submodule ℝ (MatV d)) (M : Matrix (Fin d) (Fin d) ℝ) :
    (∫ ξ : MatV d, (M * matOf d (F.starProjection ξ)).trace
        ∂(ProbabilityTheory.stdGaussian (MatV d))) = 0 := by
  have hξ : ∀ ξ : MatV d, (M * matOf d (F.starProjection ξ)).trace
      = ∑ i, coeff F ξ i * (M * orthMat F i).trace := by
    intro ξ
    rw [matOf_starProjection_eq F ξ, Finset.mul_sum, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, Matrix.trace_smul, smul_eq_mul]
  simp only [hξ]
  have hout : (∫ ξ : MatV d, ∑ i, coeff F ξ i * (M * orthMat F i).trace
        ∂(ProbabilityTheory.stdGaussian (MatV d)))
      = ∑ i, ∫ ξ : MatV d, coeff F ξ i * (M * orthMat F i).trace
        ∂(ProbabilityTheory.stdGaussian (MatV d)) :=
    MeasureTheory.integral_finsetSum (μ := ProbabilityTheory.stdGaussian (MatV d))
      (ι := Fin (Module.finrank ℝ ↥F)) (s := Finset.univ)
      (f := fun i ξ => coeff F ξ i * (M * orthMat F i).trace)
      (fun i _ => (coeff_integrable F i).mul_const _)
  rw [hout]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [MeasureTheory.integral_mul_const, integral_coeff_zero, zero_mul]

/-! ## The deterministic Taylor step -/

/-- The projected increment is symmetric. -/
lemma isSymm_starProjection (F : Submodule ℝ (MatV d)) (hF : F ≤ symV d) (ξ : MatV d) :
    (matOf d (F.starProjection ξ)).IsSymm :=
  mem_symV.mp (hF (Submodule.starProjection_apply_mem F ξ))

/-- **The deterministic Taylor bound of one step.**  If both `A` and `A + ε·π_F ξ` are positive
definite, then the logarithm of the determinant increases by at most the first three Taylor
terms. -/
theorem log_det_step_le (F : Submodule ℝ (MatV d)) (hF : F ≤ symV d) (𝔸 ξ : MatV d) {ε : ℝ}
    (hε : 0 ≤ ε) (hA : (matOf d 𝔸).PosDef)
    (hpos : (matOf d 𝔸 + ε • matOf d (F.starProjection ξ)).PosDef) :
    Real.log (matOf d (𝔸 + ε • F.starProjection ξ)).det
      ≤ Real.log (matOf d 𝔸).det
        + ε * ((matOf d 𝔸)⁻¹ * matOf d (F.starProjection ξ)).trace
        - (ε ^ 2 / 2) * ((matOf d 𝔸)⁻¹ * matOf d (F.starProjection ξ) * (matOf d 𝔸)⁻¹ *
            matOf d (F.starProjection ξ)).trace
        + (ε ^ 3 / 3) * (((matOf d 𝔸)⁻¹ * matOf d (F.starProjection ξ) * (matOf d 𝔸)⁻¹ *
            matOf d (F.starProjection ξ)).trace) ^ (3 / 2 : ℝ) := by
  have hmap : matOf d (𝔸 + ε • F.starProjection ξ)
      = matOf d 𝔸 + ε • matOf d (F.starProjection ξ) := by
    rw [map_add, map_smul]
  rw [hmap]
  exact Commons.LinearAlgebra.Matrix.log_det_add_smul_le (matOf d 𝔸)
    (matOf d (F.starProjection ξ)) hA (isSymm_starProjection F hF ξ) hε hpos

/-! ## The third moment of the projected Gaussian -/

/-- The third-moment bound of the standard Gaussian in arbitrary finite dimension. -/
theorem integral_norm_cube_stdGaussian_le_card {ι : Type*} [Fintype ι] :
    (∫ x, ‖x‖ ^ 3 ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)))
      ≤ 3 * (Fintype.card ι : ℝ) ^ (3 / 2 : ℝ) := by
  let e : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Fintype.card ι)) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin ι)
  have hmap : (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ ι)).map e
      = ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin (Fintype.card ι))) :=
    ProbabilityTheory.stdGaussian_map e
  have h1 : (∫ x : EuclideanSpace ℝ ι, ‖x‖ ^ 3 ∂(ProbabilityTheory.stdGaussian
        (EuclideanSpace ℝ ι)))
      = ∫ y : EuclideanSpace ℝ (Fin (Fintype.card ι)), ‖y‖ ^ 3
          ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin (Fintype.card ι)))) := by
    rw [← hmap, MeasureTheory.integral_map e.continuous.measurable.aemeasurable (by fun_prop)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ‖x‖ ^ 3 = ‖e x‖ ^ 3
    rw [e.norm_map]
  rw [h1]
  exact Commons.Probability.Gaussian.integral_norm_cube_stdGaussian_le (N := Fintype.card ι)

lemma rpow_three_halves_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : x ^ (3 / 2 : ℝ) = 0 := by
  rcases eq_or_lt_of_le hx with h | h
  · subst h
    rw [Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)]
  · rw [Real.rpow_def_of_neg h,
      show (3 : ℝ) / 2 * Real.pi = Real.pi / 2 + Real.pi by ring,
      Real.cos_add_pi, Real.cos_pi_div_two, neg_zero, mul_zero]

/-- `(x ^ 2) ^ (3 / 2) = x ^ 3` for `x ≥ 0`. -/
lemma rpow_three_halves_sq {x : ℝ} (hx : 0 ≤ x) : (x ^ 2) ^ (3 / 2 : ℝ) = x ^ 3 := by
  rw [show (x : ℝ) ^ 2 = x ^ ((2 : ℕ) : ℝ) by rw [Real.rpow_natCast]]
  rw [← Real.rpow_mul hx]
  norm_num

lemma rpow_three_halves_nonneg (x : ℝ) : 0 ≤ x ^ (3 / 2 : ℝ) := by
  by_cases h : 0 ≤ x
  · exact Real.rpow_nonneg h _
  · rw [rpow_three_halves_eq_zero_of_nonpos (le_of_not_ge h)]

/-- **The third moment of the projected Gaussian.**  This is the `O(ε³)` term of the Taylor
expansion of `log det`. -/
theorem integral_trace_third_moment_le (F : Submodule ℝ (MatV d)) (hF : F ≤ symV d)
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.PosDef) {c : ℝ} (hc : 0 < c)
    (hlow : ∀ x : Fin d → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (M.mulVec x)) :
    (∫ ξ : MatV d,
        (((M⁻¹ * matOf d (F.starProjection ξ) * M⁻¹ * matOf d (F.starProjection ξ)).trace)
          ^ (3 / 2 : ℝ))
        ∂(ProbabilityTheory.stdGaussian (MatV d)))
      ≤ 3 * (d : ℝ) ^ 3 / c ^ 3 := by
  have hB : ∀ ξ : MatV d, (matOf d (F.starProjection ξ)).IsSymm :=
    fun ξ => isSymm_starProjection F hF ξ
  have hYle : ∀ ξ : MatV d,
      (M⁻¹ * matOf d (F.starProjection ξ) * M⁻¹ * matOf d (F.starProjection ξ)).trace
        ≤ ‖F.starProjection ξ‖ ^ 2 / c ^ 2 := by
    intro ξ
    have hB' : (matOf d (F.starProjection ξ) * matOf d (F.starProjection ξ)).trace
        = (matOf d (F.starProjection ξ) * (matOf d (F.starProjection ξ))ᵀ).trace := by
      rw [(hB ξ).eq]
    refine le_trans (Commons.LinearAlgebra.Matrix.trace_inv_mul_inv_mul_le M _
      hM (hB ξ) hc (hlow)) ?_
    rw [hB', ← inner_eq_trace_mul_transpose (F.starProjection ξ) (F.starProjection ξ),
      real_inner_self_eq_norm_sq]
  have hpt : ∀ ξ : MatV d,
      ((M⁻¹ * matOf d (F.starProjection ξ) * M⁻¹ * matOf d (F.starProjection ξ)).trace)
          ^ (3 / 2 : ℝ)
        ≤ ‖ξ‖ ^ 3 / c ^ 3 := by
    intro ξ
    by_cases hpos : 0 ≤ (M⁻¹ * matOf d (F.starProjection ξ) * M⁻¹ *
        matOf d (F.starProjection ξ)).trace
    · refine le_trans (Real.rpow_le_rpow hpos (hYle ξ) (by norm_num)) ?_
      have hx : (0 : ℝ) ≤ ‖ξ‖ ^ 2 := by positivity
      have hproj : ‖F.starProjection ξ‖ ^ 2 ≤ ‖ξ‖ ^ 2 := by
        have h := Submodule.norm_starProjection_apply_le (K := F) ξ
        nlinarith [norm_nonneg (F.starProjection ξ), norm_nonneg ξ]
      refine le_trans (Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right hproj
        (by positivity)) (by norm_num)) ?_
      have h1 : (‖ξ‖ ^ 2 / c ^ 2) ^ (3 / 2 : ℝ) = ‖ξ‖ ^ 3 / c ^ 3 := by
        rw [Real.div_rpow (by positivity) (by positivity), rpow_three_halves_sq (norm_nonneg _),
          rpow_three_halves_sq (le_of_lt hc)]
      rw [h1]
    · rw [rpow_three_halves_eq_zero_of_nonpos (le_of_not_ge hpos)]
      positivity
  have hcube : Integrable (fun ξ : MatV d => ‖ξ‖ ^ (3 : ℕ)) (ProbabilityTheory.stdGaussian (MatV d)) :=
    (ProbabilityTheory.IsGaussian.memLp_id (ProbabilityTheory.stdGaussian (MatV d)) 3
      (by norm_num)).integrable_norm_pow (by norm_num)
  have hg : Integrable (fun ξ : MatV d => ‖ξ‖ ^ 3 / c ^ 3)
      (ProbabilityTheory.stdGaussian (MatV d)) := hcube.div_const _
  refine le_trans (MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun ξ => rpow_three_halves_nonneg _) hg
    (Filter.Eventually.of_forall fun ξ => hpt ξ)) ?_
  have h3' : (∫ ξ : MatV d, ‖ξ‖ ^ 3 ∂(ProbabilityTheory.stdGaussian (MatV d)))
      ≤ 3 * (d : ℝ) ^ 3 := by
    have h3 := integral_norm_cube_stdGaussian_le_card (ι := Fin d × Fin d)
    rw [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] at h3
    refine le_trans h3 ?_
    have hdd : ((d : ℝ) * d) = (d : ℝ) ^ 2 := by ring
    rw [hdd, rpow_three_halves_sq (Nat.cast_nonneg d)]
  rw [MeasureTheory.integral_div, div_le_div_iff₀ (by positivity) (by positivity)]
  calc (∫ ξ : MatV d, ‖ξ‖ ^ 3 ∂(ProbabilityTheory.stdGaussian (MatV d))) * c ^ 3
      ≤ (3 * (d : ℝ) ^ 3) * c ^ 3 := mul_le_mul_of_nonneg_right h3' (by positivity)
    _ = 3 * (d : ℝ) ^ 3 * c ^ 3 := by ring

end

end Submission.DriftStep
