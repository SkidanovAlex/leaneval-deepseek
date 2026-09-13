/-
# Restriction of a viscosity subsolution of `L_e = Δ - D_ee` to its slices

A continuous function `u` on an open set `s ⊆ ℝ⁴` which is a viscosity subsolution of the
degenerate Laplacian `L_e = tr((1 - e⊗e)D²) = Δ - D_ee` restricts, along the hyperplane
`e^⊥`, to a viscosity subsolution of the Laplacian on the slice.

This is the geometric step in the proof that a continuous `2`-convex function has a Hessian
measure (Chaudhuri--Trudinger `[CT]` Theorem 2.4); see `Submission/Roadmap.md`.

The key point is a *penalty* argument: given a test function `ψ` on the slice touching `u|_{slice}`
from above at `z₀`, one considers on the whole space the test function

`Φ_k(y) = Psi(ζ y) + k * ⟪y, e⟫ ^ 2`

where `ζ y` are the coordinates of `y` in a frame `b` with `b 0 = e` and `Psi` is a global smooth
extension of `ψ` (plus a small strictly concave correction).  For large `k` the penalisation by
`k ⟪y,e⟫²` forces the maximum point of `u - Φ_k` into the slice, and `L_e Φ_k = ΔPsi` because
`L_e` annihilates the `e`-direction.  A limiting argument as `k → ∞` gives `Δψ(z₀) ≥ 0`.
-/
import Mathlib
import Submission.Viscosity
import Submission.Commons.Analysis.ContDiff.exists_contDiff_eqOn_nhds_of_contDiffOn_of_ne_omega
import Submission.Commons.Analysis.Calculus.Laplacian.continuousOn_laplacian
import Submission.Commons.Analysis.Laplace.laplacian_add_quad
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_comp_add_linear
import Submission.Commons.Analysis.Calculus.Laplacian.laplacian_norm_sub_sq
import Submission.Commons.Analysis.Calculus.FDeriv.iteratedFDeriv_two_apply_add
import Submission.Commons.Analysis.Calculus.FDeriv.iteratedFDeriv_two_apply_const_mul
import Submission.Commons.Analysis.Calculus.FDeriv.laplacian_eq_sum_second_partials

open Metric MeasureTheory Filter Set Function
open scoped BigOperators RealInnerProductSpace InnerProductSpace Topology ENNReal

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The linear map giving the coordinates of `y` in the first three directions of the frame `b`. -/
noncomputable def frameCoord (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) : ℝ⁴ →L[ℝ] ℝ³ :=
  ∑ k : Fin 3, (innerSL ℝ (b (Fin.succ k))).smulRight (EuclideanSpace.single k 1)

/-- The point of `ℝ⁴` whose first three frame coordinates are `z`. -/
noncomputable def frameMap (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (z : ℝ³) : ℝ⁴ :=
  ∑ k : Fin 3, z k • b (Fin.succ k)

theorem frameCoord_apply (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (y : ℝ⁴) :
    frameCoord b y = ∑ k : Fin 3, ⟪b (Fin.succ k), y⟫_ℝ • EuclideanSpace.single k 1 := by
  rw [frameCoord]
  simp only [sum_apply, ContinuousLinearMap.smulRight_apply]
  rfl

/-- The expansion of a vector of `ℝ³` in the standard basis. -/
theorem sum_smul_single (z : ℝ³) : ∑ k : Fin 3, z k • EuclideanSpace.single k 1 = z := by
  apply PiLp.ext
  intro j
  rw [WithLp.ofLp_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    rw [WithLp.ofLp_smul, Pi.smul_apply, PiLp.single_apply, if_neg (Ne.symm hk)]
    simp
  · intro hj; exact absurd (Finset.mem_univ j) hj

/-- The expansion of a coefficient vector in the standard basis. -/
theorem sum_smul_single_coe (c : Fin 3 → ℝ) :
    ∑ k : Fin 3, c k • EuclideanSpace.single k 1 = WithLp.toLp 2 c := by
  simpa using sum_smul_single (WithLp.toLp 2 c)

theorem frameMap_apply (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (z : ℝ³) :
    frameMap b z = ∑ k : Fin 3, z k • b (Fin.succ k) := rfl

/-- The expansion of a vector of `ℝ⁴` in the orthonormal basis `b`. -/
theorem sum_repr_orthonormalBasis (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (y : ℝ⁴) :
    ∑ i : Fin 4, ⟪b i, y⟫_ℝ • b i = y := by
  have h : ∑ i : Fin 4, ⟪b i, y⟫_ℝ • b i
      = ∑ i : Fin 4, (b.repr y).ofLp i • b i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [OrthonormalBasis.repr_apply_apply]
  rw [h, b.sum_repr y]

theorem frameCoord_frameMap (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (z : ℝ³) :
    frameCoord b (frameMap b z) = z := by
  rw [frameCoord_apply, frameMap_apply]
  have h1 : ∀ k : Fin 3, ⟪b (Fin.succ k), ∑ j : Fin 3, z j • b (Fin.succ j)⟫_ℝ = z k := by
    intro k
    rw [inner_sum, Finset.sum_eq_single k]
    · rw [real_inner_smul_right, orthonormal_iff_ite.mp b.orthonormal, if_pos rfl]
      simp
    · intro j _ hj
      have hkj : k ≠ j := fun h => hj h.symm
      rw [real_inner_smul_right, orthonormal_iff_ite.mp b.orthonormal, if_neg, mul_zero]
      exact fun h => hkj (Fin.succ_injective 3 h)
    · intro hk; exact absurd (Finset.mem_univ k) hk
  simp only [h1]
  exact sum_smul_single z

/-- Reading off a coordinate of `frameCoord`. -/
theorem coord_frameCoord (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (y : ℝ⁴) (k : Fin 3) :
    (frameCoord b y) k = ⟪b (Fin.succ k), y⟫_ℝ := by
  rw [frameCoord_apply, sum_smul_single_coe, WithLp.ofLp_toLp]

theorem frameCoord_b (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (i : Fin 3) :
    frameCoord b (b (Fin.succ i)) = EuclideanSpace.single i 1 := by
  rw [frameCoord_apply]
  rw [Finset.sum_eq_single i]
  · rw [orthonormal_iff_ite.mp b.orthonormal, if_pos rfl, one_smul]
  · intro k _ hk
    have hne : (Fin.succ k : Fin 4) ≠ Fin.succ i :=
      fun h => hk (Fin.succ_injective 3 h)
    rw [orthonormal_iff_ite.mp b.orthonormal, if_neg hne, zero_smul]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- The component of `y` orthogonal to the slice. -/
theorem sub_frameMap_frameCoord (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (y : ℝ⁴) :
    y - frameMap b (frameCoord b y) = ⟪b 0, y⟫_ℝ • b 0 := by
  have hsum := sum_repr_orthonormalBasis b y
  rw [Fin.sum_univ_succ] at hsum
  have hfm : frameMap b (frameCoord b y)
      = ∑ i : Fin 3, ⟪b (Fin.succ i), y⟫_ℝ • b (Fin.succ i) := by
    rw [frameMap_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coord_frameCoord]
  rw [hfm]
  nth_rewrite 1 [hsum.symm]
  abel

/-- The frame map lands in the orthogonal complement of `b 0`. -/
theorem inner_last_frameMap (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (z : ℝ³) :
    ⟪b 0, frameMap b z⟫_ℝ = 0 := by
  rw [frameMap_apply, inner_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [real_inner_smul_right, orthonormal_iff_ite.mp b.orthonormal, if_neg, mul_zero]
  exact fun h => Fin.succ_ne_zero k h.symm

/-- The distance from `y` to the slice is the modulus of the normal coordinate. -/
theorem norm_sub_frameMap_frameCoord (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (y : ℝ⁴) :
    ‖y - frameMap b (frameCoord b y)‖ = |⟪b 0, y⟫_ℝ| := by
  rw [sub_frameMap_frameCoord, norm_smul, b.norm_eq_one 0, mul_one, Real.norm_eq_abs]

/-- Parseval in the orthonormal basis `b`. -/
theorem norm_sq_eq_sum_coords (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (y : ℝ⁴) :
    ‖y‖ ^ 2 = ∑ i : Fin 4, (⟪b i, y⟫_ℝ) ^ 2 := by
  rw [← b.repr.norm_map y, EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [OrthonormalBasis.repr_apply_apply, Real.norm_eq_abs, sq_abs]

/-- The squared norm of the slice coordinates. -/
theorem norm_sq_frameCoord (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (y : ℝ⁴) :
    ‖frameCoord b y‖ ^ 2 = ∑ k : Fin 3, (⟪b (Fin.succ k), y⟫_ℝ) ^ 2 := by
  rw [frameCoord_apply, sum_smul_single_coe, PiLp.norm_sq_eq_of_L2]
  simp [Real.norm_eq_abs, sq_abs]

/-- The slice coordinate map does not increase distances. -/
theorem norm_frameCoord_le (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (y : ℝ⁴) :
    ‖frameCoord b y‖ ≤ ‖y‖ := by
  have h1 : ‖frameCoord b y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [norm_sq_frameCoord, norm_sq_eq_sum_coords b y]
    rw [Fin.sum_univ_succ (f := fun i : Fin 4 => (⟪b i, y⟫_ℝ) ^ 2)]
    linarith [sq_nonneg (⟪b 0, y⟫_ℝ), sq_nonneg (‖frameCoord b y‖)]
  nlinarith [norm_nonneg (frameCoord b y), norm_nonneg y]



/-! ## The calculus of the frame coordinates -/

/-- `frameMap` as a continuous linear map. -/
noncomputable def frameMapCLM (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) : ℝ³ →L[ℝ] ℝ⁴ :=
  ∑ k : Fin 3, (EuclideanSpace.proj k).smulRight (b (Fin.succ k))

theorem frameMapCLM_apply (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (z : ℝ³) :
    frameMapCLM b z = frameMap b z := by
  rw [frameMap_apply]
  simp [frameMapCLM]

theorem frameMapCLM_sub (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (z w : ℝ³) :
    frameMap b z - frameMap b w = frameMap b (z - w) := by
  rw [← frameMapCLM_apply b z, ← frameMapCLM_apply b w, ← frameMapCLM_apply b (z - w),
    map_sub]

/-- The normal component map. -/
noncomputable def frameNormal (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) : ℝ⁴ →L[ℝ] ℝ⁴ :=
  1 - (frameMapCLM b).comp (frameCoord b)

theorem frameNormal_apply (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (y : ℝ⁴) :
    frameNormal b y = y - frameMap b (frameCoord b y) := by
  simp [frameNormal, frameMapCLM_apply]

theorem norm_frameNormal (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (y : ℝ⁴) :
    ‖frameNormal b y‖ = |⟪b 0, y⟫_ℝ| := by
  rw [frameNormal_apply, norm_sub_frameMap_frameCoord]

/-- The slice map does not increase distances. -/
theorem norm_frameMap_le (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (y : ℝ⁴) :
    ‖frameMap b (frameCoord b y)‖ ≤ ‖y‖ := by
  have hdec : y = frameMap b (frameCoord b y) + ⟪b 0, y⟫_ℝ • b 0 := by
    rw [← sub_frameMap_frameCoord b y]; abel
  have h4 : ⟪frameMap b (frameCoord b y), b 0⟫_ℝ = 0 := by
    rw [real_inner_comm (b 0) (frameMap b (frameCoord b y))]
    exact inner_last_frameMap b (frameCoord b y)
  have horth : ⟪frameMap b (frameCoord b y), ⟪b 0, y⟫_ℝ • b 0⟫_ℝ = 0 := by
    rw [real_inner_smul_right, h4, mul_zero]
  have h3 : ‖y‖ ^ 2
      = ‖frameMap b (frameCoord b y)‖ ^ 2 + ‖⟪b 0, y⟫_ℝ • (b 0 : ℝ⁴)‖ ^ 2 := by
    conv_lhs => rw [hdec]
    rw [norm_add_sq_real, horth]
    ring
  nlinarith [norm_nonneg (frameMap b (frameCoord b y)),
    sq_nonneg (‖⟪b 0, y⟫_ℝ • (b 0 : ℝ⁴)‖), norm_nonneg y]

/-- The chain rule for a linear parameterisation. -/
private theorem fderiv_fderiv_comp_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) (f : F → ℝ) (hf : ContDiff ℝ 2 f)
    (y u v : E) :
    (fderiv ℝ (fderiv ℝ (fun y : E => f (L y))) y) u v
      = (fderiv ℝ (fderiv ℝ f) (L y)) (L u) (L v) := by
  have h := Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_comp_add_linear L (0 : F) f hf y u v
  simpa using h

/-- Additivity of the second derivative. -/
private theorem fderiv_fderiv_add {g h : ℝ⁴ → ℝ} {y u v : ℝ⁴}
    (hg : ContDiffAt ℝ 2 g y) (hh : ContDiffAt ℝ 2 h y) :
    (fderiv ℝ (fderiv ℝ (g + h)) y) u v
      = (fderiv ℝ (fderiv ℝ g) y) u v + (fderiv ℝ (fderiv ℝ h) y) u v := by
  have h1 := Commons.Analysis.Calculus.FDeriv.iteratedFDeriv_two_apply_add
    (x := y) (a := u) (b := v) hg hh
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply, iteratedFDeriv_two_apply] at h1
  simpa using h1

/-- Scalar multiples and the second derivative. -/
private theorem fderiv_fderiv_const_mul (k : ℝ) (g : ℝ⁴ → ℝ) (y u v : ℝ⁴) :
    (fderiv ℝ (fderiv ℝ (fun y : ℝ⁴ => k * g y)) y) u v
      = k * (fderiv ℝ (fderiv ℝ g) y) u v := by
  have h1 : fderiv ℝ (fun y : ℝ⁴ => k * g y) = fun y : ℝ⁴ => k • fderiv ℝ g y := by
    rw [show (fun y : ℝ⁴ => k * g y) = k • g from by funext y; simp [smul_eq_mul]]
    rw [fderiv_const_smul_field]
    rfl
  have h2 : fderiv ℝ (fun y : ℝ⁴ => k • fderiv ℝ g y) y
      = k • (fderiv ℝ (fderiv ℝ g) y) := by
    have hb : (k • (fderiv ℝ g)) = (fun y : ℝ⁴ => k • fderiv ℝ g y) := rfl
    have hthis := congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := fderiv ℝ g) k) y
    rw [hb] at hthis
    exact hthis
  rw [h1, h2]
  simp [smul_eq_mul]

/-- The chain rule for the frame coordinate parameterisation. -/
theorem fderiv_fderiv_frameCoord {ψ : ℝ³ → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (y u v : ℝ⁴) :
    (fderiv ℝ (fderiv ℝ (fun y : ℝ⁴ => ψ (frameCoord b y))) y) u v
      = (fderiv ℝ (fderiv ℝ ψ) (frameCoord b y)) (frameCoord b u) (frameCoord b v) :=
  fderiv_fderiv_comp_clm (frameCoord b) ψ hψ y u v

/-- The Laplacian in `ℝ³` computed in the standard frame. -/
theorem laplacian_eq_sum_single {ψ : ℝ³ → ℝ} (z : ℝ³) :
    Laplacian.laplacian ψ z =
      ∑ k : Fin 3, (fderiv ℝ (fderiv ℝ ψ) z)
        (EuclideanSpace.single k 1) (EuclideanSpace.single k 1) := by
  rw [Commons.Analysis.Calculus.FDeriv.laplacian_eq_sum_second_partials
    (EuclideanSpace.basisFun (Fin 3) ℝ) ψ z]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [bilinearIteratedFDerivTwo_eq_iteratedFDeriv, iteratedFDeriv_two_apply,
    EuclideanSpace.basisFun_apply]
  simp

/-- `L_e` of a function of the frame coordinates is its Laplacian. -/
theorem frame_laplacian_comp {ψ : ℝ³ → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (y : ℝ⁴) :
    (∑ i : Fin 3, (fderiv ℝ (fderiv ℝ (fun y : ℝ⁴ => ψ (frameCoord b y))) y)
        (b (Fin.succ i)) (b (Fin.succ i)))
      = Laplacian.laplacian ψ (frameCoord b y) := by
  rw [laplacian_eq_sum_single]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_fderiv_frameCoord hψ b y, frameCoord_b]

/-- The second derivative of the normal norm square along the slice directions. -/
theorem fderiv_fderiv_norm_frameNormal (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (y : ℝ⁴)
    (i : Fin 3) :
    (fderiv ℝ (fderiv ℝ (fun y : ℝ⁴ => ‖frameNormal b y‖ ^ 2)) y)
        (b (Fin.succ i)) (b (Fin.succ i)) = 0 := by
  have hF : ContDiff ℝ 2 (fun z : ℝ⁴ => ‖z‖ ^ 2) := contDiff_norm_sq ℝ
  have h := fderiv_fderiv_comp_clm (frameNormal b) (fun z : ℝ⁴ => ‖z‖ ^ 2) hF y
    (b (Fin.succ i)) (b (Fin.succ i))
  have h2 : (fderiv ℝ (fderiv ℝ (fun z : ℝ⁴ => ‖z‖ ^ 2)) (frameNormal b y))
      (frameNormal b (b (Fin.succ i))) (frameNormal b (b (Fin.succ i)))
      = 2 * ‖frameNormal b (b (Fin.succ i))‖ ^ 2 := by
    have hsub := Commons.Analysis.Calculus.Laplacian.fderiv_fderiv_norm_sub_sq (0 : ℝ⁴)
      (frameNormal b y) (frameNormal b (b (Fin.succ i)))
    simpa using hsub
  rw [h, h2, norm_frameNormal]
  have h3 : (⟪b 0, b (Fin.succ i)⟫_ℝ) = 0 := by
    rw [orthonormal_iff_ite.mp b.orthonormal]
    exact if_neg (fun hh => Fin.succ_ne_zero i hh.symm)
  rw [h3]
  simp

/-- The `L_e`-second derivative of the penalty term vanishes. -/
theorem frame_laplacian_penalty (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (c k : ℝ) (y : ℝ⁴) :
    (∑ i : Fin 3, (fderiv ℝ (fderiv ℝ (fun y : ℝ⁴ => c + k * ‖frameNormal b y‖ ^ 2)) y)
        (b (Fin.succ i)) (b (Fin.succ i))) = 0 := by
  have hsplit : (fun y : ℝ⁴ => c + k * ‖frameNormal b y‖ ^ 2)
      = (fun _ : ℝ⁴ => c) + (fun y : ℝ⁴ => k * ‖frameNormal b y‖ ^ 2) := by
    funext y; rfl
  rw [hsplit]
  rw [Finset.sum_eq_zero]
  intro i _
  have hcd : ContDiffAt ℝ 2 (fun _ : ℝ⁴ => c) y := contDiffAt_const
  have hQ : ContDiffAt ℝ 2 (fun y : ℝ⁴ => frameNormal b y) y :=
    (frameNormal b).contDiff.contDiffAt
  have hgd : ContDiffAt ℝ 2 (fun y : ℝ⁴ => k * ‖frameNormal b y‖ ^ 2) y := by
    have h := (hQ.norm_sq ℝ).const_smul k
    simpa [smul_eq_mul] using h
  rw [fderiv_fderiv_add hcd hgd]
  have hconst : (fderiv ℝ (fderiv ℝ (fun _ : ℝ⁴ => c)) y)
      (b (Fin.succ i)) (b (Fin.succ i)) = 0 := by simp
  have hmul : (fderiv ℝ (fderiv ℝ (fun y : ℝ⁴ => k * ‖frameNormal b y‖ ^ 2)) y)
      (b (Fin.succ i)) (b (Fin.succ i)) = 0 := by
    rw [fderiv_fderiv_const_mul, fderiv_fderiv_norm_frameNormal, mul_zero]
  rw [hconst, hmul, add_zero]

/-- Evaluation of the frame coordinate map. -/
theorem frameCoord_frameMapCLM_eq (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (z : ℝ³) :
    frameCoord b (frameMap b z) = z := frameCoord_frameMap b z



/-! ## The slice theorem -/

/-- The domain of the slice through `z₀`. -/
def sliceSet (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (s : Set ℝ⁴) : Set ℝ³ :=
  {z : ℝ³ | frameMap b z ∈ s}

theorem isOpen_sliceSet (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) {s : Set ℝ⁴} (hs : IsOpen s) :
    IsOpen (sliceSet b s) := by
  have h : sliceSet b s = frameMapCLM b ⁻¹' s := rfl
  rw [h]
  exact hs.preimage (frameMapCLM b).continuous

theorem frameNormal_frameMap (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (z : ℝ³) :
    frameNormal b (frameMap b z) = 0 := by
  rw [frameNormal_apply, frameCoord_frameMap, sub_self]

theorem frameMap_sub_frameMap (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (z w : ℝ³) :
    frameMap b z - frameMap b w = frameMap b (z - w) := frameMapCLM_sub b z w

theorem frameCoord_sub (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (y y' : ℝ⁴) :
    frameCoord b y - frameCoord b y' = frameCoord b (y - y') := (map_sub _ _ _).symm

theorem frameCoord_frameMap_eq (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (y : ℝ⁴) :
    frameCoord b (frameMap b (frameCoord b y)) = frameCoord b y := frameCoord_frameMap b _

theorem inner_last_frameMap' (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (z : ℝ³) :
    ⟪b 0, frameMap b z⟫_ℝ = 0 := inner_last_frameMap b z

/-- The squared norm of the normal coordinate. -/
theorem norm_sq_frameCoord_eq (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (u : ℝ⁴) :
    ‖frameCoord b u‖ ^ 2 = ‖u‖ ^ 2 - ⟪b 0, u⟫_ℝ ^ 2 := by
  rw [norm_sq_frameCoord, norm_sq_eq_sum_coords b u]
  rw [Fin.sum_univ_succ (f := fun i : Fin 4 => (⟪b i, u⟫_ℝ) ^ 2)]
  ring

/-- The Laplacian of a function plus a positive multiple of a squared distance. -/
theorem laplacian_add_norm_sq {n : ℕ} {h : EuclideanSpace ℝ (Fin n) → ℝ}
    {c x : EuclideanSpace ℝ (Fin n)} (hh : ContDiffAt ℝ 2 h x) (δ : ℝ) :
    Laplacian.laplacian (fun y : EuclideanSpace ℝ (Fin n) => h y + δ * ‖y - c‖ ^ 2) x
      = Laplacian.laplacian h x + 2 * (n : ℝ) * δ := by
  have key := Commons.Analysis.Laplace.laplacian_add_quad (n := n) (c := c) (x := x) hh (-δ) 0
  rw [show (fun y : EuclideanSpace ℝ (Fin n) => h y + (-δ) * (0 ^ 2 - ‖y - c‖ ^ 2))
      = (fun y : EuclideanSpace ℝ (Fin n) => h y + δ * ‖y - c‖ ^ 2) from by
        funext y; ring] at key
  rw [key]
  ring

theorem frameCoord_sub_frameMap (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (y : ℝ⁴) (z : ℝ³) :
    frameCoord b y - z = frameCoord b (y - frameMap b z) := by
  conv_lhs => rw [← frameCoord_frameMap b z]
  exact frameCoord_sub b y (frameMap b z)

theorem frameMap_frameCoord_sub_frameMap (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (y : ℝ⁴) (z : ℝ³) :
    frameMap b (frameCoord b y) - frameMap b z = frameMap b (frameCoord b (y - frameMap b z)) := by
  rw [frameMap_sub_frameMap]
  congr 1
  exact frameCoord_sub_frameMap b y z

theorem inner_last_sub_frameMap (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (y : ℝ⁴) (z : ℝ³) :
    ⟪b 0, y - frameMap b z⟫_ℝ = ⟪b 0, y⟫_ℝ := by
  rw [inner_sub_right, inner_last_frameMap, sub_zero]

theorem norm_frameCoord_sub_frameMap (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (y : ℝ⁴) (z : ℝ³) :
    ‖frameCoord b y - z‖ ≤ ‖y - frameMap b z‖ := by
  rw [frameCoord_sub_frameMap]
  exact norm_frameCoord_le b _

theorem norm_sq_frameCoord_sub_frameMap (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (y : ℝ⁴) (z : ℝ³) :
    ‖frameCoord b y - z‖ ^ 2 = ‖y - frameMap b z‖ ^ 2 - ⟪b 0, y⟫_ℝ ^ 2 := by
  rw [frameCoord_sub_frameMap, norm_sq_frameCoord_eq, inner_last_sub_frameMap]

theorem norm_dist_frameNormal (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (y : ℝ⁴) :
    ‖frameNormal b y‖ = |⟪b 0, y⟫_ℝ| := norm_frameNormal b y

/-- **The slice of a viscosity subsolution of `L_e = Δ - D_ee` is a viscosity subsolution of the
Laplacian.**

This is the geometric step in the proof that a continuous `2`-convex function has a Hessian measure
(Chaudhuri--Trudinger `[CT]` Theorem 2.4). -/
theorem isViscSubsolution_slice {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s)
    (hu : ContinuousOn u s) (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴)
    (hvis : ∀ φ : ℝ⁴ → ℝ, ContDiffOn ℝ 2 φ s → ∀ x ∈ s,
        (∀ᶠ y in 𝓝[s] x, u y - φ y ≤ u x - φ x) →
        0 ≤ ∑ i : Fin 3, (fderiv ℝ (fderiv ℝ φ) x)
          (b (Fin.succ i)) (b (Fin.succ i))) :
    ∀ ψ : ℝ³ → ℝ, ContDiffOn ℝ 2 ψ (sliceSet b s) → ∀ z₀ ∈ sliceSet b s,
      (∀ᶠ z in 𝓝[sliceSet b s] z₀, u (frameMap b z) - ψ z ≤ u (frameMap b z₀) - ψ z₀) →
      0 ≤ Laplacian.laplacian ψ z₀ := by
  intro ψ hψ z₀ hz₀ hmax
  by_contra hneg
  rw [not_le] at hneg
  have hX : frameMap b z₀ ∈ s := hz₀
  -- ## the strictly concave perturbation of `ψ`
  set δ : ℝ := -Laplacian.laplacian ψ z₀ / 12 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set ψδ : ℝ³ → ℝ := fun z => ψ z + δ * ‖z - z₀‖ ^ 2 with hψδ
  have hψδon : ContDiffOn ℝ 2 ψδ (sliceSet b s) := by
    rw [hψδ]
    exact hψ.add (contDiffOn_const.mul (ContDiffOn.norm_sq ℝ (contDiffOn_id.sub contDiffOn_const)))
  have hψδlap : ∀ z ∈ sliceSet b s, Laplacian.laplacian ψδ z = Laplacian.laplacian ψ z + 6 * δ := by
    intro z hz
    have hcd : ContDiffAt ℝ 2 ψ z :=
      (hψ.contDiffWithinAt hz).contDiffAt ((isOpen_sliceSet b hs).mem_nhds hz)
    have h := laplacian_add_norm_sq (n := 3) (h := ψ) (c := z₀) (x := z) hcd δ
    rw [hψδ, h]
    ring
  -- ## the global extension of `ψδ`
  obtain ⟨Psi, hPsicd, hPsieq⟩ :=
    Commons.Analysis.ContDiff.exists_contDiff_eqOn_nhds_of_contDiffOn_of_ne_omega 2 (by decide)
      (isOpen_sliceSet b hs) hz₀ hψδon
  obtain ⟨ρ₄, hρ₄pos, hρ₄⟩ : ∃ ρ > 0, ∀ z ∈ ball z₀ ρ, Psi z = ψδ z := by
    have hev : ∀ᶠ z in 𝓝 z₀, Psi z = ψδ z := hPsieq
    rw [Filter.eventually_iff, Metric.mem_nhds_iff] at hev
    exact hev
  -- ## balls on which the Laplacian of `ψδ` stays negative
  have hcontψδ : ContinuousOn (fun z => Laplacian.laplacian ψδ z) (sliceSet b s) :=
    Commons.Analysis.Calculus.Laplacian.continuousOn_laplacian (isOpen_sliceSet b hs) hψδon
  have hmem₀ : sliceSet b s ∈ 𝓝 z₀ := (isOpen_sliceSet b hs).mem_nhds hz₀
  have hca : ContinuousAt (fun z => Laplacian.laplacian ψδ z) z₀ :=
    hcontψδ.continuousAt hmem₀
  have hδneg₀ : Laplacian.laplacian ψδ z₀ < 0 := by
    rw [hψδlap z₀ hz₀]
    have h6 : Laplacian.laplacian ψ z₀ + 6 * δ = Laplacian.laplacian ψ z₀ / 2 := by
      rw [hδ]; ring
    rw [h6]; linarith
  have hevδ : ∀ᶠ z in 𝓝 z₀, Laplacian.laplacian ψδ z < 0 :=
    hca (isOpen_Iio.mem_nhds hδneg₀)
  obtain ⟨ρ₁, hρ₁pos, hρ₁sub, hρ₁⟩ : ∃ ρ > 0, ball z₀ ρ ⊆ sliceSet b s ∧
      ∀ z ∈ ball z₀ ρ, Laplacian.laplacian ψδ z < 0 := by
    have hm : ∀ᶠ z in 𝓝 z₀, z ∈ sliceSet b s := hmem₀
    have h := hm.and hevδ
    rw [Filter.eventually_iff, Metric.mem_nhds_iff] at h
    obtain ⟨ρ, hρpos, hρ⟩ := h
    exact ⟨ρ, hρpos, fun z hz => (hρ hz).1, fun z hz => (hρ hz).2⟩
  -- ## balls on which the touching inequality holds
  obtain ⟨ρ₂, hρ₂pos, hρ₂sub, hρ₂⟩ : ∃ ρ > 0, ball z₀ ρ ⊆ sliceSet b s ∧
      ∀ z ∈ ball z₀ ρ, u (frameMap b z) - ψ z ≤ u (frameMap b z₀) - ψ z₀ := by
    have hmax' : ∀ᶠ z in 𝓝 z₀, z ∈ sliceSet b s →
        u (frameMap b z) - ψ z ≤ u (frameMap b z₀) - ψ z₀ :=
      eventually_nhdsWithin_iff.mp hmax
    rw [Filter.eventually_iff, Metric.mem_nhds_iff] at hmax'
    obtain ⟨ρ, hρpos, hρ⟩ := hmax'
    obtain ⟨ρ', hρ'pos, hρ'sub⟩ := Metric.mem_nhds_iff.mp hmem₀
    refine ⟨min ρ ρ', lt_min hρpos hρ'pos, ?_, ?_⟩
    · intro z hz
      exact hρ'sub (mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hz) (min_le_right _ _)))
    · intro z hz
      exact hρ (mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hz) (min_le_left _ _)))
        (hρ'sub (mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hz) (min_le_right _ _))))
  -- ## a ball around the centre inside `s`
  obtain ⟨ρ₃, hρ₃pos, hρ₃⟩ : ∃ ρ > 0, closedBall (frameMap b z₀) ρ ⊆ s := by
    obtain ⟨ρ, hρpos, hρ⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hX)
    refine ⟨ρ / 2, by positivity, fun z hz => hρ (mem_ball.mpr ?_)⟩
    exact lt_of_le_of_lt (mem_closedBall.mp hz) (by linarith)
  -- ## the working radius
  set r : ℝ := min (min (min ρ₁ ρ₂) ρ₄) ρ₃ / 8 with hr
  have hrpos : 0 < r := by rw [hr]; positivity
  have hmin₁ : min (min (min ρ₁ ρ₂) ρ₄) ρ₃ ≤ ρ₁ :=
    (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hmin₂ : min (min (min ρ₁ ρ₂) ρ₄) ρ₃ ≤ ρ₂ :=
    (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hmin₄ : min (min (min ρ₁ ρ₂) ρ₄) ρ₃ ≤ ρ₄ :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hmin₃ : min (min (min ρ₁ ρ₂) ρ₄) ρ₃ ≤ ρ₃ := min_le_right _ _
  have hr₁ : r < ρ₁ := by rw [hr]; linarith
  have hr₂ : r < ρ₂ := by rw [hr]; linarith
  have hr₄ : r < ρ₄ := by rw [hr]; linarith
  have hr₃ : r < ρ₃ := by rw [hr]; linarith
  set K : Set ℝ⁴ := closedBall (frameMap b z₀) r with hK
  have hKsub : K ⊆ s := (closedBall_subset_closedBall hr₃.le).trans hρ₃
  have hKcomp : IsCompact K := isCompact_closedBall _ r
  have hKne : K.Nonempty :=
    ⟨frameMap b z₀, by rw [hK, mem_closedBall, dist_self]; exact hrpos.le⟩
  -- ## uniform bounds
  obtain ⟨M, hMnn, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ K, |u y| ≤ M := by
    obtain ⟨C, hC⟩ := hKcomp.exists_bound_of_continuousOn (hu.mono hKsub)
    refine ⟨max C 0, le_max_right _ _, fun y hy => ?_⟩
    rw [← Real.norm_eq_abs]
    exact (hC y hy).trans (le_max_left _ _)
  obtain ⟨t₁, ht₁pos, ht₁⟩ : ∃ t > 0, ∀ y ∈ K, ∀ z ∈ K, dist y z ≤ t →
      |u y - u z| ≤ δ * r ^ 2 / 4 := by
    have hunif := hKcomp.uniformContinuousOn_of_continuous (hu.mono hKsub)
    obtain ⟨t, htpos, ht⟩ :=
      Metric.uniformContinuousOn_iff_le.mp hunif (δ * r ^ 2 / 4) (by positivity)
    refine ⟨t, htpos, fun y hy z hz hyz => ?_⟩
    have h := ht y hy z hz hyz
    rwa [Real.dist_eq] at h
  set μ : ℝ := min t₁ (r / 2) with hμ
  have hμpos : 0 < μ := by rw [hμ]; exact lt_min ht₁pos (by positivity)
  have hμt : μ ≤ t₁ := by rw [hμ]; exact min_le_left _ _
  have hμr : μ ≤ r / 2 := by rw [hμ]; exact min_le_right _ _
  -- ## the penalty weight
  obtain ⟨k, hkpos, hkbig⟩ : ∃ k : ℝ, 0 < k ∧ 2 * M < k * μ ^ 2 := by
    refine ⟨(2 * M + 1) / μ ^ 2, div_pos (by linarith) (by positivity), ?_⟩
    rw [div_mul_cancel₀ _ (by positivity)]
    linarith
  -- ## the test function
  set c₀ : ℝ := u (frameMap b z₀) - ψ z₀ with hc₀
  set Φ : ℝ⁴ → ℝ := fun y => Psi (frameCoord b y) + (c₀ + k * ‖frameNormal b y‖ ^ 2) with hΦ
  have hΦcd : ContDiff ℝ 2 Φ := by
    have h1 : ContDiff ℝ 2 (fun y : ℝ⁴ => Psi (frameCoord b y)) :=
      hPsicd.comp (frameCoord b).contDiff
    have h2 : ContDiff ℝ 2 (fun y : ℝ⁴ => c₀ + k * ‖frameNormal b y‖ ^ 2) := by
      refine contDiff_const.add ?_
      have hbase : ContDiff ℝ 2 (fun y : ℝ⁴ => frameNormal b y) := (frameNormal b).contDiff
      have h3 : ContDiff ℝ 2 (fun y : ℝ⁴ => k * ‖frameNormal b y‖ ^ 2) := by
        have h4 := (hbase.norm_sq (𝕜 := ℝ)).const_smul k
        simpa [smul_eq_mul] using h4
      simpa using h3
    rw [hΦ]
    exact h1.add h2
  -- ## the maximum
  obtain ⟨y₀, hy₀K, hy₀max⟩ := hKcomp.exists_isMaxOn hKne
    ((hu.mono hKsub).sub hΦcd.continuous.continuousOn)
  -- ## the value at the centre is zero
  have hPsiz₀ : Psi z₀ = ψ z₀ := by
    rw [hρ₄ z₀ (mem_ball.mpr (by rw [dist_self]; exact hρ₄pos))]
    simp [hψδ]
  have hvalX₀ : u (frameMap b z₀) - Φ (frameMap b z₀) = 0 := by
    rw [hΦ]
    simp only [frameCoord_frameMap, frameNormal_frameMap, norm_zero, hPsiz₀, hc₀]
    ring
  -- ## the boundary values are strictly negative
  have hbd : ∀ y ∈ sphere (frameMap b z₀) r, u y - Φ y < 0 := by
    intro y hy
    have hyK : y ∈ K := sphere_subset_closedBall hy
    have hyr : ‖y - frameMap b z₀‖ = r := by
      have h := hy; rw [mem_sphere, dist_eq_norm] at h; exact h
    have hζK : frameMap b (frameCoord b y) ∈ K := by
      rw [hK, mem_closedBall, dist_eq_norm]
      calc ‖frameMap b (frameCoord b y) - frameMap b z₀‖
          = ‖frameMap b (frameCoord b (y - frameMap b z₀))‖ := by
            rw [frameMap_frameCoord_sub_frameMap]
        _ ≤ ‖y - frameMap b z₀‖ := norm_frameMap_le b _
        _ = r := hyr
    have hζnrm : ‖frameCoord b y - z₀‖ ≤ r :=
      (norm_frameCoord_sub_frameMap b y z₀).trans_eq hyr
    have hζball₄ : frameCoord b y ∈ ball z₀ ρ₄ :=
      mem_ball.mpr (lt_of_le_of_lt hζnrm hr₄)
    have hζball₂ : frameCoord b y ∈ ball z₀ ρ₂ :=
      mem_ball.mpr (lt_of_le_of_lt hζnrm hr₂)
    have htouch : u (frameMap b (frameCoord b y)) - ψ (frameCoord b y) ≤ c₀ := hρ₂ _ hζball₂
    have hPsimid : Psi (frameCoord b y) = ψ (frameCoord b y) + δ * ‖frameCoord b y - z₀‖ ^ 2 := by
      rw [hρ₄ _ hζball₄, hψδ]
    have hdecomp : u y - Φ y
        = (u y - u (frameMap b (frameCoord b y)))
          + ((u (frameMap b (frameCoord b y)) - ψ (frameCoord b y)) - c₀)
          - δ * ‖frameCoord b y - z₀‖ ^ 2 - k * ‖frameNormal b y‖ ^ 2 := by
      show u y - (Psi (frameCoord b y) + (c₀ + k * ‖frameNormal b y‖ ^ 2)) = _
      rw [hPsimid]
      ring
    have hnrm : ‖frameCoord b y - z₀‖ ^ 2 = r ^ 2 - ‖frameNormal b y‖ ^ 2 := by
      rw [norm_sq_frameCoord_sub_frameMap, hyr, norm_frameNormal, sq_abs]
    have hnval : ‖frameNormal b y‖ ^ 2 = ⟪b 0, y⟫_ℝ ^ 2 := by
      rw [norm_frameNormal, sq_abs]
    have hdist : dist y (frameMap b (frameCoord b y)) = |⟪b 0, y⟫_ℝ| := by
      rw [dist_eq_norm]; exact norm_sub_frameMap_frameCoord b y
    rcases le_or_gt |⟪b 0, y⟫_ℝ| μ with hsmall | hbig
    · have hdist' : dist y (frameMap b (frameCoord b y)) ≤ t₁ := by
        rw [hdist]; exact hsmall.trans hμt
      have hA : u y - u (frameMap b (frameCoord b y)) ≤ δ * r ^ 2 / 4 := by
        have h := ht₁ y hyK _ hζK hdist'
        rw [abs_le] at h
        linarith [h.2]
      have hsq : ⟪b 0, y⟫_ℝ ^ 2 ≤ μ ^ 2 := by
        have h := abs_le.mp hsmall
        nlinarith [h.1, h.2]
      have hμ2 : μ ^ 2 ≤ r ^ 2 / 4 := by nlinarith [hμr, hrpos]
      have hq2 : ‖frameNormal b y‖ ^ 2 ≤ r ^ 2 / 4 := by
        rw [hnval]; linarith
      have hnonneg : δ * ‖frameCoord b y - z₀‖ ^ 2 ≥ δ * (r ^ 2 - r ^ 2 / 4) := by
        rw [hnrm]
        nlinarith [hq2, hδpos]
      have hval : u y - Φ y ≤ δ * r ^ 2 / 4 - δ * ‖frameCoord b y - z₀‖ ^ 2 := by
        rw [hdecomp]
        linarith [hA, htouch, mul_nonneg hkpos.le (sq_nonneg (‖frameNormal b y‖))]
      have hpos : 0 < δ * r ^ 2 := mul_pos hδpos (pow_pos hrpos 2)
      linarith [hval, hnonneg, hpos]
    · have hA : u y - u (frameMap b (frameCoord b y)) ≤ 2 * M := by
        have h1 := hM y hyK
        have h2 := hM _ hζK
        rw [abs_le] at h1 h2
        linarith [h1.2, h2.1]
      have hsq : μ ^ 2 < ⟪b 0, y⟫_ℝ ^ 2 := by
        rcases lt_abs.mp hbig with h | h <;> nlinarith
      have hnonneg : 0 ≤ δ * ‖frameCoord b y - z₀‖ ^ 2 :=
        mul_nonneg hδpos.le (sq_nonneg _)
      have hval : u y - Φ y ≤ 2 * M - k * ‖frameNormal b y‖ ^ 2 := by
        rw [hdecomp]
        linarith [hA, htouch, hnonneg]
      have hmul : k * μ ^ 2 < k * ‖frameNormal b y‖ ^ 2 := by
        have hsq' : μ ^ 2 < ‖frameNormal b y‖ ^ 2 := by rw [hnval]; exact hsq
        exact mul_lt_mul_of_pos_left hsq' hkpos
      linarith [hval, hmul, hkbig]
  -- ## the maximum is attained in the interior
  have hint : dist y₀ (frameMap b z₀) < r := by
    by_contra hge
    have hy₀sph : y₀ ∈ sphere (frameMap b z₀) r := by
      rw [mem_sphere, dist_eq_norm]
      have h1 : dist y₀ (frameMap b z₀) ≤ r := mem_closedBall.mp hy₀K
      rw [dist_eq_norm] at h1
      exact le_antisymm h1 (not_lt.mp hge)
    have h1 : u (frameMap b z₀) - Φ (frameMap b z₀) ≤ u y₀ - Φ y₀ :=
      hy₀max (show frameMap b z₀ ∈ K from by
        rw [hK, mem_closedBall, dist_self]; exact hrpos.le)
    have h2 := hbd y₀ hy₀sph
    rw [hvalX₀] at h1
    linarith
  -- ## the viscosity inequality at `y₀`
  have hy₀s : y₀ ∈ s := hKsub hy₀K
  have hloc : ∀ᶠ y in 𝓝[s] y₀, u y - Φ y ≤ u y₀ - Φ y₀ := by
    have hδ' : 0 < r - dist y₀ (frameMap b z₀) := by linarith
    have hball : ball y₀ (r - dist y₀ (frameMap b z₀)) ⊆ K := by
      intro z hz
      rw [hK, mem_closedBall]
      rw [mem_ball] at hz
      exact le_of_lt (by
        calc dist z (frameMap b z₀) ≤ dist z y₀ + dist y₀ (frameMap b z₀) := dist_triangle _ _ _
          _ < r := by linarith)
    rw [eventually_nhdsWithin_iff]
    refine Filter.mem_of_superset (Metric.ball_mem_nhds y₀ hδ') ?_
    intro z hz _
    exact hy₀max (hball hz)
  have hv := hvis Φ hΦcd.contDiffOn y₀ hy₀s hloc
  -- ## computing `L_e Φ`
  have hsplit : ∀ i : Fin 3,
      (fderiv ℝ (fderiv ℝ Φ) y₀) (b (Fin.succ i)) (b (Fin.succ i))
      = (fderiv ℝ (fderiv ℝ (fun y : ℝ⁴ => Psi (frameCoord b y))) y₀)
          (b (Fin.succ i)) (b (Fin.succ i))
        + (fderiv ℝ (fderiv ℝ (fun y : ℝ⁴ => c₀ + k * ‖frameNormal b y‖ ^ 2)) y₀)
          (b (Fin.succ i)) (b (Fin.succ i)) := by
    intro i
    have hg : ContDiffAt ℝ 2 (fun y : ℝ⁴ => Psi (frameCoord b y)) y₀ :=
      hPsicd.contDiffAt.comp y₀ (frameCoord b).contDiff.contDiffAt
    have hh : ContDiffAt ℝ 2 (fun y : ℝ⁴ => c₀ + k * ‖frameNormal b y‖ ^ 2) y₀ := by
      refine contDiffAt_const.add ?_
      have hbase : ContDiffAt ℝ 2 (fun y : ℝ⁴ => frameNormal b y) y₀ :=
        (frameNormal b).contDiff.contDiffAt
      have h3 : ContDiffAt ℝ 2 (fun y : ℝ⁴ => k * ‖frameNormal b y‖ ^ 2) y₀ := by
        have h4 := (hbase.norm_sq (𝕜 := ℝ)).const_smul k
        simpa [smul_eq_mul] using h4
      simpa using h3
    rw [hΦ]
    exact fderiv_fderiv_add hg hh
  have hpen : (∑ i : Fin 3, (fderiv ℝ (fderiv ℝ (fun y : ℝ⁴ => c₀ + k * ‖frameNormal b y‖ ^ 2)) y₀)
      (b (Fin.succ i)) (b (Fin.succ i))) = 0 :=
    frame_laplacian_penalty b c₀ k y₀
  have hpsi : (∑ i : Fin 3, (fderiv ℝ (fderiv ℝ (fun y : ℝ⁴ => Psi (frameCoord b y))) y₀)
      (b (Fin.succ i)) (b (Fin.succ i))) = Laplacian.laplacian Psi (frameCoord b y₀) :=
    frame_laplacian_comp hPsicd b y₀
  have hsum : (∑ i : Fin 3, (fderiv ℝ (fderiv ℝ Φ) y₀) (b (Fin.succ i)) (b (Fin.succ i)))
      = Laplacian.laplacian Psi (frameCoord b y₀) := by
    rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib, hpsi, hpen]
    ring
  rw [hsum] at hv
  -- ## contradiction
  have hlt : ‖frameCoord b y₀ - z₀‖ < r :=
    (norm_frameCoord_sub_frameMap b y₀ z₀).trans_lt hint
  have hζball₁ : frameCoord b y₀ ∈ ball z₀ ρ₁ :=
    mem_ball.mpr (by rw [dist_eq_norm]; exact hlt.trans hr₁)
  have hζball₄ : frameCoord b y₀ ∈ ball z₀ ρ₄ :=
    mem_ball.mpr (by rw [dist_eq_norm]; exact hlt.trans hr₄)
  have heqL : Laplacian.laplacian Psi (frameCoord b y₀) = Laplacian.laplacian ψδ (frameCoord b y₀) := by
    have hε : 0 < ρ₄ - dist (frameCoord b y₀) z₀ := sub_pos.mpr hζball₄
    have hev : Psi =ᶠ[𝓝 (frameCoord b y₀)] ψδ := by
      refine Filter.mem_of_superset (Metric.ball_mem_nhds _ hε) ?_
      intro z hz
      refine hρ₄ z (mem_ball.mpr ?_)
      rw [mem_ball] at hz
      calc dist z z₀ ≤ dist z (frameCoord b y₀) + dist (frameCoord b y₀) z₀ := dist_triangle _ _ _
        _ < (ρ₄ - dist (frameCoord b y₀) z₀) + dist (frameCoord b y₀) z₀ := by linarith
        _ = ρ₄ := by ring
    exact (InnerProductSpace.laplacian_congr_nhds hev).eq_of_nhds
  have hlap := hψδlap (frameCoord b y₀) (hρ₁sub hζball₁)
  rw [heqL, hlap] at hv
  have hnegδ : Laplacian.laplacian ψδ (frameCoord b y₀) < 0 := hρ₁ _ hζball₁
  rw [hlap] at hnegδ
  linarith




/-- The slice of `s` through the affine plane `c + e^⊥` (in the frame `b`). -/
def sliceSetAt (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (c : ℝ⁴) (s : Set ℝ⁴) : Set ℝ³ :=
  {z : ℝ³ | c + frameMap b z ∈ s}

/-- **The slice of a viscosity subsolution of `L_e = Δ - D_ee`, at an arbitrary centre.**

This is the form of `isViscSubsolution_slice` needed for the Fubini decomposition of the
distributional inequality: the slices of `s` by the affine planes `c + e^⊥`. -/
theorem isViscSubsolution_slice_add {u : ℝ⁴ → ℝ} {s : Set ℝ⁴} (hs : IsOpen s)
    (hu : ContinuousOn u s) (b : OrthonormalBasis (Fin 4) ℝ ℝ⁴) (c : ℝ⁴)
    (hvis : ∀ φ : ℝ⁴ → ℝ, ContDiffOn ℝ 2 φ s → ∀ x ∈ s,
        (∀ᶠ y in 𝓝[s] x, u y - φ y ≤ u x - φ x) →
        0 ≤ ∑ i : Fin 3, (fderiv ℝ (fderiv ℝ φ) x)
          (b (Fin.succ i)) (b (Fin.succ i))) :
    ∀ ψ : ℝ³ → ℝ, ContDiffOn ℝ 2 ψ (sliceSetAt b c s) → ∀ z₀ ∈ sliceSetAt b c s,
      (∀ᶠ z in 𝓝[sliceSetAt b c s] z₀,
        u (c + frameMap b z) - ψ z ≤ u (c + frameMap b z₀) - ψ z₀) →
      0 ≤ Laplacian.laplacian ψ z₀ := by
  set s' : Set ℝ⁴ := {y | c + y ∈ s} with hs'def
  have hs' : IsOpen s' := hs.preimage (continuous_const.add continuous_id)
  have hu' : ContinuousOn (fun y : ℝ⁴ => u (c + y)) s' :=
    hu.comp (continuous_const.add continuous_id).continuousOn (fun y hy => hy)
  have hvis' : ∀ φ : ℝ⁴ → ℝ, ContDiffOn ℝ 2 φ s' → ∀ x ∈ s',
      (∀ᶠ y in 𝓝[s'] x, u (c + y) - φ y ≤ u (c + x) - φ x) →
      0 ≤ ∑ i : Fin 3, (fderiv ℝ (fderiv ℝ φ) x)
        (b (Fin.succ i)) (b (Fin.succ i)) := by
    intro φ hφ x hx hmax
    obtain ⟨φg, hφgcd, hφgeq⟩ :=
      Commons.Analysis.ContDiff.exists_contDiff_eqOn_nhds_of_contDiffOn_of_ne_omega 2 (by decide)
        hs' hx hφ
    set ρ : ℝ⁴ → ℝ := fun y => φg ((-c) + y) with hρ
    have hρcd : ContDiff ℝ 2 ρ := hφgcd.comp (contDiff_const.add contDiff_id)
    have hdist : ∀ y : ℝ⁴, dist ((-c) + y) x = dist y (c + x) := fun y => by
      rw [dist_eq_norm, dist_eq_norm]
      congr 1
      abel
    obtain ⟨ρ₀, hρ₀pos, hρ₀⟩ : ∃ ρ > 0, ∀ y ∈ ball x ρ, y ∈ s' →
        u (c + y) - φ y ≤ u (c + x) - φ x := by
      have h := eventually_nhdsWithin_iff.mp hmax
      rw [Filter.eventually_iff, Metric.mem_nhds_iff] at h
      exact h
    have hmaxφ : ∀ᶠ y in 𝓝[s] (c + x), u y - φ ((-c) + y) ≤ u (c + x) - φ x := by
      rw [eventually_nhdsWithin_iff, Filter.eventually_iff, Metric.mem_nhds_iff]
      refine ⟨ρ₀, hρ₀pos, ?_⟩
      intro y hy hys
      have hy' : (-c) + y ∈ ball x ρ₀ := by
        rw [mem_ball] at hy ⊢
        rwa [hdist y]
      have hys' : (-c) + y ∈ s' := by
        show c + ((-c) + y) ∈ s
        rw [show c + ((-c) + y) = y from by abel]
        exact hys
      have h := hρ₀ _ hy' hys'
      rwa [show c + ((-c) + y) = y from by abel] at h
    have hφx : φg x = φ x := hφgeq.self_of_nhds
    have hmaxρ : ∀ᶠ y in 𝓝[s] (c + x), u y - ρ y ≤ u (c + x) - ρ (c + x) := by
      obtain ⟨ρ₁, hρ₁pos, hρ₁⟩ : ∃ ρ > 0, ∀ y ∈ ball x ρ, φg y = φ y := by
        have h : ∀ᶠ y in 𝓝 x, φg y = φ y := hφgeq
        rw [Filter.eventually_iff, Metric.mem_nhds_iff] at h
        exact h
      rw [eventually_nhdsWithin_iff, Filter.eventually_iff, Metric.mem_nhds_iff]
      refine ⟨min ρ₀ ρ₁, lt_min hρ₀pos hρ₁pos, ?_⟩
      intro y hy hys
      have hy' : (-c) + y ∈ ball x (min ρ₀ ρ₁) := by
        rw [mem_ball] at hy ⊢
        rwa [hdist y]
      have hys' : (-c) + y ∈ s' := by
        show c + ((-c) + y) ∈ s
        rw [show c + ((-c) + y) = y from by abel]
        exact hys
      have hle : u (c + ((-c) + y)) - φ ((-c) + y) ≤ u (c + x) - φ x :=
        hρ₀ _ (mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hy') (min_le_left _ _))) hys'
      have heq : φg ((-c) + y) = φ ((-c) + y) :=
        hρ₁ _ (mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hy') (min_le_right _ _)))
      rw [hρ]
      show u y - φg ((-c) + y) ≤ u (c + x) - φg ((-c) + (c + x))
      rw [heq, show (-c) + (c + x) = x from by abel, hφx]
      rw [show c + ((-c) + y) = y from by abel] at hle
      exact hle
    have hres := hvis ρ hρcd.contDiffOn (c + x) hx hmaxρ
    have hder : ∀ i : Fin 3,
        (fderiv ℝ (fderiv ℝ ρ) (c + x)) (b (Fin.succ i)) (b (Fin.succ i))
          = (fderiv ℝ (fderiv ℝ φ) x) (b (Fin.succ i)) (b (Fin.succ i)) := by
      intro i
      have h1 := Commons.Analysis.Calculus.FDeriv.fderiv_fderiv_comp_add_linear
        (1 : ℝ⁴ →L[ℝ] ℝ⁴) (-c) φg hφgcd (c + x)
        (b (Fin.succ i)) (b (Fin.succ i))
      simp only [ContinuousLinearMap.one_apply] at h1
      rw [show (-c) + (c + x) = x from by abel] at h1
      have h2 : (fderiv ℝ (fderiv ℝ φg) x) (b (Fin.succ i)) (b (Fin.succ i))
          = (fderiv ℝ (fderiv ℝ φ) x) (b (Fin.succ i)) (b (Fin.succ i)) := by
        rw [hφgeq.fderiv.fderiv_eq]
      rw [← h2]
      exact h1
    rw [Finset.sum_congr rfl (fun i _ => hder i)] at hres
    exact hres
  intro ψ hψ z₀ hz₀ hmax
  exact isViscSubsolution_slice hs' hu' b hvis' ψ hψ z₀ hz₀ hmax


end Submission