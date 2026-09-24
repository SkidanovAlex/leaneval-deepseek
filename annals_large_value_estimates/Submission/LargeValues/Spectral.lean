import Submission.LargeValues.KeyProp
import Submission.Commons.LinearAlgebra.Matrix.spectral_large_values_bound_fintype
import Submission.Commons.LinearAlgebra.InnerProductSpace.singularValues_top_sq_le_trace

open LargeValueEstimates
open Asymptotics Complex
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The matrix `M_W` of Guth–Maynard §4

`MWmat N W` is the matrix with rows indexed by `t ∈ W` and columns by `n = N + j`
(`j : Fin (N+1)`), with entries `w(n/N)·n^{it}`.  We prove that `smoothedPoly N b t` is the
`t`-coordinate of `M_W b` and that `∑_{t∈W} ‖smoothedPoly N b t‖² = ‖M_W b‖²`, so that the
operator-norm bound (`singularValues_zero_mul_norm_le`) gives Guth–Maynard Lemma 4.2.
-/

namespace Submission.LargeValues

/-- Guth–Maynard's matrix `M_W` (§4): rows `t ∈ W`, columns `n = N + j`, `j : Fin (N+1)`. -/
noncomputable def MWmat (N : ℕ) (W : Finset ℝ) : Matrix W (Fin (N + 1)) ℂ :=
  fun t j => ((bumpW (((N + (j : ℕ)) : ℝ) / (N : ℝ))) : ℂ)
    * (((N + (j : ℕ)) : ℂ) ^ (I * ((t : ℝ) : ℂ)))

/-- Reindexing `∑_{n=N}^{2N} = ∑_{j : Fin (N+1)}` of `n = N + j`. -/
theorem sum_Icc_eq_sum_fin {M : Type*} [AddCommMonoid M] (N : ℕ) (f : ℕ → M) :
    ∑ n ∈ Finset.Icc N (2 * N), f n = ∑ j : Fin (N + 1), f (N + (j : ℕ)) := by
  rw [Fin.sum_univ_eq_sum_range (fun j => f (N + j)) (N + 1)]
  rw [show Finset.Icc N (2 * N) = Finset.Ico N (2 * N + 1) by
    ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega]
  rw [Finset.sum_Ico_eq_sum_range]
  have h : 2 * N + 1 - N = N + 1 := by omega
  rw [h]

/-- The `t`-coordinate of `M_W` applied to the coefficient vector is the matrix-vector product. -/
theorem euclideanLin_apply (N : ℕ) (W : Finset ℝ) (b : ℕ → ℂ) (t : W) :
    (Matrix.toEuclideanLin (MWmat N W)
        (WithLp.toLp 2 (fun j : Fin (N + 1) => b (N + (j : ℕ))))) t
      = ∑ j : Fin (N + 1), MWmat N W t j * b (N + (j : ℕ)) := by
  rw [← WithLp.toLp_ofLp (p := 2)
    (x := (Matrix.toEuclideanLin (MWmat N W)
      (WithLp.toLp 2 (fun j : Fin (N + 1) => b (N + (j : ℕ))))))]
  rw [Matrix.ofLp_toLpLin]
  rfl

/-- `smoothedPoly N b t` is the `t`-coordinate of `M_W b`. -/
theorem smoothedPoly_eq_mulVec (N : ℕ) (W : Finset ℝ) (b : ℕ → ℂ) (t : W) :
    smoothedPoly N b (t : ℝ)
      = (Matrix.toEuclideanLin (MWmat N W)
          (WithLp.toLp 2 (fun j : Fin (N+1) => b (N + (j:ℕ))))) t := by
  rw [euclideanLin_apply]
  rw [smoothedPoly, sum_Icc_eq_sum_fin]
  apply Finset.sum_congr rfl
  intro j _
  simp only [MWmat]
  push_cast
  ring

/-- `∑_{t∈W} ‖smoothedPoly N b t‖² = ‖M_W b‖²` where `b` is the vector of coefficients. -/
theorem sum_normSq_eq_norm_sq (N : ℕ) (W : Finset ℝ) (b : ℕ → ℂ) :
    ∑ t ∈ W, ‖smoothedPoly N b t‖ ^ 2
      = ‖(Matrix.toEuclideanLin (MWmat N W)
          (WithLp.toLp 2 (fun j : Fin (N + 1) => b (N + (j : ℕ)))))‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  rw [← Finset.sum_attach W (fun t => ‖smoothedPoly N b t‖ ^ 2)]
  apply Finset.sum_congr rfl
  intro t _
  rw [smoothedPoly_eq_mulVec N W b t]

/-- **Guth–Maynard Lemma 4.2.** If `|smoothedPoly N b t| ≥ V` on `W`, then
`|W|·V² ≤ (N+1)·s₁(M_W)²`. -/
theorem card_mul_sq_le_singular (N : ℕ) (hN : 1 ≤ N) (W : Finset ℝ) (b : ℕ → ℂ) (V : ℝ)
    (hV : 0 < V) (hb : ∀ n, ‖b n‖ ≤ 1) (hval : ∀ t ∈ W, V ≤ ‖smoothedPoly N b t‖) :
    (W.card : ℝ) * V ^ 2
      ≤ ((Matrix.toEuclideanLin (MWmat N W)).singularValues 0) ^ 2 * ((N : ℝ) + 1) := by
  classical
  have h := Commons.LinearAlgebra.Matrix.spectral_large_values_bound_fintype (MWmat N W)
    (WithLp.toLp 2 (fun j : Fin (N + 1) => b (N + (j : ℕ)))) V hV
    (fun j => by
      show ‖(WithLp.toLp 2 (fun j : Fin (N + 1) => b (N + (j : ℕ)))) j‖ ≤ 1
      rw [WithLp.ofLp_toLp]
      exact hb _)
    (fun t => by
      have h1 : (∑ j : Fin (N + 1), MWmat N W t j *
            (WithLp.toLp 2 (fun j : Fin (N + 1) => b (N + (j : ℕ)))) j)
          = (Matrix.toEuclideanLin (MWmat N W)
              (WithLp.toLp 2 (fun j : Fin (N + 1) => b (N + (j : ℕ))))) t := by
        rw [euclideanLin_apply]
      rw [h1, ← smoothedPoly_eq_mulVec N W b t]
      exact hval t t.2)
  have h1 : (Fintype.card W : ℝ) = (W.card : ℝ) := by rw [Fintype.card_coe]
  have h2 : (Fintype.card (Fin (N + 1)) : ℝ) = (N : ℝ) + 1 := by
    rw [Fintype.card_fin]; push_cast; ring
  rw [h1, h2] at h
  exact h

/-- **Guth–Maynard §4, second half.**  Combining Lemma 4.2 with the singular-value/trace bound
(Lemma 4.4), the number of large values is controlled by the two trace expressions
`Σ σᵢ⁶ − (Σ σᵢ²)³/|W|²` and `Σ σᵢ²/|W|`. -/
theorem card_mul_sq_le_trace_terms (N : ℕ) (hN : 1 ≤ N) (W : Finset ℝ) (b : ℕ → ℂ) (V : ℝ)
    (hV : 0 < V) (hb : ∀ n, ‖b n‖ ≤ 1) (hval : ∀ t ∈ W, V ≤ ‖smoothedPoly N b t‖)
    (hW : 0 < W.card) :
    (W.card : ℝ) * V ^ 2 ≤ ((N : ℝ) + 1) *
      (8 * (∑ i : Fin (N + 1),
              (Matrix.toEuclideanLin (MWmat N W)).singularValues i ^ 6
            - (∑ i : Fin (N + 1),
                (Matrix.toEuclideanLin (MWmat N W)).singularValues i ^ 2) ^ 3
              / (W.card : ℝ) ^ 2) ^ (1 / 3 : ℝ)
        + 8 * ((∑ i : Fin (N + 1),
              (Matrix.toEuclideanLin (MWmat N W)).singularValues i ^ 2) / (W.card : ℝ))) := by
  classical
  set T := Matrix.toEuclideanLin (MWmat N W) with hT
  have hfE : Module.finrank ℂ (EuclideanSpace ℂ (Fin (N + 1))) = N + 1 := by
    rw [finrank_euclideanSpace]
    simp
  have hfF : Module.finrank ℂ (EuclideanSpace ℂ ↥W) = W.card := by
    rw [finrank_euclideanSpace, Fintype.card_coe]
  have htrace := Commons.LinearAlgebra.InnerProductSpace.singularValues_top_sq_le_trace T
    (m := W.card) hfF hW
  rw [hfE] at htrace
  have h1 := card_mul_sq_le_singular N hN W b V hV hb hval
  have hσ0 : 0 ≤ T.singularValues 0 ^ 2 := sq_nonneg _
  have hpos : 0 ≤ ((N : ℝ) + 1) := by positivity
  have hkey : ((N : ℝ) + 1) * T.singularValues 0 ^ 2
      ≤ ((N : ℝ) + 1) *
        (8 * (∑ i : Fin (N + 1), T.singularValues i ^ 6
              - (∑ i : Fin (N + 1), T.singularValues i ^ 2) ^ 3 / (W.card : ℝ) ^ 2)
            ^ (1 / 3 : ℝ)
          + 8 * ((∑ i : Fin (N + 1), T.singularValues i ^ 2) / (W.card : ℝ))) :=
    mul_le_mul_of_nonneg_left htrace hpos
  calc (W.card : ℝ) * V ^ 2
      ≤ ((N : ℝ) + 1) * T.singularValues 0 ^ 2 := by
        rw [← hT] at h1
        linarith [h1, mul_comm ((N : ℝ) + 1) (T.singularValues 0 ^ 2)]
    _ ≤ _ := hkey

end Submission.LargeValues
