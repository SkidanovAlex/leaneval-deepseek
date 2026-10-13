/-
  WilG4c/PuncturedAux/Basic — elementary lemmas about finite-dimensional spaces of the form
  `Fin N → ℝ` and continuous linear maps out of them, used by the punctured-continuation
  criterion `Work.WilG4c.PuncturedCriterion`.

  The ingredients are:

  * `sum_single_smul`: the standard basis expansion of a vector of `ℝ^N`;
  * `NormSubLeSumSingle`: the operator norm of a difference of continuous linear maps out of
    `Fin N → ℝ` is bounded by the sum of the norms of its values on the standard basis
    (both spaces being finite dimensional, the coordinate functionals detect the norm);
  * `SumSmulRightSingle`: the linear map `∑ i, proj i · (S i)` takes the value `S j` at the
    `j`-th standard basis vector, so it is *the* continuous linear map with prescribed values
    on the basis;
  * `TendstoClmOfCoord`: consequently, a family of continuous linear maps on `Fin N → ℝ`
    converges as soon as its values on the standard basis vectors converge, and the limit is
    the map built from the limits.
-/
import Mathlib

set_option autoImplicit false
noncomputable section

open scoped Topology
open Filter

namespace Work.WilG4c.PuncturedAux

/-- The standard basis expansion of a vector of `ℝ^N`. -/
lemma sum_single_smul {N : ℕ} (x : Fin N → ℝ) :
    (∑ i, x i • (Pi.single i (1 : ℝ) : Fin N → ℝ)) = x := by
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- The operator norm of the difference of two continuous linear maps out of `Fin N → ℝ` is
bounded by the sum of the norms of their differences on the standard basis vectors. -/
lemma NormSubLeSumSingle {N : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (Λ Ψ : (Fin N → ℝ) →L[ℝ] G) :
    ‖Λ - Ψ‖ ≤ ∑ i, ‖(Λ - Ψ) (Pi.single i 1)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun i _ => norm_nonneg _)
    fun x => ?_
  have hx : (Λ - Ψ) x = ∑ i, x i • (Λ - Ψ) (Pi.single i 1) := by
    conv_lhs => rw [← sum_single_smul x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
  calc ‖(Λ - Ψ) x‖
      = ‖∑ i, x i • (Λ - Ψ) (Pi.single i 1)‖ := by rw [hx]
    _ ≤ ∑ i, ‖x i • (Λ - Ψ) (Pi.single i 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖x‖ * ‖(Λ - Ψ) (Pi.single i 1)‖ :=
        Finset.sum_le_sum fun i _ =>
          le_trans (by rw [norm_smul]) (mul_le_mul_of_nonneg_right (norm_le_pi_norm x i)
            (norm_nonneg _))
    _ = (∑ i, ‖(Λ - Ψ) (Pi.single i 1)‖) * ‖x‖ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The continuous linear map `∑ i, (proj i).smulRight (S i)` takes the value `S j` at the
`j`-th standard basis vector. -/
lemma SumSmulRightSingle {N : ℕ} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (S : Fin N → G) (j : Fin N) :
    (∑ i, (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ).smulRight (S i))
        (Pi.single j 1) = S j := by
  rw [sum_apply]
  simpa using Fintype.sum_single_smul (f := S) (r := (1 : ℝ)) j

/-- Coordinatewise convergence of a family of continuous linear maps on `Fin N → ℝ`: the limit
is the continuous linear map with the coordinate limits as values on the standard basis. -/
lemma TendstoClmOfCoord {N : ℕ} (hN : 1 ≤ N) {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {Λ : (Fin N → ℝ) → ((Fin N → ℝ) →L[ℝ] G)} {S : Fin N → G}
    {c : Fin N → ℝ}
    (h : ∀ j : Fin N, Tendsto (fun x => Λ x (Pi.single j 1)) (𝓝[≠] c) (𝓝 (S j))) :
    Tendsto Λ (𝓝[≠] c)
      (𝓝 (∑ j, (ContinuousLinearMap.proj j : (Fin N → ℝ) →L[ℝ] ℝ).smulRight (S j))) := by
  have hterm : ∀ j : Fin N, Tendsto
      (fun x => ‖(Λ x - (∑ i, (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ).smulRight
        (S i))) (Pi.single j 1)‖) (𝓝[≠] c) (𝓝 0) := by
    intro j
    have h2 : Tendsto (fun x => Λ x (Pi.single j 1) - S j) (𝓝[≠] c) (𝓝 0) := by
      simpa using (h j).sub_const (S j)
    have h3 : Tendsto (fun x => ‖Λ x (Pi.single j 1) - S j‖) (𝓝[≠] c) (𝓝 0) := by
      simpa using h2.norm
    refine h3.congr' ?_
    filter_upwards with x
    simp only [sub_apply, SumSmulRightSingle S j]
  have hsum : Tendsto (fun x => ∑ j, ‖(Λ x - (∑ i,
      (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ).smulRight (S i))) (Pi.single j 1)‖)
      (𝓝[≠] c) (𝓝 0) := by
    have := tendsto_finsetSum Finset.univ (fun j (_ : j ∈ Finset.univ) => hterm j)
    simpa using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _)
    (Eventually.of_forall fun x => NormSubLeSumSingle _ _) hsum

end Work.WilG4c.PuncturedAux
