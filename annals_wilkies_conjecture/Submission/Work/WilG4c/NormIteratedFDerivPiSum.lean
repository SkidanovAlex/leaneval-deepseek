import Mathlib

open scoped BigOperators

namespace Work.WilG4c

/-- For a finite family of elements of seminormed additive groups, the sup-norm of the family is
bounded by the sum of the norms of its members. -/
private lemma norm_pi_le_sum {ι : Type*} [Fintype ι] {G : ι → Type*}
    [∀ i, SeminormedAddGroup (G i)] (x : (i : ι) → G i) :
    ‖x‖ ≤ ∑ i, ‖x i‖ := by
  rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun i _ => norm_nonneg _))]
  intro i
  exact Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ i)

theorem NormIteratedFDerivPiSum {μ n m : ℕ} (f : (Fin μ → ℝ) → (Fin n → ℝ)) (x : Fin μ → ℝ)
    (hf : ContDiffAt ℝ m f x) :
    ‖iteratedFDeriv ℝ m f x‖ ≤
      ∑ i : Fin n, ‖iteratedFDeriv ℝ m (fun t : Fin μ → ℝ => f t i) x‖ := by
  -- The `m`-th derivative of `f` as a continuous multilinear map `A`, and its coordinate
  -- projections `B i = proj i ∘ A`.
  set A : ContinuousMultilinearMap ℝ (fun _ : Fin m => (Fin μ → ℝ)) (Fin n → ℝ) :=
    iteratedFDeriv ℝ m f x with hA
  set B : (i : Fin n) → ContinuousMultilinearMap ℝ (fun _ : Fin m => (Fin μ → ℝ)) ℝ :=
    fun i => (ContinuousLinearMap.proj i).compContinuousMultilinearMap A with hB
  -- The family of projections reassembles `A`.
  have hpi : ContinuousMultilinearMap.pi B = A := by
    ext v j
    simp only [hB, ContinuousMultilinearMap.pi_apply,
      ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
      ContinuousLinearMap.proj_apply]
  -- Each projection of `A` is the iterated derivative of the corresponding coordinate function.
  have hcomp : ∀ i : Fin n, B i =
      iteratedFDeriv ℝ m (fun t : Fin μ → ℝ => f t i) x := by
    intro i
    simp only [hB]
    rw [← ContinuousLinearMap.iteratedFDeriv_comp_left (ContinuousLinearMap.proj i) hf
      (i := m) (le_refl _)]
    congr 1
  calc ‖iteratedFDeriv ℝ m f x‖
      = ‖ContinuousMultilinearMap.pi B‖ := by rw [hpi, hA]
    _ = ‖B‖ := ContinuousMultilinearMap.opNorm_pi B
    _ ≤ ∑ i : Fin n, ‖B i‖ := norm_pi_le_sum B
    _ = ∑ i : Fin n, ‖iteratedFDeriv ℝ m (fun t : Fin μ → ℝ => f t i) x‖ :=
        Finset.sum_congr rfl (fun i _ => by rw [hcomp i])

end Work.WilG4c
