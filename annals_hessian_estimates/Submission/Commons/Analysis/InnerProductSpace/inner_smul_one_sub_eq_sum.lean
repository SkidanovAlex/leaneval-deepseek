import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Commons.Analysis.InnerProductSpace

open scoped RealInnerProductSpace in
open scoped BigOperators in
theorem inner_smul_one_sub_eq_sum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι] {T : E →L[ℝ] E} (v : OrthonormalBasis ι ℝ E) (lam : ι → ℝ)
    (hdiag : ∀ i : ι, T (v i) = lam i • v i) (S : ℝ) (x : E) :
    ⟪(S • (1 : E →L[ℝ] E) - T) x, x⟫ = ∑ i : ι, (S - lam i) * (⟪v i, x⟫) ^ 2 := by
  classical
  let c : ι → ℝ := fun i => ⟪v i, x⟫
  -- The coordinates of `x` in the orthonormal basis `v`.
  have hc_repr : c = fun i => (v.repr x).ofLp i := by
    funext i
    simp only [c, OrthonormalBasis.repr_apply_apply]
  have hx : (∑ i, c i • v i : E) = x := by
    rw [hc_repr]
    exact v.sum_repr x
  -- `(S • 1 - T) x` in the basis.
  have hcalc : (S • (1 : E →L[ℝ] E) - T) x = ∑ i, ((S - lam i) * c i) • v i := by
    rw [sub_apply, smul_apply, one_apply_eq_self]
    rw [← hx, map_sum]
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [ContinuousLinearMap.map_smul, hdiag, smul_smul, smul_smul, ← sub_smul]
    congr 1
    ring
  have hmain : ⟪(S • (1 : E →L[ℝ] E) - T) x, x⟫ = ∑ i, (S - lam i) * (c i) ^ 2 := by
    rw [hcalc, ← hx]
    rw [Orthonormal.inner_sum v.orthonormal (fun i => (S - lam i) * c i) c Finset.univ]
    apply Finset.sum_congr rfl
    intro i _
    rw [starRingEnd_apply, star_trivial]
    ring
  simpa [c] using hmain

end Commons.Analysis.InnerProductSpace