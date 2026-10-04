import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `n`-th derivative of a function into a finite product is bounded by the sum of the
`n`-th derivatives of its components

For `f : E → (ι → J)` with `ι` finite and `f` smooth at `x` (in fact `C^⊤`, i.e. analytic),
the operator norm of `iteratedFDeriv ℝ n f x` is at most the sum of the operator norms of the
iterated derivatives of the components `fun y => f y i`.

The proof has two ingredients:

* `ContinuousLinearMap.iteratedFDeriv_comp_left` identifies the iterated derivative of the `i`-th
  component with the composition of `ContinuousLinearMap.proj i` with `iteratedFDeriv ℝ n f x`;
* for a continuous multilinear map `g` with values in a finite product, the operator norm is
  bounded by the sum of the operator norms of its "components"
  `(ContinuousLinearMap.proj i).compContinuousMultilinearMap g` (each `g v` is the tuple of its
  components, and the sup norm of a tuple is at most the sum of the norms of its entries).
-/

namespace Work.Diff.EXT

lemma norm_iteratedFDeriv_pi_le_sum
    {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {J : Type*} [NormedAddCommGroup J] [NormedSpace ℝ J]
    (f : E → (ι → J)) (x : E) (n : ℕ) (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x) :
    ‖iteratedFDeriv ℝ n f x‖ ≤ ∑ i, ‖iteratedFDeriv ℝ n (fun y => f y i) x‖ := by
  set g : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) (ι → J) := iteratedFDeriv ℝ n f x
  -- Identify the components of the iterated derivative of `f` with the iterated derivatives of
  -- the components of `f`.
  have hcomp : ∀ i : ι, iteratedFDeriv ℝ n (fun y => f y i) x =
      (ContinuousLinearMap.proj (R := ℝ) i).compContinuousMultilinearMap g := by
    intro i
    have h := (ContinuousLinearMap.proj (R := ℝ) i :
        (ι → J) →L[ℝ] J).iteratedFDeriv_comp_left (n := (⊤ : ℕ∞)) hf (i := n)
      (by exact_mod_cast le_top)
    simpa [Function.comp_def, ContinuousLinearMap.proj_apply, g] using h
  have hsum : (∑ i, ‖iteratedFDeriv ℝ n (fun y => f y i) x‖)
      = ∑ i, ‖(ContinuousLinearMap.proj (R := ℝ) i).compContinuousMultilinearMap g‖ := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hcomp i]
  rw [hsum]
  refine ContinuousMultilinearMap.opNorm_le_bound (f := g)
    (Finset.sum_nonneg (fun i _ => norm_nonneg _)) (fun v => ?_)
  -- `g v` is the tuple of its components.
  have hgv : g v
      = fun i => ((ContinuousLinearMap.proj (R := ℝ) i).compContinuousMultilinearMap g) v := by
    ext i
    simp [ContinuousLinearMap.compContinuousMultilinearMap_coe, ContinuousLinearMap.proj_apply]
  have h1 : ‖g v‖
      ≤ ∑ i, ‖((ContinuousLinearMap.proj (R := ℝ) i).compContinuousMultilinearMap g) v‖ := by
    rw [hgv]
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun i _ => norm_nonneg _))).2
      (fun i => ?_)
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun i => ‖((ContinuousLinearMap.proj (R := ℝ) i).compContinuousMultilinearMap g) v‖)
      (fun j _ => norm_nonneg _) (Finset.mem_univ i)
  have h2 : (∑ i, ‖((ContinuousLinearMap.proj (R := ℝ) i).compContinuousMultilinearMap g) v‖)
      ≤ (∑ i, ‖(ContinuousLinearMap.proj (R := ℝ) i).compContinuousMultilinearMap g‖)
        * ∏ j, ‖v j‖ := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum (fun i _ => ?_)
    exact ContinuousMultilinearMap.le_opNorm
      ((ContinuousLinearMap.proj (R := ℝ) i).compContinuousMultilinearMap g) v
  exact h1.trans h2

end Work.Diff.EXT
