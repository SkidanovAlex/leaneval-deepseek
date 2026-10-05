import Mathlib

/-!
# The iterated derivative of a composition depends only on the jets

We show that `iteratedDeriv k (F ∘ u) 0` only depends on the derivatives of `u` at `0` up to
order `k` and on the derivatives of `F` at `u 0`.

The key ingredient is the Faà di Bruno formula in Mathlib, packaged as
`iteratedFDeriv_comp`: the `i`-th Fréchet derivative of `g ∘ f` is the `i`-th Taylor composition
`(ftaylorSeries 𝕜 g (f x)).taylorComp (ftaylorSeries 𝕜 f x) i` of the two Taylor series. In the
one-dimensional case, evaluating this composition at the constant vector `(1, …, 1)` produces a
sum over ordered set partitions whose summands involve only the diagonal values
`(ftaylorSeries 𝕜 f x) j (fun _ => 1)`, which are exactly `iteratedDeriv j f x`.
-/

namespace Work.RPB.B5

/-- Evaluating the Faà di Bruno Taylor composition of two formal multilinear series at the
constant vector `(1, ..., 1)` gives a sum over ordered set partitions in which each `B` only
appears evaluated at the constant vector `(1, ..., 1)`. -/
private lemma taylorComp_apply_const_one {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (A : FormalMultilinearSeries ℝ X Y) (B : FormalMultilinearSeries ℝ ℝ X) (k : ℕ) :
    (A.taylorComp B k) (fun _ => (1 : ℝ)) =
      ∑ c : OrderedFinpartition k,
        A c.length (fun m => B (c.partSize m) (fun _ => (1 : ℝ))) := by
  simp only [FormalMultilinearSeries.taylorComp, sum_apply,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply, Function.comp_def]

/-- The evaluation at the constant vector `(1, ..., 1)` of the Faà di Bruno Taylor composition of
`A` and `B` depends on `B` only through the values `B j (fun _ => 1)` for `j ≤ k`. -/
private lemma taylorComp_apply_const_one_congr {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {A : FormalMultilinearSeries ℝ X Y} {B B' : FormalMultilinearSeries ℝ ℝ X} {k : ℕ}
    (hB : ∀ j ≤ k, B j (fun _ => (1 : ℝ)) = B' j (fun _ => (1 : ℝ))) :
    (A.taylorComp B k) (fun _ => (1 : ℝ)) = (A.taylorComp B' k) (fun _ => (1 : ℝ)) := by
  rw [taylorComp_apply_const_one, taylorComp_apply_const_one]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  congr 1
  ext m
  exact hB (c.partSize m) (c.partSize_le m)

theorem iteratedDeriv_comp_congr {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] {F : X → Y} {n : ℕ} (hF : ContDiff ℝ n F) {u u' : ℝ → X} (hu : ContDiffAt ℝ n u 0) (hu' : ContDiffAt ℝ n u' 0) (h : ∀ k ≤ n, iteratedDeriv k u 0 = iteratedDeriv k u' 0) {k : ℕ} (hk : k ≤ n) : iteratedDeriv k (fun σ => F (u σ)) 0 = iteratedDeriv k (fun σ => F (u' σ)) 0 := by
  -- `u` and `u'` agree at `0`, since `iteratedDeriv 0 = id`
  have h0 : u 0 = u' 0 := by
    have := h 0 (Nat.zero_le n)
    simpa using this
  -- both iterated derivatives are the `k`-th Taylor composition of `F` and of the curve,
  -- evaluated at the constant vector `(1, ..., 1)`
  have key : ∀ (v : ℝ → X), ContDiffAt ℝ n v 0 →
      iteratedDeriv k (fun σ => F (v σ)) 0 =
        ((ftaylorSeries ℝ F (v 0)).taylorComp (ftaylorSeries ℝ v 0) k)
          (fun _ => (1 : ℝ)) := by
    intro v hv
    rw [iteratedDeriv_eq_iteratedFDeriv]
    exact congrArg (fun m => m (fun _ => (1 : ℝ)))
      (iteratedFDeriv_comp (𝕜 := ℝ) (g := F) (f := v) (x := 0) hF.contDiffAt hv
        (by exact_mod_cast hk))
  rw [key u hu, key u' hu', h0]
  -- the Faà di Bruno sum only sees `iteratedDeriv j u 0` for `j ≤ k`, which are given by `h`
  exact taylorComp_apply_const_one_congr (A := ftaylorSeries ℝ F (u' 0)) fun j hj => by
    rw [show (ftaylorSeries ℝ u 0) j (fun _ => (1 : ℝ)) = iteratedDeriv j u 0 from rfl,
      show (ftaylorSeries ℝ u' 0) j (fun _ => (1 : ℝ)) = iteratedDeriv j u' 0 from rfl]
    exact h j (le_trans hj hk)

end Work.RPB.B5
