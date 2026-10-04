import Mathlib
import Submission.Work.Diff.EXT.OrderedFinpartition_ne_atomic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `n`-th slice jet of a smooth function on `Ico 0 T ×ˢ U`

We prove that, for a function `φ : ℝ × E → Z` which is smooth on the product
`(Ico 0 T) ×ˢ U` (with `U` open), the `n`-th iterated Fréchet derivative of `φ` at `(0, y)`
evaluated on the constant direction `(1, 0)` coincides with the `n`-th iterated derivative of
the slice `t ↦ φ (t, y)` within `Ico 0 T` at `0`.

The proof is the one-dimensional Faà di Bruno formula
(`iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition`) applied to `g = φ` and to the affine
curve `γ t = (t, y)`.  Since `γ` is affine, all its iterated derivatives of order `≥ 2` vanish
and its first derivative is `(1, 0)`; hence, by multilinearity, every term of the Faà di Bruno
sum indexed by a partition having a block of size `≥ 2` vanishes, and the only surviving term is
the one of the atomic partition `OrderedFinpartition.atomic n` (all blocks of size `1`).
-/

open Set Filter
open scoped ContDiff

namespace Work.Diff.EXT

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The first derivative of the affine curve `t ↦ (t, y)` within `Ico 0 T` at `0` is `(1, 0)`. -/
lemma iteratedDerivWithin_sliceCurve_one {T : ℝ} (hT : 0 < T) (y : E) :
    iteratedDerivWithin 1 (fun t : ℝ => (t, y)) (Set.Ico 0 T) 0 = ((1 : ℝ), (0 : E)) := by
  have hx : (0 : ℝ) ∈ Set.Ico 0 T := Set.left_mem_Ico.mpr hT
  have hs : UniqueDiffOn ℝ (Set.Ico 0 T) := uniqueDiffOn_Ico 0 T
  have h := iteratedFDerivWithin_prodMk (𝕜 := ℝ) (s := Set.Ico 0 T) (x := 0)
    (f := id) (g := fun _ : ℝ => y) (n := (⊤ : WithTop ℕ∞))
    contDiffWithinAt_id contDiffWithinAt_const hs hx (i := 1) le_top
  simp only [iteratedDerivWithin]
  rw [show (fun t' : ℝ => (t', y)) = (fun x : ℝ => (id x, (fun _ : ℝ => y) x)) from rfl]
  rw [h, ContinuousMultilinearMap.prod_apply]
  rw [← iteratedDerivWithin_eq_iteratedFDerivWithin, ← iteratedDerivWithin_eq_iteratedFDerivWithin]
  rw [iteratedDerivWithin_id hx hs, iteratedDerivWithin_const]
  norm_num

/-- All iterated derivatives of order `≥ 2` of the affine curve `t ↦ (t, y)` within
`Ico 0 T` at `0` vanish. -/
lemma iteratedDerivWithin_sliceCurve_eq_zero {T : ℝ} (hT : 0 < T) (y : E) {k : ℕ}
    (hk : 2 ≤ k) :
    iteratedDerivWithin k (fun t : ℝ => (t, y)) (Set.Ico 0 T) 0 = 0 := by
  have hx : (0 : ℝ) ∈ Set.Ico 0 T := Set.left_mem_Ico.mpr hT
  have hs : UniqueDiffOn ℝ (Set.Ico 0 T) := uniqueDiffOn_Ico 0 T
  have h := iteratedFDerivWithin_prodMk (𝕜 := ℝ) (s := Set.Ico 0 T) (x := 0)
    (f := id) (g := fun _ : ℝ => y) (n := (⊤ : WithTop ℕ∞))
    contDiffWithinAt_id contDiffWithinAt_const hs hx (i := k) le_top
  simp only [iteratedDerivWithin]
  rw [show (fun t' : ℝ => (t', y)) = (fun x : ℝ => (id x, (fun _ : ℝ => y) x)) from rfl]
  rw [h, ContinuousMultilinearMap.prod_apply]
  rw [← iteratedDerivWithin_eq_iteratedFDerivWithin, ← iteratedDerivWithin_eq_iteratedFDerivWithin]
  rw [iteratedDerivWithin_id hx hs, iteratedDerivWithin_const]
  simp only [show k ≠ 0 by omega, show k ≠ 1 by omega, ite_false]
  rfl

theorem sliceJet_iteratedDerivWithin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {T : ℝ} (hT : 0 < T) {U : Set E} (hU : IsOpen U) (φ : ℝ × E → Z)
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ ((Set.Ico 0 T) ×ˢ U)) (n : ℕ) {y : E} (hy : y ∈ U) :
    iteratedFDerivWithin ℝ n φ ((Set.Ico 0 T) ×ˢ U) ((0 : ℝ), y) (fun _ => ((1 : ℝ), (0 : E)))
      = iteratedDerivWithin n (fun t : ℝ => φ (t, y)) (Set.Ico 0 T) 0 := by
  have hx : (0 : ℝ) ∈ Set.Ico 0 T := Set.left_mem_Ico.mpr hT
  have hs : UniqueDiffOn ℝ (Set.Ico 0 T) := uniqueDiffOn_Ico 0 T
  have ht : UniqueDiffOn ℝ (Set.Ico 0 T ×ˢ U) := hs.prod hU.uniqueDiffOn
  have hγ0 : ((0 : ℝ), y) ∈ Set.Ico 0 T ×ˢ U := ⟨hx, hy⟩
  -- Smoothness of the two ingredients of Faà di Bruno's formula.
  have hφ' : ContDiffWithinAt ℝ (n : WithTop ℕ∞) φ (Set.Ico 0 T ×ˢ U) ((0 : ℝ), y) :=
    (hφ.of_le (WithTop.coe_le_coe.mpr le_top)) _ hγ0
  have hγ' : ContDiffWithinAt ℝ (n : WithTop ℕ∞) (fun t' : ℝ => (t', y)) (Set.Ico 0 T) 0 := by
    simpa using contDiffWithinAt_id.prodMk (contDiffWithinAt_const (c := y) :
      ContDiffWithinAt ℝ (n : WithTop ℕ∞) (fun _ : ℝ => y) (Set.Ico 0 T) 0)
  have hst : Set.MapsTo (fun t' : ℝ => (t', y)) (Set.Ico 0 T) (Set.Ico 0 T ×ˢ U) :=
    fun x hxx => ⟨hxx, hy⟩
  -- Faà di Bruno for the composition `φ ∘ (fun t => (t, y))`.
  have hFB := iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition (𝕜 := ℝ) (g := φ)
    (f := fun t' : ℝ => (t', y)) (s := Set.Ico 0 T) (t := Set.Ico 0 T ×ˢ U) (x := 0)
    (n := (n : WithTop ℕ∞)) (i := n) hφ' hγ' ht hs hx hst le_rfl
  -- The derivative facts for the affine curve.
  have hw1 : iteratedDerivWithin 1 (fun t' : ℝ => (t', y)) (Set.Ico 0 T) 0 = ((1 : ℝ), (0 : E)) :=
    iteratedDerivWithin_sliceCurve_one hT y
  have hw2 : ∀ k, 2 ≤ k → iteratedDerivWithin k (fun t' : ℝ => (t', y)) (Set.Ico 0 T) 0 = 0 :=
    fun k hk => iteratedDerivWithin_sliceCurve_eq_zero hT y hk
  -- Collapse of the Faà di Bruno sum: only the atomic partition survives.
  have hsum : (∑ c : OrderedFinpartition n,
        (iteratedFDerivWithin ℝ c.length φ ((Set.Ico 0 T) ×ˢ U) ((0 : ℝ), y))
          (fun j => iteratedDerivWithin (c.partSize j) (fun t' : ℝ => (t', y)) (Set.Ico 0 T) 0))
      = (iteratedFDerivWithin ℝ n φ ((Set.Ico 0 T) ×ˢ U) ((0 : ℝ), y))
          (fun _ => ((1 : ℝ), (0 : E))) := by
    rw [Fintype.sum_eq_single (OrderedFinpartition.atomic n)]
    · simp only [OrderedFinpartition.atomic_partSize, hw1]
      rfl
    · intro c hc
      obtain ⟨j, hj⟩ := OrderedFinpartition_ne_atomic c hc
      exact ContinuousMultilinearMap.map_coord_zero _ j (hw2 (c.partSize j) hj)
  rw [← hsum, ← hFB]
  rfl

end Work.Diff.EXT
