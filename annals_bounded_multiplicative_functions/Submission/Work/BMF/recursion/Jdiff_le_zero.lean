import Mathlib
import Submission.Work.BMF.recursion.Defs
import Submission.Work.BMF.recursion.card_sub_eq_sum_fiber

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators

namespace Work.BMF.recursion

/-- Auxiliary combinatorial core of `Jdiff_le_zero`: for a map `f : S → V` into an additive
commutative group, the sum of squares of the fibre counts `#{x | f x = v}` evaluated at the
*translated* values `v + d` is at most the sum of squares of the fibre counts themselves.  Indeed
reindexing along the injection `v ↦ v + d` turns the left-hand side into a sum of the same
non-negative terms over the set `(image f) + d`, and the fibre count vanishes off `image f`. -/
private lemma fiber_card_shift_sq_le {S V : Type*} [Fintype S] [AddCommGroup V] [DecidableEq V]
    (f : S → V) (d : V) :
    (∑ v ∈ (Finset.univ : Finset S).image f,
        ((Finset.univ : Finset S).filter (fun y => f y = v + d)).card ^ 2)
      ≤ ∑ v ∈ (Finset.univ : Finset S).image f,
        ((Finset.univ : Finset S).filter (fun x => f x = v)).card ^ 2 := by
  classical
  set W : Finset V := (Finset.univ : Finset S).image f with hW
  set a : V → ℕ := fun v => ((Finset.univ : Finset S).filter (fun x => f x = v)).card with ha
  have ha0 : ∀ x, x ∉ W → a x = 0 := by
    intro x hx
    have hempty : (Finset.univ : Finset S).filter (fun y => f y = x) = ∅ :=
      Finset.filter_false_of_mem
        (fun y _ hy => hx (hy ▸ Finset.mem_image_of_mem f (Finset.mem_univ y)))
    simp only [ha]
    rw [hempty, Finset.card_empty]
  have hinj : Set.InjOn (fun v : V => v + d) (↑W : Set V) := fun x _ y _ h => add_right_cancel h
  have hreindex : (∑ v ∈ W, a (v + d) ^ 2) = ∑ w ∈ W.image (fun v => v + d), a w ^ 2 := by
    rw [Finset.sum_image hinj]
  have hstep1 : ∑ w ∈ W.image (fun v => v + d), a w ^ 2
      = ∑ w ∈ (W.image (fun v => v + d)) ∩ W, a w ^ 2 := by
    refine (Finset.sum_subset (Finset.inter_subset_left) ?_).symm
    intro x hx hxnot
    have hxW : x ∉ W := fun h => hxnot (Finset.mem_inter.mpr ⟨hx, h⟩)
    simp [ha0 x hxW]
  have hstep2 : ∑ w ∈ (W.image (fun v => v + d)) ∩ W, a w ^ 2 ≤ ∑ w ∈ W, a w ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun i _ _ => by simp)
  have hgoal : (∑ v ∈ W, a (v + d) ^ 2) ≤ ∑ v ∈ W, a v ^ 2 := by
    rw [hreindex, hstep1]
    exact hstep2
  simpa only [hW, ha] using hgoal

/-- **Zero representation dominates** (Ford, *Vinogradov's integral and bounds for the Riemann zeta
function*, Prop. ZRD; the classical "diagonal dominates" lemma).  The number of pairs of `m`-tuples
with a *prescribed* moment-difference vector is at most the number with difference `0`:
`Jdiff m k X d ≤ Jdiff m k X 0` for every `d : Fin (k+1) → ℤ`, where
`Jdiff m k X d = #{((x,y) : (Fin m → Icc 1 X)²) | powerSums x - powerSums y = d}`
(`Submission.Work.BMF.recursion.Defs`).

Route (Cauchy–Schwarz on the fibres of the moment map): writing `c v = #{x : powerSums x = v}`,
`Jdiff m k X d = Σ_v c(v)·c(v-d)` and `Σ_v c(v)c(v-d) ≤ (Σ_v c(v)²)^{1/2}(Σ_v c(v-d)²)^{1/2}`.
An alternative route is the integral representation plus `|∫ …| ≤ ∫ ‖·‖`.  Only the inequality is
needed. -/
theorem Jdiff_le_zero (m k X : ℕ) (d : Fin (k + 1) → ℤ) : Jdiff m k X d ≤ Jdiff m k X 0 := by
  classical
  set f : Tup m X → (Fin (k + 1) → ℤ) :=
    Submission.Vinogradov.powerSums (s := m) (X := X) k with hf
  set W : Finset (Fin (k + 1) → ℤ) := (Finset.univ : Finset (Tup m X)).image f with hW
  set a : (Fin (k + 1) → ℤ) → ℕ :=
    fun v => ((Finset.univ : Finset (Tup m X)).filter (fun x => f x = v)).card with ha
  -- The fibre decomposition of the discrepancy count.
  have hB : ∀ d' : Fin (k + 1) → ℤ, Jdiff m k X d' = ∑ v ∈ W, a v * a (v + d') := by
    intro d'
    have h := card_sub_eq_sum_fiber (f := Submission.Vinogradov.powerSums (s := m) (X := X) k) d'
    simpa only [Jdiff, ha, hW, hf] using h
  have hC : ∀ d' : Fin (k + 1) → ℤ, (∑ v ∈ W, a (v + d') ^ 2) ≤ ∑ v ∈ W, a v ^ 2 := by
    intro d'
    simpa only [ha, hW, hf] using fiber_card_shift_sq_le f d'
  -- The diagonal count is the `L²` mass of the fibre-count function.
  have h0' : Jdiff m k X 0 = ∑ v ∈ W, a v ^ 2 := by
    rw [hB 0]
    exact Finset.sum_congr rfl (fun v _ => by rw [add_zero, pow_two])
  -- Cauchy–Schwarz on the fibres, with the second factor bounded by the first.
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (s := W) (fun v => a v) (fun v => a (v + d))
  have hstep : (Jdiff m k X d) ^ 2 ≤ (Jdiff m k X 0) ^ 2 := by
    rw [hB d, h0']
    calc (∑ v ∈ W, a v * a (v + d)) ^ 2
        ≤ (∑ v ∈ W, a v ^ 2) * (∑ v ∈ W, a (v + d) ^ 2) := hCS
      _ ≤ (∑ v ∈ W, a v ^ 2) * (∑ v ∈ W, a v ^ 2) := Nat.mul_le_mul_left _ (hC d)
      _ = (∑ v ∈ W, a v ^ 2) ^ 2 := by rw [pow_two]
  exact (Nat.pow_le_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp hstep

end Work.BMF.recursion
