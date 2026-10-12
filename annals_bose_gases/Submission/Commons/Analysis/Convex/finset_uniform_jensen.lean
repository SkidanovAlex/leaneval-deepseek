import Mathlib.RingTheory.TotallySplit
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.RCLike.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Algebra.Order.Star.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Finite uniform Jensen inequality

The arithmetic mean version of Jensen's inequality for a convex function `F` on the
nonnegative real half-line.
-/

namespace Commons.Analysis.Convex

theorem finset_uniform_jensen {ι : Type*} [Fintype ι] [Nonempty ι] {F : ℝ → ℝ}
    (hF : ConvexOn ℝ (Set.Ici (0 : ℝ)) F) (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) :
    F ((∑ i : ι, x i) / (Fintype.card ι : ℝ))
      ≤ (∑ i : ι, F (x i)) / (Fintype.card ι : ℝ) := by
  classical
  -- `c` is the uniform weight `1 / card ι`, nonnegative and summing to one.
  let c : ℝ := (1 : ℝ) / (Fintype.card ι : ℝ)
  have hcard : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ‹Nonempty ι›)
  have hw0 : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ (fun _ : ι => c) i := by
    intro i _
    dsimp
    exact div_nonneg zero_le_one (le_of_lt hcard)
  have hw1 : (∑ i : ι, c) = 1 := by
    dsimp [c]
    simp [hcard.ne']
  have hmem : ∀ i ∈ (Finset.univ : Finset ι), x i ∈ Set.Ici (0 : ℝ) := by
    intro i _
    simpa [Set.mem_Ici] using (hx i)
  -- Convex Jensen inequality with equal weights `c`.
  have hj : F (∑ i : ι, c • x i) ≤ ∑ i : ι, c • F (x i) := by
    simpa using
      (hF.map_sum_le (s := Set.Ici (0 : ℝ)) (t := (Finset.univ : Finset ι))
        (w := fun _ : ι => c) (p := x) hw0 hw1 hmem)
  -- The uniform average of `f` equals the `c`-weighted sum of the `f i`.
  have hid (f : ι → ℝ) :
      (∑ i : ι, f i) / (Fintype.card ι : ℝ) = ∑ i : ι, c • f i := by
    dsimp [c]
    simp [Finset.sum_mul, div_eq_mul_inv, mul_comm]
  calc
    F ((∑ i : ι, x i) / (Fintype.card ι : ℝ)) = F (∑ i : ι, c • x i) := by
      rw [hid x]
    _ ≤ ∑ i : ι, c • F (x i) := hj
    _ = (∑ i : ι, F (x i)) / (Fintype.card ι : ℝ) := by
      rw [← hid (fun i => F (x i))]

end Commons.Analysis.Convex