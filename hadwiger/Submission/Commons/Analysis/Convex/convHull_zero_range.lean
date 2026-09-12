import Mathlib.Analysis.Convex.Combination
import Mathlib.Data.Real.Basic
import Mathlib.Order.CompletePartialOrder

namespace Commons.Analysis.Convex

theorem convHull_zero_range {ι : Type*} [Fintype ι] {W : Type*} [AddCommGroup W]
    [Module ℝ W] (u : ι → W) :
    convexHull ℝ (({0} ∪ Set.range u) : Set W) =
      {x | ∃ t : ι → ℝ, (∀ i : ι, 0 ≤ t i) ∧ (∑ i : ι, t i) ≤ 1 ∧
        x = ∑ i : ι, t i • u i} := by
  classical
  let S : Set W := ({0} ∪ Set.range u)
  let T : Set W := {x | ∃ t : ι → ℝ, (∀ i : ι, 0 ≤ t i) ∧ (∑ i : ι, t i) ≤ 1 ∧
        x = ∑ i : ι, t i • u i}
  have hgen0 : (0 : W) ∈ T := by
    refine ⟨fun _ => (0 : ℝ), ?_, ?_, ?_⟩
    · intro i
      exact le_rfl
    · simp
    · simp
  have hgenj (j : ι) : u j ∈ T := by
    refine ⟨fun i => if i = j then (1 : ℝ) else 0, ?_, ?_, ?_⟩
    · intro i
      by_cases h : i = j <;> simp [h]
    · simp
    · simp
  have hSsubsetT : S ⊆ T := by
    intro x hx
    rcases hx with rfl | hx2
    · exact hgen0
    · rw [Set.mem_range] at hx2
      rcases hx2 with ⟨j, rfl⟩
      exact hgenj j
  have hconvexT : Convex ℝ T := by
    intro x hx y hy a b ha hb hab
    rcases hx with ⟨tx, htx0, htx1, htxe⟩
    rcases hy with ⟨ty, hty0, hty1, htye⟩
    refine ⟨fun i => a * tx i + b * ty i, ?_, ?_, ?_⟩
    · intro i
      exact add_nonneg (mul_nonneg ha (htx0 i)) (mul_nonneg hb (hty0 i))
    · calc
        (∑ i : ι, (a * tx i + b * ty i)) = a * (∑ i : ι, tx i) + b * (∑ i : ι, ty i) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        _ ≤ a * 1 + b * 1 := by
          exact add_le_add (mul_le_mul_of_nonneg_left htx1 ha)
            (mul_le_mul_of_nonneg_left hty1 hb)
        _ = 1 := by
          simpa using hab
    · rw [htxe, htye]
      rw [Finset.smul_sum, Finset.smul_sum]
      rw [← Finset.sum_add_distrib]
      simp_rw [← mul_smul]
      simp_rw [← add_smul]
  have hTsub : T ⊆ convexHull ℝ S := by
    intro x hx
    rcases hx with ⟨t, ht0, ht1, hte⟩
    let c : ℝ := ∑ i : ι, t i
    let f : Option ι → W := fun o => o.elim 0 u
    let w : Option ι → ℝ := fun o => o.elim (1 - c) t
    have hw0 : ∀ o : Option ι, 0 ≤ w o := by
      intro o
      cases o with
      | none => dsimp [w, c]
                exact sub_nonneg.mpr ht1
      | some i => dsimp [w]
                  exact ht0 i
    have hw1 : (∑ o : Option ι, w o) = 1 := by
      simp [w, c, Fintype.sum_option]
    have hfS : ∀ o : Option ι, f o ∈ S := by
      intro o
      cases o with
      | none => simp [f, S]
      | some i => simp [f, S]
    have hmem : (∑ o : Option ι, w o • f o) ∈ convexHull ℝ S := by
      refine (convex_convexHull ℝ S).sum_mem (t := (Finset.univ : Finset (Option ι)))
        (w := w) (z := f) ?_ ?_ ?_
      · intro o _
        exact hw0 o
      · simpa using hw1
      · intro o _
        exact subset_convexHull ℝ S (hfS o)
    have hv : (∑ o : Option ι, w o • f o) = ∑ i : ι, t i • u i := by
      simp [w, f, c, Fintype.sum_option]
    have hxmem : x ∈ convexHull ℝ S := by
      rw [hte]
      rw [← hv]
      exact hmem
    exact hxmem
  calc
    convexHull ℝ S = T := by
      exact le_antisymm (convexHull_min hSsubsetT hconvexT) hTsub
    _ = {x | ∃ t : ι → ℝ, (∀ i : ι, 0 ≤ t i) ∧ (∑ i : ι, t i) ≤ 1 ∧
        x = ∑ i : ι, t i • u i} := rfl

end Commons.Analysis.Convex