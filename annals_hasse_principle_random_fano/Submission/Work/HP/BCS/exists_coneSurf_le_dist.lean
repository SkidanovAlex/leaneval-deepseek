import Mathlib
import Submission.Work.HP.BCS.Defs

/-!
# `Work.HP.BCS.exists_coneSurf_le_dist`

If `p` lies in the closed cone `{|⟪a,p⟫| ≤ c‖p‖}` and `q` lies strictly outside it
(`c‖q‖ < |⟪a,q⟫|`), and `x` is within distance `r` of both `p` and `q`, then `x` is within
distance `r` of the cone *surface* `{|⟪a,y⟫| = c‖y‖`.

Geometrically: the segment `[p,q]` joins the inside of the cone to its exterior, so by the
intermediate value theorem it meets the cone surface at some point `y`; and every point of the
segment is within distance `r` of `x` (the distance to `x` is a convex function on the segment,
bounded by the max of its endpoint values).
-/

set_option autoImplicit false

namespace Work.HP.BCS

/-- The geometric core: the segment joining a point of the closed cone `{|⟪a,·⟫| ≤ c‖·‖}` to a
point strictly outside it meets the cone surface `{|⟪a,·⟫| = c‖·‖}` at a point `y` that is still
within distance `r` of `x`. -/
theorem exists_coneSurf_le_dist {k : ℕ} (a : EuclideanSpace ℝ (Fin k)) (c r : ℝ)
    {p q x : EuclideanSpace ℝ (Fin k)}
    (hp : |inner ℝ a p| ≤ c * ‖p‖) (hq : c * ‖q‖ < |inner ℝ a q|)
    (hpx : ‖x - p‖ ≤ r) (hqx : ‖x - q‖ ≤ r) :
    ∃ y : EuclideanSpace ℝ (Fin k), |inner ℝ a y| = c * ‖y‖ ∧ ‖x - y‖ ≤ r := by
  -- The restriction of `t ↦ |⟪a, p + t(q-p)⟫| - c‖p + t(q-p)‖` to `[0,1]`.
  set f : ℝ → ℝ := fun t => |inner ℝ a (p + t • (q - p))| - c * ‖p + t • (q - p)‖ with hf
  have hfcont : ContinuousOn f (Set.Icc 0 1) := by
    rw [hf]; fun_prop
  have hf0 : f 0 = |inner ℝ a p| - c * ‖p‖ := by rw [hf]; simp
  have hf1 : f 1 = |inner ℝ a q| - c * ‖q‖ := by rw [hf]; simp
  have h0 : f 0 ≤ 0 := by rw [hf0]; linarith
  have h1 : 0 ≤ f 1 := by rw [hf1]; linarith
  -- Intermediate value theorem: the path crosses the cone surface.
  obtain ⟨t, ht, hft⟩ :=
    (intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hfcont) ⟨h0, h1⟩
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  refine ⟨p + t • (q - p), ?_, ?_⟩
  · -- `y = p + t(q-p)` lies on the cone surface.
    rw [hf] at hft; linarith
  · -- `x` is within distance `r` of every point of the segment `[p,q]`.
    have hxy : x - (p + t • (q - p)) = (1 - t) • (x - p) + t • (x - q) := by module
    calc ‖x - (p + t • (q - p))‖
        = ‖(1 - t) • (x - p) + t • (x - q)‖ := by rw [hxy]
      _ ≤ ‖(1 - t) • (x - p)‖ + ‖t • (x - q)‖ := norm_add_le _ _
      _ = (1 - t) * ‖x - p‖ + t * ‖x - q‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - t), abs_of_nonneg ht0]
      _ ≤ (1 - t) * r + t * r := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left hpx (by linarith)
            · exact mul_le_mul_of_nonneg_left hqx ht0
      _ = r := by ring

end Work.HP.BCS
