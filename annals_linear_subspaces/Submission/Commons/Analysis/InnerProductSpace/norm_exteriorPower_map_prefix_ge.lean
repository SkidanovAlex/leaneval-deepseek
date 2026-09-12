import Mathlib
import Submission.Commons.Analysis.InnerProductSpace.exteriorPower_norm_concat_le
import Submission.Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod

set_option linter.unusedVariables false

open scoped BigOperators

namespace Commons.Analysis.InnerProductSpace

open exteriorPower

/-- If `w : Fin (k + m) → E` is split into its first `k` and last `m` entries, then
`Fin.append` of the two pieces recovers `w`. -/
private lemma fin_append_prefix_suffix {E : Type*} {k m : ℕ} (w : Fin (k + m) → E) :
    Fin.append (fun i : Fin k => w (Fin.castLE (Nat.le_add_right k m) i))
      (fun j : Fin m => w (Fin.natAdd k j)) = w := by
  funext i
  refine Fin.addCases (motive := fun i =>
      Fin.append (fun i : Fin k => w (Fin.castLE (Nat.le_add_right k m) i))
        (fun j : Fin m => w (Fin.natAdd k j)) i = w i) ?_ ?_ i
  · intro i0
    rw [Fin.append_left]
    congr 1
  · intro j
    rw [Fin.append_right]

/-- The norm of a prefix wedge is not larger than the norm of the whole wedge, when the
linear map is a contraction on a real inner product space.

Since `P` is a linear contraction, `‖P (u i)‖ ≤ ‖u i‖ = 1`, and the wedge of the trailing
`m` vectors has norm at most `1`; the concatenation inequality
`‖a ∧ b‖ ≤ ‖a‖ ‖b‖` then gives the claim. -/
theorem norm_exteriorPower_map_prefix_ge {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {k m : ℕ} (P : E →ₗ[ℝ] E) (hP : ∀ x, ‖P x‖ ≤ ‖x‖)
    (hidem : ∀ x, P (P x) = P x) {u : Fin (k + m) → E} (hu : Orthonormal ℝ u) :
    ‖exteriorPower.map (k + m) P (exteriorPower.ιMulti ℝ (k + m) u)‖ ≤
      ‖exteriorPower.map k P (exteriorPower.ιMulti ℝ k
        (fun i : Fin k => u (Fin.castLE (Nat.le_add_right k m) i)))‖ := by
  classical
  have hnorm : ∀ i : Fin (k + m), ‖(P ∘ u) i‖ ≤ 1 := by
    intro i
    calc ‖(P ∘ u) i‖ = ‖P (u i)‖ := rfl
      _ ≤ ‖u i‖ := hP _
      _ = 1 := hu.norm_eq_one i
  have hsplit : Fin.append (fun i : Fin k => (P ∘ u) (Fin.castLE (Nat.le_add_right k m) i))
      (fun j : Fin m => (P ∘ u) (Fin.natAdd k j)) = (P ∘ u) :=
    fin_append_prefix_suffix (P ∘ u)
  have hsecond :
      ‖exteriorPower.ιMulti ℝ m (fun j : Fin m => (P ∘ u) (Fin.natAdd k j))‖ ≤ 1 := by
    calc ‖exteriorPower.ιMulti ℝ m (fun j : Fin m => (P ∘ u) (Fin.natAdd k j))‖
        ≤ ∏ j : Fin m, ‖(P ∘ u) (Fin.natAdd k j)‖ :=
          exteriorPower_norm_wedge_le_prod _
      _ ≤ ∏ _j : Fin m, (1 : ℝ) :=
          Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => hnorm (Fin.natAdd k j))
      _ = 1 := Finset.prod_const_one
  calc
    ‖exteriorPower.map (k + m) P (exteriorPower.ιMulti ℝ (k + m) u)‖
        = ‖exteriorPower.ιMulti ℝ (k + m) (P ∘ u)‖ := by
          rw [exteriorPower.map_apply_ιMulti]
    _ = ‖exteriorPower.ιMulti ℝ (k + m)
          (Fin.append (fun i : Fin k => (P ∘ u) (Fin.castLE (Nat.le_add_right k m) i))
            (fun j : Fin m => (P ∘ u) (Fin.natAdd k j)))‖ := by
          rw [hsplit]
    _ ≤ ‖exteriorPower.ιMulti ℝ k
            (fun i : Fin k => (P ∘ u) (Fin.castLE (Nat.le_add_right k m) i))‖
          * ‖exteriorPower.ιMulti ℝ m (fun j : Fin m => (P ∘ u) (Fin.natAdd k j))‖ :=
          exteriorPower_norm_concat_le _ _
    _ ≤ ‖exteriorPower.ιMulti ℝ k
            (fun i : Fin k => (P ∘ u) (Fin.castLE (Nat.le_add_right k m) i))‖ * 1 :=
          mul_le_mul_of_nonneg_left hsecond (norm_nonneg _)
    _ = ‖exteriorPower.ιMulti ℝ k
            (fun i : Fin k => (P ∘ u) (Fin.castLE (Nat.le_add_right k m) i))‖ :=
          mul_one _
    _ = ‖exteriorPower.map k P (exteriorPower.ιMulti ℝ k
          (fun i : Fin k => u (Fin.castLE (Nat.le_add_right k m) i)))‖ := by
          rw [exteriorPower.map_apply_ιMulti]
          rfl

end Commons.Analysis.InnerProductSpace
