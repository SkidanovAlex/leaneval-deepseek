import Mathlib
import Submission.Work.WilkiesH.Norm.JointDefs
import Submission.Work.WilG5.Reindex3

namespace Work.WilkiesH.Norm

open WilkiesDesign WilkiesConjecture
open Work.WilG5

/-- `MvPolynomial.X i` has total degree at most `2` (for indices `i : Fin 2`). -/
private lemma td_X_le_two (i : Fin 2) :
    (MvPolynomial.X i : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 2 :=
  le_trans (td_X_le i) (by norm_num)

/-- The constant polynomial `1` has total degree at most `2`. -/
private lemma td_one_le_two :
    (MvPolynomial.C (1 : ℝ) : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 2 :=
  le_trans (td_C_le (1 : ℝ)) (by norm_num)

/-- The relation polynomial of a shape has total degree at most `2`: it is linear for the two
non-inverting shapes and bilinear for the two inverting ones.  This uniform bound is what makes
`coordPre_mem` applicable to every `shapeRelSet i (σ i)` at once. -/
theorem shapeRelPoly_totalDegree_le (s : NormShape) : (shapeRelPoly s).totalDegree ≤ 2 := by
  cases s
  · show (MvPolynomial.X (0 : Fin 2) - MvPolynomial.X (1 : Fin 2) :
        MvPolynomial (Fin 2) ℝ).totalDegree ≤ 2
    exact le_trans (td_sub_le _ _) (max_le (td_X_le_two 0) (td_X_le_two 1))
  · show (MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) :
        MvPolynomial (Fin 2) ℝ).totalDegree ≤ 2
    exact le_trans (MvPolynomial.totalDegree_add _ _) (max_le (td_X_le_two 0) (td_X_le_two 1))
  · show (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) - MvPolynomial.C 1 :
        MvPolynomial (Fin 2) ℝ).totalDegree ≤ 2
    refine le_trans (td_sub_le _ _) (max_le ?_ ?_)
    · exact le_trans (td_mul_le _ _)
        (le_trans (add_le_add (td_X_le (0 : Fin 2)) (td_X_le (1 : Fin 2))) (by norm_num))
    · exact td_one_le_two
  · show (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) + MvPolynomial.C 1 :
        MvPolynomial (Fin 2) ℝ).totalDegree ≤ 2
    refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
    · exact le_trans (td_mul_le _ _)
        (le_trans (add_le_add (td_X_le (0 : Fin 2)) (td_X_le (1 : Fin 2))) (by norm_num))
    · exact td_one_le_two

/-- The two-variable graph set of a shape is `Ω`-definable with format `2` and degree `2`. -/
theorem shapeGraphSet_mem (S : WilkiesDesign.SOMin) (s : NormShape) :
    shapeGraphSet s ∈ S.Ω 2 2 2 :=
  mem_mono (S.hyp 2 (shapeRelPoly s)) 2 2 le_rfl (shapeRelPoly_totalDegree_le s)

/-- Each single relation `shapeRelSet i (σ i)` is `Ω`-definable with format and degree depending
only on the ambient dimension `n + n` (and not on the index `i`). -/
theorem shapeRelSet_mem {n : ℕ} (S : WilkiesDesign.SOMin) (σ : Fin n → NormShape) (i : Fin n) :
    shapeRelSet i (σ i) ∈
      S.Ω (2 + 64 * (n + n + 2) + 64) (2 + 32 * (n + n + 2) + 32) (n + n) :=
  coordPre_mem (S := S) (m := 2) (N := n + n) (ι := shapeCoordMap i)
    (A := shapeGraphSet (σ i)) (shapeGraphSet_mem S (σ i))

/-- The joint graph of a shape vector is `Ω`-definable, with bounds depending only on `n`:
it is the finite intersection of the `n` relations `shapeRelSet i (σ i)`, each of which costs
a uniform format/degree amount (`shapeRelSet_mem`), and the format grows by one and the degrees
add up under `SOMin.inter`. -/
theorem normJointGraph_mem {n : ℕ} (σ : Fin n → NormShape) :
    ∃ a b : ℕ, ∀ S : WilkiesDesign.SOMin, normJointGraph σ ∈ S.Ω a b (n + n) := by
  refine ⟨(2 + 64 * (n + n + 2) + 64) + 1,
    ∑ _ : Fin n, (2 + 32 * (n + n + 2) + 32), ?_⟩
  intro S
  have hInt := S.inter (fun _ : Fin n => 2 + 32 * (n + n + 2) + 32)
    (fun i : Fin n => shapeRelSet i (σ i)) (fun i => shapeRelSet_mem S σ i)
  simpa only [normJointGraph] using hInt

end Work.WilkiesH.Norm
