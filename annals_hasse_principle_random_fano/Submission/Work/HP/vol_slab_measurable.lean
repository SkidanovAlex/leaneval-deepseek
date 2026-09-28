import Mathlib
import Submission.Work.HP.ArchDefs

/-!
# Measurability of the archimedean slab

The set of pairs `(a, x)` of a real coefficient vector and a real point for which
`‖a‖ ≤ 1`, `1 ≤ ‖x‖ ≤ 1 + t`, `|f_a(x)| ≤ eps` and `|∂_j f_a(x)| ≤ del` for all `j`
is a Borel subset of `(Mon d n → ℝ) × (Fin (n+1) → ℝ)`.

Everything is a level set of a *continuous* function of `(a, x)`:
`rNorm`, `formEvalR` and `gradVec` are finite sums/products of coordinate
projections, hence continuous on the product space.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace Work.HP

variable {d n : ℕ}

/-- `p ↦ ‖p.1‖` is continuous on `(Mon d n → ℝ) × (Fin (n+1) → ℝ)`. -/
lemma continuous_rNorm_fst_pair (d n : ℕ) :
    Continuous (fun p : (Mon d n → ℝ) × (Fin (n + 1) → ℝ) => rNorm p.1) := by
  unfold rNorm
  apply Continuous.sqrt
  apply continuous_finsetSum
  intro i _
  exact ((continuous_apply i).comp continuous_fst).pow 2

/-- `p ↦ ‖p.2‖` is continuous on `(Mon d n → ℝ) × (Fin (n+1) → ℝ)`. -/
lemma continuous_rNorm_snd_pair (d n : ℕ) :
    Continuous (fun p : (Mon d n → ℝ) × (Fin (n + 1) → ℝ) => rNorm p.2) := by
  unfold rNorm
  apply Continuous.sqrt
  apply continuous_finsetSum
  intro i _
  exact ((continuous_apply i).comp continuous_snd).pow 2

/-- `p ↦ f_{p.1}(p.2)` is continuous on `(Mon d n → ℝ) × (Fin (n+1) → ℝ)`. -/
lemma continuous_formEvalR_pair (d n : ℕ) :
    Continuous (fun p : (Mon d n → ℝ) × (Fin (n + 1) → ℝ) => formEvalR d n p.1 p.2) := by
  unfold formEvalR veronese
  apply continuous_finsetSum
  intro m _
  apply Continuous.mul
  · exact (continuous_apply m).comp continuous_fst
  · apply continuous_finsetProd
    intro i _
    exact ((continuous_apply i).comp continuous_snd).pow _

/-- `p ↦ ∂_j f_{p.1}(p.2)` is continuous on `(Mon d n → ℝ) × (Fin (n+1) → ℝ)`. -/
lemma continuous_gradVec_pair (d n : ℕ) (j : Fin (n + 1)) :
    Continuous (fun p : (Mon d n → ℝ) × (Fin (n + 1) → ℝ) => gradVec d n p.1 p.2 j) := by
  unfold gradVec gradF
  apply continuous_finsetSum
  intro m _
  apply Continuous.mul
  · apply Continuous.mul
    · apply Continuous.mul
      · exact (continuous_apply m).comp continuous_fst
      · exact continuous_const
    · exact ((continuous_apply j).comp continuous_snd).pow _
  · apply continuous_finsetProd
    intro l _
    exact ((continuous_apply l).comp continuous_snd).pow _

/-- The archimedean slab is Borel measurable. -/
theorem vol_slab_measurable (d n : ℕ) (t eps del : ℝ) :
    MeasurableSet {p : (Work.HP.Mon d n → ℝ) × (Fin (n + 1) → ℝ) |
      Work.HP.rNorm p.1 ≤ 1 ∧ 1 ≤ Work.HP.rNorm p.2 ∧ Work.HP.rNorm p.2 ≤ 1 + t ∧
      |Work.HP.formEvalR d n p.1 p.2| ≤ eps ∧
      ∀ j : Fin (n + 1), |Work.HP.gradVec d n p.1 p.2 j| ≤ del} := by
  have hA : MeasurableSet {p : (Mon d n → ℝ) × (Fin (n + 1) → ℝ) | rNorm p.1 ≤ 1} :=
    measurableSet_le (continuous_rNorm_fst_pair d n).measurable measurable_const
  have hB : MeasurableSet {p : (Mon d n → ℝ) × (Fin (n + 1) → ℝ) | 1 ≤ rNorm p.2} :=
    measurableSet_le measurable_const (continuous_rNorm_snd_pair d n).measurable
  have hC : MeasurableSet {p : (Mon d n → ℝ) × (Fin (n + 1) → ℝ) | rNorm p.2 ≤ 1 + t} :=
    measurableSet_le (continuous_rNorm_snd_pair d n).measurable measurable_const
  have hD : MeasurableSet {p : (Mon d n → ℝ) × (Fin (n + 1) → ℝ) |
      |formEvalR d n p.1 p.2| ≤ eps} :=
    measurableSet_le (continuous_formEvalR_pair d n).abs.measurable measurable_const
  have hE : MeasurableSet {p : (Mon d n → ℝ) × (Fin (n + 1) → ℝ) |
      ∀ j : Fin (n + 1), |gradVec d n p.1 p.2 j| ≤ del} := by
    rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro j
    exact measurableSet_le (continuous_gradVec_pair d n j).abs.measurable measurable_const
  have hEq : {p : (Mon d n → ℝ) × (Fin (n + 1) → ℝ) |
      rNorm p.1 ≤ 1 ∧ 1 ≤ rNorm p.2 ∧ rNorm p.2 ≤ 1 + t ∧
      |formEvalR d n p.1 p.2| ≤ eps ∧
      ∀ j : Fin (n + 1), |gradVec d n p.1 p.2 j| ≤ del}
      = {p : (Mon d n → ℝ) × (Fin (n + 1) → ℝ) | rNorm p.1 ≤ 1} ∩
        {p : (Mon d n → ℝ) × (Fin (n + 1) → ℝ) | 1 ≤ rNorm p.2} ∩
        {p : (Mon d n → ℝ) × (Fin (n + 1) → ℝ) | rNorm p.2 ≤ 1 + t} ∩
        {p : (Mon d n → ℝ) × (Fin (n + 1) → ℝ) | |formEvalR d n p.1 p.2| ≤ eps} ∩
        {p : (Mon d n → ℝ) × (Fin (n + 1) → ℝ) |
          ∀ j : Fin (n + 1), |gradVec d n p.1 p.2 j| ≤ del} := by
    ext p; simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]; tauto
  rw [hEq]
  exact ((((hA.inter hB).inter hC).inter hD).inter hE)

end Work.HP
