import Mathlib
import Submission.Work.EKLContract.Defs

namespace Work.EKLC6Route

/-- `SL₃(ℝ)` carries the subspace topology of `Matrix (Fin 3) (Fin 3) ℝ`, so the underlying
matrix of a convergent sequence of group elements converges entrywise.  The `(i,j)`-matrix
entry is a continuous function of the matrix (a projection of the product `Fin 3 → Fin 3 → ℝ`),
and the coercion `SL₃(ℝ) → Mat₃(ℝ)` is the subtype inclusion, hence continuous. -/
theorem entries_tendsto_of_tendsto {w : ℕ → Work.EKLContract.SL3}
    (hw : Filter.Tendsto w Filter.atTop (nhds (1 : Work.EKLContract.SL3))) (i j : Fin 3) :
    Filter.Tendsto (fun k => ((w k : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j)
      Filter.atTop (nhds ((1 : Matrix (Fin 3) (Fin 3) ℝ) i j)) := by
  have hcoe : Continuous
      (fun g : Work.EKLContract.SL3 => (g : Matrix (Fin 3) (Fin 3) ℝ)) :=
    continuous_subtype_val
  have hentry : Continuous (fun M : Matrix (Fin 3) (Fin 3) ℝ => M i j) :=
    (continuous_apply j).comp (continuous_apply i)
  have hmain : Filter.Tendsto
      (fun k => ((w k : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j) Filter.atTop
      (nhds (((1 : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j)) :=
    ((hentry.comp hcoe).tendsto (1 : Work.EKLContract.SL3)).comp hw
  have h1 : ((1 : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j =
      (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := by
    rw [Matrix.SpecialLinearGroup.coe_one]
  simpa only [h1] using hmain

end Work.EKLC6Route
