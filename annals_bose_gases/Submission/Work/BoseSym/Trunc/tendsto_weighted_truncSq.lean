import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSym.Trunc

theorem tendsto_weighted_truncSq {N : ℕ} {ψ : ℕ → ℝ → ℝ}
    (hψc : ∀ n, Continuous (ψ n)) (hψb : ∀ n t, |ψ n t| ≤ |t|)
    (hψt : ∀ t, Filter.Tendsto (fun n => ψ n t) Filter.atTop (nhds t))
    {s : Set (Work.BoseSym.Conf N)} {W : Work.BoseSym.Conf N → ℝ} (hW0 : 0 ≤ W)
    (hWm : AEMeasurable W (MeasureTheory.volume.restrict s))
    {f : Work.BoseSym.Conf N → ℝ}
    (hf : MeasureTheory.AEStronglyMeasurable f (MeasureTheory.volume.restrict s))
    (hint : MeasureTheory.IntegrableOn (fun x => W x * (f x) ^ 2) s MeasureTheory.volume) :
    Filter.Tendsto (fun n => ∫ x in s, W x * (ψ n (f x)) ^ 2) Filter.atTop
      (nhds (∫ x in s, W x * (f x) ^ 2)) := by
  -- Dominated convergence on `volume.restrict s`, with dominating function
  -- `W · (f ·)²` (integrable by hypothesis).  Pointwise domination holds
  -- everywhere: `W ≥ 0` and `|ψ n (f x)| ≤ |f x|`, so `(ψ n (f x))² ≤ (f x)²`.
  have htend := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := MeasureTheory.volume.restrict s)
    (F := fun n x => W x * (ψ n (f x)) ^ 2)
    (f := fun x => W x * (f x) ^ 2)
    (fun x => W x * (f x) ^ 2)
    (fun n => (hWm.aestronglyMeasurable).mul (((hψc n).comp_aestronglyMeasurable hf).pow 2))
    hint
    (fun n => Filter.Eventually.of_forall (fun x => by
      have hsq : (ψ n (f x)) ^ 2 ≤ (f x) ^ 2 := (sq_le_sq).2 (hψb n (f x))
      have hnn : 0 ≤ W x * (ψ n (f x)) ^ 2 := mul_nonneg (hW0 x) (sq_nonneg _)
      rw [Real.norm_of_nonneg hnn]
      exact mul_le_mul_of_nonneg_left hsq (hW0 x)))
    (Filter.Eventually.of_forall (fun x => by
      have h1 : Filter.Tendsto (fun n => (ψ n (f x)) ^ 2) Filter.atTop (nhds ((f x) ^ 2)) :=
        (hψt (f x)).pow 2
      simpa using h1.const_mul (W x)))
  exact htend

end Work.BoseSym.Trunc
