import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.DominatedConvergence

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PressureOn.Auxiliary

theorem tendsto_integral_of_compact_support {F : ℕ → EuclideanSpace ℝ (Fin 3) → ℝ}
    {f : EuclideanSpace ℝ (Fin 3) → ℝ} {K : Set (EuclideanSpace ℝ (Fin 3))} {C : ℝ}
    (hK : IsCompact K) (hC : 0 ≤ C)
    (hFmeas : ∀ n, MeasureTheory.AEStronglyMeasurable (F n) MeasureTheory.volume)
    (hFsupp : ∀ n, Function.support (F n) ⊆ K)
    (hfsupp : Function.support f ⊆ K)
    (hFbound : ∀ n x, ‖F n x‖ ≤ C)
    (hlim : ∀ x, Filter.Tendsto (fun n => F n x) Filter.atTop (nhds (f x))) :
    Filter.Tendsto (fun n => ∫ x, F n x) Filter.atTop (nhds (∫ x, f x)) := by
  have _ := hC
  have hKfin : MeasureTheory.volume K ≠ ⊤ := hK.measure_lt_top.ne
  have hbound_int : MeasureTheory.Integrable (fun _ : EuclideanSpace ℝ (Fin 3) => C)
      (MeasureTheory.volume.restrict K) :=
    MeasureTheory.integrableOn_const hKfin
  have key : Filter.Tendsto (fun n => ∫ x, F n x ∂(MeasureTheory.volume.restrict K))
      Filter.atTop (nhds (∫ x, f x ∂(MeasureTheory.volume.restrict K))) :=
    MeasureTheory.tendsto_integral_of_dominated_convergence (μ := MeasureTheory.volume.restrict K)
      (fun _ => C)
      (fun n => (hFmeas n).restrict)
      hbound_int
      (fun n => Filter.Eventually.of_forall (fun x => hFbound n x))
      (Filter.Eventually.of_forall (fun x => hlim x))
  have hFn : ∀ n, (∫ x in K, F n x) = ∫ x, F n x := fun n =>
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      by_contra h; exact hx (hFsupp n h))
  have hf : (∫ x in K, f x) = ∫ x, f x :=
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      by_contra h; exact hx (hfsupp h))
  rw [hf] at key
  exact key.congr' (Filter.Eventually.of_forall hFn)

end Work.FTS.PressureOn.Auxiliary
