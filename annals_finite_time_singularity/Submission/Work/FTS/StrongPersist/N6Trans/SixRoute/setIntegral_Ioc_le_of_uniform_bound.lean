import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllSol.VthAux.traceAux.PowerHardyTrunc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.StrongPersist.N6Trans.SixRoute

theorem setIntegral_Ioc_le_of_uniform_bound {ε C K : ℝ} (hε : 0 < ε)
    {F G : ℝ → ℝ}
    (hFint : MeasureTheory.IntegrableOn F (Set.Ioc (0 : ℝ) ε))
    (hGint : MeasureTheory.IntegrableOn G (Set.Ioc (0 : ℝ) ε))
    (hineq : ∀ δ ∈ Set.Ioo (0 : ℝ) ε,
      (∫ x in Set.Ioc δ ε, F x) ≤ C * (∫ x in Set.Ioc δ ε, G x) + K) :
    (∫ x in Set.Ioc (0 : ℝ) ε, F x) ≤ C * (∫ x in Set.Ioc (0 : ℝ) ε, G x) + K := by
  -- We exhaust `Ioc 0 ε` by the increasing family `Ioc (ε/(n+2)) ε` and pass to the limit
  -- in the hypothesis, which holds for every point of that family.
  have hunion : (⋃ n : ℕ, Set.Ioc (ε / ((n : ℝ) + 2)) ε) = Set.Ioc (0 : ℝ) ε := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Ioc]
    constructor
    · rintro ⟨n, hn1, hn2⟩
      exact ⟨lt_of_lt_of_le (by positivity) (le_of_lt hn1), hn2⟩
    · rintro ⟨hx0, hxε⟩
      obtain ⟨n, hn⟩ := exists_nat_gt (ε / x)
      refine ⟨n, ?_, hxε⟩
      have h3 : ε < (n : ℝ) * x := (div_lt_iff₀ hx0).mp hn
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 2)]
      nlinarith [h3, hx0]
  have hs : ∀ n : ℕ, MeasurableSet (Set.Ioc (ε / ((n : ℝ) + 2)) ε) := fun _ => measurableSet_Ioc
  have hmono : Monotone (fun n : ℕ => Set.Ioc (ε / ((n : ℝ) + 2)) ε) := by
    intro n m hnm x hx
    simp only [Set.mem_Ioc] at hx ⊢
    have hle : ε / ((m : ℝ) + 2) ≤ ε / ((n : ℝ) + 2) :=
      div_le_div_of_nonneg_left hε.le (by positivity)
        (by exact_mod_cast Nat.add_le_add_right hnm 2)
    exact ⟨lt_of_le_of_lt hle hx.1, hx.2⟩
  have hF_tend : Filter.Tendsto (fun n : ℕ => ∫ x in Set.Ioc (ε / ((n : ℝ) + 2)) ε, F x)
      Filter.atTop (nhds (∫ x in Set.Ioc (0 : ℝ) ε, F x)) := by
    have h := MeasureTheory.tendsto_setIntegral_of_monotone hs hmono (by rw [hunion]; exact hFint)
    rwa [hunion] at h
  have hG_tend : Filter.Tendsto (fun n : ℕ => ∫ x in Set.Ioc (ε / ((n : ℝ) + 2)) ε, G x)
      Filter.atTop (nhds (∫ x in Set.Ioc (0 : ℝ) ε, G x)) := by
    have h := MeasureTheory.tendsto_setIntegral_of_monotone hs hmono (by rw [hunion]; exact hGint)
    rwa [hunion] at h
  have hR_tend : Filter.Tendsto
      (fun n : ℕ => C * (∫ x in Set.Ioc (ε / ((n : ℝ) + 2)) ε, G x) + K) Filter.atTop
      (nhds (C * (∫ x in Set.Ioc (0 : ℝ) ε, G x) + K)) :=
    (tendsto_const_nhds.mul hG_tend).add tendsto_const_nhds
  refine le_of_tendsto_of_tendsto hF_tend hR_tend (Filter.Eventually.of_forall fun n => ?_)
  exact hineq _ ⟨by positivity,
    div_lt_self hε (by have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)⟩

end Work.FTS.StrongPersist.N6Trans.SixRoute
