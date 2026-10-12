import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

open MeasureTheory Filter Metric Set

open scoped ENNReal Pointwise Topology

/-- A continuous compactly supported function on `EuclideanSpace ℝ (Fin 3)` is bounded. -/
lemma exists_bound_of_continuous_hasCompactSupport {k : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hk : Continuous k) (hks : HasCompactSupport k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖k x‖ ≤ C := by
  have hb : Bornology.IsBounded (Set.range k) := (hks.isCompact_range hk).isBounded
  obtain ⟨r, hr⟩ := (isBounded_iff_subset_closedBall (0 : ℂ)).1 hb
  refine ⟨max r 0, le_max_right _ _, fun x => ?_⟩
  have hx := hr (Set.mem_range_self x)
  rw [mem_closedBall, dist_eq_norm, sub_zero] at hx
  exact hx.trans (le_max_left _ _)

/-- Continuity of translation in `L¹` for continuous compactly supported functions. -/
lemma tendsto_integral_norm_sub_compactSupport {k : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hk : Continuous k) (hks : HasCompactSupport k) :
    Filter.Tendsto (fun u : EuclideanSpace ℝ (Fin 3) => ∫ x, ‖k (x - u) - k x‖)
      (nhds 0) (nhds 0) := by
  obtain ⟨C, _hC0, hC⟩ := exists_bound_of_continuous_hasCompactSupport hk hks
  set S : Set (EuclideanSpace ℝ (Fin 3)) :=
    tsupport k + closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 with hSdef
  have hScomp : IsCompact S := by
    rw [hSdef]
    exact hks.isCompact.add (isCompact_closedBall 0 1)
  have hSmeas : MeasurableSet S := hScomp.isClosed.measurableSet
  have hSne : volume S ≠ ∞ := hScomp.measure_lt_top.ne
  have hbound_int : Integrable (fun x => S.indicator (fun _ => 2 * C) x) volume := by
    rw [integrable_indicator_iff hSmeas]
    exact integrableOn_const (by simpa using hSne)
  have hmeas : ∀ᶠ u in 𝓝 (0 : EuclideanSpace ℝ (Fin 3)),
      AEStronglyMeasurable (fun x => ‖k (x - u) - k x‖) volume := by
    filter_upwards with u
    exact (((hk.comp (continuous_id.sub continuous_const)).sub hk).aestronglyMeasurable).norm
  have hdom : ∀ᶠ u in 𝓝 (0 : EuclideanSpace ℝ (Fin 3)),
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))),
        ‖(fun x => ‖k (x - u) - k x‖) x‖ ≤ S.indicator (fun _ => 2 * C) x := by
    filter_upwards [ball_mem_nhds (0 : EuclideanSpace ℝ (Fin 3)) one_pos] with u hu
    filter_upwards with x
    rw [norm_norm]
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      calc ‖k (x - u) - k x‖ ≤ ‖k (x - u)‖ + ‖k x‖ := norm_sub_le _ _
        _ ≤ C + C := add_le_add (hC _) (hC _)
        _ = 2 * C := by ring
    · have hx' : x ∉ tsupport k + closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
        intro h
        exact hx (by rw [hSdef]; exact h)
      have hxu : k (x - u) = 0 := by
        by_contra hc
        exact (fun h => hx' (Set.mem_add.2
            ⟨x - u, h, u, Metric.ball_subset_closedBall hu, sub_add_cancel _ _⟩))
          (subset_tsupport k (Function.mem_support.2 hc))
      have hxt : k x = 0 := by
        by_contra hc
        exact (fun h => hx' (Set.mem_add.2 ⟨x, h, 0, by simp, add_zero x⟩))
          (subset_tsupport k (Function.mem_support.2 hc))
      have hz : S.indicator (fun _ => 2 * C) x = 0 :=
        Set.indicator_of_notMem hx (fun _ => 2 * C)
      simp [hxu, hxt, hz]
  have hlim : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))),
      Tendsto (fun u => ‖k (x - u) - k x‖) (𝓝 (0 : EuclideanSpace ℝ (Fin 3)))
        (𝓝 ((fun _ => (0 : ℝ)) x)) := by
    filter_upwards with x
    have hcont : Continuous fun u : EuclideanSpace ℝ (Fin 3) => k (x - u) - k x :=
      (hk.comp (continuous_const.sub continuous_id)).sub continuous_const
    simpa using (hcont.tendsto (0 : EuclideanSpace ℝ (Fin 3))).norm
  simpa using tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))))
    (l := 𝓝 (0 : EuclideanSpace ℝ (Fin 3)))
    (F := fun u x => ‖k (x - u) - k x‖)
    (f := fun _ => (0 : ℝ))
    (bound := fun x => S.indicator (fun _ => 2 * C) x)
    hmeas hdom hbound_int hlim

theorem tendsto_integral_norm_sub_translate {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hg : MeasureTheory.Integrable g) :
    Filter.Tendsto (fun u : EuclideanSpace ℝ (Fin 3) => ∫ x, ‖g (x - u) - g x‖)
      (nhds 0) (nhds 0) := by
  rw [tendsto_order]
  constructor
  · intro b hb
    filter_upwards with u
    exact lt_of_lt_of_le hb (integral_nonneg fun x => norm_nonneg _)
  · intro b hb
    obtain ⟨k, hks, hkg, hkc, hki⟩ :=
      hg.exists_hasCompactSupport_integral_sub_le (show (0 : ℝ) < b / 3 by linarith)
    have hklt : ∀ᶠ u in 𝓝 (0 : EuclideanSpace ℝ (Fin 3)),
        ∫ x, ‖k (x - u) - k x‖ < b / 3 :=
      (tendsto_order.1 (tendsto_integral_norm_sub_compactSupport hkc hks)).2 (b / 3)
        (by linarith)
    filter_upwards [hklt] with u hu
    have hA : Integrable (fun x => ‖g (x - u) - k (x - u)‖) volume :=
      ((hg.comp_sub_right u).sub (hki.comp_sub_right u)).norm
    have hB : Integrable (fun x => ‖k (x - u) - k x‖) volume :=
      ((hki.comp_sub_right u).sub hki).norm
    have hC : Integrable (fun x => ‖k x - g x‖) volume := (hki.sub hg).norm
    have hL : Integrable (fun x => ‖g (x - u) - g x‖) volume :=
      ((hg.comp_sub_right u).sub hg).norm
    have hpt : ∀ x, ‖g (x - u) - g x‖ ≤
        ‖g (x - u) - k (x - u)‖ + ‖k (x - u) - k x‖ + ‖k x - g x‖ := by
      intro x
      have hsplit : g (x - u) - g x =
          (g (x - u) - k (x - u)) + (k (x - u) - k x) + (k x - g x) := by ring
      rw [hsplit]
      exact norm_add₃_le
    have h1 : ∫ x, ‖g (x - u) - k (x - u)‖ = ∫ x, ‖g x - k x‖ :=
      integral_sub_right_eq_self (fun y => ‖g y - k y‖) u
    have h2 : ∫ x, ‖k x - g x‖ = ∫ x, ‖g x - k x‖ :=
      integral_congr_ae (Eventually.of_forall fun x => norm_sub_rev (k x) (g x))
    have hsum2 : ∫ x, (‖g (x - u) - k (x - u)‖ + ‖k (x - u) - k x‖ + ‖k x - g x‖)
        = (∫ x, (‖g (x - u) - k (x - u)‖ + ‖k (x - u) - k x‖)) + ∫ x, ‖k x - g x‖ :=
      integral_add (f := fun x => ‖g (x - u) - k (x - u)‖ + ‖k (x - u) - k x‖)
        (g := fun x => ‖k x - g x‖) (hA.add hB) hC
    have hsum1 : ∫ x, (‖g (x - u) - k (x - u)‖ + ‖k (x - u) - k x‖)
        = (∫ x, ‖g (x - u) - k (x - u)‖) + ∫ x, ‖k (x - u) - k x‖ :=
      integral_add (f := fun x => ‖g (x - u) - k (x - u)‖)
        (g := fun x => ‖k (x - u) - k x‖) hA hB
    calc ∫ x, ‖g (x - u) - g x‖
        ≤ ∫ x, (‖g (x - u) - k (x - u)‖ + ‖k (x - u) - k x‖ + ‖k x - g x‖) :=
          integral_mono hL ((hA.add hB).add hC) hpt
      _ = (∫ x, ‖g (x - u) - k (x - u)‖) + (∫ x, ‖k (x - u) - k x‖)
            + ∫ x, ‖k x - g x‖ := by
          rw [hsum2, hsum1]
      _ < b := by
          rw [h1, h2]
          linarith

end Work.BoseFixB1
