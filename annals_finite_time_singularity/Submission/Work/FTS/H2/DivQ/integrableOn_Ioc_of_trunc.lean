import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.DivQ

open MeasureTheory Filter Set
open scoped Topology

/-- A function which is continuous on the open interval `(0, x₁)` and whose right endpoint
`b` is strictly below `x₁` is integrable on any `Ioc a b` with `0 < a`.  (The interval
`Icc a b` is compact and disjoint from `0`, hence contained in the (open) set of continuity;
`Ioc a b` is contained in it.) -/
private lemma integrableOn_Ioc_of_contOn_Ioo {v : ℝ → ℝ} {x₁ : ℝ}
    (hv : ContinuousOn v (Set.Ioo 0 x₁)) {a b : ℝ} (ha : 0 < a) (hb : b < x₁) :
    IntegrableOn v (Set.Ioc a b) volume := by
  have hsub : Set.Icc a b ⊆ Set.Ioo (0 : ℝ) x₁ := fun t ht =>
    ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  exact ((hv.mono hsub).integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self

/-- The core of `integrableOn_Ioc_of_trunc`: an `AECover`-based argument (exhausting
`(0, x₁)` by the intervals `Ioc (x₁/(2(n+2))) (x₁ - x₁/(2(n+2)))`, on which the interval
integral is bounded by `K` by hypothesis) giving both integrability on `Ioc 0 x₁` and the
bound `∫_{Ioc 0 x₁} u ≤ K`. -/
private lemma main_aux {u : ℝ → ℝ} {x₁ K : ℝ} (hx₁ : 0 < x₁)
    (hnn : ∀ t, 0 ≤ u t) (hcont : ContinuousOn u (Set.Ioo 0 x₁))
    (hb : ∀ y x : ℝ, 0 < y → y < x → x < x₁ → (∫ t in y..x, u t) ≤ K) :
    Integrable u (volume.restrict (Set.Ioc 0 x₁)) ∧
      (∫ x, u x ∂(volume.restrict (Set.Ioc 0 x₁))) ≤ K := by
  have hden : ∀ n : ℕ, (0:ℝ) < 2 * ((n:ℝ) + 2) := fun n => by positivity
  have ha_pos : ∀ n : ℕ, (0:ℝ) < x₁ / (2 * ((n:ℝ) + 2)) := fun n => div_pos hx₁ (hden n)
  have hb_lt : ∀ n : ℕ, x₁ - x₁ / (2 * ((n:ℝ) + 2)) < x₁ := fun n => by
    have h := ha_pos n; linarith
  have hab : ∀ n : ℕ, x₁ / (2 * ((n:ℝ) + 2)) < x₁ - x₁ / (2 * ((n:ℝ) + 2)) := fun n => by
    have hc : (1:ℝ) < (n:ℝ) + 2 := by
      have : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n; linarith
    have key : x₁ / ((n:ℝ) + 2) < x₁ := by
      rw [div_lt_iff₀ (by linarith : (0:ℝ) < (n:ℝ) + 2)]
      nlinarith [mul_lt_mul_of_pos_left hc hx₁]
    have h2 : 2 * (x₁ / (2 * ((n:ℝ) + 2))) = x₁ / ((n:ℝ) + 2) := by
      rw [← mul_div_assoc]
      exact mul_div_mul_left x₁ ((n:ℝ) + 2) two_ne_zero
    linarith [key, h2]
  have ha_tend : Tendsto (fun n : ℕ => x₁ / (2 * ((n:ℝ) + 2))) atTop (𝓝 0) := by
    have hg : Tendsto (fun n : ℕ => 2 * ((n:ℝ) + 2)) atTop atTop := by
      have h1 : Tendsto (fun n : ℕ => ((n:ℝ) + 2)) atTop atTop :=
        (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add tendsto_const_nhds
      exact h1.const_mul_atTop (by norm_num)
    exact tendsto_const_nhds.div_atTop hg
  have hb_tend : Tendsto (fun n : ℕ => x₁ - x₁ / (2 * ((n:ℝ) + 2))) atTop (𝓝 x₁) := by
    have h := (tendsto_const_nhds (x := x₁) : Tendsto (fun _ : ℕ => x₁) atTop (𝓝 x₁)).sub ha_tend
    simpa using h
  have hcover : AECover (volume.restrict (Set.Ioc (0:ℝ) x₁)) atTop
      (fun n : ℕ => Set.Ioc (x₁ / (2 * ((n:ℝ) + 2))) (x₁ - x₁ / (2 * ((n:ℝ) + 2)))) :=
    aecover_Ioc_of_Ioc (μ := volume) (A := (0:ℝ)) (B := x₁) ha_tend hb_tend
  have hmeas : ∀ n : ℕ,
      (volume.restrict (Set.Ioc (0:ℝ) x₁)).restrict
        (Set.Ioc (x₁ / (2 * ((n:ℝ) + 2))) (x₁ - x₁ / (2 * ((n:ℝ) + 2))))
      = volume.restrict (Set.Ioc (x₁ / (2 * ((n:ℝ) + 2))) (x₁ - x₁ / (2 * ((n:ℝ) + 2)))) := by
    intro n
    rw [Measure.restrict_restrict measurableSet_Ioc]
    congr 1
    exact Set.inter_eq_left.2 (fun t ht =>
      ⟨lt_trans (ha_pos n) ht.1, le_trans ht.2 (le_of_lt (hb_lt n))⟩)
  have hfi : ∀ n : ℕ, IntegrableOn u
      (Set.Ioc (x₁ / (2 * ((n:ℝ) + 2))) (x₁ - x₁ / (2 * ((n:ℝ) + 2))))
      (volume.restrict (Set.Ioc (0:ℝ) x₁)) := by
    intro n
    show Integrable u ((volume.restrict (Set.Ioc (0:ℝ) x₁)).restrict
      (Set.Ioc (x₁ / (2 * ((n:ℝ) + 2))) (x₁ - x₁ / (2 * ((n:ℝ) + 2)))))
    rw [hmeas n]
    exact integrableOn_Ioc_of_contOn_Ioo hcont (ha_pos n) (hb_lt n)
  have hbounded : ∀ᶠ n : ℕ in atTop, (∫ x in
      Set.Ioc (x₁ / (2 * ((n:ℝ) + 2))) (x₁ - x₁ / (2 * ((n:ℝ) + 2))), u x
      ∂(volume.restrict (Set.Ioc (0:ℝ) x₁))) ≤ K := by
    filter_upwards with n
    rw [hmeas n, ← intervalIntegral.integral_of_le (le_of_lt (hab n))]
    exact hb _ _ (ha_pos n) (hab n) (hb_lt n)
  have hInt : Integrable u (volume.restrict (Set.Ioc 0 x₁)) :=
    hcover.integrable_of_integral_bounded_of_nonneg_ae K hfi (ae_of_all _ hnn) hbounded
  refine ⟨hInt, ?_⟩
  exact le_of_tendsto (hcover.integral_tendsto_of_countably_generated hInt) hbounded

theorem integrableOn_Ioc_of_trunc {u : ℝ → ℝ} {x₁ K : ℝ} (hx₁ : 0 < x₁)
    (hnn : ∀ t, 0 ≤ u t) (hcont : ContinuousOn u (Set.Ioo 0 x₁))
    (hb : ∀ y x : ℝ, 0 < y → y < x → x < x₁ → (∫ t in y..x, u t) ≤ K) :
    MeasureTheory.IntegrableOn u (Set.Ioc 0 x₁) ∧ (∫ t in (0 : ℝ)..x₁, u t) ≤ K := by
  obtain ⟨h1, h2⟩ := main_aux hx₁ hnn hcont hb
  refine ⟨h1, ?_⟩
  rw [intervalIntegral.integral_of_le hx₁.le]
  exact h2

end Work.FTS.H2.DivQ
