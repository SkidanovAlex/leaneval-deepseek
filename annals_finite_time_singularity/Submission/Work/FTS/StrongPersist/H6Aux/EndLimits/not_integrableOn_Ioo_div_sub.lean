import Mathlib.Analysis.SpecialFunctions.NonIntegrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Aux.EndLimits

theorem not_integrableOn_Ioo_div_sub {c L t : ℝ} (hc : 0 < c) (ht : t < L) :
    ¬ MeasureTheory.IntegrableOn (fun θ : ℝ => c / (L - θ)) (Set.Ioo t L) := by
  intro h
  -- shrink the interval to `(m, L)` with `t < m < L` so that `L` is an interior endpoint
  obtain ⟨m, htm, hmL⟩ : ∃ m : ℝ, t < m ∧ m < L := ⟨(t + L) / 2, by linarith, by linarith⟩
  have h1 : MeasureTheory.IntegrableOn (fun θ : ℝ => c / (L - θ)) (Set.Ioo m L) :=
    h.mono_set (Set.Ioo_subset_Ioo_left htm.le)
  have hI : IntervalIntegrable (fun θ : ℝ => c / (L - θ)) MeasureTheory.volume m L :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hmL.le).mpr h1
  -- `c / (L - x) = -c * (x - L)⁻¹`, hence integrability of `(· - L)⁻¹` on `m..L`
  have hpt : ∀ x : ℝ, (-c⁻¹) * (c / (L - x)) = (x - L)⁻¹ := by
    intro x
    have hx : (x - L)⁻¹ = -((L - x)⁻¹) := by rw [← neg_sub x L, inv_neg, neg_neg]
    rw [hx, div_eq_mul_inv, neg_mul, inv_mul_cancel_left₀ (ne_of_gt hc)]
  have h2 : IntervalIntegrable (fun θ : ℝ => (θ - L)⁻¹) MeasureTheory.volume m L := by
    have h3 : IntervalIntegrable (fun θ : ℝ => (-c⁻¹) * (c / (L - θ))) MeasureTheory.volume m L :=
      hI.const_mul (-c⁻¹)
    exact h3.congr (fun x _ => hpt x)
  -- but `(· - L)⁻¹` is interval integrable on `m..L` only if `L ∉ [[m, L]]`
  rw [intervalIntegrable_sub_inv_iff] at h2
  rcases h2 with h2 | h2
  · exact absurd h2 (ne_of_lt hmL)
  · exact h2 (by rw [Set.uIcc_of_le hmL.le]; exact ⟨hmL.le, le_rfl⟩)

end Work.FTS.StrongPersist.H6Aux.EndLimits
