import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

namespace Commons.Analysis.Calculus

open Filter Set MeasureTheory
open scoped Topology

/-- Mean value inequality for absolutely continuous maps into a normed space: if `g : ℝ → F` is
absolutely continuous on `[d, b]`, has derivative `g'` at almost every point of `(d, b)`, and
`‖g' t‖ ≤ η` at almost every point of `(d, b)`, then `dist (g d) (g b) ≤ η * (b - d)`.

This is the bounded-derivative version of `AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero`
and needs no completeness or finite-dimensionality of `F`. -/
theorem mean_value_inequality_absolutelyContinuous {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g g' : ℝ → F} {d b η : ℝ} (hdb : d ≤ b) (hη : 0 ≤ η)
    (hg : AbsolutelyContinuousOnInterval g d b)
    (hderiv : Filter.Eventually (fun t => t ∈ Set.Ioo d b → HasDerivAt g (g' t) t)
      (MeasureTheory.ae (MeasureTheory.volume : MeasureTheory.Measure ℝ)))
    (hbound : Filter.Eventually (fun t => t ∈ Set.Ioo d b → ‖g' t‖ ≤ η)
      (MeasureTheory.ae (MeasureTheory.volume : MeasureTheory.Measure ℝ))) :
    dist (g d) (g b) ≤ η * (b - d) := by
  classical
  rcases hdb.eq_or_lt with rfl | hlt
  · simp
  have hbdpos : 0 < b - d := sub_pos.mpr hlt
  suffices key : ∀ ε > 0, dist (g d) (g b) ≤ (η + ε) * (b - d) by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have hε : 0 < δ / (b - d) := div_pos hδ hbdpos
    have h := key _ hε
    have h1 : (η + δ / (b - d)) * (b - d) = η * (b - d) + δ := by
      field_simp
    rwa [h1] at h
  intro ε hε
  -- Replace `g'` by a function that is bounded by `η` *everywhere* on `(d,b)`, and that is still
  -- an a.e. derivative of `g` on `(d,b)`.
  set φ : ℝ → F := fun x => if HasDerivAt g (g' x) x ∧ ‖g' x‖ ≤ η then g' x else 0 with hφ
  have hφ_deriv : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ioo d b → HasDerivAt g (φ x) x := by
    filter_upwards [hderiv, hbound] with x hdx hbx hx
    have hd : HasDerivAt g (g' x) x := hdx hx
    have hb : ‖g' x‖ ≤ η := hbx hx
    have hval : φ x = g' x := by
      simp only [hφ]
      rw [if_pos ⟨hd, hb⟩]
    rw [hval]
    exact hd
  have hφ_bound : ∀ x ∈ Ioo d b, ‖φ x‖ ≤ η := by
    intro x _
    simp only [hφ]
    by_cases h : HasDerivAt g (g' x) x ∧ ‖g' x‖ ≤ η
    · rw [if_pos h]; exact h.2
    · rw [if_neg h]; simpa using hη
  obtain ⟨u, hu₁, hu₂, hu₃⟩ :=
    exists_dist_slope_lt_pairwiseDisjoint_hasSum hlt.le hφ_deriv hε
  -- Pointwise bound on each member of the covering.
  have hpt (z : u) : dist (g z.val.1) (g z.val.2) ≤ (η + ε) * (z.val.2 - z.val.1) := by
    obtain ⟨⟨hz1, hz2, hz3⟩, hzd⟩ := hu₁ z.val z.property
    have hzI : z.val.1 ∈ Ioo d b := ⟨hz1, by linarith⟩
    have hbnd : ‖φ z.val.1‖ ≤ η := hφ_bound _ hzI
    have hslope : ‖slope g z.val.1 z.val.2‖ ≤ η + ε := by
      have h1 : ‖slope g z.val.1 z.val.2 - φ z.val.1‖ < ε := by
        rw [dist_eq_norm] at hzd; exact hzd
      calc ‖slope g z.val.1 z.val.2‖
          = ‖(slope g z.val.1 z.val.2 - φ z.val.1) + φ z.val.1‖ := by rw [sub_add_cancel]
        _ ≤ ‖slope g z.val.1 z.val.2 - φ z.val.1‖ + ‖φ z.val.1‖ := norm_add_le _ _
        _ ≤ ε + η := by linarith [h1.le]
        _ = η + ε := by ring
    have hpos : 0 < z.val.2 - z.val.1 := by linarith
    have hdist : dist (g z.val.1) (g z.val.2)
        = ‖(z.val.2 - z.val.1) • slope g z.val.1 z.val.2‖ := by
      rw [dist_eq_norm, norm_sub_rev, sub_smul_slope, vsub_eq_sub]
    rw [hdist, norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
    calc (z.val.2 - z.val.1) * ‖slope g z.val.1 z.val.2‖
        ≤ (z.val.2 - z.val.1) * (η + ε) := mul_le_mul_of_nonneg_left hslope hpos.le
      _ = (η + ε) * (z.val.2 - z.val.1) := by ring
  -- Assemble the `HasSum` statement.
  let G : u → ℝ := fun z => dist (g z.val.1) (g z.val.2)
  have G_nonneg : 0 ≤ G := fun z => dist_nonneg
  have G_bound (s : Finset u) : ∑ z ∈ s, G z ≤ (η + ε) * (b - d) := by
    calc ∑ z ∈ s, G z
        ≤ ∑ z ∈ s, (η + ε) * (z.val.2 - z.val.1) := Finset.sum_le_sum (fun z _ => hpt z)
      _ = (η + ε) * ∑ z ∈ s, (z.val.2 - z.val.1) := by rw [Finset.mul_sum]
      _ ≤ (η + ε) * (b - d) := by
          gcongr
          exact hu₃.tsum_eq ▸ Summable.sum_le_tsum s (fun z _ => by
              have h := (hu₁ z.val z.property).1.2.1; linarith) hu₃.summable
  have hu₄ : HasSum G (∑' z, G z) := (summable_of_sum_le G_nonneg G_bound).hasSum
  have hfinal := hg.dist_le_of_pairwiseDisjoint_hasSum hlt.le (fun z hz => (hu₁ z hz).1) hu₂ hu₃ hu₄
  have G_sum_bound : ∑' z, G z ≤ (η + ε) * (b - d) :=
    Real.tsum_le_of_sum_le G_nonneg G_bound
  linarith [hfinal, G_sum_bound]

end Commons.Analysis.Calculus