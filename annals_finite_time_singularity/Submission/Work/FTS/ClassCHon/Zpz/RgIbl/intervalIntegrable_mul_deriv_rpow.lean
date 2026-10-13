import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Separation.CompletelyRegular

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.Zpz.RgIbl

theorem intervalIntegrable_mul_deriv_rpow {q p : ℝ} (hq : 0 < q) (hp : 0 ≤ p) {c : ℝ → ℝ}
    (hd0 : MeasureTheory.IntegrableOn
      (fun t : ℝ => t * deriv c t * t ^ (q - 1)) (Set.Ioo 0 1))
    (hdinf : MeasureTheory.IntegrableOn
      (fun t : ℝ => t * deriv c t * t ^ (-p - 1)) (Set.Ioi 1))
    {z : ℝ} (hz : 0 < z) :
    IntervalIntegrable (fun t : ℝ => t * deriv c t * t ^ (q - 1)) MeasureTheory.volume 0 z := by
  -- The two hypotheses are not needed as *inequalities*: on `(0,1)` the function `F` of the
  -- conclusion is exactly the integrand of `hd0`, and on `(1,∞)` it is the integrand of
  -- `hdinf` multiplied by the *locally bounded* factor `t ↦ t ^ (q + p)` (note
  -- `t ^ (q - 1) = t ^ (q + p) * t ^ (-p - 1)` for `t > 0`).  Only the first interval of
  -- the conclusion is unbounded, and it is cut off at the finite point `z`.
  rcases le_or_gt z 1 with hz1 | hz1
  · -- `z ≤ 1`: the whole interval `(0,z)` sits inside `(0,1)`.
    have hIoo : MeasureTheory.IntegrableOn
        (fun t : ℝ => t * deriv c t * t ^ (q - 1)) (Set.Ioo 0 z) :=
      hd0.mono_set (fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 hz1⟩)
    have hIoc : MeasureTheory.IntegrableOn
        (fun t : ℝ => t * deriv c t * t ^ (q - 1)) (Set.Ioc 0 z) :=
      (integrableOn_Ioc_iff_integrableOn_Ioo
        (f := fun t : ℝ => t * deriv c t * t ^ (q - 1))).2 hIoo
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hz.le).2 hIoc
  · -- `1 < z`: split `(0,z]` as `(0,1] ∪ (1,z]`.
    have h01 : MeasureTheory.IntegrableOn
        (fun t : ℝ => t * deriv c t * t ^ (q - 1)) (Set.Ioc 0 1) :=
      (integrableOn_Ioc_iff_integrableOn_Ioo
        (f := fun t : ℝ => t * deriv c t * t ^ (q - 1))).2 hd0
    have hG : MeasureTheory.IntegrableOn
        (fun t : ℝ => t * deriv c t * t ^ (-p - 1)) (Set.Ioc 1 z) :=
      hdinf.mono_set (fun t ht => ht.1)
    have hcont : ContinuousOn (fun t : ℝ => t ^ (q + p)) (Set.Ioc 1 z) := by
      intro t ht
      exact (Real.continuousAt_rpow_const t (q + p)
        (Or.inl (ne_of_gt (lt_trans zero_lt_one ht.1)))).continuousWithinAt
    have hmeas : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => t ^ (q + p))
        (MeasureTheory.volume.restrict (Set.Ioc 1 z)) :=
      hcont.aestronglyMeasurable measurableSet_Ioc
    have hbdd : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioc 1 z)),
        ‖t ^ (q + p)‖ ≤ max 1 ((max 1 z) ^ (q + p)) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht.1
      rw [Real.norm_of_nonneg (Real.rpow_nonneg ht0.le _)]
      rcases le_or_gt 0 (q + p) with hexp | hexp
      · -- nonnegative exponent: monotone in the base
        exact le_trans (Real.rpow_le_rpow ht0.le (le_trans ht.2 (le_max_right _ _)) hexp)
          (le_max_right _ _)
      · -- negative exponent: `t ^ (q + p) ≤ 1` for `t ≥ 1`
        have hle1 : t ^ (q + p) ≤ 1 := by
          have h := Real.rpow_le_rpow_of_exponent_le ht.1.le hexp.le
          rwa [Real.rpow_zero] at h
        exact le_trans hle1 (le_max_left _ _)
    have hprod : MeasureTheory.IntegrableOn
        (fun t : ℝ => t * deriv c t * t ^ (-p - 1) * t ^ (q + p)) (Set.Ioc 1 z) :=
      hG.mul_bdd hmeas hbdd
    have hEq : Set.EqOn (fun t : ℝ => t * deriv c t * t ^ (-p - 1) * t ^ (q + p))
        (fun t : ℝ => t * deriv c t * t ^ (q - 1)) (Set.Ioc 1 z) := by
      intro t ht
      have ht0 : 0 < t := lt_trans zero_lt_one ht.1
      have hsplit : t ^ (q - 1) = t ^ (q + p) * t ^ (-p - 1) := by
        have h := Real.rpow_add ht0 (q + p) (-p - 1)
        rw [show (q + p) + (-p - 1) = q - 1 by ring] at h
        exact h
      show t * deriv c t * t ^ (-p - 1) * t ^ (q + p) = t * deriv c t * t ^ (q - 1)
      rw [hsplit]; ring
    have h1z : MeasureTheory.IntegrableOn
        (fun t : ℝ => t * deriv c t * t ^ (q - 1)) (Set.Ioc 1 z) :=
      hprod.congr_fun hEq measurableSet_Ioc
    have hIoc_eq : Set.Ioc (0 : ℝ) z = Set.Ioc 0 1 ∪ Set.Ioc 1 z := by
      ext t
      simp only [Set.mem_Ioc, Set.mem_union]
      constructor
      · rintro ⟨h0, hzt⟩
        rcases le_or_gt t 1 with h | h
        · exact Or.inl ⟨h0, h⟩
        · exact Or.inr ⟨h, hzt⟩
      · rintro (⟨h0, h1⟩ | ⟨h1, hzt⟩)
        · exact ⟨h0, le_trans h1 hz1.le⟩
        · exact ⟨lt_trans zero_lt_one h1, hzt⟩
    have hIoc : MeasureTheory.IntegrableOn
        (fun t : ℝ => t * deriv c t * t ^ (q - 1)) (Set.Ioc 0 z) := by
      rw [hIoc_eq, MeasureTheory.integrableOn_union]
      exact ⟨h01, h1z⟩
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hz.le).2 hIoc

end Work.FTS.ClassCHon.Zpz.RgIbl
