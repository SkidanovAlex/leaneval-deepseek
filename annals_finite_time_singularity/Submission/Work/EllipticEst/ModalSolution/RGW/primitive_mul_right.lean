import Mathlib.MeasureTheory.Integral.Prod

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.ModalSolution.RGW

open MeasureTheory Set
open scoped Topology

/-- For `z ∈ [a,b]`, the integral of `g` over `z..b` is the set integral over `Ioc a b` of the
indicator of `Ioi z` against `g`. -/
private lemma integral_indicator_Ioi {a b z : ℝ} (haz : a ≤ z) (hzb : z ≤ b) {g : ℝ → ℝ} :
    ∫ t, (Set.Ioi z).indicator g t ∂(volume.restrict (Set.Ioc a b)) = ∫ t in z..b, g t := by
  rw [intervalIntegral.integral_of_le hzb]
  rw [MeasureTheory.setIntegral_indicator measurableSet_Ioi]
  have hset : Set.Ioc a b ∩ Set.Ioi z = Set.Ioc z b := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro ⟨⟨-, htb⟩, hzt⟩; exact ⟨hzt, htb⟩
    · rintro ⟨hzt, htb⟩; exact ⟨⟨lt_of_le_of_lt haz hzt, htb⟩, hzt⟩
  rw [hset]

/-- For `t ∈ [a,b]`, the integral of `f` over `a..t` is the set integral over `Ioc a b` of `f`
weighted by the indicator of `Iio t`. -/
private lemma integral_indicator_Iio {a b t : ℝ} (hat : a ≤ t) (htb : t ≤ b) {f : ℝ → ℝ} :
    ∫ z, f z * (Set.Iio t).indicator (fun _ => (1 : ℝ)) z ∂(volume.restrict (Set.Ioc a b))
      = ∫ z in a..t, f z := by
  have h1 : ∀ z, f z * (Set.Iio t).indicator (fun _ => (1 : ℝ)) z
      = (Set.Iio t).indicator f z := by
    intro z
    by_cases hz : z ∈ Set.Iio t
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, mul_one]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, mul_zero]
  simp only [h1]
  rw [intervalIntegral.integral_of_le hat]
  rw [MeasureTheory.setIntegral_indicator measurableSet_Iio]
  have hset : Set.Ioc a b ∩ Set.Iio t = Set.Ioo a t := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iio, Set.mem_Ioo]
    constructor
    · rintro ⟨⟨haz, -⟩, hzt⟩; exact ⟨haz, hzt⟩
    · rintro ⟨haz, hzt⟩; exact ⟨⟨haz, le_trans hzt.le htb⟩, hzt⟩
  rw [hset, ← MeasureTheory.integral_Ioc_eq_integral_Ioo]

theorem primitive_mul_right {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume a b) (hf : IntervalIntegrable f volume a b) :
    ∫ z in a..b, (∫ t in z..b, g t) * f z = ∫ t in a..b, g t * (∫ z in a..t, f z) := by
  have hfI : Integrable f (volume.restrict (Set.Ioc a b)) := hf.1
  have hgI : Integrable g (volume.restrict (Set.Ioc a b)) := hg.1
  -- the joint integrand on the square `(a,b] × (a,b]`
  have hJ : Integrable (fun p : ℝ × ℝ => (if p.1 < p.2 then f p.1 * g p.2 else 0))
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc a b))) := by
    have hbase : Integrable (fun p : ℝ × ℝ => f p.1 * g p.2)
        ((volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc a b))) :=
      hfI.mul_prod hgI
    have hmeas : MeasurableSet ({p : ℝ × ℝ | p.1 < p.2}) :=
      (isOpen_lt continuous_fst continuous_snd).measurableSet
    have heq : ({p : ℝ × ℝ | p.1 < p.2}.indicator (fun p => f p.1 * g p.2))
        = fun p : ℝ × ℝ => (if p.1 < p.2 then f p.1 * g p.2 else 0) := by
      funext p; rw [Set.indicator_apply]; rfl
    have hb := hbase.indicator hmeas
    rw [heq] at hb
    exact hb
  -- the left-hand side as an iterated integral over the square
  have hL1 : ∫ z in Set.Ioc a b, (∫ t in z..b, g t) * f z
      = ∫ z, ∫ t, (if z < t then f z * g t else 0)
          ∂(volume.restrict (Set.Ioc a b)) ∂(volume.restrict (Set.Ioc a b)) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with z hz
    have haz : a ≤ z := hz.1.le
    have hzb : z ≤ b := hz.2
    rw [← integral_indicator_Ioi (a := a) (b := b) haz hzb (g := g),
      ← MeasureTheory.integral_mul_const]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro t
    change (Set.Ioi z).indicator g t * f z = (if z < t then f z * g t else 0)
    by_cases h : z < t
    · rw [Set.indicator_of_mem (Set.mem_Ioi.mpr h), if_pos h]; ring
    · rw [Set.indicator_of_notMem (by simp only [Set.mem_Ioi]; exact h), if_neg h, zero_mul]
  -- the right-hand side as the same iterated integral, in the other order
  have hR1 : ∫ t in Set.Ioc a b, g t * (∫ z in a..t, f z)
      = ∫ t, ∫ z, (if z < t then f z * g t else 0)
          ∂(volume.restrict (Set.Ioc a b)) ∂(volume.restrict (Set.Ioc a b)) := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    have hat : a ≤ t := ht.1.le
    have htb : t ≤ b := ht.2
    rw [← integral_indicator_Iio (a := a) (b := b) hat htb (f := f),
      ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro z
    change g t * (f z * (Set.Iio t).indicator (fun _ => (1 : ℝ)) z)
      = (if z < t then f z * g t else 0)
    by_cases h : z < t
    · rw [Set.indicator_of_mem (Set.mem_Iio.mpr h), if_pos h]; ring
    · rw [Set.indicator_of_notMem (by simp only [Set.mem_Iio]; exact h), if_neg h]
      ring
  have hL : ∫ z in a..b, (∫ t in z..b, g t) * f z
      = ∫ t, ∫ z, (if z < t then f z * g t else 0)
          ∂(volume.restrict (Set.Ioc a b)) ∂(volume.restrict (Set.Ioc a b)) :=
    (intervalIntegral.integral_of_le hab).trans
      (hL1.trans (MeasureTheory.integral_integral_swap hJ))
  have hR : ∫ t in a..b, g t * (∫ z in a..t, f z)
      = ∫ t, ∫ z, (if z < t then f z * g t else 0)
          ∂(volume.restrict (Set.Ioc a b)) ∂(volume.restrict (Set.Ioc a b)) :=
    (intervalIntegral.integral_of_le hab).trans hR1
  exact hL.trans hR.symm

end Work.EllipticEst.ModalSolution.RGW
