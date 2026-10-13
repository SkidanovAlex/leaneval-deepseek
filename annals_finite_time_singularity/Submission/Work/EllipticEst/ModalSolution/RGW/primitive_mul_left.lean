import Mathlib.MeasureTheory.Integral.Prod

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.ModalSolution.RGW

open MeasureTheory

theorem primitive_mul_left {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume a b) (hf : IntervalIntegrable f volume a b) :
    ∫ z in a..b, (∫ t in a..z, g t) * f z = ∫ t in a..b, g t * (∫ z in t..b, f z) := by
  set F : ℝ → ℝ → ℝ := fun x y => if y ≤ x then g y * f x else 0 with hF
  have hgint : Integrable g (volume.restrict (Set.uIoc a b)) := by
    rw [Set.uIoc_of_le hab]; exact hg.1
  have hfint : Integrable f (volume.restrict (Set.uIoc a b)) := by
    rw [Set.uIoc_of_le hab]; exact hf.1
  have hbase : Integrable (fun p : ℝ × ℝ => g p.2 * f p.1)
      ((volume.restrict (Set.uIoc a b)).prod (volume.restrict (Set.uIoc a b))) :=
    (Integrable.mul_prod hfint hgint).congr
      (Filter.Eventually.of_forall (fun p => by ring))
  have hFint : IntegrableOn (Function.uncurry F) (Set.uIoc a b ×ˢ Set.uIoc a b) volume := by
    rw [IntegrableOn, MeasureTheory.Measure.volume_eq_prod ℝ ℝ,
      ← MeasureTheory.Measure.prod_restrict]
    have hs : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} := measurableSet_le measurable_snd measurable_fst
    refine (hbase.indicator hs).congr (Filter.Eventually.of_forall (fun p => ?_))
    simp only [Function.uncurry, Set.indicator_apply, Set.mem_setOf_eq, hF]
  have hswap := MeasureTheory.intervalIntegral_intervalIntegral_swap (F := F)
    (a := a) (b := b) (c := a) (d := b) hFint
  have hL : ∀ x ∈ Set.Ioc a b, (∫ t in a..x, g t) * f x = ∫ y in a..b, F x y := by
    intro x hx
    obtain ⟨hax, hxb⟩ := hx
    have hax' : a ≤ x := le_of_lt hax
    rw [intervalIntegral.integral_of_le hab]
    rw [show (∫ y in Set.Ioc a b, F x y)
          = ∫ y in Set.Ioc a b, (Set.Iic x).indicator (fun y => g y * f x) y from
        setIntegral_congr_fun measurableSet_Ioc
          (fun y _ => by simp only [hF, Set.indicator_apply, Set.mem_Iic])]
    rw [MeasureTheory.setIntegral_indicator measurableSet_Iic]
    rw [show Set.Ioc a b ∩ Set.Iic x = Set.Ioc a x by
        rw [Set.Ioc_inter_Iic, inf_eq_right.mpr hxb]]
    rw [MeasureTheory.integral_mul_const, ← intervalIntegral.integral_of_le hax']
  have hR : ∀ t ∈ Set.Ioc a b, g t * (∫ z in t..b, f z) = ∫ z in a..b, F z t := by
    intro t ht
    obtain ⟨hat, htb⟩ := ht
    rw [intervalIntegral.integral_of_le hab]
    rw [show (∫ z in Set.Ioc a b, F z t)
          = ∫ z in Set.Ioc a b, (Set.Ici t).indicator (fun z => g t * f z) z from
        setIntegral_congr_fun measurableSet_Ioc
          (fun z _ => by simp only [hF, Set.indicator_apply, Set.mem_Ici])]
    rw [MeasureTheory.setIntegral_indicator measurableSet_Ici]
    rw [show Set.Ioc a b ∩ Set.Ici t = Set.Icc t b by
        ext z; simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, Set.mem_Icc]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h3, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, h2⟩, h1⟩]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le htb]
  calc
    ∫ z in a..b, (∫ t in a..z, g t) * f z
        = ∫ z in Set.Ioc a b, (∫ t in a..z, g t) * f z := intervalIntegral.integral_of_le hab
    _ = ∫ z in Set.Ioc a b, (∫ y in a..b, F z y) :=
          setIntegral_congr_fun measurableSet_Ioc (fun z hz => hL z hz)
    _ = ∫ z in a..b, (∫ y in a..b, F z y) := (intervalIntegral.integral_of_le hab).symm
    _ = ∫ y in a..b, (∫ z in a..b, F z y) := hswap
    _ = ∫ y in Set.Ioc a b, (∫ z in a..b, F z y) := intervalIntegral.integral_of_le hab
    _ = ∫ y in Set.Ioc a b, g y * (∫ z in y..b, f z) :=
          setIntegral_congr_fun measurableSet_Ioc (fun y hy => (hR y hy).symm)
    _ = ∫ y in a..b, g y * (∫ z in y..b, f z) := (intervalIntegral.integral_of_le hab).symm

end Work.EllipticEst.ModalSolution.RGW
