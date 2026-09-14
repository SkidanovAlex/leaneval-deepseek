import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory Set

/-!
# The sliding-window estimate for the Lebesgue integral on the line

For `0 < s` and an almost everywhere measurable `F : ℝ → ENNReal`,

`∫⁻ t in (a, b - s], ∫⁻ u in (t, t + s], F u ≤ ofReal s * ∫⁻ u in (a, b], F u`.

This is the elementary Tonelli/Fubini estimate underlying the "sliding" difference-quotient
inequality used in the PDE approach to the hyperbolic `N`-body problem: sliding the window
`(t, t+s]` along `t ∈ (a, b-s]` covers every point of `(a,b]` with multiplicity at most `s`.
No relation between `a` and `b` is needed: the estimate holds trivially when the windows are
empty.
-/

namespace Commons.MeasureTheory.Integral

/-- Change of variable `u = t + w` for the sliding window, turning the interval `(t, t+s]`
into the fixed window `(0, s]`. -/
private lemma lintegral_Ioc_add_eq (F : ℝ → ENNReal) (t s : ℝ) :
    (∫⁻ u in Set.Ioc t (t + s), F u) = ∫⁻ w in Set.Ioc (0 : ℝ) s, F (t + w) := by
  have h1 : (∫⁻ u in Set.Ioc t (t + s), F u)
      = ∫⁻ u, (Set.Ioc t (t + s)).indicator F u :=
    (lintegral_indicator measurableSet_Ioc F).symm
  have h2 : (∫⁻ u, (Set.Ioc t (t + s)).indicator F u)
      = ∫⁻ w, (Set.Ioc t (t + s)).indicator F (w + t) :=
    (lintegral_add_right_eq_self ((Set.Ioc t (t + s)).indicator F) t).symm
  have h3 : (∫⁻ w, (Set.Ioc t (t + s)).indicator F (w + t))
      = ∫⁻ w in Set.Ioc (0 : ℝ) s, F (w + t) := by
    rw [← lintegral_indicator measurableSet_Ioc (fun w => F (w + t))]
    refine lintegral_congr (fun w => ?_)
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hw : w ∈ Set.Ioc (0 : ℝ) s
    · have hwt : w + t ∈ Set.Ioc t (t + s) := ⟨by linarith [hw.1], by linarith [hw.2]⟩
      rw [if_pos hwt, if_pos hw]
    · have hwt : w + t ∉ Set.Ioc t (t + s) :=
        fun hc => hw ⟨by linarith [hc.1], by linarith [hc.2]⟩
      rw [if_neg hwt, if_neg hw]
  have h4 : (∫⁻ w in Set.Ioc (0 : ℝ) s, F (w + t))
      = ∫⁻ w in Set.Ioc (0 : ℝ) s, F (t + w) :=
    setLIntegral_congr_fun measurableSet_Ioc (fun w _ => by rw [add_comm])
  rw [h1, h2, h3, h4]

/-- Shifting the integration variable by `w` moves `(a, b-s]` into `(a, b]` when `w ∈ (0, s]`. -/
private lemma setLIntegral_Ioc_add_le (F : ℝ → ENNReal) {a b s w : ℝ}
    (hw : w ∈ Set.Ioc (0 : ℝ) s) :
    (∫⁻ t in Set.Ioc a (b - s), F (t + w)) ≤ ∫⁻ u in Set.Ioc a b, F u := by
  classical
  have hshift : (∫⁻ t in Set.Ioc a (b - s), F (t + w))
      = ∫⁻ u in (fun t => t + w) '' Set.Ioc a (b - s), F u := by
    have h1 : (∫⁻ t in Set.Ioc a (b - s), F (t + w))
        = ∫⁻ t, (Set.Ioc a (b - s)).indicator (fun t => F (t + w)) t :=
      (lintegral_indicator measurableSet_Ioc _).symm
    have h2 : (∫⁻ t, (Set.Ioc a (b - s)).indicator (fun t => F (t + w)) t)
        = ∫⁻ u, ((fun t => t + w) '' Set.Ioc a (b - s)).indicator F (u + w) := by
      refine lintegral_congr (fun t => ?_)
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases ht : t ∈ Set.Ioc a (b - s)
      · have hmem : t + w ∈ (fun t => t + w) '' Set.Ioc a (b - s) := ⟨t, ht, rfl⟩
        rw [if_pos ht, if_pos hmem]
      · have hmem : t + w ∉ (fun t => t + w) '' Set.Ioc a (b - s) := by
          rintro ⟨t', ht', heq⟩
          have h' : t' = t := by linarith
          exact ht (h' ▸ ht')
        rw [if_neg ht, if_neg hmem]
    have h3 : (∫⁻ u, ((fun t => t + w) '' Set.Ioc a (b - s)).indicator F (u + w))
        = ∫⁻ u, ((fun t => t + w) '' Set.Ioc a (b - s)).indicator F u :=
      lintegral_add_right_eq_self _ w
    have h4 : (∫⁻ u, ((fun t => t + w) '' Set.Ioc a (b - s)).indicator F u)
        = ∫⁻ u in (fun t => t + w) '' Set.Ioc a (b - s), F u :=
      lintegral_indicator (by rw [Set.image_add_const_Ioc]; exact measurableSet_Ioc) F
    rw [h1, h2, h3, h4]
  rw [hshift]
  refine lintegral_mono' (Measure.restrict_mono ?_ (le_refl volume)) le_rfl
  rw [Set.image_add_const_Ioc]
  exact Set.Ioc_subset_Ioc (by linarith [hw.1]) (by linarith [hw.2])

/-- The sliding-window estimate for a measurable `F`. -/
private lemma lintegral_Ioc_sliding_le_measurable {a b s : ℝ}
    (F : ℝ → ENNReal) (hF : Measurable F) :
    (∫⁻ t in Set.Ioc a (b - s), ∫⁻ u in Set.Ioc t (t + s), F u)
      ≤ ENNReal.ofReal s * ∫⁻ u in Set.Ioc a b, F u := by
  classical
  have hstep : (∫⁻ t in Set.Ioc a (b - s), ∫⁻ u in Set.Ioc t (t + s), F u)
      = ∫⁻ t in Set.Ioc a (b - s), ∫⁻ w in Set.Ioc (0 : ℝ) s, F (t + w) :=
    setLIntegral_congr_fun measurableSet_Ioc (fun t _ => lintegral_Ioc_add_eq F t s)
  have hf : AEMeasurable (fun z : ℝ × ℝ => F (z.1 + z.2))
      ((volume.prod volume).restrict (Set.Ioc a (b - s) ×ˢ Set.Ioc (0 : ℝ) s)) :=
    ((hF.comp (measurable_fst.add measurable_snd)).aemeasurable).restrict
  have hswap : (∫⁻ t in Set.Ioc a (b - s), ∫⁻ w in Set.Ioc (0 : ℝ) s, F (t + w))
      = ∫⁻ w in Set.Ioc (0 : ℝ) s, ∫⁻ t in Set.Ioc a (b - s), F (t + w) :=
    (setLIntegral_prod (μ := volume) (ν := volume)
        (s := Set.Ioc a (b - s)) (t := Set.Ioc (0 : ℝ) s)
        (fun z : ℝ × ℝ => F (z.1 + z.2)) hf).symm.trans
      (setLIntegral_prod_symm (μ := volume) (ν := volume)
        (s := Set.Ioc a (b - s)) (t := Set.Ioc (0 : ℝ) s)
        (fun z : ℝ × ℝ => F (z.1 + z.2)) hf)
  rw [hstep, hswap]
  calc (∫⁻ w in Set.Ioc (0 : ℝ) s, ∫⁻ t in Set.Ioc a (b - s), F (t + w))
      ≤ ∫⁻ w in Set.Ioc (0 : ℝ) s, ∫⁻ u in Set.Ioc a b, F u :=
        setLIntegral_mono' measurableSet_Ioc (fun w hw => setLIntegral_Ioc_add_le F hw)
    _ = (∫⁻ u in Set.Ioc a b, F u) * ENNReal.ofReal s := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero]
    _ = ENNReal.ofReal s * ∫⁻ u in Set.Ioc a b, F u := mul_comm _ _

theorem lintegral_Ioc_sliding_le {a b s : ℝ} (hs : 0 < s)
    (F : ℝ → ENNReal) (hF : AEMeasurable F MeasureTheory.volume) :
    (∫⁻ t in Set.Ioc a (b - s), ∫⁻ u in Set.Ioc t (t + s), F u)
      ≤ ENNReal.ofReal s * ∫⁻ u in Set.Ioc a b, F u := by
  classical
  have hae : ∀ᵐ x ∂MeasureTheory.volume, F x = hF.mk F x := hF.ae_eq_mk
  have hLHS : (∫⁻ t in Set.Ioc a (b - s), ∫⁻ u in Set.Ioc t (t + s), F u)
      = (∫⁻ t in Set.Ioc a (b - s), ∫⁻ u in Set.Ioc t (t + s), hF.mk F u) :=
    setLIntegral_congr_fun measurableSet_Ioc
      (fun t _ => setLIntegral_congr_fun_ae measurableSet_Ioc (hae.mono (fun x hx _ => hx)))
  have hRHS : (∫⁻ u in Set.Ioc a b, F u) = ∫⁻ u in Set.Ioc a b, hF.mk F u :=
    setLIntegral_congr_fun_ae measurableSet_Ioc (hae.mono (fun x hx _ => hx))
  rw [hLHS, hRHS]
  exact lintegral_Ioc_sliding_le_measurable (hF.mk F) hF.measurable_mk

end Commons.MeasureTheory.Integral