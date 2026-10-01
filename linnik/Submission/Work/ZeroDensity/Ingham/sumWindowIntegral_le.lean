import Mathlib
import Submission.Work.ZeroDensity.Montgomery.sepCardLe

open MeasureTheory intervalIntegral
open scoped BigOperators

namespace Work.ZeroDensity.Ingham

/-- **Sharp pointwise Montgomery window bound.**  For a finite set `Sp` of `1`-separated reals
contained in `[-T, T]` and any nonnegative `f`, the number of windows `(s - S, s + S]` (`s ∈ Sp`)
containing a fixed point `x` is at most `2 * S + 1` (for `S ≥ 1`), and a window containing `x`
forces `x ∈ (-(T + S), T + S]`.  Hence the indicator-weighted sum is bounded by
`(2 * S + 1) * f x` on that interval and by `0` outside it.

This is the sharp version of `Work.ZeroDensity.Montgomery.windowPointwiseLe`, whose outer interval
is one unit wider on each side. -/
theorem windowPointwiseLe_sharp {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    {Sp : Finset ℝ} {S T : ℝ} (hS : 1 ≤ S) (_hT : 0 ≤ T)
    (hsep : ∀ s ∈ Sp, ∀ s' ∈ Sp, s ≠ s' → 1 ≤ |s - s'|)
    (hbd : ∀ s ∈ Sp, |s| ≤ T) (x : ℝ) :
    ∑ s ∈ Sp, (Set.Ioc (s - S) (s + S)).indicator f x
      ≤ (2 * S + 1) * (Set.Ioc (-(T + S)) (T + S)).indicator f x := by
  classical
  set A : Finset ℝ := Sp.filter (fun s => x ∈ Set.Ioc (s - S) (s + S)) with hA
  have hmf : ∀ s : ℝ, s ∈ A ↔ s ∈ Sp ∧ x ∈ Set.Ioc (s - S) (s + S) := by
    intro s
    simp only [hA, Finset.mem_filter]
  have hsum : ∑ s ∈ Sp, (Set.Ioc (s - S) (s + S)).indicator f x = (A.card : ℝ) * f x := by
    have h1 : ∑ s ∈ Sp, (Set.Ioc (s - S) (s + S)).indicator f x
        = ∑ s ∈ Sp, (if x ∈ Set.Ioc (s - S) (s + S) then f x else 0) := by
      apply Finset.sum_congr rfl
      intro s _
      rw [Set.indicator_apply]
    have h2 : ∑ s ∈ Sp, (if x ∈ Set.Ioc (s - S) (s + S) then f x else 0)
        = ∑ s ∈ Sp.filter (fun s => x ∈ Set.Ioc (s - S) (s + S)), f x :=
      (Finset.sum_filter (s := Sp) (p := fun s => x ∈ Set.Ioc (s - S) (s + S))
        (f := fun _ => f x)).symm
    have h3 : ∑ s ∈ Sp.filter (fun s => x ∈ Set.Ioc (s - S) (s + S)), f x
        = (A.card : ℝ) * f x := by
      rw [← hA]
      rw [Finset.sum_const, nsmul_eq_mul]
    exact h1.trans (h2.trans h3)
  rw [hsum]
  by_cases hx : x ∈ Set.Ioc (-(T + S)) (T + S)
  · rw [Set.indicator_of_mem hx f]
    have hcardbound : (A.card : ℝ) ≤ 2 * S + 1 := by
      have hle : (A.card : ℝ) ≤ (x + S) - (x - S) + 1 := by
        apply Work.ZeroDensity.Montgomery.sepCardLe
        · linarith
        · intro s hs s' hs' hne
          exact hsep s ((hmf s).mp hs).1 s' ((hmf s').mp hs').1 hne
        · intro s hs
          obtain ⟨hsSp, hxw⟩ := (hmf s).mp hs
          rw [Set.mem_Ioc] at hxw
          exact ⟨by linarith [hxw.2], by linarith [hxw.1]⟩
      linarith
    exact mul_le_mul_of_nonneg_right hcardbound (hf0 x)
  · rw [Set.indicator_of_notMem hx f, mul_zero]
    have hAempty : A = ∅ := by
      refine Finset.eq_empty_iff_forall_notMem.mpr (fun s hs => ?_)
      obtain ⟨hsSp, hxw⟩ := (hmf s).mp hs
      rw [Set.mem_Ioc] at hxw
      have hsT : |s| ≤ T := hbd s hsSp
      have hsge : -T ≤ s := (abs_le.mp hsT).1
      have hsle : s ≤ T := (abs_le.mp hsT).2
      have hxle : x ≤ T + S := by linarith [hxw.2, hsle]
      have hxgt : -(T + S) < x := by linarith [hxw.1, hsge]
      exact hx (by rw [Set.mem_Ioc]; exact ⟨hxgt, hxle⟩)
    rw [hAempty]
    simp

/-- **Overlap bound for the windows of a `1`-separated set.**  Let `S` be a finite set of reals
that is `1`-separated and contained in `[-T, T]`, let `1 ≤ L`, and let `F : ℝ → ℝ` be continuous
and nonnegative.  Then the sum over `x ∈ S` of the integrals of `F` over the windows
`[x - L, x + L]` is at most `(2 * L + 1)` times the integral of `F` over `[-(T + L), T + L]`. -/
theorem sumWindowIntegral_le (F : ℝ → ℝ) {L T : ℝ} (hL : 1 ≤ L) (hT : 0 ≤ T)
    (hF : Continuous F) (hF0 : ∀ x, 0 ≤ F x) {S : Finset ℝ}
    (hbd : ∀ x ∈ S, |x| ≤ T) (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) :
    ∑ x ∈ S, (∫ t in (x - L)..(x + L), F t) ≤ (2 * L + 1) * ∫ t in (-(T + L))..(T + L), F t := by
  have Hpt : ∀ x : ℝ, ∑ s ∈ S, (Set.Ioc (s - L) (s + L)).indicator F x
      ≤ (2 * L + 1) * (Set.Ioc (-(T + L)) (T + L)).indicator F x :=
    fun x => windowPointwiseLe_sharp hF0 hL hT hsep hbd x
  have hM : -(T + L) ≤ T + L := by linarith
  have hint : ∀ s ∈ S, Integrable ((Set.Ioc (s - L) (s + L)).indicator F) := by
    intro s _
    exact (integrable_indicator_iff measurableSet_Ioc).2 (hF.integrableOn_Ioc (μ := volume))
  have hsingle : ∀ s ∈ S, (∫ x, (Set.Ioc (s - L) (s + L)).indicator F x)
      = ∫ x in (s - L)..(s + L), F x := by
    intro s _
    have hle : s - L ≤ s + L := by linarith
    rw [MeasureTheory.integral_indicator measurableSet_Ioc]
    exact (intervalIntegral.integral_of_le hle).symm
  have hsumint : Integrable (fun x => ∑ s ∈ S, (Set.Ioc (s - L) (s + L)).indicator F x) :=
    MeasureTheory.integrable_finsetSum S hint
  have hIocInt : Integrable ((Set.Ioc (-(T + L)) (T + L)).indicator F) :=
    (integrable_indicator_iff measurableSet_Ioc).2 (hF.integrableOn_Ioc (μ := volume))
  have hRint : Integrable
      (fun x => (2 * L + 1) * (Set.Ioc (-(T + L)) (T + L)).indicator F x) :=
    hIocInt.const_mul _
  calc ∑ s ∈ S, ∫ x in (s - L)..(s + L), F x
      = ∑ s ∈ S, ∫ x, (Set.Ioc (s - L) (s + L)).indicator F x :=
        Finset.sum_congr rfl (fun s hs => (hsingle s hs).symm)
    _ = ∫ x, ∑ s ∈ S, (Set.Ioc (s - L) (s + L)).indicator F x :=
        (MeasureTheory.integral_finsetSum S hint).symm
    _ ≤ ∫ x, (2 * L + 1) * (Set.Ioc (-(T + L)) (T + L)).indicator F x :=
        MeasureTheory.integral_mono hsumint hRint Hpt
    _ = (2 * L + 1) * ∫ x, (Set.Ioc (-(T + L)) (T + L)).indicator F x :=
        MeasureTheory.integral_const_mul (2 * L + 1)
          (fun x => (Set.Ioc (-(T + L)) (T + L)).indicator F x)
    _ = (2 * L + 1) * ∫ x in (-(T + L))..(T + L), F x := by
        rw [MeasureTheory.integral_indicator measurableSet_Ioc,
          intervalIntegral.integral_of_le hM]

end Work.ZeroDensity.Ingham
