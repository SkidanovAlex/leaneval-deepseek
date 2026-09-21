import Mathlib
import Submission.Work.OddRadon.Core
import Submission.Work.OddRadon.Abel

/-!
# The odd-dimensional profile transform is an Abel transform

For odd `d = 2n+1` (`n ≥ 1`) and an **even** profile `γ`, the one-variable reduction of the
spherical Radon transform, `radonProfile (2n+1) γ c`, is an explicit constant times the forward
Abel-type transform `abelTrans (n - 3/2) γ c`:

  `radonProfile (2n+1) γ c = 2 * |S^{2n-2}| * (c^{2n-2})⁻¹ * ∫_0^c γ s (c² - s²)^{n-3/2} ds`.

The two ingredients are:

* `integral_even_neg_eq_two_mul`: for an even integrand the integral over `[-c, c]` is twice the
  integral over `[0, c]` (unconditionally — the Bochner integral of a non-integrable function is
  `0`, and integrability over the two halves of `[-c,c]` is equivalent);
* `integral_neg_one_one_eq`: the substitution `s ↦ c s` in the normalization interval `[-1,1]`,
  which turns the weight `(1 - s²)^α` into `c^{-(2α+1)} (c² - u²)^α` on `[-c,c]`.

Neither uses any regularity of `γ` beyond its evenness; the continuity hypothesis `hγ` in the
statement of `radonProfile_eq_abelTrans` is part of the interface required by the caller but is
not needed for this identity.
-/

noncomputable section

open MeasureTheory
open scoped RealInnerProductSpace Pointwise Interval Topology

namespace Work.OddRadon

/-- **Integrability over `[-c,0]` and over `[0,c]` is the same for an even function.** -/
lemma intervalIntegrable_even_neg_iff {f : ℝ → ℝ} (hf : ∀ t, f (-t) = f t) (a b : ℝ) :
    IntervalIntegrable f volume (-b) (-a) ↔ IntervalIntegrable f volume a b := by
  have h1 : IntervalIntegrable f volume (-b) (-a) ↔
      IntervalIntegrable (fun x => f (-x)) volume (-(-b)) (-(-a)) :=
    IntervalIntegrable.iff_comp_neg (f := f) (a := -b) (b := -a)
  rw [neg_neg, neg_neg] at h1
  have h2 : IntervalIntegrable (fun x => f (-x)) volume b a ↔
      IntervalIntegrable (fun x => f (-x)) volume a b :=
    ⟨fun h => h.symm, fun h => h.symm⟩
  have h3 : IntervalIntegrable (fun x => f (-x)) volume a b ↔
      IntervalIntegrable f volume a b :=
    ⟨fun h => IntervalIntegrable.congr (fun x _ => hf x) h,
     fun h => IntervalIntegrable.congr (fun x _ => (hf x).symm) h⟩
  exact h1.trans (h2.trans h3)

/-- **The integral of an even function over `[-c,c]` is twice its integral over `[0,c]`.**

The statement is unconditional: if the function fails to be integrable there is nothing to
prove, because `∫_[-c,0]` and `∫_[0,c]` are then both `0` as well. -/
lemma integral_even_neg_eq_two_mul {f : ℝ → ℝ} (hf : ∀ t, f (-t) = f t) {c : ℝ}
    (hc : 0 < c) : (∫ x in (-c)..c, f x) = 2 * ∫ x in (0:ℝ)..c, f x := by
  have hhalf : (∫ x in (-c)..(0:ℝ), f x) = ∫ x in (0:ℝ)..c, f x := by
    have h := intervalIntegral.integral_comp_neg (f := f) (a := -c) (b := (0:ℝ))
    simp only [neg_zero, neg_neg] at h
    rw [← h]
    exact intervalIntegral.integral_congr fun x _ => (hf x).symm
  by_cases h0 : IntervalIntegrable f volume (0:ℝ) c
  · have h1 : IntervalIntegrable f volume (-c) 0 := by
      simpa using (intervalIntegrable_even_neg_iff hf 0 c).mpr h0
    rw [← intervalIntegral.integral_add_adjacent_intervals h1 h0, hhalf]
    ring
  · have hz0 : (∫ x in (0:ℝ)..c, f x) = 0 := intervalIntegral.integral_undef h0
    have hz1 : (∫ x in (-c)..c, f x) = 0 := by
      refine intervalIntegral.integral_undef fun h => h0 ?_
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : -c ≤ c)] at h
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hc.le]
      exact h.mono_set (Set.Ioc_subset_Ioc_left (neg_nonpos.mpr hc.le))
    rw [hz0, hz1]
    ring

/-- **The substitution `s = u / c` on the normalization interval.**

For `c > 0`, any `α : ℝ` and any `G : ℝ → ℝ`,

  `∫_{-1}^{1} (1 - s²)^α G (c s) ds = c^{-(2α+1)} ∫_{-c}^{c} (c² - u²)^α G u du`,

the pointwise identity being `(1 - s²)^α = c^{-2α} (c² - (c s)²)^α` and `(c² - (cs)²)^α du`
being tied to `(1-s²)^α ds` by the Jacobian factor `c^{2α+1}`. -/
lemma integral_neg_one_one_eq {α c : ℝ} (G : ℝ → ℝ) (hc : 0 < c) :
    (∫ s in (-1:ℝ)..1, (1 - s^2)^α * G (c * s))
      = c^(-(2*α+1)) * (∫ u in (-c)..c, (c^2 - u^2)^α * G u) := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hc2 : 0 < c^2 := by positivity
  have hcongr : (∫ s in (-1:ℝ)..1, (1 - s^2)^α * G (c * s))
      = ∫ s in (-1:ℝ)..1, c^(-(2*α)) * ((c^2 - (c*s)^2)^α * G (c*s)) := by
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp only
    rw [Set.uIcc_of_le (by norm_num : (-1:ℝ) ≤ 1)] at hs
    have hs2 : 0 ≤ 1 - s^2 := by nlinarith [hs.1, hs.2]
    have hne : c^(2*α) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hc (2*α))
    have h3 : (c^2 : ℝ)^α = c^(2*α) := by
      rw [← Real.rpow_two, Real.rpow_mul hc.le]
    have step : (1 - s^2)^α = c^(-(2*α)) * (c^2 - (c*s)^2)^α := by
      rw [show c^2 - (c*s)^2 = c^2 * (1 - s^2) by ring,
        Real.mul_rpow hc2.le hs2, h3, Real.rpow_neg hc.le (2*α)]
      rw [inv_mul_cancel_left₀ hne]
    rw [step]; ring
  rw [hcongr, intervalIntegral.integral_const_mul]
  have hcomp : (∫ s in (-1:ℝ)..1, (c^2 - (c*s)^2)^α * G (c*s))
      = c⁻¹ * (∫ u in (-c)..c, (c^2 - u^2)^α * G u) := by
    have h := intervalIntegral.integral_comp_mul_left (f := fun u => (c^2 - u^2)^α * G u)
      (a := (-1:ℝ)) (b := 1) hcne
    simpa only [mul_neg, mul_one, smul_eq_mul] using h
  rw [hcomp, ← Real.rpow_neg_one c, ← mul_assoc, ← Real.rpow_add hc]
  congr 1
  ring_nf

set_option linter.unusedVariables false in
theorem radonProfile_eq_abelTrans (n : ℕ) (hn : 1 ≤ n) {γ : ℝ → ℝ}
    (hγ : ContinuousOn γ (Set.Icc (-1) 1)) (heven : ∀ t, γ (-t) = γ t)
    {c : ℝ} (hc : 0 < c) :
    radonProfile (2 * n + 1) γ c
      = 2 * sphereArea (2 * n - 2) * (c ^ (2 * n - 2))⁻¹
          * abelTrans ((n : ℝ) - 3 / 2) γ c := by
  set α : ℝ := (n : ℝ) - 3 / 2 with hαdef
  have hcast : ((2 * n + 1 : ℕ) : ℝ) = 2 * (n : ℝ) + 1 := by push_cast; ring
  have hexp : ((2 * n + 1 : ℕ) : ℝ) / 2 - 2 = α := by rw [hαdef, hcast]; ring
  have hsub : 2 * n + 1 - 3 = 2 * n - 2 := by omega
  have hnat : ((2 * n - 2 : ℕ) : ℝ) = 2 * (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ 2 * n)]
    push_cast
    ring
  have h2a : 2 * α + 1 = ((2 * n - 2 : ℕ) : ℝ) := by rw [hαdef, hnat]; ring
  have hpow : c ^ (-(2 * α + 1)) = (c ^ (2 * n - 2))⁻¹ := by
    rw [Real.rpow_neg hc.le, h2a, Real.rpow_natCast]
  have habel : (∫ u in (0:ℝ)..c, (c ^ 2 - u ^ 2) ^ α * γ u) = abelTrans α γ c := by
    rw [abelTrans]
    exact intervalIntegral.integral_congr fun x _ => by ring
  simp only [radonProfile, hsub, hexp]
  rw [integral_neg_one_one_eq (G := γ) (α := α) hc]
  rw [integral_even_neg_eq_two_mul (f := fun u => (c ^ 2 - u ^ 2) ^ α * γ u) ?_ hc]
  · rw [habel, hpow]
    ring
  · intro t
    rw [neg_sq, heven t]

end Work.OddRadon
