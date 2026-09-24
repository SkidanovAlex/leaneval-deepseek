import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.prof
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiDelay
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiSharpCrude
import Submission.Work.NumberTheory.Chen.APSwitchUpper.crudeLevelBounds
import Submission.Work.NumberTheory.Chen.APSwitchUpper.crudeUV_intervalIntegrable
import Submission.Work.NumberTheory.Chen.ApSumTenth.TailAux
import Submission.Work.NumberTheory.Chen.ApSumTenth.riPhi_delay_identity
import Submission.Work.NumberTheory.Chen.ApSumTenth.riPhi_delay_system

namespace Work.ChenPlan.LinearSieve.JR2

open MeasureTheory
open Work.NumberTheory.Chen.APSwitchUpper

noncomputable section

/-!
# `riUp` and `riPsi` are Lipschitz on `[2, ∞)`

The Rosser–Iwaniec delay pair `(riPhi, riPsi)` (`APSwitchUpper.prof`), with `riUp = 1 + riPhi`,
satisfies the summed delay identities

* `s * riPhi s = (3 - s)·1_{s ≤ 3} + ∫_{Ici (max (s-1) 2)} riPsi`   (`s ≥ 1`),
* `s * riPsi s = ∫_{Ici (s-1)} riPhi`                               (`s ≥ 2`),

proved in `ApSumTenth/riPhi_delay_identity.lean` / `riPhi_delay_system.lean`.  Together with the
two crude pointwise bounds of the campaign,

* `riPhi ≤ crudeU ≤ 8` on `[1,∞)`   (`crudeUV_intervalIntegrable.crudeU_norm_le`),
* `riPsi ≤ crudeV ≤ 6` on `[2,∞)`   (`riPhiSharpCrude.crudeV`),

and the half-line difference estimate `∫_{Ici a} f - ∫_{Ici b} f = ∫_a^b f`
(`intervalIntegral.integral_Ici_sub_Ici'`) they give Lipschitz bounds with the explicit constant
`100` on `[2,∞)`:

```
|riUp s - riUp t| ≤ 100 (s - t),   |riPsi s - riPsi t| ≤ 100 (s - t)     (2 ≤ t ≤ s).
```

The mechanism is the classical one: differencing `u ↦ u·riPhi u` resp. `u ↦ u·riPsi u` at `s` and
`t` turns the difference into the integral of the *other* profile over the short interval
`[t-1, s-1]`, whence `|s·f s - t·f t| ≤ M (s-t)`; subtracting `(s-t)·f t` and dividing by `s ≥ 2`
gives the claim.  The range `[2,3]` of the `riPhi` half is handled directly from the
`(3-s)`-term (there the two half-line integrals cancel), which is also why the domain restriction
`2 ≤ t` is needed: `riPsi` jumps at `s = 2`.
-/

/-! ## Pointwise bounds on the pair -/

/-- `riPhi ≤ 8` on `[1,∞)`: the crude majorant `crudeU` is bounded by `8` (`crudeU_norm_le`). -/
private lemma riPhi_le_eight {x : ℝ} (hx : 1 ≤ x) : riPhi x ≤ 8 := by
  have h1 : riPhi x ≤ crudeU x := Work.NumberTheory.Chen.ApSumTenth.riPhi_le_crudeU hx
  have h2 : crudeU x ≤ 8 := by
    have h := crudeU_norm_le x
    rw [Real.norm_eq_abs] at h
    linarith [(abs_le.mp h).2]
  linarith

/-- `riPsi ≤ 6` on `[2,∞)`: `crudeV s = 6 e^{2-s} ≤ 6` there. -/
private lemma riPsi_le_six {x : ℝ} (hx : 2 ≤ x) : riPsi x ≤ 6 := by
  have h1 : riPsi x ≤ crudeV x := Work.NumberTheory.Chen.ApSumTenth.riPsi_le_crudeV hx
  have h2 : crudeV x ≤ 6 := by
    rw [show crudeV x = 6 * Real.exp (2 - x) from rfl]
    have : Real.exp (2 - x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  linarith

/-! ## The half-line difference estimate -/

/-- If `f ≥ 0` on `[a,∞)`, `f ≤ M` on `[a,∞)` and `f` is integrable on `Ici a`, then the two
half-line integrals of `f` at `a` and `b ≥ a` differ by at most `M (b - a)`. -/
private lemma abs_integral_Ici_sub_Ici_le {f : ℝ → ℝ} {a b M : ℝ} (hab : a ≤ b)
    (hf : IntegrableOn f (Set.Ici a) volume) (hM : ∀ x, a ≤ x → f x ≤ M)
    (h0 : ∀ x, a ≤ x → 0 ≤ f x) :
    |(∫ x in Set.Ici a, f x) - (∫ x in Set.Ici b, f x)| ≤ M * (b - a) := by
  have hf' : IntegrableOn f (Set.Ici b) volume := hf.mono_set (Set.Ici_subset_Ici.mpr hab)
  rw [intervalIntegral.integral_Ici_sub_Ici' hf hf']
  rw [← Real.norm_eq_abs]
  have hbound : ‖∫ x in a..b, f x‖ ≤ M * (b - a) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (f := f) (a := a) (b := b) (C := M)
      (fun x hx => by
        rw [Set.uIoc_of_le hab] at hx
        rw [Real.norm_eq_abs, abs_of_nonneg (h0 x hx.1.le)]
        exact hM x hx.1.le)
    rwa [abs_of_nonneg (by linarith : (0:ℝ) ≤ b - a)] at h
  exact hbound

/-! ## The `riPhi` half -/

/-- `|riPhi t - riPhi s| ≤ 100 (s - t)` for `3 ≤ t ≤ s`.  Both delay identities read
`s·riPhi s = ∫_{Ici (s-1)} riPsi`, so the difference of the products is the integral of `riPsi`
over `[t-1, s-1] ⊆ [2,∞)`, of length `s - t`. -/
private lemma riPhi_abs_sub_le_of_three_le (s t : ℝ) (ht : 3 ≤ t) (hts : t ≤ s) :
    |riPhi t - riPhi s| ≤ 100 * (s - t) := by
  have hs : 3 ≤ s := le_trans ht hts
  have hst : 0 ≤ s - t := by linarith
  have hsnn : (0:ℝ) ≤ s := by linarith
  have hid : ∀ u : ℝ, 3 ≤ u → u * riPhi u = ∫ x in Set.Ici (u - 1), riPsi x := by
    intro u hu
    have h := Work.NumberTheory.Chen.ApSumTenth.riPhi_delay_identity u (by linarith)
    have hmax : max (u - 1) 2 = u - 1 := max_eq_left (by linarith)
    have hif : (3 - u) * (if u ≤ 3 then (1:ℝ) else 0) = 0 := by
      by_cases h3 : u ≤ 3
      · rw [if_pos h3, mul_one]; linarith
      · rw [if_neg h3, mul_zero]
    rw [hmax, hif, zero_add] at h
    exact h
  have hIs : IntegrableOn riPsi (Set.Ici (t - 1)) volume :=
    Work.NumberTheory.Chen.ApSumTenth.integrableOn_riPsi_Ici_two.mono_set
      (Set.Ici_subset_Ici.mpr (by linarith : (2:ℝ) ≤ t - 1))
  have hdiff : |(∫ x in Set.Ici (t - 1), riPsi x) - (∫ x in Set.Ici (s - 1), riPsi x)|
      ≤ 6 * (s - t) := by
    have hab : t - 1 ≤ s - 1 := by linarith
    have h := abs_integral_Ici_sub_Ici_le (f := riPsi) hab hIs
        (fun x hx => riPsi_le_six (le_trans (by linarith : (2:ℝ) ≤ t - 1) hx))
        (fun x _ => riPsi_nonneg x)
    linarith [h]
  have hkey : |s * riPhi s - t * riPhi t| ≤ 6 * (s - t) := by
    rw [hid s hs, hid t ht, abs_sub_comm]
    exact hdiff
  have hPt : riPhi t ≤ 8 := riPhi_le_eight (by linarith)
  have heq : s * (riPhi t - riPhi s) = (t * riPhi t - s * riPhi s) + (s - t) * riPhi t := by ring
  have hmain : s * |riPhi t - riPhi s| ≤ 14 * (s - t) := by
    calc s * |riPhi t - riPhi s| = |s * (riPhi t - riPhi s)| := by
          rw [abs_mul, abs_of_nonneg hsnn]
    _ = |(t * riPhi t - s * riPhi s) + (s - t) * riPhi t| := by rw [heq]
    _ ≤ |t * riPhi t - s * riPhi s| + |(s - t) * riPhi t| := abs_add_le _ _
    _ = |s * riPhi s - t * riPhi t| + (s - t) * riPhi t := by
          rw [abs_sub_comm (t * riPhi t) (s * riPhi s),
            abs_of_nonneg (mul_nonneg hst (riPhi_nonneg t))]
    _ ≤ 6 * (s - t) + 8 * (s - t) := by nlinarith [hkey, hPt, hst]
    _ = 14 * (s - t) := by ring
  have hdiv : |riPhi t - riPhi s| ≤ 14 * (s - t) / s := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < s)]
    nlinarith [hmain]
  have hlast : 14 * (s - t) / s ≤ 100 * (s - t) := by
    rw [div_le_iff₀ (by linarith : (0:ℝ) < s)]
    nlinarith [hst]
  linarith

/-- `|riPhi t - riPhi s| ≤ 100 (s - t)` for `2 ≤ t ≤ s ≤ 3`.  Here the two delay identities have
the *same* half-line integral `∫_{Ici 2} riPsi`, so the difference of the products is exactly
`t - s`. -/
private lemma riPhi_abs_sub_le_of_le_three (s t : ℝ) (ht : 2 ≤ t) (hts : t ≤ s) (hs3 : s ≤ 3) :
    |riPhi t - riPhi s| ≤ 100 * (s - t) := by
  have ht3 : t ≤ 3 := le_trans hts hs3
  have hst : 0 ≤ s - t := by linarith
  have hsnn : (0:ℝ) ≤ s := by linarith
  have hid : ∀ u : ℝ, 2 ≤ u → u ≤ 3 → u * riPhi u = (3 - u) + ∫ x in Set.Ici (2:ℝ), riPsi x := by
    intro u hu hu3
    have h := Work.NumberTheory.Chen.ApSumTenth.riPhi_delay_identity u (by linarith)
    have hmax : max (u - 1) 2 = 2 := max_eq_right (by linarith)
    rw [hmax, if_pos hu3, mul_one] at h
    exact h
  have hkey : |s * riPhi s - t * riPhi t| ≤ s - t := by
    rw [hid s (le_trans ht hts) hs3, hid t ht ht3]
    have hsub : (3 - s) + (∫ x in Set.Ici (2:ℝ), riPsi x)
        - ((3 - t) + ∫ x in Set.Ici (2:ℝ), riPsi x) = t - s := by ring
    rw [hsub, abs_of_nonpos (by linarith : t - s ≤ 0)]
    linarith
  have hPt : riPhi t ≤ 8 := riPhi_le_eight (by linarith)
  have heq : s * (riPhi t - riPhi s) = (t * riPhi t - s * riPhi s) + (s - t) * riPhi t := by ring
  have hmain : s * |riPhi t - riPhi s| ≤ 9 * (s - t) := by
    calc s * |riPhi t - riPhi s| = |s * (riPhi t - riPhi s)| := by
          rw [abs_mul, abs_of_nonneg hsnn]
    _ = |(t * riPhi t - s * riPhi s) + (s - t) * riPhi t| := by rw [heq]
    _ ≤ |t * riPhi t - s * riPhi s| + |(s - t) * riPhi t| := abs_add_le _ _
    _ = |s * riPhi s - t * riPhi t| + (s - t) * riPhi t := by
          rw [abs_sub_comm (t * riPhi t) (s * riPhi s),
            abs_of_nonneg (mul_nonneg hst (riPhi_nonneg t))]
    _ ≤ (s - t) + 8 * (s - t) := by nlinarith [hkey, hPt, hst]
    _ = 9 * (s - t) := by ring
  have hdiv : |riPhi t - riPhi s| ≤ 9 * (s - t) / s := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < s)]
    nlinarith [hmain]
  have hlast : 9 * (s - t) / s ≤ 100 * (s - t) := by
    rw [div_le_iff₀ (by linarith : (0:ℝ) < s)]
    nlinarith [hst]
  linarith

/-- `|riPhi t - riPhi s| ≤ 100 (s - t)` for all `2 ≤ t ≤ s`. -/
private lemma riPhi_abs_sub_le (s t : ℝ) (ht : 2 ≤ t) (hts : t ≤ s) :
    |riPhi t - riPhi s| ≤ 100 * (s - t) := by
  by_cases h1 : s ≤ 3
  · exact riPhi_abs_sub_le_of_le_three s t ht hts h1
  · by_cases h2 : 3 ≤ t
    · exact riPhi_abs_sub_le_of_three_le s t h2 hts
    · -- the interval straddles `3`: split at `3`
      have ht3 : t ≤ 3 := le_of_lt (lt_of_not_ge h2)
      have hs3 : 3 ≤ s := le_of_lt (lt_of_not_ge h1)
      have hsplit : riPhi t - riPhi s = (riPhi t - riPhi 3) + (riPhi 3 - riPhi s) := by ring
      calc |riPhi t - riPhi s| = |(riPhi t - riPhi 3) + (riPhi 3 - riPhi s)| := by rw [hsplit]
      _ ≤ |riPhi t - riPhi 3| + |riPhi 3 - riPhi s| := abs_add_le _ _
      _ ≤ 100 * (3 - t) + 100 * (s - 3) := by
            refine add_le_add ?_ ?_
            · exact riPhi_abs_sub_le_of_le_three 3 t ht ht3 le_rfl
            · exact riPhi_abs_sub_le_of_three_le s 3 le_rfl hs3
      _ = 100 * (s - t) := by ring

/-! ## The `riPsi` half -/

/-- `|riPsi t - riPsi s| ≤ 100 (s - t)` for all `2 ≤ t ≤ s`.  The delay identity
`s·riPsi s = ∫_{Ici (s-1)} riPhi` holds on the whole range `s ≥ 2`, so no case distinction is
needed. -/
private lemma riPsi_abs_sub_le (s t : ℝ) (ht : 2 ≤ t) (hts : t ≤ s) :
    |riPsi t - riPsi s| ≤ 100 * (s - t) := by
  have hs : 2 ≤ s := le_trans ht hts
  have hst : 0 ≤ s - t := by linarith
  have hsnn : (0:ℝ) ≤ s := by linarith
  have hIt : IntegrableOn riPhi (Set.Ici (t - 1)) volume :=
    Work.NumberTheory.Chen.ApSumTenth.integrableOn_riPhi_Ici_one.mono_set
      (Set.Ici_subset_Ici.mpr (by linarith : (1:ℝ) ≤ t - 1))
  have hdiff : |(∫ x in Set.Ici (t - 1), riPhi x) - (∫ x in Set.Ici (s - 1), riPhi x)|
      ≤ 8 * (s - t) := by
    have hab : t - 1 ≤ s - 1 := by linarith
    have h := abs_integral_Ici_sub_Ici_le (f := riPhi) hab hIt
        (fun x hx => riPhi_le_eight (le_trans (by linarith : (1:ℝ) ≤ t - 1) hx))
        (fun x _ => riPhi_nonneg x)
    linarith [h]
  have hsys_s := Work.NumberTheory.Chen.ApSumTenth.riPhi_delay_system.2 s hs
  have hsys_t := Work.NumberTheory.Chen.ApSumTenth.riPhi_delay_system.2 t ht
  have hkey : |s * riPsi s - t * riPsi t| ≤ 8 * (s - t) := by
    rw [hsys_s, hsys_t, abs_sub_comm]
    exact hdiff
  have hQt : riPsi t ≤ 6 := riPsi_le_six ht
  have heq : s * (riPsi t - riPsi s) = (t * riPsi t - s * riPsi s) + (s - t) * riPsi t := by ring
  have hmain : s * |riPsi t - riPsi s| ≤ 14 * (s - t) := by
    calc s * |riPsi t - riPsi s| = |s * (riPsi t - riPsi s)| := by
          rw [abs_mul, abs_of_nonneg hsnn]
    _ = |(t * riPsi t - s * riPsi s) + (s - t) * riPsi t| := by rw [heq]
    _ ≤ |t * riPsi t - s * riPsi s| + |(s - t) * riPsi t| := abs_add_le _ _
    _ = |s * riPsi s - t * riPsi t| + (s - t) * riPsi t := by
          rw [abs_sub_comm (t * riPsi t) (s * riPsi s),
            abs_of_nonneg (mul_nonneg hst (riPsi_nonneg t))]
    _ ≤ 8 * (s - t) + 6 * (s - t) := by nlinarith [hkey, hQt, hst]
    _ = 14 * (s - t) := by ring
  have hdiv : |riPsi t - riPsi s| ≤ 14 * (s - t) / s := by
    rw [le_div_iff₀ (by linarith : (0:ℝ) < s)]
    nlinarith [hmain]
  have hlast : 14 * (s - t) / s ≤ 100 * (s - t) := by
    rw [div_le_iff₀ (by linarith : (0:ℝ) < s)]
    nlinarith [hst]
  linarith

/-- **`riUp` and `riPsi` are Lipschitz on `[2, ∞)`** (with an explicit constant `C`), which is what
lets the assembly compare the sharp sieve's bound at a *shifted* parameter `σ - δ` with the
contract's `Utab σ` / `1 - riPsi` when `δ` is tiny: the shift is `log Q / log z ≤ 5·10⁻⁶` by the
choice of `z₀`, so `C·δ ≤ 10⁻⁵` is negligible against the `1/1000` slack proved in
`Numerics/riUp_le_Utab` / `Numerics/riPsi_le`.

NOTE the domain restriction `2 ≤ t`: `riPsi` genuinely JUMPS at `s = 2` (`riPsi s = 0` for `s < 2`,
`riPsi 2 = 1`), so the estimate must only be asked for `2 ≤ t ≤ s` (both arguments at least `2`).

TRUE because `riUp = 1 + riPhi` and `riPsi` solve the delay–differential system
`s·riPhi(s) = ∫_{s-1}^∞ riPsi`, `s·riPsi(s) = ∫_{s-1}^∞ riPhi` (see `APSwitchUpper/riPhiDelay.lean`,
`riDelay`), whose right-hand sides are bounded on `s ≥ 2` by the exponentially decaying tails
(`riPhi_nonneg`, `riPsi_nonneg`, `errH`-type decay).  Only the existence of an explicit `C` matters. -/
theorem riUp_riPsi_lipschitz :
    ∃ C : ℝ, 0 ≤ C ∧ C ≤ 100 ∧
      (∀ s t : ℝ, 2 ≤ t → t ≤ s →
        |Work.NumberTheory.Chen.APSwitchUpper.riUp t
            - Work.NumberTheory.Chen.APSwitchUpper.riUp s| ≤ C * (s - t)) ∧
      (∀ s t : ℝ, 2 ≤ t → t ≤ s →
        |Work.NumberTheory.Chen.APSwitchUpper.riPsi t
            - Work.NumberTheory.Chen.APSwitchUpper.riPsi s| ≤ C * (s - t)) := by
  refine ⟨100, by norm_num, le_rfl, ?_, ?_⟩
  · intro s t ht hts
    have h := riPhi_abs_sub_le s t ht hts
    have heq : riUp t - riUp s = riPhi t - riPhi s := by
      rw [riUp, riUp]; ring
    rw [heq]
    exact h
  · intro s t ht hts
    exact riPsi_abs_sub_le s t ht hts

end

end Work.ChenPlan.LinearSieve.JR2
