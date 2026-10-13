import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.ClassCHon.radGreen_compact_source_interval
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `FTS/ClassCHon/radGreen_size_bound`

The **mode-uniform size bound** for the radial Euler Green function
`radGreen α m c` on a *compactly supported* source, with an absolute constant `A`:

  `m² · |radGreen α m c z| ≤ A · M`

for every `α ∈ (0, 1/4]`, every `m ≥ 1`, every source `c` which is `C^∞` on `(0,∞)`,
bounded by `M ≥ 0` and vanishes off an interval `[a,b]` with `a > 0`, and every `z > 0`.
The single constant `A` is *independent* of `α`, `m`, `a`, `b`, `M`, `c` and `z`; we use
`A = 1/4` (which is essentially sharp, see the asymptotics below).

## The computation

With `q := (2m+5)/α > 0` and `p := 2m/α > 0`, the definition

  `radGreen α m c z = 1/(α(4m+5)) · ( z^{-q} ∫_0^z c t^{q-1} dt + z^{p} ∫_z^∞ c t^{-p-1} dt )`

gives, using only `|c| ≤ M` and the two elementary rpow integrals
(`∫_0^z t^{q-1} = z^q/q` for `q > 0`, `∫_z^∞ t^{-p-1} = z^{-p}/p` for `p > 0`, `z > 0`):

  `z^{-q} · |∫_0^z c t^{q-1}| ≤ z^{-q} · M z^q/q = M/q = Mα/(2m+5)`,
  `z^{p} · |∫_z^∞ c t^{-p-1}| ≤ z^{p} · M z^{-p}/p = M/p = Mα/(2m)`.

Hence

  `|radGreen α m c z| ≤ Mα/(α(4m+5)) · (1/(2m+5) + 1/(2m)) = M/(4m+5) · (1/(2m+5) + 1/(2m))`,

and since `1/(2m+5) ≤ 1/(2m)` for `m ≥ 1`,

  `m² |radGreen α m c z| ≤ M · m²/(4m+5) · (1/m) = M · m/(4m+5) ≤ M/4`.

(The bound is sharp: `m²/(4m+5)·(1/(2m+5)+1/(2m)) → 1/4` as `m → ∞`.)

Nothing beyond `|c| ≤ M` and `z > 0` is used: neither the continuity hypothesis, nor the
support hypothesis, nor `0 < a`, nor `0 ≤ M` is needed for the *inequality* itself (they are
part of the requested statement).  The two integral estimates are isolated in the private
lemmas `near_int_bound` and `far_int_bound`.

Note that the `a`-smallness is irrelevant here (unlike in the pointwise near-field and
far-field bounds `radGreen_near_pointwise_bound` / `radGreen_far_pointwise_bound` of
`FTS/ClassC/HonestCut/`): the *global* `m`-uniform `L^∞` bound uses only the size of the
source and the explicit form of the Green kernel.
-/

noncomputable section

open MeasureTheory Set
open scoped Real Topology

namespace Work.FTS.ClassCHon

/-- **The near-field (`0 < t < z`) integral estimate.**  For `z > 0`, `Q > 0` and a source
bounded by `M`,

  `|∫_0^z c t · t^{Q-1} dt| ≤ M · z^Q / Q`.

This is the sharp bound: the dominating function `M t^{Q-1}` is integrable on `(0,z)`
precisely because `Q - 1 > -1`, and its integral is `M z^Q/Q`. -/
private theorem near_int_bound {z M Q : ℝ} (hz : 0 < z) (hQ : 0 < Q) {c : ℝ → ℝ}
    (hc : ∀ t : ℝ, |c t| ≤ M) :
    |∫ t in (0 : ℝ)..z, c t * t ^ (Q - 1)| ≤ M * z ^ Q / Q := by
  have hQ1 : (-1 : ℝ) < Q - 1 := by linarith
  have hbnd : ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      t ∈ Set.Ioc (0 : ℝ) z → ‖c t * t ^ (Q - 1)‖ ≤ M * t ^ (Q - 1) := by
    filter_upwards with t ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.1.le _)]
    exact mul_le_mul_of_nonneg_right (hc t) (Real.rpow_nonneg ht.1.le _)
  have hint : IntervalIntegrable (fun t : ℝ => M * t ^ (Q - 1)) MeasureTheory.volume (0 : ℝ) z :=
    (intervalIntegral.intervalIntegrable_rpow' hQ1).const_mul M
  have h2 : ∫ t in (0 : ℝ)..z, M * t ^ (Q - 1) = M * z ^ Q / Q := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hQ1)]
    have h : Q - 1 + 1 = Q := by ring
    rw [h, Real.zero_rpow hQ.ne', sub_zero]
    ring
  have h1 := intervalIntegral.norm_integral_le_of_norm_le hz.le hbnd hint
  rw [h2] at h1
  rwa [Real.norm_eq_abs] at h1

/-- **The far-field (`t > z`) integral estimate.**  For `z > 0`, `P > 0` and a source bounded
by `M`,

  `|∫_z^∞ c t · t^{-P-1} dt| ≤ M · z^{-P} / P`.

Here the dominating function `M t^{-P-1}` is integrable on `(z,∞)` (for `z > 0`) precisely
because `-P - 1 < -1`, and its integral is `M z^{-P}/P`. -/
private theorem far_int_bound {z M P : ℝ} (hz : 0 < z) (hP : 0 < P) {c : ℝ → ℝ}
    (hc : ∀ t : ℝ, |c t| ≤ M) :
    |∫ t in Set.Ioi z, c t * t ^ (-P - 1)| ≤ M * z ^ (-P) / P := by
  have hP1 : -P - 1 < (-1 : ℝ) := by linarith
  have hg : MeasureTheory.Integrable (fun t : ℝ => M * t ^ (-P - 1))
      (MeasureTheory.volume.restrict (Set.Ioi z)) :=
    (integrableOn_Ioi_rpow_of_lt hP1 hz).const_mul M
  have hbnd : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi z)),
      ‖c t * t ^ (-P - 1)‖ ≤ M * t ^ (-P - 1) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans hz ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    exact mul_le_mul_of_nonneg_right (hc t) (Real.rpow_nonneg ht0.le _)
  have h2 : ∫ t in Set.Ioi z, M * t ^ (-P - 1) = M * z ^ (-P) / P := by
    rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt hP1 hz]
    have h : -P - 1 + 1 = -P := by ring
    rw [h]
    field_simp
  have h1 := MeasureTheory.norm_integral_le_of_norm_le hg hbnd
  rw [h2] at h1
  rwa [Real.norm_eq_abs] at h1

theorem radGreen_size_bound :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 / 4 → ∀ (m : ℕ), 1 ≤ m →
      ∀ {a b M : ℝ}, 0 < a → 0 ≤ M → ∀ {c : ℝ → ℝ},
        (∀ n : ℕ, ContDiffOn ℝ n c (Set.Ioi 0)) → (∀ t : ℝ, |c t| ≤ M) →
        (∀ z : ℝ, z ∉ Set.Icc a b → c z = 0) →
        ∀ z : ℝ, 0 < z →
          (m : ℝ) ^ 2 * |Work.FTS.PhiStar.Radial.radGreen α m c z| ≤ A * M := by
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro α hα _hα4 m hm _a _b M _ha hM c _hc hbound _hsupp z hz
  -- the two exponents `Q = (2m+5)/α` (decaying branch) and `P = 2m/α` (growing branch)
  set Q : ℝ := (2 * (m : ℝ) + 5) / α with hQ
  set P : ℝ := 2 * (m : ℝ) / α with hP
  set L : ℝ := 1 / (α * (4 * (m : ℝ) + 5)) with hL
  have hQpos : 0 < Q := by rw [hQ]; positivity
  have hPpos : 0 < P := by rw [hP]; positivity
  have hLpos : 0 < L := by rw [hL]; positivity
  -- the two integral estimates
  have hI1 : |∫ t in (0 : ℝ)..z, c t * t ^ (Q - 1)| ≤ M * z ^ Q / Q :=
    near_int_bound hz hQpos hbound
  have hI2 : |∫ t in Set.Ioi z, c t * t ^ (-P - 1)| ≤ M * z ^ (-P) / P :=
    far_int_bound hz hPpos hbound
  -- `radGreen` in terms of `Q`, `P`, `L`
  have hrad : Work.FTS.PhiStar.Radial.radGreen α m c z
      = L * (z ^ (-Q) * (∫ t in (0 : ℝ)..z, c t * t ^ (Q - 1))
          + z ^ P * (∫ t in Set.Ioi z, c t * t ^ (-P - 1))) := by
    simp only [Work.FTS.PhiStar.Radial.radGreen, hQ, hP, hL]
    rw [neg_div]
  have hzQ : z ^ (-Q) * z ^ Q = 1 := by
    rw [← Real.rpow_add hz, neg_add_cancel, Real.rpow_zero]
  have hzP : z ^ P * z ^ (-P) = 1 := by
    rw [← Real.rpow_add hz, add_neg_cancel, Real.rpow_zero]
  -- the absolute value of `radGreen`
  have hmain : |Work.FTS.PhiStar.Radial.radGreen α m c z| ≤ L * (M / Q + M / P) := by
    rw [hrad, abs_mul, abs_of_pos hLpos]
    calc L * |z ^ (-Q) * (∫ t in (0 : ℝ)..z, c t * t ^ (Q - 1))
              + z ^ P * (∫ t in Set.Ioi z, c t * t ^ (-P - 1))|
        ≤ L * (z ^ (-Q) * |∫ t in (0 : ℝ)..z, c t * t ^ (Q - 1)|
              + z ^ P * |∫ t in Set.Ioi z, c t * t ^ (-P - 1)|) := by
          apply mul_le_mul_of_nonneg_left _ hLpos.le
          calc |z ^ (-Q) * (∫ t in (0 : ℝ)..z, c t * t ^ (Q - 1))
                + z ^ P * (∫ t in Set.Ioi z, c t * t ^ (-P - 1))|
              ≤ |z ^ (-Q) * (∫ t in (0 : ℝ)..z, c t * t ^ (Q - 1))|
                + |z ^ P * (∫ t in Set.Ioi z, c t * t ^ (-P - 1))| := abs_add_le _ _
            _ = z ^ (-Q) * |∫ t in (0 : ℝ)..z, c t * t ^ (Q - 1)|
                + z ^ P * |∫ t in Set.Ioi z, c t * t ^ (-P - 1)| := by
                rw [abs_mul, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hz _),
                    abs_of_pos (Real.rpow_pos_of_pos hz _)]
      _ ≤ L * (z ^ (-Q) * (M * z ^ Q / Q) + z ^ P * (M * z ^ (-P) / P)) := by
          apply mul_le_mul_of_nonneg_left _ hLpos.le
          exact add_le_add
            (mul_le_mul_of_nonneg_left hI1 (le_of_lt (Real.rpow_pos_of_pos hz _)))
            (mul_le_mul_of_nonneg_left hI2 (le_of_lt (Real.rpow_pos_of_pos hz _)))
      _ = L * (M / Q + M / P) := by
          have hA : z ^ (-Q) * (M * z ^ Q / Q) = M / Q := by
            rw [← mul_div_assoc, mul_comm M (z ^ Q), ← mul_assoc, hzQ, one_mul]
          have hB : z ^ P * (M * z ^ (-P) / P) = M / P := by
            rw [← mul_div_assoc, mul_comm M (z ^ (-P)), ← mul_assoc, hzP, one_mul]
          rw [hA, hB]
  -- the pure arithmetic: `m² · L · (1/Q + 1/P) ≤ 1/4`
  have hQinv : 1 / Q = α / (2 * (m : ℝ) + 5) := by rw [hQ]; field_simp
  have hPinv : 1 / P = α / (2 * (m : ℝ)) := by rw [hP]; field_simp
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have harith : (m : ℝ) ^ 2 * (L * (1 / Q + 1 / P)) ≤ 1 / 4 := by
    rw [hQinv, hPinv, hL]
    rw [← sub_nonneg]
    field_simp
    nlinarith [hm1]
  calc (m : ℝ) ^ 2 * |Work.FTS.PhiStar.Radial.radGreen α m c z|
      ≤ (m : ℝ) ^ 2 * (L * (M / Q + M / P)) := by
        apply mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = M * ((m : ℝ) ^ 2 * (L * (1 / Q + 1 / P))) := by ring
    _ ≤ M * (1 / 4) := mul_le_mul_of_nonneg_left harith hM
    _ = (1 / 4) * M := by ring

end Work.FTS.ClassCHon
