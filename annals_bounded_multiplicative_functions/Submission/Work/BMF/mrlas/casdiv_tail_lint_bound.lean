import Mathlib
import Submission.Work.BMF.halasz_defs
import Submission.Work.BMF.mrlas.casdiv_tail_helpers

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory intervalIntegral Filter
open scoped ENNReal

namespace Work.BMF.mrlas

/-- Sum of the per-window `ofReal` bounds: `∑ₖ ofReal (B/(1+(T+k)²)) ≤ ofReal (2B/T)`. -/
private lemma tsum_window_le {B T : ℝ} (hB : 0 ≤ B) (hT : 1 ≤ T)
    (hsumm : Summable (fun k : ℕ => (1:ℝ) / (1 + (T + k)^2)))
    (htsum : ∑' k : ℕ, (1:ℝ) / (1 + (T + k)^2) ≤ 2 / T) :
    (∑' k : ℕ, ENNReal.ofReal (B / (1 + (T + k)^2))) ≤ ENNReal.ofReal (2 * B / T) := by
  have h1 : (∑' k : ℕ, ENNReal.ofReal (B / (1 + (T + k)^2)))
      = ENNReal.ofReal (∑' k : ℕ, B / (1 + (T + k)^2)) :=
    (ENNReal.ofReal_tsum_of_nonneg (f := fun k : ℕ => B / (1 + (T + k)^2))
      (fun k => by positivity) (by simpa only [div_eq_mul_inv, one_mul] using hsumm.mul_left B)).symm
  have h2 : (∑' k : ℕ, B / (1 + (T + k)^2)) = B * ∑' k : ℕ, 1 / (1 + (T + k)^2) := by
    simp_rw [div_eq_mul_inv, one_mul]
    rw [tsum_mul_left]
  rw [h1, h2]
  apply ENNReal.ofReal_le_ofReal
  calc B * ∑' k : ℕ, 1 / (1 + (T + k)^2) ≤ B * (2 / T) :=
        mul_le_mul_of_nonneg_left htsum hB
    _ = 2 * B / T := by ring

/-- Right tail: `∫⁻_{τ > T} ofReal (F τ/(a²+τ²)) ≤ ofReal (2B/T)`. -/
private lemma tail_Ioi_le {F : ℝ → ℝ} (hF : Continuous F) (hFnn : ∀ τ, 0 ≤ F τ)
    {B a T : ℝ} (ha : 1 ≤ a) (hT : 1 ≤ T) (hB : 0 ≤ B)
    (hwin : ∀ c : ℝ, (∫ τ in c..(c+1), F τ) ≤ B) :
    (∫⁻ τ in Set.Ioi T, ENNReal.ofReal (F τ / (a ^ 2 + τ ^ 2)))
      ≤ ENNReal.ofReal (2 * B / T) := by
  obtain ⟨hsumm, htsum⟩ := summable_and_tsum_one_div_one_add_sq_shift_le T hT
  calc (∫⁻ τ in Set.Ioi T, ENNReal.ofReal (F τ / (a ^ 2 + τ ^ 2)))
      ≤ ∫⁻ τ in (⋃ k : ℕ, Set.Ioc (T + k) (T + k + 1)),
          ENNReal.ofReal (F τ / (a ^ 2 + τ ^ 2)) :=
        lintegral_mono_set (iUnion_Ioc_cover_Ioi T)
    _ ≤ ∑' k : ℕ, ∫⁻ τ in Set.Ioc (T + k) (T + k + 1),
          ENNReal.ofReal (F τ / (a ^ 2 + τ ^ 2)) := lintegral_iUnion_le _ _
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (B / (1 + (T + k)^2)) := by
        apply ENNReal.tsum_le_tsum
        intro k
        have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
        refine window_lintegral_ofReal_le (a := a) (c := T + (k:ℝ)) (d := T + (k:ℝ) + 1)
          (m := T + (k:ℝ)) hF hFnn ha (by positivity) (by linarith) (hwin (T + (k:ℝ))) ?_
        intro τ hτ
        rw [abs_of_nonneg (by linarith [hτ.1, hk, hT])]
        exact hτ.1
    _ ≤ ENNReal.ofReal (2 * B / T) := tsum_window_le hB hT hsumm htsum

/-- Left tail: `∫⁻_{τ < -T} ofReal (F τ/(a²+τ²)) ≤ ofReal (2B/T)`. -/
private lemma tail_Iio_le {F : ℝ → ℝ} (hF : Continuous F) (hFnn : ∀ τ, 0 ≤ F τ)
    {B a T : ℝ} (ha : 1 ≤ a) (hT : 1 ≤ T) (hB : 0 ≤ B)
    (hwin : ∀ c : ℝ, (∫ τ in c..(c+1), F τ) ≤ B) :
    (∫⁻ τ in Set.Iio (-T), ENNReal.ofReal (F τ / (a ^ 2 + τ ^ 2)))
      ≤ ENNReal.ofReal (2 * B / T) := by
  obtain ⟨hsumm, htsum⟩ := summable_and_tsum_one_div_one_add_sq_shift_le T hT
  calc (∫⁻ τ in Set.Iio (-T), ENNReal.ofReal (F τ / (a ^ 2 + τ ^ 2)))
      ≤ ∫⁻ τ in (⋃ k : ℕ, Set.Ioc (-(T + k + 1)) (-(T + k))),
          ENNReal.ofReal (F τ / (a ^ 2 + τ ^ 2)) :=
        lintegral_mono_set (iUnion_Ioc_cover_Iio T)
    _ ≤ ∑' k : ℕ, ∫⁻ τ in Set.Ioc (-(T + k + 1)) (-(T + k)),
          ENNReal.ofReal (F τ / (a ^ 2 + τ ^ 2)) := lintegral_iUnion_le _ _
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (B / (1 + (T + k)^2)) := by
        apply ENNReal.tsum_le_tsum
        intro k
        have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
        have hcd : -(T + (k:ℝ) + 1) ≤ -(T + (k:ℝ)) := by linarith
        have hwin' : (∫ τ in (-(T + (k:ℝ) + 1))..(-(T + (k:ℝ))), F τ) ≤ B := by
          have h := hwin (-(T + (k:ℝ) + 1))
          have hud : -(T + (k:ℝ) + 1) + 1 = -(T + (k:ℝ)) := by ring
          simpa [hud] using h
        refine window_lintegral_ofReal_le (a := a) (c := -(T + (k:ℝ) + 1))
          (d := -(T + (k:ℝ))) (m := T + (k:ℝ)) hF hFnn ha (by positivity) hcd hwin' ?_
        intro τ hτ
        rw [abs_of_nonpos (by linarith [hτ.2, hk, hT])]
        linarith [hτ.2]
    _ ≤ ENNReal.ofReal (2 * B / T) := tsum_window_le hB hT hsumm htsum

/-- **Tail weighted `lintegral` bound (companion of `Work.BMF.mrlas.casdiv_middle_lint_bound`).**
If `F ≥ 0` is continuous and every unit-window integral `∫_c^{c+1} F` is at most `B`, then for
`a ≥ 1` and `T ≥ 1` the two tails of the weighted `lintegral` of `F τ/(a²+τ²)` are jointly
`O(B/T)`.

Proof route.  On the window `[T+k, T+k+1]` one has `1/(a²+τ²) ≤ 1/(1+(T+k)²)` and
`∫_{T+k}^{T+k+1} F ≤ B`, so each tail piece is at most `B/(1+(T+k)²)`; the tail is the disjoint
union of the windows `Ioc (T+k) (T+k+1)` (`k ∈ ℕ`), so `lintegral_iUnion` turns the tail lintegral
into the sum of the window lintegrals, and each window lintegral equals `ENNReal.ofReal` of the
corresponding (finite) integral (`ofReal_integral_eq_lintegral_ofReal`, using continuity on the
compact window).  Finally `∑'_{k} 1/(1+(T+k)²) ≤ 2/T` for `T ≥ 1`
(telescoping: `1/(T+k+1)² ≤ 1/(T+k) - 1/(T+k+1)`, so the tail of the sum is `≤ 1/T`, and the
`k = 0` term is `≤ 1/T²`).  The negative tail is the mirror image with the windows
`Ioc (-(T+k+1)) (-(T+k))`. -/
theorem casdiv_tail_lint_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ℝ → ℝ), Continuous F → (∀ τ, 0 ≤ F τ) →
      ∀ B a T : ℝ, 1 ≤ a → 1 ≤ T → (∀ c : ℝ, (∫ τ in c..(c+1), F τ) ≤ B) →
        (∫⁻ τ in Set.Ioi T, ENNReal.ofReal (F τ / (a ^ 2 + τ ^ 2))) +
        (∫⁻ τ in Set.Iio (-T), ENNReal.ofReal (F τ / (a ^ 2 + τ ^ 2)))
          ≤ ENNReal.ofReal (C * B / T) := by
  refine ⟨4, by norm_num, ?_⟩
  intro F hF hFnn B a T ha hT hwin
  have hB : 0 ≤ B := by
    have h1 : (0:ℝ) ≤ ∫ τ in (0:ℝ)..(0+1), F τ :=
      intervalIntegral.integral_nonneg (by norm_num) (fun τ _ => hFnn τ)
    have h2 := hwin 0
    linarith
  have hpos := tail_Ioi_le hF hFnn ha hT hB hwin
  have hneg := tail_Iio_le hF hFnn ha hT hB hwin
  calc (∫⁻ τ in Set.Ioi T, ENNReal.ofReal (F τ / (a ^ 2 + τ ^ 2))) +
        (∫⁻ τ in Set.Iio (-T), ENNReal.ofReal (F τ / (a ^ 2 + τ ^ 2)))
      ≤ ENNReal.ofReal (2 * B / T) + ENNReal.ofReal (2 * B / T) := add_le_add hpos hneg
    _ = ENNReal.ofReal (2 * B / T + 2 * B / T) :=
        (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ = ENNReal.ofReal (4 * B / T) := by congr 1; ring

end Work.BMF.mrlas
