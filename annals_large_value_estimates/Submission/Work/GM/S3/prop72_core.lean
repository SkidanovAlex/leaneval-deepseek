import Mathlib
import Submission.Work.GM.S3.Base
import Submission.Work.GM.S3.Defs
import Submission.Work.GM.S3.prop71_main
import Submission.Work.GM.S3.prop71_defs
import Submission.Work.GM.S3.RtildeSq_eq_zero_of_notMem

/-!
# The core estimate of GM Prop 7.2 (`Work.GM.S3.prop72_paper`)

Ingredients turning the per-`m` estimate of GM Proposition 7.1 (`Work.GM.S3.prop71_main`) into the
per-`m` estimate of GM Proposition 7.2:

* **`window_normSq_le_Rtilde`** — the *majorization* of a window of `‖R‖²` by the smoothing: if
  `[a,b]` lies in the `ψ₁`-window of `x` (i.e. `|N B (x - u)| ≤ 1`) and in `[1/2,2] ⊂ {ψ₂ ≥ 1}`,
  then `∫_a^b ‖R(u)‖² du ≤ R̃(x)²/(N B)`.
-/

namespace Work.GM.S3

open Complex Finset MeasureTheory
open scoped BigOperators
open Submission.GM (Rfun Iterm Spart nzCount Separated hhat hfun)
open Submission.LargeValues (M bumpW)

theorem RtildeSq_integrable {W : Finset ℝ} {N : ℕ} {B : ℝ} {ψ₁ ψ₂ : ℝ → ℝ} {C₀ x : ℝ}
    (hC₀ : 1 ≤ C₀) (h₁ : IsBumpAtZero ψ₁ C₀) (h₂ : IsBumpAtOne ψ₂ C₀)
    (hB : 0 < (N : ℝ) * B) :
    Integrable (fun u : ℝ =>
      (N : ℝ) * B * ψ₁ ((N : ℝ) * B * (x - u)) * ψ₂ u * ‖Rfun W u‖ ^ 2) := by
  have h₁supp := h₁.2.2.1
  have h₂supp := h₂.2.2.1
  obtain ⟨c₁, hc₁0, hc₁⟩ := h₁.2.2.2.2 0
  obtain ⟨c₂, hc₂0, hc₂⟩ := h₂.2.2.2.2 0
  have hc₁' : ∀ x, |ψ₁ x| ≤ c₁ := by
    intro x
    have h := hc₁ x
    rw [iteratedDeriv_zero] at h
    exact h
  have hc₂' : ∀ x, |ψ₂ x| ≤ c₂ := by
    intro x
    have h := hc₂ x
    rw [iteratedDeriv_zero] at h
    exact h
  set g : ℝ → ℝ := fun u => (N : ℝ) * B * ψ₁ ((N : ℝ) * B * (x - u)) * ψ₂ u * ‖Rfun W u‖ ^ 2
    with hg
  -- integrability of the complexification, then take real parts
  have hgc : Integrable (fun u : ℝ => ((g u : ℝ) : ℂ)) := by
    refine integrable_of_measurable_bounded_support
      (K := Set.Icc (1 / C₀ - C₀ / ((N : ℝ) * B)) (C₀ + C₀ / ((N : ℝ) * B)))
      isCompact_Icc ?_ ?_ (C := |(N : ℝ) * B| * c₁ * c₂ * (W.card : ℝ) ^ 2) ?_
    · have h0 : Measurable (fun u : ℝ => (N : ℝ) * B * ψ₁ ((N : ℝ) * B * (x - u))) :=
        measurable_const.mul (h₁.1.continuous.measurable.comp (by fun_prop))
      have hreal : Measurable g := by
        rw [hg]
        exact (h0.mul h₂.1.continuous.measurable).mul
          ((Rfun_measurable W).norm.pow_const 2)
      exact Complex.measurable_ofReal.comp hreal
    · intro u
      rw [Function.mem_support]
      intro hu
      have hnn : g u ≠ 0 := by
        intro h0
        exact hu (by rw [h0]; simp)
      have h1 : ψ₁ ((N : ℝ) * B * (x - u)) ≠ 0 := by
        intro h
        apply hnn
        rw [hg]
        simp only
        rw [h]
        ring
      have h2 : ψ₂ u ≠ 0 := by
        intro h
        apply hnn
        rw [hg]
        simp only
        rw [h]
        ring
      have h3 : |(N : ℝ) * B * (x - u)| ≤ C₀ := h₁supp _ h1
      have h4 : u ∈ Set.Icc (1 / C₀) C₀ := h₂supp u h2
      have hBabs : |(N : ℝ) * B * (x - u)| = ((N : ℝ) * B) * |x - u| := by
        rw [abs_mul, abs_of_pos hB]
      have h5 : |x - u| ≤ C₀ / ((N : ℝ) * B) := by
        rw [le_div_iff₀ hB, mul_comm]
        rw [← hBabs]; exact h3
      rw [Set.mem_Icc]
      constructor <;> linarith [abs_le.mp h5, h4.1, h4.2]
    · intro u
      have h3 : |ψ₁ ((N : ℝ) * B * (x - u))| ≤ c₁ := hc₁' _
      have h4 : |ψ₂ u| ≤ c₂ := hc₂' _
      have h5 : |‖Rfun W u‖ ^ 2| ≤ (W.card : ℝ) ^ 2 := by
        rw [abs_of_nonneg (sq_nonneg (‖Rfun W u‖))]
        have h := Rfun_norm_le_card W u
        have hc : (0 : ℝ) ≤ (W.card : ℝ) := Nat.cast_nonneg _
        nlinarith [norm_nonneg (Rfun W u), hc, h]
      have habs : |((N : ℝ) * B * ψ₁ ((N : ℝ) * B * (x - u)) * ψ₂ u * ‖Rfun W u‖ ^ 2 : ℝ)|
          = |(N : ℝ) * B| * |ψ₁ ((N : ℝ) * B * (x - u))| * |ψ₂ u| * |‖Rfun W u‖ ^ 2| := by
        simp only [abs_mul]
      have key : |((N : ℝ) * B * ψ₁ ((N : ℝ) * B * (x - u)) * ψ₂ u * ‖Rfun W u‖ ^ 2 : ℝ)|
          ≤ |(N : ℝ) * B| * c₁ * c₂ * (W.card : ℝ) ^ 2 := by
        rw [habs]
        gcongr
      change ‖(((N : ℝ) * B * ψ₁ ((N : ℝ) * B * (x - u)) * ψ₂ u * ‖Rfun W u‖ ^ 2 : ℝ) : ℂ)‖
        ≤ |(N : ℝ) * B| * c₁ * c₂ * (W.card : ℝ) ^ 2
      rwa [Complex.norm_real]
  have hre := hgc.re
  have hfun : (fun x : ℝ => RCLike.re (((g x : ℝ)) : ℂ)) = g := by
    funext u
    exact Complex.ofReal_re (g u)
  rw [hfun] at hre
  exact hre

/-- **Majorization of a window of `‖R‖²` by the smoothing `R̃`.**  Let `B_s = N B > 0`,
`ψ₁` a bump at `0`, `ψ₂` a bump at `1`, with `ψ₁ ≥ 1` on `|x| ≤ 1` and `ψ₂ ≥ 1` on `[1/2,2]`.
If `[a,b]` is inside the `ψ₁`-window `|B_s (x - u)| ≤ 1` of `x` and inside `[1/2,2]`, then
`∫_a^b ‖Rfun W u‖² du ≤ Rtilde W N B ψ₁ ψ₂ x ^ 2 / (N B)`. -/
theorem window_normSq_le_Rtilde {W : Finset ℝ} {N : ℕ} {B : ℝ} {ψ₁ ψ₂ : ℝ → ℝ} {C₀ : ℝ}
    (hC₀ : 1 ≤ C₀) (hψ₁ : IsBumpAtZero ψ₁ C₀) (hψ₂ : IsBumpAtOne ψ₂ C₀)
    (hB : 0 < (N : ℝ) * B) (hψ₁ge : ∀ x, |x| ≤ 1 → 1 ≤ ψ₁ x)
    (hψ₂ge : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, 1 ≤ ψ₂ x)
    (x : ℝ) {a b : ℝ} (hab : a ≤ b)
    (hwin : ∀ u ∈ Set.Icc a b, |(N : ℝ) * B * (x - u)| ≤ 1)
    (hpos : ∀ u ∈ Set.Icc a b, u ∈ Set.Icc (1 / 2 : ℝ) 2) :
    ∫ u in a..b, ‖Rfun W u‖ ^ 2 ≤ Rtilde W N B ψ₁ ψ₂ x ^ 2 / ((N : ℝ) * B) := by
  have hψ₁nn : ∀ x, 0 ≤ ψ₁ x := hψ₁.2.1
  have hψ₂nn : ∀ x, 0 ≤ ψ₂ x := hψ₂.2.1
  have hBnn : 0 ≤ (N : ℝ) * B := le_of_lt hB
  have hBpos : 0 ≤ B := by
    by_contra h
    push Not at h
    exact absurd (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg N) h.le) (not_le.mpr hB)
  have hsq : Rtilde W N B ψ₁ ψ₂ x ^ 2 = RtildeSq W N B ψ₁ ψ₂ x :=
    Rtilde_sq W N B ψ₁ ψ₂ x (RtildeSq_nonneg W N B ψ₁ ψ₂ x hψ₁nn hψ₂nn hBpos)
  have hint := RtildeSq_integrable (W := W) (N := N) (B := B) (C₀ := C₀) (x := x)
    hC₀ hψ₁ hψ₂ hB
  have hpt : ∀ u : ℝ,
      (Set.Ioc a b).indicator (fun u => (N : ℝ) * B * ‖Rfun W u‖ ^ 2) u ≤
        (N : ℝ) * B * ψ₁ ((N : ℝ) * B * (x - u)) * ψ₂ u * ‖Rfun W u‖ ^ 2 := by
    intro u
    by_cases hu : u ∈ Set.Ioc a b
    · rw [Set.indicator_of_mem hu]
      have huI : u ∈ Set.Icc a b := ⟨le_of_lt hu.1, hu.2⟩
      have h1 : 1 ≤ ψ₁ ((N : ℝ) * B * (x - u)) := hψ₁ge _ (hwin u huI)
      have h2 : 1 ≤ ψ₂ u := hψ₂ge u (hpos u huI)
      calc (N : ℝ) * B * ‖Rfun W u‖ ^ 2
          = (N : ℝ) * B * 1 * 1 * ‖Rfun W u‖ ^ 2 := by ring
        _ ≤ (N : ℝ) * B * ψ₁ ((N : ℝ) * B * (x - u)) * ψ₂ u * ‖Rfun W u‖ ^ 2 := by gcongr
    · rw [Set.indicator_of_notMem hu]
      exact mul_nonneg (mul_nonneg (mul_nonneg hBnn (hψ₁nn _)) (hψ₂nn _)) (sq_nonneg _)
  have hmono : ∫ u : ℝ, (Set.Ioc a b).indicator
        (fun u => (N : ℝ) * B * ‖Rfun W u‖ ^ 2) u ≤
      ∫ u : ℝ, (N : ℝ) * B * ψ₁ ((N : ℝ) * B * (x - u)) * ψ₂ u * ‖Rfun W u‖ ^ 2 := by
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall (fun u => by
        by_cases hu : u ∈ Set.Ioc a b
        · rw [Set.indicator_of_mem hu]; positivity
        · rw [Set.indicator_of_notMem hu]; norm_num)
    · simpa using hint
    · exact Filter.Eventually.of_forall hpt
  have hleft : ∫ u : ℝ, (Set.Ioc a b).indicator
        (fun u => (N : ℝ) * B * ‖Rfun W u‖ ^ 2) u =
      (N : ℝ) * B * ∫ u in a..b, ‖Rfun W u‖ ^ 2 := by
    rw [MeasureTheory.integral_indicator measurableSet_Ioc]
    rw [MeasureTheory.integral_const_mul, intervalIntegral.integral_of_le hab]
  rw [hsq, RtildeSq, le_div_iff₀ hB]
  rw [hleft, mul_comm ((N : ℝ) * B)] at hmono
  exact hmono

/-- **Majorization of a *set* of `‖R‖²` by the smoothing `R̃`** (the form used for the constraint
window of GM Prop 7.1, which is a set rather than a fixed interval).  -/
theorem set_normSq_le_Rtilde {W : Finset ℝ} {N : ℕ} {B : ℝ} {ψ₁ ψ₂ : ℝ → ℝ} {C₀ : ℝ}
    (hC₀ : 1 ≤ C₀) (hψ₁ : IsBumpAtZero ψ₁ C₀) (hψ₂ : IsBumpAtOne ψ₂ C₀)
    (hB : 0 < (N : ℝ) * B) (hψ₁ge : ∀ x, |x| ≤ 1 → 1 ≤ ψ₁ x)
    (hψ₂ge : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 2, 1 ≤ ψ₂ x)
    (x : ℝ) {S : Set ℝ} (hmeas : MeasurableSet S)
    (hwin : ∀ u ∈ S, |(N : ℝ) * B * (x - u)| ≤ 1)
    (hpos : ∀ u ∈ S, u ∈ Set.Icc (1 / 2 : ℝ) 2) :
    ∫ u in S, ‖Rfun W u‖ ^ 2 ≤ Rtilde W N B ψ₁ ψ₂ x ^ 2 / ((N : ℝ) * B) := by
  have hψ₁nn : ∀ x, 0 ≤ ψ₁ x := hψ₁.2.1
  have hψ₂nn : ∀ x, 0 ≤ ψ₂ x := hψ₂.2.1
  have hBnn : 0 ≤ (N : ℝ) * B := le_of_lt hB
  have hBpos : 0 ≤ B := by
    by_contra h
    push Not at h
    exact absurd (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg N) h.le) (not_le.mpr hB)
  have hsq : Rtilde W N B ψ₁ ψ₂ x ^ 2 = RtildeSq W N B ψ₁ ψ₂ x :=
    Rtilde_sq W N B ψ₁ ψ₂ x (RtildeSq_nonneg W N B ψ₁ ψ₂ x hψ₁nn hψ₂nn hBpos)
  have hint := RtildeSq_integrable (W := W) (N := N) (B := B) (C₀ := C₀) (x := x)
    hC₀ hψ₁ hψ₂ hB
  have hpt : ∀ u : ℝ, S.indicator (fun u => (N : ℝ) * B * ‖Rfun W u‖ ^ 2) u ≤
        (N : ℝ) * B * ψ₁ ((N : ℝ) * B * (x - u)) * ψ₂ u * ‖Rfun W u‖ ^ 2 := by
    intro u
    by_cases hu : u ∈ S
    · rw [Set.indicator_of_mem hu]
      have h1 : 1 ≤ ψ₁ ((N : ℝ) * B * (x - u)) := hψ₁ge _ (hwin u hu)
      have h2 : 1 ≤ ψ₂ u := hψ₂ge u (hpos u hu)
      calc (N : ℝ) * B * ‖Rfun W u‖ ^ 2
          = (N : ℝ) * B * 1 * 1 * ‖Rfun W u‖ ^ 2 := by ring
        _ ≤ (N : ℝ) * B * ψ₁ ((N : ℝ) * B * (x - u)) * ψ₂ u * ‖Rfun W u‖ ^ 2 := by gcongr
    · rw [Set.indicator_of_notMem hu]
      exact mul_nonneg (mul_nonneg (mul_nonneg hBnn (hψ₁nn _)) (hψ₂nn _)) (sq_nonneg _)
  have hmono : ∫ u : ℝ, S.indicator (fun u => (N : ℝ) * B * ‖Rfun W u‖ ^ 2) u ≤
      ∫ u : ℝ, (N : ℝ) * B * ψ₁ ((N : ℝ) * B * (x - u)) * ψ₂ u * ‖Rfun W u‖ ^ 2 := by
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall (fun u => by
        by_cases hu : u ∈ S
        · rw [Set.indicator_of_mem hu]; positivity
        · rw [Set.indicator_of_notMem hu]; norm_num)
    · simpa using hint
    · exact Filter.Eventually.of_forall hpt
  have hleft : ∫ u : ℝ, S.indicator (fun u => (N : ℝ) * B * ‖Rfun W u‖ ^ 2) u =
      (N : ℝ) * B * ∫ u in S, ‖Rfun W u‖ ^ 2 := by
    rw [MeasureTheory.integral_indicator hmeas, MeasureTheory.integral_const_mul]
  rw [hsq, RtildeSq, le_div_iff₀ hB]
  rw [hleft, mul_comm ((N : ℝ) * B)] at hmono
  exact hmono


end Work.GM.S3
