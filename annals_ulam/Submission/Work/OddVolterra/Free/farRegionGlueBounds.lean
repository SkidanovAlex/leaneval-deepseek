import Mathlib
import Submission.Work.OddVolterra.Free.glueChainAux
import Submission.Work.OddVolterra.Free.glueChainAux2
import Submission.Work.OddVolterra.Free.glueChainAux3

/-!
# Far-region glue bounds

This proves `Work.OddVolterra.Free.farRegionGlueBounds`: for `4/5 ≤ cos α` and functions `R`, `S`
which are twice differentiable (in the pointwise sense) at `cos α`, with
`|R (cos α)|, |deriv R (cos α)|, |deriv (deriv R) (cos α)| ≤ M` (and the same for `S`), the
quantities `2 R (cos α) / cos α ^ 2`, `2 S (cos α) / cos α` and their first two derivatives are
bounded by `K * M` for a universal constant `K`.

The pointwise nature of the hypotheses is essential: `deriv` is `0` at points of
non-differentiability, and the second derivative of `α ↦ 2 R (cos α) / cos α ^ 2` can only be
controlled through the junk-value aware chain rule `deriv_cos_comp`, the explicit second
derivative bound `deriv_deriv_two_mul_div_sq_bound` at `cos α`, and a slope estimate in the
degenerate case `cos α = 1`.
-/

namespace Work.OddVolterra.Free

open Filter
open scoped Topology

/-- Auxiliary: the second derivative at `α` of `F ∘ cos`, in terms of the junk-value aware
derivatives of `F` at `cos α`.  It uses the pointwise chain rule `deriv_cos_comp` twice, so it
requires only that `deriv F` be differentiable at `cos α`. -/
theorem deriv_deriv_cos_comp (F : ℝ → ℝ) (α : ℝ)
    (h : DifferentiableAt ℝ (deriv F) (Real.cos α)) :
    deriv (deriv (fun y : ℝ => F (Real.cos y))) α
      = deriv (deriv F) (Real.cos α) * Real.sin α ^ 2 - deriv F (Real.cos α) * Real.cos α := by
  have hH : deriv (fun y : ℝ => F (Real.cos y))
      = fun y : ℝ => deriv F (Real.cos y) * (-Real.sin y) := funext (deriv_cos_comp F)
  rw [hH]
  have hA : DifferentiableAt ℝ (fun y : ℝ => deriv F (Real.cos y)) α :=
    h.comp α Real.differentiableAt_cos
  have hB : DifferentiableAt ℝ (fun y : ℝ => -Real.sin y) α := by fun_prop
  change deriv ((fun y : ℝ => deriv F (Real.cos y)) * fun y : ℝ => -Real.sin y) α
    = deriv (deriv F) (Real.cos α) * Real.sin α ^ 2 - deriv F (Real.cos α) * Real.cos α
  rw [deriv_mul hA hB]
  have hAd : deriv (fun y : ℝ => deriv F (Real.cos y)) α
      = deriv (deriv F) (Real.cos α) * (-Real.sin α) := deriv_cos_comp (deriv F) α
  have hBd : deriv (fun y : ℝ => -Real.sin y) α = -Real.cos α := by
    have hs : HasDerivAt (fun y : ℝ => -Real.sin y) (-Real.cos α) α := (Real.hasDerivAt_sin α).neg
    rw [HasDerivAt.deriv hs]
  rw [hAd, hBd]
  ring

theorem farRegionGlueBounds :
    ∃ K : ℝ, 0 < K ∧ ∀ {R S : ℝ → ℝ} {M α : ℝ},
      0 ≤ M →
      4 / 5 ≤ Real.cos α →
      DifferentiableAt ℝ R (Real.cos α) →
      DifferentiableAt ℝ (deriv R) (Real.cos α) →
      DifferentiableAt ℝ S (Real.cos α) →
      DifferentiableAt ℝ (deriv S) (Real.cos α) →
      |R (Real.cos α)| ≤ M →
      |deriv R (Real.cos α)| ≤ M →
      |deriv (deriv R) (Real.cos α)| ≤ M →
      |S (Real.cos α)| ≤ M →
      |deriv S (Real.cos α)| ≤ M →
      |deriv (deriv S) (Real.cos α)| ≤ M →
      |2 * R (Real.cos α) / Real.cos α ^ 2| ≤ K * M ∧
      |deriv (fun α : ℝ => 2 * R (Real.cos α) / Real.cos α ^ 2) α| ≤ K * M ∧
      |deriv (deriv (fun α : ℝ => 2 * R (Real.cos α) / Real.cos α ^ 2)) α| ≤ K * M ∧
      |2 * S (Real.cos α) / Real.cos α| ≤ K * M ∧
      |deriv (fun α : ℝ => 2 * S (Real.cos α) / Real.cos α) α| ≤ K * M ∧
      |deriv (deriv (fun α : ℝ => 2 * S (Real.cos α) / Real.cos α)) α| ≤ K * M := by
  obtain ⟨KR, hKRpos, hKRb⟩ := deriv_deriv_two_mul_div_sq_bound
  obtain ⟨KS, hKSpos, hKSb⟩ := deriv_deriv_two_mul_div_bound
  refine ⟨1000 + KR + KS, by positivity, ?_⟩
  intro R S M α hM hcos hRd hRd' hSd hSd' hRu hR'u hR''u hSu hS'u hS''u
  have hupos : 0 < Real.cos α := by linarith
  have hue : Real.cos α ≠ 0 := ne_of_gt hupos
  have hK : (1000 + KR + KS) * M = 1000 * M + KR * M + KS * M := by ring
  have hKRm : (0:ℝ) ≤ KR * M := mul_nonneg (le_of_lt hKRpos) hM
  have hKSm : (0:ℝ) ≤ KS * M := mul_nonneg (le_of_lt hKSpos) hM
  have hbig : ∀ x : ℝ, x ≤ 11 * M + (KR * M + KS * M) → x ≤ 1000 * M + KR * M + KS * M := by
    intro x hx
    linarith [hx, hM, hKRm, hKSm]
  have hI1 : 1 / Real.cos α ≤ 5 / 4 := by
    calc 1 / Real.cos α ≤ 1 / ((4:ℝ) / 5) := one_div_le_one_div_of_le (by norm_num) hcos
      _ = 5 / 4 := by norm_num
  have hI2 : 1 / Real.cos α ^ 2 ≤ 25 / 16 := by
    have hp : ((4:ℝ) / 5) ^ 2 ≤ Real.cos α ^ 2 := by gcongr
    calc 1 / Real.cos α ^ 2 ≤ 1 / (((4:ℝ) / 5) ^ 2) := one_div_le_one_div_of_le (by norm_num) hp
      _ = 25 / 16 := by norm_num
  have hI3 : 1 / Real.cos α ^ 3 ≤ 125 / 64 := by
    have hp : ((4:ℝ) / 5) ^ 3 ≤ Real.cos α ^ 3 := by gcongr
    calc 1 / Real.cos α ^ 3 ≤ 1 / (((4:ℝ) / 5) ^ 3) := one_div_le_one_div_of_le (by norm_num) hp
      _ = 125 / 64 := by norm_num
  have hI4 : 1 / Real.cos α ^ 4 ≤ 625 / 256 := by
    have hp : ((4:ℝ) / 5) ^ 4 ≤ Real.cos α ^ 4 := by gcongr
    calc 1 / Real.cos α ^ 4 ≤ 1 / (((4:ℝ) / 5) ^ 4) := one_div_le_one_div_of_le (by norm_num) hp
      _ = 625 / 256 := by norm_num
  -- a general term estimate
  have hterm : ∀ (c : ℝ), 0 ≤ c → ∀ (D : ℝ), |D| ≤ M → ∀ (k : ℕ), ∀ (C : ℝ),
      1 / Real.cos α ^ k ≤ C → |c * D / Real.cos α ^ k| ≤ c * M * C := by
    intro c hc D hD k C hC
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < Real.cos α ^ k), abs_mul, abs_of_nonneg hc]
    calc c * |D| / Real.cos α ^ k = c * |D| * (1 / Real.cos α ^ k) := by ring
      _ ≤ c * M * (1 / Real.cos α ^ k) := by gcongr
      _ ≤ c * M * C := by gcongr
  -- the glue functions and their first derivatives
  have hFRd : DifferentiableAt ℝ (fun v : ℝ => 2 * R v / v ^ 2) (Real.cos α) :=
    differentiableAt_two_mul_div_sq R hue hRd
  have hFRv : deriv (fun v : ℝ => 2 * R v / v ^ 2) (Real.cos α)
      = 2 * deriv R (Real.cos α) / Real.cos α ^ 2 - 4 * R (Real.cos α) / Real.cos α ^ 3 :=
    deriv_two_mul_div_sq R hue hRd
  have hFSd : DifferentiableAt ℝ (fun v : ℝ => 2 * S v / v) (Real.cos α) :=
    differentiableAt_two_mul_div S hue hSd
  have hFSv : deriv (fun v : ℝ => 2 * S v / v) (Real.cos α)
      = 2 * deriv S (Real.cos α) / Real.cos α - 2 * S (Real.cos α) / Real.cos α ^ 2 :=
    deriv_two_mul_div S hue hSd
  have hFRb : |deriv (fun v : ℝ => 2 * R v / v ^ 2) (Real.cos α)| ≤ 11 * M := by
    rw [hFRv]
    have h1 := hterm 2 (by norm_num) (deriv R (Real.cos α)) hR'u 2 (25 / 16) hI2
    have h2 := hterm 4 (by norm_num) (R (Real.cos α)) hRu 3 (125 / 64) hI3
    have h3 := abs_sub_le_abs_add (2 * deriv R (Real.cos α) / Real.cos α ^ 2)
      (4 * R (Real.cos α) / Real.cos α ^ 3)
    calc |2 * deriv R (Real.cos α) / Real.cos α ^ 2 - 4 * R (Real.cos α) / Real.cos α ^ 3|
        ≤ |2 * deriv R (Real.cos α) / Real.cos α ^ 2| + |4 * R (Real.cos α) / Real.cos α ^ 3| := h3
      _ ≤ 2 * M * (25 / 16) + 4 * M * (125 / 64) := by linarith only [h1, h2]
      _ ≤ 11 * M := by linarith only [hM]
  have hFSb : |deriv (fun v : ℝ => 2 * S v / v) (Real.cos α)| ≤ 11 * M := by
    rw [hFSv]
    have h1 := hterm 2 (by norm_num) (deriv S (Real.cos α)) hS'u 1 (5 / 4) (by simpa using hI1)
    rw [pow_one] at h1
    have h2 := hterm 2 (by norm_num) (S (Real.cos α)) hSu 2 (25 / 16) hI2
    have h3 := abs_sub_le_abs_add (2 * deriv S (Real.cos α) / Real.cos α)
      (2 * S (Real.cos α) / Real.cos α ^ 2)
    calc |2 * deriv S (Real.cos α) / Real.cos α - 2 * S (Real.cos α) / Real.cos α ^ 2|
        ≤ |2 * deriv S (Real.cos α) / Real.cos α| + |2 * S (Real.cos α) / Real.cos α ^ 2| := h3
      _ ≤ 2 * M * (5 / 4) + 2 * M * (25 / 16) := by linarith only [h1, h2]
      _ ≤ 11 * M := by linarith only [hM]
  -- first derivative bound for a composition with `cos`
  have hcompbound : ∀ (F : ℝ → ℝ), DifferentiableAt ℝ F (Real.cos α) →
      |deriv F (Real.cos α)| ≤ 11 * M →
      |deriv (fun α : ℝ => F (Real.cos α)) α| ≤ (1000 + KR + KS) * M := by
    intro F hFd hFb
    have hc : deriv (fun α : ℝ => F (Real.cos α)) α
        = deriv F (Real.cos α) * deriv Real.cos α :=
      deriv_comp (h₂ := F) (h := Real.cos) (x := α) hFd Real.differentiableAt_cos
    rw [hc, Real.deriv_cos, hK]
    have hs : |Real.sin α| ≤ 1 := Real.abs_sin_le_one α
    have h1 : |deriv F (Real.cos α) * -Real.sin α| ≤ 11 * M := by
      rw [abs_mul, abs_neg]
      calc |deriv F (Real.cos α)| * |Real.sin α| ≤ 11 * M * 1 :=
            mul_le_mul hFb hs (abs_nonneg _) (by positivity)
        _ = 11 * M := by ring
    linarith [h1, hM, hKRm, hKSm]
  -- bound 1
  have b1 : |2 * R (Real.cos α) / Real.cos α ^ 2| ≤ (1000 + KR + KS) * M := by
    have h := hterm 2 (by norm_num) (R (Real.cos α)) hRu 2 (25 / 16) hI2
    rw [hK]
    linarith [h, hM, hKRm, hKSm]
  -- bound 2
  have b2 := hcompbound (fun v : ℝ => 2 * R v / v ^ 2) hFRd hFRb
  -- bound 4
  have b4 : |2 * S (Real.cos α) / Real.cos α| ≤ (1000 + KR + KS) * M := by
    have h := hterm 2 (by norm_num) (S (Real.cos α)) hSu 1 (5 / 4) (by simpa using hI1)
    rw [pow_one] at h
    rw [hK]
    linarith [h, hM, hKRm, hKSm]
  -- bound 5
  have b5 := hcompbound (fun v : ℝ => 2 * S v / v) hFSd hFSb
  -- bound 3
  have b3 : |deriv (deriv (fun α : ℝ => 2 * R (Real.cos α) / Real.cos α ^ 2)) α|
      ≤ (1000 + KR + KS) * M := by
    change |deriv (deriv (fun y : ℝ => (fun v : ℝ => 2 * R v / v ^ 2) (Real.cos y))) α| ≤ _
    by_cases hD : DifferentiableAt ℝ (deriv (fun v : ℝ => 2 * R v / v ^ 2)) (Real.cos α)
    · rw [deriv_deriv_cos_comp (fun v : ℝ => 2 * R v / v ^ 2) α hD]
      have h1 : |deriv (deriv (fun v : ℝ => 2 * R v / v ^ 2)) (Real.cos α)| ≤ KR * M :=
        hKRb hM hcos hRd hRd' hRu hR'u hR''u
      have h4 : |deriv (deriv (fun v : ℝ => 2 * R v / v ^ 2)) (Real.cos α)| * Real.sin α ^ 2
          ≤ KR * M := by
        calc |deriv (deriv (fun v : ℝ => 2 * R v / v ^ 2)) (Real.cos α)| * Real.sin α ^ 2
            ≤ KR * M * 1 := by
              exact mul_le_mul h1 (Real.sin_sq_le_one α) (sq_nonneg _) (by positivity)
          _ = KR * M := by ring
      have h5 : |deriv (fun v : ℝ => 2 * R v / v ^ 2) (Real.cos α)| * |Real.cos α| ≤ 11 * M := by
        calc |deriv (fun v : ℝ => 2 * R v / v ^ 2) (Real.cos α)| * |Real.cos α| ≤ 11 * M * 1 := by
              exact mul_le_mul hFRb (Real.abs_cos_le_one α) (abs_nonneg _) (by positivity)
          _ = 11 * M := by ring
      have h3 := abs_sub_le_abs_add
        (deriv (deriv (fun v : ℝ => 2 * R v / v ^ 2)) (Real.cos α) * Real.sin α ^ 2)
        (deriv (fun v : ℝ => 2 * R v / v ^ 2) (Real.cos α) * Real.cos α)
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (Real.sin α))] at h3
      rw [hK]
      linarith [h3, h4, h5, hM, hKRm, hKSm]
    · by_cases hsin : Real.sin α = 0
      · -- degenerate case: `cos α = 1`
        have hc1 : Real.cos α = 1 := by
          have hsq : Real.cos α ^ 2 = 1 := by
            have h : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
            rw [hsin] at h
            simpa using h
          have h2 : Real.cos α = 1 ∨ Real.cos α = -1 := sq_eq_one_iff.mp hsq
          rcases h2 with h3 | h3
          · exact h3
          · linarith only [h3, hcos]
        have hH0 : deriv (fun y : ℝ => (fun v : ℝ => 2 * R v / v ^ 2) (Real.cos y)) α = 0 := by
          have hc : deriv (fun y : ℝ => (fun v : ℝ => 2 * R v / v ^ 2) (Real.cos y)) α
              = deriv (fun v : ℝ => 2 * R v / v ^ 2) (Real.cos α) * deriv Real.cos α :=
            deriv_comp (h₂ := fun v : ℝ => 2 * R v / v ^ 2) (h := Real.cos) (x := α)
              hFRd Real.differentiableAt_cos
          rw [hc, Real.deriv_cos, hsin]
          ring
        have hbd := eventually_abs_deriv_two_mul_div_sq_le (R := R) (M := M) hM
          (by simpa [hc1] using hRd)
          (by simpa [hc1] using hRd')
          (by simpa [hc1] using hRu)
          (by simpa [hc1] using hR'u)
          (by simpa [hc1] using hR''u)
        have hdeg := abs_deriv_deriv_comp_cos_degenerate (F := fun v : ℝ => 2 * R v / v ^ 2)
          (α := α) (M := M) (C := 40) hM (by norm_num) hc1 hsin hFRd hH0 hbd
        rw [hK]
        linarith [hdeg, hM, hKRm, hKSm]
      · -- `sin α ≠ 0`: the slope of `deriv (F ∘ cos)` at `α` is unbounded, so the derivative is `0`
        have hnot : ¬ DifferentiableAt ℝ
            (deriv (fun y : ℝ => (fun v : ℝ => 2 * R v / v ^ 2) (Real.cos y))) α := by
          intro hdH
          have hA : ¬ DifferentiableAt ℝ ((deriv (fun v : ℝ => 2 * R v / v ^ 2)) ∘ Real.cos) α :=
            not_differentiableAt_comp_cos hsin hD
          apply hA
          have hsin_near : ∀ᶠ y in 𝓝 α, Real.sin y ≠ 0 :=
            Real.continuous_sin.continuousAt.eventually
              (eventually_ne_nhds (a := Real.sin α) (b := 0) hsin)
          have hev : ((deriv (fun v : ℝ => 2 * R v / v ^ 2)) ∘ Real.cos) =ᶠ[𝓝 α]
              (fun y : ℝ => deriv (fun y : ℝ => (fun v : ℝ => 2 * R v / v ^ 2) (Real.cos y)) y
                * (-1 / Real.sin y)) := by
            filter_upwards [hsin_near] with y hy
            rw [Function.comp_apply, deriv_cos_comp (fun v : ℝ => 2 * R v / v ^ 2) y]
            field_simp
          exact hev.differentiableAt_iff.mpr (hdH.mul ((differentiableAt_const (-1)).div
            Real.differentiableAt_sin hsin))
        rw [deriv_zero_of_not_differentiableAt hnot, abs_zero]
        rw [hK]
        have h0 : (0:ℝ) ≤ 1000 * M + KR * M + KS * M := by linarith [hM, hKRm, hKSm]
        exact h0
  -- bound 6
  have b6 : |deriv (deriv (fun α : ℝ => 2 * S (Real.cos α) / Real.cos α)) α|
      ≤ (1000 + KR + KS) * M := by
    change |deriv (deriv (fun y : ℝ => (fun v : ℝ => 2 * S v / v) (Real.cos y))) α| ≤ _
    by_cases hD : DifferentiableAt ℝ (deriv (fun v : ℝ => 2 * S v / v)) (Real.cos α)
    · rw [deriv_deriv_cos_comp (fun v : ℝ => 2 * S v / v) α hD]
      have h1 : |deriv (deriv (fun v : ℝ => 2 * S v / v)) (Real.cos α)| ≤ KS * M :=
        hKSb hM hcos hSd hSd' hSu hS'u hS''u
      have h4 : |deriv (deriv (fun v : ℝ => 2 * S v / v)) (Real.cos α)| * Real.sin α ^ 2
          ≤ KS * M := by
        calc |deriv (deriv (fun v : ℝ => 2 * S v / v)) (Real.cos α)| * Real.sin α ^ 2
            ≤ KS * M * 1 := by
              exact mul_le_mul h1 (Real.sin_sq_le_one α) (sq_nonneg _) (by positivity)
          _ = KS * M := by ring
      have h5 : |deriv (fun v : ℝ => 2 * S v / v) (Real.cos α)| * |Real.cos α| ≤ 11 * M := by
        calc |deriv (fun v : ℝ => 2 * S v / v) (Real.cos α)| * |Real.cos α| ≤ 11 * M * 1 := by
              exact mul_le_mul hFSb (Real.abs_cos_le_one α) (abs_nonneg _) (by positivity)
          _ = 11 * M := by ring
      have h3 := abs_sub_le_abs_add
        (deriv (deriv (fun v : ℝ => 2 * S v / v)) (Real.cos α) * Real.sin α ^ 2)
        (deriv (fun v : ℝ => 2 * S v / v) (Real.cos α) * Real.cos α)
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (Real.sin α))] at h3
      rw [hK]
      linarith [h3, h4, h5, hM, hKRm, hKSm]
    · by_cases hsin : Real.sin α = 0
      · have hc1 : Real.cos α = 1 := by
          have hsq : Real.cos α ^ 2 = 1 := by
            have h : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
            rw [hsin] at h
            simpa using h
          have h2 : Real.cos α = 1 ∨ Real.cos α = -1 := sq_eq_one_iff.mp hsq
          rcases h2 with h3 | h3
          · exact h3
          · linarith only [h3, hcos]
        have hH0 : deriv (fun y : ℝ => (fun v : ℝ => 2 * S v / v) (Real.cos y)) α = 0 := by
          have hc : deriv (fun y : ℝ => (fun v : ℝ => 2 * S v / v) (Real.cos y)) α
              = deriv (fun v : ℝ => 2 * S v / v) (Real.cos α) * deriv Real.cos α :=
            deriv_comp (h₂ := fun v : ℝ => 2 * S v / v) (h := Real.cos) (x := α)
              hFSd Real.differentiableAt_cos
          rw [hc, Real.deriv_cos, hsin]
          ring
        have hbd := eventually_abs_deriv_two_mul_div_le (S := S) (M := M) hM
          (by simpa [hc1] using hSd)
          (by simpa [hc1] using hSd')
          (by simpa [hc1] using hSu)
          (by simpa [hc1] using hS'u)
          (by simpa [hc1] using hS''u)
        have hdeg := abs_deriv_deriv_comp_cos_degenerate (F := fun v : ℝ => 2 * S v / v)
          (α := α) (M := M) (C := 12) hM (by norm_num) hc1 hsin hFSd hH0 hbd
        rw [hK]
        linarith [hdeg, hM, hKRm, hKSm]
      · have hnot : ¬ DifferentiableAt ℝ
            (deriv (fun y : ℝ => (fun v : ℝ => 2 * S v / v) (Real.cos y))) α := by
          intro hdH
          have hA : ¬ DifferentiableAt ℝ ((deriv (fun v : ℝ => 2 * S v / v)) ∘ Real.cos) α :=
            not_differentiableAt_comp_cos hsin hD
          apply hA
          have hsin_near : ∀ᶠ y in 𝓝 α, Real.sin y ≠ 0 :=
            Real.continuous_sin.continuousAt.eventually
              (eventually_ne_nhds (a := Real.sin α) (b := 0) hsin)
          have hev : ((deriv (fun v : ℝ => 2 * S v / v)) ∘ Real.cos) =ᶠ[𝓝 α]
              (fun y : ℝ => deriv (fun y : ℝ => (fun v : ℝ => 2 * S v / v) (Real.cos y)) y
                * (-1 / Real.sin y)) := by
            filter_upwards [hsin_near] with y hy
            rw [Function.comp_apply, deriv_cos_comp (fun v : ℝ => 2 * S v / v) y]
            field_simp
          exact hev.differentiableAt_iff.mpr (hdH.mul ((differentiableAt_const (-1)).div
            Real.differentiableAt_sin hsin))
        rw [deriv_zero_of_not_differentiableAt hnot, abs_zero]
        rw [hK]
        have h0 : (0:ℝ) ≤ 1000 * M + KR * M + KS * M := by linarith [hM, hKRm, hKSm]
        exact h0
  exact ⟨b1, b2, b3, b4, b5, b6⟩

end Work.OddVolterra.Free
