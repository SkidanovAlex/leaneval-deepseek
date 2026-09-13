/-
# The two-sided (full) Harnack inequality on a ball

`Submission.Savin.HarnackScale.harnack_scaled` is the *pointwise* Harnack inequality: a nonnegative
solution on `ball x₀ (5ρ/2)` satisfies `Φ ≤ C Φ x₀` on `closedBall x₀ (ρ/6)`.

The classical oscillation/"Hölder" iteration (Savin's Corollary 1.2 and Corollary 3.3) is instead
driven by the **two-sided** form

  `sup_{B_R(x₀)} Φ ≤ C inf_{B_R(x₀)} Φ   (Φ ≥ 0 a solution, small)`,

which follows from the pointwise form by a *chain of balls*: for `x, y ∈ closedBall x₀ (R/2)` one
subdivides the segment `[y,x]` into `60` pieces of length `< (R/5)/6` and applies the pointwise
Harnack at the successive centres.  Along the chain the smallness hypotheses are *uniform* because
every ball has radius comparable with `R` (this is why the chain is run at fixed scale rather than
at geometrically decreasing scales).

Two ingredients are isolated here:
* `harnack_scaled_nonneg`: `harnack_scaled` with `0 ≤ ε` (rather than `0 < ε`); the case `ε = 0`
  is the strong maximum principle `Φ x₀ = 0 → Φ ≡ 0` and is obtained as a limit of the positive
  case,
* `harnack_full`: the chain.
-/
import Mathlib
import ChallengeDeps
import Submission.Savin.HarnackScale

open Metric MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace Topology ENNReal Pointwise

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

/-- **The scale-invariant Harnack inequality with `0 ≤ ε`.**  Same as `harnack_scaled`, but the
normalisation constant is only assumed nonnegative; the case `ε = 0` is the strong maximum
principle for the small-perturbation equation (a nonnegative small solution vanishing at an
interior point vanishes on a ball around it). -/
theorem harnack_scaled_nonneg_uniform {c c' Y p M : ℝ} (hc : 0 < c) (hc'pos : 0 < c')
    (hYnn : 0 ≤ Y) (hp : 0 < p) (hM1 : 1 < M)
    (hM : M = 1 + 128 * ((1 / p) * (2 ^ p - 1))) (hpbig : 16 * c' / c + 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : ℝ⁴ →L[ℝ] ℝ⁴) (hA : A.IsSymmetric) (hA1 : s2 A = 1)
      (htrA : 0 < trOp A) (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪cofOp A v, v⟫)
      (hcq' : ∀ v : ℝ⁴, ⟪cofOp A v, v⟫ ≤ c' * ‖v‖ ^ 2)
      (hYb : 2 * trOp (cofOp A) / c ≤ Y)
      (Φ : ℝ⁴ → ℝ) (x₀ : ℝ⁴) (R ε Λ : ℝ), 0 < R → 0 ≤ ε → 0 < Λ →
      ContDiffOn ℝ 2 Φ (ball x₀ (5 * R / 2)) →
      (∀ x ∈ ball x₀ (5 * R / 2), s2 (A + hessOp Φ x) = 1) →
      (∀ x ∈ ball x₀ (5 * R / 2), 0 < trOp (A + hessOp Φ x)) →
      (∀ x ∈ ball x₀ (5 * R / 2), 0 ≤ Φ x) → (∀ x ∈ ball x₀ (5 * R / 2), Φ x ≤ Λ) →
      Φ x₀ ≤ ε →
      768 * Λ * 2 ^ (2 * p + 4) ≤ c * R ^ 2 → 1536 * ε * M ≤ c * R ^ 2 →
      ∀ y ∈ closedBall x₀ (R / 6), Φ y ≤ C * ε := by
  obtain ⟨C, hCpos, hC⟩ := harnack_scaled_uniform (Y := Y) hc hc'pos hYnn hp hM1 hM hpbig
  have hMpos : 0 < M := by linarith
  refine ⟨C, hCpos, ?_⟩
  intro A hA hA1 htrA hcq hcq' hYb Φ x₀ R ε Λ hR hε hΛ hΦ heq hpos hpos0 hub h0 hsmallc hsmallε
  rcases lt_or_eq_of_le hε with hεpos | hε0
  · exact hC A hA hA1 htrA hcq hcq' hYb Φ x₀ R ε Λ hR hεpos hΛ hΦ heq hpos hpos0 hub h0 hsmallc
      hsmallε
  · -- `ε = 0`: the strong maximum principle at `x₀`
    subst hε0
    intro y hy
    refine le_of_forall_pos_le_add (fun δ hδ => ?_)
    have hx₀ball : x₀ ∈ ball x₀ (5 * R / 2) := by
      rw [mem_ball, dist_self]; linarith
    have hΦx₀ : Φ x₀ = 0 := le_antisymm (by simpa using h0) (hpos0 x₀ hx₀ball)
    have hC1 : (0 : ℝ) < C + 1 := by linarith
    set ε' : ℝ := min (δ / (2 * (C + 1))) (c * R ^ 2 / (1536 * M * (C + 1))) with hε'def
    have hcR : 0 < c * R ^ 2 / (1536 * M * (C + 1)) := by positivity
    have hε'pos : 0 < ε' := by
      rw [hε'def]; exact lt_min (by positivity) hcR
    have hε'lt : C * ε' ≤ δ / 2 := by
      rw [hε'def]
      have h2 : min (δ / (2 * (C + 1))) (c * R ^ 2 / (1536 * M * (C + 1)))
          ≤ δ / (2 * (C + 1)) := min_le_left _ _
      have h3 : C * min (δ / (2 * (C + 1))) (c * R ^ 2 / (1536 * M * (C + 1)))
          ≤ C * (δ / (2 * (C + 1))) := mul_le_mul_of_nonneg_left h2 hCpos.le
      have h4 : C * (δ / (2 * (C + 1))) = C * δ / (2 * (C + 1)) := by ring
      rw [h4] at h3
      have h5 : C * δ / (2 * (C + 1)) ≤ δ / 2 := by
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (C + 1))
          (by norm_num : (0 : ℝ) < 2)]
        nlinarith [hδ, hCpos]
      linarith [h3, h5]
    have hsc : 1536 * ε' * M ≤ c * R ^ 2 := by
      rw [hε'def]
      have h2 : min (δ / (2 * (C + 1))) (c * R ^ 2 / (1536 * M * (C + 1)))
          ≤ c * R ^ 2 / (1536 * M * (C + 1)) := min_le_right _ _
      have h4 : (0 : ℝ) ≤ 1536 * M := by positivity
      have h3 : 1536 * min (δ / (2 * (C + 1))) (c * R ^ 2 / (1536 * M * (C + 1))) * M
          ≤ 1536 * (c * R ^ 2 / (1536 * M * (C + 1))) * M := by nlinarith [h2, h4]
      have h5 : 1536 * (c * R ^ 2 / (1536 * M * (C + 1))) * M = c * R ^ 2 / (C + 1) := by
        field_simp
      rw [h5] at h3
      have h6 : c * R ^ 2 / (C + 1) ≤ c * R ^ 2 := by
        rw [div_le_iff₀ hC1]; nlinarith [hc, hR, hCpos]
      linarith [h3, h6]
    have h0' : Φ x₀ ≤ ε' := by rw [hΦx₀]; exact hε'pos.le
    have hres := hC A hA hA1 htrA hcq hcq' hYb Φ x₀ R ε' Λ hR hε'pos hΛ hΦ heq hpos hpos0 hub
      h0' hsmallc hsc
    have hval := hres y hy
    linarith [hval, hε'lt, hδ]

/-- **The two-sided Harnack inequality on a ball.**  Every nonnegative solution of
`s2 (A + D²Φ) = 1` with the positive branch on `ball x₀ R` whose sup `Λ` is small
(`Λ * 25 * 768 * 2^{2p+4} ≤ c R²` and `Λ * 25 * 1536 * M ≤ c R²`) satisfies
`Φ x ≤ C Φ y` for all `x, y ∈ closedBall x₀ (R/2)`. -/
theorem harnack_full_uniform {c c' Y p M : ℝ} (hc : 0 < c) (hc'pos : 0 < c') (hYnn : 0 ≤ Y)
    (hp : 0 < p) (hM1 : 1 < M) (hM : M = 1 + 128 * ((1 / p) * (2 ^ p - 1)))
    (hpbig : 16 * c' / c + 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : ℝ⁴ →L[ℝ] ℝ⁴) (hA : A.IsSymmetric) (hA1 : s2 A = 1)
      (htrA : 0 < trOp A) (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪cofOp A v, v⟫)
      (hcq' : ∀ v : ℝ⁴, ⟪cofOp A v, v⟫ ≤ c' * ‖v‖ ^ 2)
      (hYb : 2 * trOp (cofOp A) / c ≤ Y)
      (Φ : ℝ⁴ → ℝ) (x₀ : ℝ⁴) (R Λ : ℝ), 0 < R → 0 < Λ →
      ContDiffOn ℝ 2 Φ (ball x₀ R) →
      (∀ x ∈ ball x₀ R, s2 (A + hessOp Φ x) = 1) →
      (∀ x ∈ ball x₀ R, 0 < trOp (A + hessOp Φ x)) →
      (∀ x ∈ ball x₀ R, 0 ≤ Φ x) → (∀ x ∈ ball x₀ R, Φ x ≤ Λ) →
      768 * Λ * 2 ^ (2 * p + 4) ≤ c * R ^ 2 / 25 →
      1536 * Λ * M ≤ c * R ^ 2 / 25 →
      ∀ x ∈ closedBall x₀ (R / 2), ∀ y ∈ closedBall x₀ (R / 2), Φ x ≤ C * Φ y := by
  obtain ⟨C, hCpos, hC⟩ := harnack_scaled_nonneg_uniform (Y := Y) hc hc'pos hYnn hp hM1 hM hpbig
  have hMpos : 0 < M := by linarith
  refine ⟨C ^ 60, by positivity, ?_⟩
  intro A hA hA1 htrA hcq hcq' hYb Φ x₀ R Λ hR hΛ hΦ heq hpos hpos0 hub hsc hse x hx y hy
  have hxR : ‖x - x₀‖ ≤ R / 2 := by simpa [mem_closedBall, dist_eq_norm] using hx
  have hyR : ‖y - x₀‖ ≤ R / 2 := by simpa [mem_closedBall, dist_eq_norm] using hy
  set z : ℕ → ℝ⁴ := fun i => y + ((i : ℝ) / 60) • (x - y) with hzdef
  -- the points of the chain lie in `closedBall x₀ (R/2)`
  have hzmem : ∀ i : ℕ, i ≤ 60 → ‖z i - x₀‖ ≤ R / 2 := by
    intro i hi
    have ht0 : (0 : ℝ) ≤ (i : ℝ) / 60 := by positivity
    have ht1 : (i : ℝ) / 60 ≤ 1 := by
      rw [div_le_one (by norm_num : (0 : ℝ) < 60)]
      exact_mod_cast hi
    have hz : z i - x₀ = (1 - (i : ℝ) / 60) • (y - x₀) + ((i : ℝ) / 60) • (x - x₀) := by
      simp only [hzdef]
      module
    rw [hz]
    calc ‖(1 - (i : ℝ) / 60) • (y - x₀) + ((i : ℝ) / 60) • (x - x₀)‖
        ≤ ‖(1 - (i : ℝ) / 60) • (y - x₀)‖ + ‖((i : ℝ) / 60) • (x - x₀)‖ := norm_add_le _ _
      _ = (1 - (i : ℝ) / 60) * ‖y - x₀‖ + ((i : ℝ) / 60) * ‖x - x₀‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (by linarith), abs_of_nonneg ht0]
      _ ≤ (1 - (i : ℝ) / 60) * (R / 2) + ((i : ℝ) / 60) * (R / 2) := by
          have h1 := mul_le_mul_of_nonneg_left hyR (by linarith : (0 : ℝ) ≤ 1 - (i : ℝ) / 60)
          have h2 := mul_le_mul_of_nonneg_left hxR ht0
          linarith
      _ = R / 2 := by ring
  -- the steps of the chain
  have hstep : ∀ i : ℕ, i < 60 → Φ (z (i + 1)) ≤ C * Φ (z i) := by
    intro i hi
    have hzm : ‖z i - x₀‖ ≤ R / 2 := hzmem i (by omega)
    have hsub : ball (z i) (5 * (R / 5) / 2) ⊆ ball x₀ R := by
      intro w hw
      rw [mem_ball] at hw ⊢
      have he : 5 * (R / 5) / 2 = R / 2 := by ring
      rw [he] at hw
      rw [dist_eq_norm] at hw ⊢
      have h1 : ‖w - x₀‖ ≤ ‖w - z i‖ + ‖z i - x₀‖ := by
        calc ‖w - x₀‖ = ‖(w - z i) + (z i - x₀)‖ := by rw [sub_add_sub_cancel]
          _ ≤ ‖w - z i‖ + ‖z i - x₀‖ := norm_add_le _ _
      linarith
    have hR5 : (0 : ℝ) < R / 5 := by linarith
    have hzi : z i ∈ ball (z i) (5 * (R / 5) / 2) := by
      rw [mem_ball, dist_self]
      have h5 : 5 * (R / 5) / 2 = R / 2 := by ring
      rw [h5]; linarith
    have hcd : ContDiffOn ℝ 2 Φ (ball (z i) (5 * (R / 5) / 2)) := hΦ.mono hsub
    have heq' : ∀ w ∈ ball (z i) (5 * (R / 5) / 2), s2 (A + hessOp Φ w) = 1 :=
      fun w hw => heq w (hsub hw)
    have hpos' : ∀ w ∈ ball (z i) (5 * (R / 5) / 2), 0 < trOp (A + hessOp Φ w) :=
      fun w hw => hpos w (hsub hw)
    have hpos0' : ∀ w ∈ ball (z i) (5 * (R / 5) / 2), 0 ≤ Φ w :=
      fun w hw => hpos0 w (hsub hw)
    have hub' : ∀ w ∈ ball (z i) (5 * (R / 5) / 2), Φ w ≤ Λ :=
      fun w hw => hub w (hsub hw)
    have hsc' : 768 * Λ * 2 ^ (2 * p + 4) ≤ c * (R / 5) ^ 2 := by
      rw [show c * (R / 5) ^ 2 = c * R ^ 2 / 25 from by ring]
      exact hsc
    have hse' : 1536 * Φ (z i) * M ≤ c * (R / 5) ^ 2 := by
      rw [show c * (R / 5) ^ 2 = c * R ^ 2 / 25 from by ring]
      have hle : Φ (z i) ≤ Λ := hub _ (hsub hzi)
      have hm : (0 : ℝ) ≤ 1536 * M := by positivity
      have h2 : Φ (z i) * (1536 * M) ≤ Λ * (1536 * M) := mul_le_mul_of_nonneg_right hle hm
      have h3 : Φ (z i) * (1536 * M) = 1536 * Φ (z i) * M := by ring
      have h4 : Λ * (1536 * M) = 1536 * Λ * M := by ring
      linarith [h2, h3, h4, hse]
    have hres := hC A hA hA1 htrA hcq hcq' hYb Φ (z i) (R / 5) (Φ (z i)) Λ hR5
      (hpos0 _ (hsub hzi)) hΛ hcd heq' hpos' hpos0' hub' le_rfl hsc' hse'
    -- the next point is in the inner ball
    have hnext : ‖z (i + 1) - z i‖ ≤ (R / 5) / 6 := by
      have hz : z (i + 1) - z i = ((1 : ℝ) / 60) • (x - y) := by
        simp only [hzdef, Nat.cast_add, Nat.cast_one]
        module
      rw [hz, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 60)]
      have hxy : ‖x - y‖ ≤ R := by
        have h1 : ‖x - y‖ ≤ ‖x - x₀‖ + ‖x₀ - y‖ := by
          calc ‖x - y‖ = ‖(x - x₀) + (x₀ - y)‖ := by rw [sub_add_sub_cancel]
            _ ≤ ‖x - x₀‖ + ‖x₀ - y‖ := norm_add_le _ _
        have h2 : ‖x₀ - y‖ = ‖y - x₀‖ := norm_sub_rev x₀ y
        linarith [h1, h2, hxR, hyR]
      linarith
    have hmem : z (i + 1) ∈ closedBall (z i) ((R / 5) / 6) := by
      rwa [mem_closedBall, dist_eq_norm]
    exact hres _ hmem
  have hind : ∀ i : ℕ, i ≤ 60 → Φ (z i) ≤ C ^ i * Φ (z 0) := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ j ih =>
        intro hj
        have hj60 : j ≤ 60 := by omega
        have h1 : Φ (z (j + 1)) ≤ C * Φ (z j) := hstep j (by omega)
        have h2 : Φ (z j) ≤ C ^ j * Φ (z 0) := ih hj60
        calc Φ (z (j + 1)) ≤ C * Φ (z j) := h1
          _ ≤ C * (C ^ j * Φ (z 0)) := mul_le_mul_of_nonneg_left h2 hCpos.le
          _ = C ^ (j + 1) * Φ (z 0) := by ring
  have hz60 : z 60 = x := by
    have h : ((60 : ℕ) : ℝ) / 60 = 1 := by norm_num
    simp only [hzdef, h, one_smul]
    abel
  have hz0 : z 0 = y := by
    simp only [hzdef, Nat.cast_zero, zero_div, zero_smul, add_zero]
  have hfin := hind 60 le_rfl
  rw [hz60, hz0] at hfin
  exact hfin

/-- The ellipticity data of a base `A`: `c' > 0` and the trace bound used for the uniform
constants. -/
theorem harnack_base_data {A : ℝ⁴ →L[ℝ] ℝ⁴} {c c' : ℝ} (hc : 0 < c)
    (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪cofOp A v, v⟫)
    (hcq' : ∀ v : ℝ⁴, ⟪cofOp A v, v⟫ ≤ c' * ‖v‖ ^ 2) :
    0 < c' ∧ 0 ≤ 2 * trOp (cofOp A) / c := by
  have hc'pos : 0 < c' := by
    have h1 := hcq (stdB4 0)
    have h2 := hcq' (stdB4 0)
    have h3 : ‖stdB4 0‖ = 1 := stdB4.orthonormal.1 0
    simp only [h3, one_pow, mul_one] at h1 h2
    linarith
  have htrCo : 0 ≤ trOp (cofOp A) := by
    rw [trOp_eq_sum]
    refine Finset.sum_nonneg fun i _ => ?_
    have h2 := hcq (stdB4 i)
    have h3 : ‖stdB4 i‖ = 1 := stdB4.orthonormal.1 i
    rw [h3] at h2
    nlinarith [h2, hc]
  exact ⟨hc'pos, div_nonneg (by linarith [htrCo]) hc.le⟩

/-- **The scale-invariant Harnack inequality with `0 ≤ ε`.**  Same as `harnack_scaled`, but the
normalisation constant is only assumed nonnegative; the case `ε = 0` is the strong maximum
principle for the small-perturbation equation (a nonnegative small solution vanishing at an
interior point vanishes on a ball around it). -/
theorem harnack_scaled_nonneg {A : ℝ⁴ →L[ℝ] ℝ⁴} (hA : A.IsSymmetric) (hA1 : s2 A = 1)
    (htrA : 0 < trOp A) {c c' : ℝ} (hc : 0 < c)
    (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪cofOp A v, v⟫)
    (hcq' : ∀ v : ℝ⁴, ⟪cofOp A v, v⟫ ≤ c' * ‖v‖ ^ 2)
    {p M : ℝ} (hp : 0 < p) (hM1 : 1 < M) (hM : M = 1 + 128 * ((1 / p) * (2 ^ p - 1)))
    (hpbig : 16 * c' / c + 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Φ : ℝ⁴ → ℝ) (x₀ : ℝ⁴) (R ε Λ : ℝ), 0 < R → 0 ≤ ε → 0 < Λ →
      ContDiffOn ℝ 2 Φ (ball x₀ (5 * R / 2)) →
      (∀ x ∈ ball x₀ (5 * R / 2), s2 (A + hessOp Φ x) = 1) →
      (∀ x ∈ ball x₀ (5 * R / 2), 0 < trOp (A + hessOp Φ x)) →
      (∀ x ∈ ball x₀ (5 * R / 2), 0 ≤ Φ x) → (∀ x ∈ ball x₀ (5 * R / 2), Φ x ≤ Λ) →
      Φ x₀ ≤ ε →
      768 * Λ * 2 ^ (2 * p + 4) ≤ c * R ^ 2 → 1536 * ε * M ≤ c * R ^ 2 →
      ∀ y ∈ closedBall x₀ (R / 6), Φ y ≤ C * ε := by
  obtain ⟨hc'pos, hYnn⟩ := harnack_base_data hc hcq hcq'
  obtain ⟨C, hCpos, hC⟩ :=
    harnack_scaled_nonneg_uniform (Y := 2 * trOp (cofOp A) / c) hc hc'pos hYnn hp hM1 hM hpbig
  exact ⟨C, hCpos, hC A hA hA1 htrA hcq hcq' le_rfl⟩

/-- **The two-sided Harnack inequality on a ball.**  Every nonnegative solution of
`s2 (A + D²Φ) = 1` with the positive branch on `ball x₀ R` whose sup `Λ` is small
(`Λ * 25 * 768 * 2^{2p+4} ≤ c R²` and `Λ * 25 * 1536 * M ≤ c R²`) satisfies
`Φ x ≤ C Φ y` for all `x, y ∈ closedBall x₀ (R/2)`. -/
theorem harnack_full {A : ℝ⁴ →L[ℝ] ℝ⁴} (hA : A.IsSymmetric) (hA1 : s2 A = 1)
    (htrA : 0 < trOp A) {c c' : ℝ} (hc : 0 < c)
    (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪cofOp A v, v⟫)
    (hcq' : ∀ v : ℝ⁴, ⟪cofOp A v, v⟫ ≤ c' * ‖v‖ ^ 2)
    {p M : ℝ} (hp : 0 < p) (hM1 : 1 < M) (hM : M = 1 + 128 * ((1 / p) * (2 ^ p - 1)))
    (hpbig : 16 * c' / c + 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Φ : ℝ⁴ → ℝ) (x₀ : ℝ⁴) (R Λ : ℝ), 0 < R → 0 < Λ →
      ContDiffOn ℝ 2 Φ (ball x₀ R) →
      (∀ x ∈ ball x₀ R, s2 (A + hessOp Φ x) = 1) →
      (∀ x ∈ ball x₀ R, 0 < trOp (A + hessOp Φ x)) →
      (∀ x ∈ ball x₀ R, 0 ≤ Φ x) → (∀ x ∈ ball x₀ R, Φ x ≤ Λ) →
      768 * Λ * 2 ^ (2 * p + 4) ≤ c * R ^ 2 / 25 →
      1536 * Λ * M ≤ c * R ^ 2 / 25 →
      ∀ x ∈ closedBall x₀ (R / 2), ∀ y ∈ closedBall x₀ (R / 2), Φ x ≤ C * Φ y := by
  obtain ⟨hc'pos, hYnn⟩ := harnack_base_data hc hcq hcq'
  obtain ⟨C, hCpos, hC⟩ :=
    harnack_full_uniform (Y := 2 * trOp (cofOp A) / c) hc hc'pos hYnn hp hM1 hM hpbig
  exact ⟨C, hCpos, hC A hA hA1 htrA hcq hcq' le_rfl⟩

end

end Submission
