import Mathlib
import Submission.Work.GM.Affine.far_part_defs
import Submission.Work.GM.Affine.far_window_defs
import Submission.Work.GM.Affine.psi1hat_decay

/-!
# GM §9, the window part of the far weight: definitions

Vocabulary for `Work.GM.Affine.window_part_L2_bound`:

* `Wmaj K T M₁ M₂ M₃ B f ξ`, the weighted window majorant
  `Σ_{p ∈ Pwin T M₁ M₃ B ξ} (M₃²/p.1²)‖Bsum f M₂ (ξ/p.1)‖²‖ψ̂₁(M₃(p.2 - ξ/p.1))‖`;
* `Wcnt K T M₁ M₃ B ξ`, the companion count weight `Σ_{p ∈ Pwin} ‖ψ̂₁(M₃(p.2 - ξ/p.1))‖`;

together with the rewriting lemmas `Wwin_eq_finsum` (the `∑'_ℓ` defining `Wwin` is a finite sum on
the window range `|ℓ| ≤ Lwin`) and `Wwin_sum_eq_pairs` (the `m₁`-sum of `Wwin` is the pair sum over
`Pwin`), used by the pointwise Cauchy–Schwarz step.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false

namespace Work.GM.Affine

noncomputable section

/-- The weighted window majorant: the second factor of the Cauchy–Schwarz bound. -/
def Wmaj (K T M₁ M₂ M₃ B : ℝ) (f : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  ∑ p ∈ Pwin T M₁ M₃ B ξ,
    (M₃ ^ 2 / (p.1 : ℝ) ^ 2) * ‖Bsum f M₂ (ξ / (p.1 : ℝ))‖ ^ 2 *
      ‖psi1hat K (M₃ * ((p.2 : ℝ) - ξ / (p.1 : ℝ)))‖

/-- The companion count weight of the pointwise Cauchy–Schwarz bound. -/
def Wcnt (K T M₁ M₃ B : ℝ) (ξ : ℝ) : ℝ :=
  ∑ p ∈ Pwin T M₁ M₃ B ξ,
    ‖psi1hat K (M₃ * ((p.2 : ℝ) - ξ / (p.1 : ℝ)))‖

lemma Wmaj_nonneg (K T M₁ M₂ M₃ B : ℝ) (f : ℝ → ℝ) (ξ : ℝ) : 0 ≤ Wmaj K T M₁ M₂ M₃ B f ξ := by
  rw [Wmaj]
  exact Finset.sum_nonneg (fun p _ => by positivity)

lemma Wcnt_nonneg (K T M₁ M₃ B : ℝ) (ξ : ℝ) : 0 ≤ Wcnt K T M₁ M₃ B ξ := by
  rw [Wcnt]
  exact Finset.sum_nonneg (fun p _ => by positivity)


/-! ## The window pair sum -/


/-! ## The window pairs -/




/-- **The window weight is a finite `ℓ`-sum.** -/
lemma Wwin_eq_finsum (K T M₁ M₃ B : ℝ) (hM₁ : 0 < M₁) (hM₃ : 0 < M₃) {ξ : ℝ} {m₁ : ℤ}
    (hm₁ : m₁ ∈ R1 M₁) (hξ : |ξ| ≤ T ^ 6) :
    Wwin K M₃ B (ξ / (m₁ : ℝ)) =
      (M₃ : ℂ) * ∑ ℓ ∈ Finset.Icc (-(Lwin T M₁ M₃ B)) (Lwin T M₁ M₃ B),
        (if 2 / M₃ < |(ℓ : ℝ) - ξ / (m₁ : ℝ)| ∧ |(ℓ : ℝ) - ξ / (m₁ : ℝ)| ≤ B / M₃ then
          psi1hat K (M₃ * ((ℓ : ℝ) - ξ / (m₁ : ℝ))) else 0) := by
  have hm₁pos : M₁ < |(m₁ : ℝ)| := (Finset.mem_filter.mp hm₁).2
  have habs : M₁ ≤ |(m₁ : ℝ)| := le_of_lt hm₁pos
  have hy : |ξ / (m₁ : ℝ)| ≤ T ^ 6 / M₁ := by
    rw [abs_div]
    have h1 : |ξ| / |(m₁:ℝ)| ≤ T ^ 6 / |(m₁:ℝ)| :=
      div_le_div_of_nonneg_right hξ (abs_nonneg _)
    have h2 : T ^ 6 / |(m₁:ℝ)| ≤ T ^ 6 / M₁ :=
      div_le_div_of_nonneg_left (by positivity) hM₁ habs
    linarith
  have hceil : ((⌈T ^ 6 / M₁ + B / M₃⌉ : ℤ) : ℝ) ≥ T ^ 6 / M₁ + B / M₃ := by
    have := Int.le_ceil (T ^ 6 / M₁ + B / M₃); push_cast; linarith
  have hLbound : ((Lwin T M₁ M₃ B : ℤ) : ℝ) ≥ T ^ 6 / M₁ + B / M₃ + 1 := by
    rw [Lwin]; push_cast; linarith [hceil]
  rw [Wwin]
  congr 1
  refine tsum_eq_sum (fun ℓ hℓ => ?_)
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hℓ
  have hfar : B / M₃ < |(ℓ : ℝ) - ξ / (m₁ : ℝ)| := by
    rcases hℓ with h | h
    · have h1 : ℓ ≤ -(Lwin T M₁ M₃ B) - 1 := by omega
      have h2 : ((ℓ:ℤ) : ℝ) ≤ -((Lwin T M₁ M₃ B : ℤ) : ℝ) - 1 := by exact_mod_cast h1
      have h5 : |((ℓ:ℤ) : ℝ) - ξ / (m₁:ℝ)| ≥ -((ℓ:ℤ) : ℝ) - |ξ / (m₁:ℝ)| := by
        have h6 : |((ℓ:ℤ) : ℝ)| ≤ |((ℓ:ℤ) : ℝ) - ξ/(m₁:ℝ)| + |ξ/(m₁:ℝ)| := by
          have h7 := abs_add_le (((ℓ:ℤ) : ℝ) - ξ/(m₁:ℝ)) (ξ/(m₁:ℝ))
          rwa [sub_add_cancel] at h7
        have h8 : |((ℓ:ℤ) : ℝ)| ≥ -((ℓ:ℤ) : ℝ) := neg_le_abs _
        linarith
      linarith
    · have h1 : (Lwin T M₁ M₃ B) + 1 ≤ ℓ := by omega
      have h2 : ((Lwin T M₁ M₃ B : ℤ) : ℝ) + 1 ≤ ((ℓ:ℤ) : ℝ) := by exact_mod_cast h1
      have h5 : |((ℓ:ℤ) : ℝ) - ξ / (m₁:ℝ)| ≥ ((ℓ:ℤ) : ℝ) - |ξ / (m₁:ℝ)| := by
        have h6 : |((ℓ:ℤ) : ℝ)| ≤ |((ℓ:ℤ) : ℝ) - ξ/(m₁:ℝ)| + |ξ/(m₁:ℝ)| := by
          have h7 := abs_add_le (((ℓ:ℤ) : ℝ) - ξ/(m₁:ℝ)) (ξ/(m₁:ℝ))
          rwa [sub_add_cancel] at h7
        have h8 : |((ℓ:ℤ) : ℝ)| ≥ ((ℓ:ℤ) : ℝ) := le_abs_self _
        linarith
      linarith
  rw [if_neg (fun hh => absurd hh.2 (not_le.mpr hfar))]

/-- **The window part of `ghatFar` is the pair sum over `Pwin`.** -/
lemma Wwin_sum_eq_pairs (K T M₁ M₂ M₃ B : ℝ) (hM₁ : 0 < M₁) (hM₃ : 0 < M₃)
    {f : ℝ → ℝ} {ξ : ℝ} (hξ : |ξ| ≤ T ^ 6) :
    (∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
        Wwin K M₃ B (ξ / (m₁ : ℝ)))
      = ∑ p ∈ Pwin T M₁ M₃ B ξ, aTerm K M₂ M₃ f ξ p := by
  have h1 : (∑ m₁ ∈ R1 M₁, ((|(m₁ : ℝ)| : ℝ) : ℂ)⁻¹ * Bsum f M₂ (ξ / (m₁ : ℝ)) *
        Wwin K M₃ B (ξ / (m₁ : ℝ)))
      = ∑ m₁ ∈ R1 M₁, ∑ ℓ ∈ Finset.Icc (-(Lwin T M₁ M₃ B)) (Lwin T M₁ M₃ B),
          (if 2 / M₃ < |(ℓ : ℝ) - ξ / (m₁ : ℝ)| ∧ |(ℓ : ℝ) - ξ / (m₁ : ℝ)| ≤ B / M₃ then
            aTerm K M₂ M₃ f ξ (m₁, ℓ) else 0) := by
    apply Finset.sum_congr rfl
    intro m₁ hm₁
    rw [Wwin_eq_finsum K T M₁ M₃ B hM₁ hM₃ hm₁ hξ, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    by_cases h : 2 / M₃ < |(ℓ : ℝ) - ξ / (m₁ : ℝ)| ∧ |(ℓ : ℝ) - ξ / (m₁ : ℝ)| ≤ B / M₃
    · rw [if_pos h, if_pos h]
      simp only [aTerm]
    · rw [if_neg h, if_neg h, mul_zero, mul_zero]
  rw [h1, Pwin, Finset.sum_filter]
  exact (Finset.sum_product (R1 M₁) (Finset.Icc (-(Lwin T M₁ M₃ B)) (Lwin T M₁ M₃ B))
    (fun p : ℤ × ℤ => if 2 / M₃ < |((p.2 : ℝ) - ξ / (p.1 : ℝ))| ∧
      |((p.2 : ℝ) - ξ / (p.1 : ℝ))| ≤ B / M₃ then aTerm K M₂ M₃ f ξ p else 0)).symm




end

end Work.GM.Affine
