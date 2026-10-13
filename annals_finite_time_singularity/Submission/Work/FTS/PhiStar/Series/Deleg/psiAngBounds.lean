/-
# `Work.FTS.PhiStar.Series.Deleg.psiAngBounds`

Angular bounds for the Gegenbauer family `eFam m θ = cos θ · C^{(3/2)}_{2m+1}(sin θ)`;
the auxiliary definitions and lemmas live in `...Deleg.psiAngDefs`.
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.gC_ode
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero
import Submission.Work.FTS.PhiStar.Series.Deleg.psiAngDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real
open Filter

namespace Work.FTS.PhiStar.Series.Deleg

open Work.FTS.PhiStar.Gegenbauer (eFam gC gC_ode contDiff_gC)


/-! ## The target -/

theorem psiAngBounds :
    (∀ m : ℕ, ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
          ≤ Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))) ∧
    (∀ m : ℕ, ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |deriv (Work.FTS.PhiStar.Gegenbauer.eFam m) θ|
          ≤ 100 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos θ) ^ 2) ∧
    (∀ m : ℕ, ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |iteratedDeriv 2 (Work.FTS.PhiStar.Gegenbauer.eFam m) θ|
          ≤ 1000 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
              * Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
            / (Real.cos θ) ^ 4) ∧
    (∀ m : ℕ, ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |deriv (fun θ' => Real.tan θ' * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ|
          ≤ 1000 * ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (Real.cos θ) ^ 3) := by
  have hsqr : ∀ m : ℕ, Real.sqrt (Npsi m) * Real.sqrt (Npsi m) = Npsi m :=
    fun m => Real.mul_self_sqrt (le_of_lt (Npsi_pos m))
  have hsqrt1 : ∀ m : ℕ, 1 ≤ Real.sqrt (Npsi m) := by
    intro m
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (Npsi_ge_one m)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m θ hθ
    show |eFam m θ| ≤ Real.sqrt (Npsi m)
    obtain ⟨hc, hc1, hs0, hs1, hsq⟩ := sin_cos_facts hθ
    have he : eFam m θ = ug m (Real.sin θ) / Real.cos θ := by
      show Real.cos θ * gC (2 * m + 1) (Real.sin θ) = ug m (Real.sin θ) / Real.cos θ
      rw [gC_div_ug m hθ]
      field_simp
    rw [he, abs_div, abs_of_pos hc, div_le_iff₀ hc]
    exact ug_sin_bound m hθ
  · intro m θ hθ
    show |deriv (Work.FTS.PhiStar.Gegenbauer.eFam m) θ|
      ≤ 100 * Npsi m / (Real.cos θ) ^ 2
    obtain ⟨hc, hc1, hs0, hs1, hsq⟩ := sin_cos_facts hθ
    have hsabs : |Real.sin θ| ≤ 1 := by
      rw [abs_le]; exact ⟨by linarith, hs1⟩
    rw [deriv_eFam m θ]
    calc |-Real.sin θ * gC (2 * m + 1) (Real.sin θ)
          + (Real.cos θ) ^ 2 * deriv (gC (2 * m + 1)) (Real.sin θ)|
        ≤ |Real.sin θ * gC (2 * m + 1) (Real.sin θ)|
          + |(Real.cos θ) ^ 2 * deriv (gC (2 * m + 1)) (Real.sin θ)| := by
            have h2 : |(-Real.sin θ) * gC (2 * m + 1) (Real.sin θ)|
                = |Real.sin θ * gC (2 * m + 1) (Real.sin θ)| := by
              simp only [abs_mul, abs_neg]
            rw [← h2]
            exact abs_add_le _ _
      _ = |Real.sin θ| * |gC (2 * m + 1) (Real.sin θ)|
          + |(Real.cos θ) ^ 2 * deriv (gC (2 * m + 1)) (Real.sin θ)| := by
            simp only [abs_mul]
      _ ≤ 1 * (Real.sqrt (Npsi m) / Real.cos θ)
          + (Npsi m + 2 * Real.sqrt (Npsi m) / Real.cos θ) := by
            refine add_le_add ?_ ?_
            · exact mul_le_mul hsabs (gC_abs_bound m hθ) (abs_nonneg _) (by norm_num)
            · rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Real.cos θ) ^ 2)]
              exact c2_mul_deriv_gC_bound m hθ
      _ = Npsi m + 3 * Real.sqrt (Npsi m) / Real.cos θ := by ring
      _ ≤ 100 * Npsi m / (Real.cos θ) ^ 2 := by
            have h := arith2 hc hc1 (hsqrt1 m)
            rw [Real.sq_sqrt (le_of_lt (Npsi_pos m))] at h
            exact h
  · intro m θ hθ
    show |iteratedDeriv 2 (Work.FTS.PhiStar.Gegenbauer.eFam m) θ|
      ≤ 1000 * Npsi m * Real.sqrt (Npsi m) / (Real.cos θ) ^ 4
    obtain ⟨hc, hc1, hs0, hs1, hsq⟩ := sin_cos_facts hθ
    have hi : iteratedDeriv 2 (eFam m) θ = deriv (deriv (eFam m)) θ := by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rw [hi, deriv2_eFam m θ]
    have hlin : -Real.cos θ * gC (2 * m + 1) (Real.sin θ)
        - 3 * Real.sin θ * Real.cos θ * deriv (gC (2 * m + 1)) (Real.sin θ)
        + (Real.cos θ) ^ 3 * deriv (deriv (gC (2 * m + 1))) (Real.sin θ)
        = Real.sin θ * Real.cos θ * deriv (gC (2 * m + 1)) (Real.sin θ)
          - (Npsi m - 1) * (Real.cos θ * gC (2 * m + 1) (Real.sin θ)) := by
      have hode := (gC_ode (2 * m + 1)).2 (Real.sin θ)
      have hN : Npsi m - 2 = (((2 * m + 1 : ℕ) : ℝ) * (((2 * m + 1 : ℕ) : ℝ) + 3)) := by
        rw [Npsi_eq_two]; ring
      have hkey : (Real.cos θ) ^ 2 * deriv (deriv (gC (2 * m + 1))) (Real.sin θ)
          = 4 * Real.sin θ * deriv (gC (2 * m + 1)) (Real.sin θ)
            - (Npsi m - 2) * gC (2 * m + 1) (Real.sin θ) := by
        have hh := hode
        rw [hsq, ← hN] at hh
        linarith
      linear_combination Real.cos θ * hkey
    rw [hlin]
    have hN1 : 0 ≤ Npsi m - 1 := by have h := Npsi_ge_one m; linarith
    calc |Real.sin θ * Real.cos θ * deriv (gC (2 * m + 1)) (Real.sin θ)
          - (Npsi m - 1) * (Real.cos θ * gC (2 * m + 1) (Real.sin θ))|
        ≤ |Real.sin θ * Real.cos θ * deriv (gC (2 * m + 1)) (Real.sin θ)|
          + |(Npsi m - 1) * (Real.cos θ * gC (2 * m + 1) (Real.sin θ))| :=
            abs_sub_le_add _ _
      _ ≤ (Npsi m + 2 * Real.sqrt (Npsi m) / Real.cos θ) / Real.cos θ
          + (Npsi m - 1) * Real.sqrt (Npsi m) := by
            refine add_le_add (scq_bound m hθ) ?_
            rw [abs_mul, abs_of_nonneg hN1, abs_mul, abs_of_nonneg (le_of_lt hc)]
            exact mul_le_mul_of_nonneg_left (c_mul_gC_bound m hθ) hN1
      _ = Npsi m / Real.cos θ + 2 * Real.sqrt (Npsi m) / (Real.cos θ) ^ 2
          + (Npsi m - 1) * Real.sqrt (Npsi m) := by
            have hcne : Real.cos θ ≠ 0 := ne_of_gt hc
            field_simp
            try ring
      _ ≤ 1000 * Npsi m * Real.sqrt (Npsi m) / (Real.cos θ) ^ 4 := by
            have h := arith3 hc hc1 (hsqrt1 m)
            rw [Real.sq_sqrt (le_of_lt (Npsi_pos m))] at h
            exact h
  · intro m θ hθ
    show |deriv (fun θ' => Real.tan θ' * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ|
      ≤ 1000 * Npsi m / (Real.cos θ) ^ 3
    obtain ⟨hc, hc1, hs0, hs1, hsq⟩ := sin_cos_facts hθ
    rw [deriv_tan_eFam m (ne_of_gt hc)]
    calc |Real.cos θ * gC (2 * m + 1) (Real.sin θ)
          + Real.sin θ * Real.cos θ * deriv (gC (2 * m + 1)) (Real.sin θ)|
        ≤ |Real.cos θ * gC (2 * m + 1) (Real.sin θ)|
          + |Real.sin θ * Real.cos θ * deriv (gC (2 * m + 1)) (Real.sin θ)| :=
            abs_add_le _ _
      _ ≤ Real.sqrt (Npsi m)
          + (Npsi m + 2 * Real.sqrt (Npsi m) / Real.cos θ) / Real.cos θ := by
            refine add_le_add ?_ (scq_bound m hθ)
            rw [abs_mul, abs_of_nonneg (le_of_lt hc)]
            exact c_mul_gC_bound m hθ
      _ = Real.sqrt (Npsi m) + Npsi m / Real.cos θ
          + 2 * Real.sqrt (Npsi m) / (Real.cos θ) ^ 2 := by
            have hcne : Real.cos θ ≠ 0 := ne_of_gt hc
            field_simp
            try ring
      _ ≤ 1000 * Npsi m / (Real.cos θ) ^ 3 := by
            have h := arith4 hc hc1 (hsqrt1 m)
            rw [Real.sq_sqrt (le_of_lt (Npsi_pos m))] at h
            exact h

end Work.FTS.PhiStar.Series.Deleg
