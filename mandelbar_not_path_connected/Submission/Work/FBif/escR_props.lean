import Mathlib
import Submission.Work.FBif.Glue

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FBif

open LeanEval.ComplexAnalysis (Tantibar)

/-! ## The escape radius of `T_c`

`escR c = (1 + √(1 + 4‖c‖)) / 2` is the positive root of `X² - X - ‖c‖`.  Outside the ball of
radius `escR c` the modulus is nondecreasing along the orbit of `T_c` (and strictly increasing in
the open complement), so a bounded periodic orbit stays inside it. -/

/-- `escR c` is at least `1`. -/
theorem one_le_escR (c : ℂ) : 1 ≤ escR c := by
  unfold escR
  have hS1 : (1 : ℝ) ≤ Real.sqrt (1 + 4 * ‖c‖) := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 1 + 4 * ‖c‖ by
      have hc : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
      linarith)
    rwa [Real.sqrt_one] at h
  linarith

/-- `escR c` is a root of `X² - X - ‖c‖`. -/
theorem escR_sq_sub (c : ℂ) : escR c ^ 2 - escR c = ‖c‖ := by
  unfold escR
  have harg : (0 : ℝ) ≤ 1 + 4 * ‖c‖ := by positivity
  have hS2 : (Real.sqrt (1 + 4 * ‖c‖)) ^ 2 = 1 + 4 * ‖c‖ := Real.sq_sqrt harg
  nlinarith [hS2]

/-- `escR c` is nonnegative. -/
theorem nonneg_escR (c : ℂ) : 0 ≤ escR c := le_trans zero_le_one (one_le_escR c)

/-- Lower bound for `‖T_c z‖` in terms of `‖z‖` and `‖c‖`. -/
theorem norm_tantibar_ge (c z : ℂ) : ‖z‖ ^ 2 - ‖c‖ ≤ ‖Tantibar c z‖ := by
  have h1 := norm_sub_le (Tantibar c z) c
  have h2 : Tantibar c z - c = (starRingEnd ℂ z) ^ 2 := by
    simp [LeanEval.ComplexAnalysis.Tantibar]
  have h3 : ‖(starRingEnd ℂ z) ^ 2‖ = ‖z‖ ^ 2 := by rw [norm_pow]; simp
  rw [h2, h3] at h1
  linarith

/-- Outside the escape radius, `T_c` does not decrease the modulus. -/
theorem le_norm_tantibar (c z : ℂ) (hz : escR c ≤ ‖z‖) : ‖z‖ ≤ ‖Tantibar c z‖ := by
  have hlow := norm_tantibar_ge c z
  have hfac : ‖z‖ ^ 2 - ‖c‖ - ‖z‖ = (‖z‖ - escR c) * (‖z‖ + escR c - 1) := by
    nlinarith [escR_sq_sub c]
  have h1 : 0 ≤ ‖z‖ - escR c := by linarith
  have h2 : 0 ≤ ‖z‖ + escR c - 1 := by linarith [one_le_escR c]
  have : 0 ≤ ‖z‖ ^ 2 - ‖c‖ - ‖z‖ := by rw [hfac]; exact mul_nonneg h1 h2
  linarith

/-- Strictly outside the escape radius, `T_c` strictly increases the modulus. -/
theorem lt_norm_tantibar (c z : ℂ) (hz : escR c < ‖z‖) : ‖z‖ < ‖Tantibar c z‖ := by
  have hlow := norm_tantibar_ge c z
  have hfac : ‖z‖ ^ 2 - ‖c‖ - ‖z‖ = (‖z‖ - escR c) * (‖z‖ + escR c - 1) := by
    nlinarith [escR_sq_sub c]
  have h1 : 0 < ‖z‖ - escR c := by linarith
  have h2 : 0 < ‖z‖ + escR c - 1 := by linarith [one_le_escR c]
  have : 0 < ‖z‖ ^ 2 - ‖c‖ - ‖z‖ := by rw [hfac]; exact mul_pos h1 h2
  linarith

/-- The cycle points of a `5`-periodic point of `T_c` stay within the escape radius: a point
outside would have strictly increasing successive moduli, contradicting periodicity. -/
theorem cyclePt_norm_le_escR (c z₁ : ℂ) (h5 : (Tantibar c)^[5] z₁ = z₁) (j : ℕ) :
    ‖cyclePt c z₁ j‖ ≤ escR c := by
  let z : ℕ → ℂ := fun i => (Tantibar c)^[i] z₁
  have hper : ∀ i, z (i + 5) = z i := by
    intro i
    show (Tantibar c)^[i + 5] z₁ = (Tantibar c)^[i] z₁
    rw [Function.iterate_add_apply, h5]
  have hstep : ∀ i, escR c < ‖z i‖ → ‖z i‖ < ‖z (i + 1)‖ := by
    intro i hi
    have hzi : z (i + 1) = Tantibar c (z i) :=
      Function.iterate_succ_apply' (Tantibar c) i z₁
    rw [hzi]
    exact lt_norm_tantibar c (z i) hi
  by_contra hcon
  push_neg at hcon
  have key : ∀ n : ℕ, ‖z j‖ < ‖z (j + (n + 1))‖ := by
    intro n
    induction n with
    | zero => simpa using hstep j hcon
    | succ n ih =>
        have hlt : escR c < ‖z (j + (n + 1))‖ := lt_trans hcon ih
        have hs := hstep (j + (n + 1)) hlt
        have hEq : j + (n + 1) + 1 = j + (n + 1 + 1) := by omega
        rw [hEq] at hs
        exact lt_trans ih hs
  have hk := key 4
  have hp := hper j
  rw [show (4 : ℕ) + 1 = 5 from rfl] at hk
  rw [hp] at hk
  exact lt_irrefl _ hk

theorem escR_props (c : ℂ) :
    0 ≤ Work.FBif.escR c ∧ 1 ≤ Work.FBif.escR c ∧ ‖c‖ ≤ (Work.FBif.escR c) ^ 2 - Work.FBif.escR c ∧
      (∀ z : ℂ, Work.FBif.escR c ≤ ‖z‖ → ‖z‖ ≤ ‖LeanEval.ComplexAnalysis.Tantibar c z‖) ∧
      (∀ z₁ : ℂ, (LeanEval.ComplexAnalysis.Tantibar c)^[5] z₁ = z₁ → ∀ j : ℕ,
        ‖Work.FBif.cyclePt c z₁ j‖ ≤ Work.FBif.escR c) :=
  ⟨nonneg_escR c, one_le_escR c, le_of_eq (escR_sq_sub c).symm,
   fun z hz => le_norm_tantibar c z hz,
   fun z₁ h5 j => cyclePt_norm_le_escR c z₁ h5 j⟩

end Work.FBif
