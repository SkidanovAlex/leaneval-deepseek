import Mathlib
import Submission.Work.TMC14Core.RatRot

open Filter
open scoped Topology
open Work.TMComp.RotBasics

namespace Work.TMC14Core

/-- Each `q`-step iterate `E ↦ qIter p q lam E x m` is antitone in the energy.

The single step `qMap` is antitone in `E` (pointwise) and monotone in the angle; hence so is
every iterate, by comparing `qMap E₂ (qIter E₂)` with `qMap E₂ (qIter E₁)` (monotonicity in the
angle) and then `qMap E₂ (qIter E₁)` with `qMap E₁ (qIter E₁)` (antitonicity in the energy). -/
theorem qIter_antitone_E (p : ℤ) (q : ℕ) (lam x : ℝ) (m : ℕ) :
    Antitone (fun E : ℝ => qIter p q lam E x m) := by
  induction m with
  | zero =>
    intro E₁ E₂ _
    simp [qIter_zero]
  | succ m ih =>
    intro E₁ E₂ h12
    simp only [qIter_succ]
    have hmono : Monotone (qMap p q lam E₂ x) :=
      pruferIter_mono_t ((p : ℝ) / (q : ℝ)) lam E₂ q x
    have h1 : qMap p q lam E₂ x (qIter p q lam E₂ x m) ≤
        qMap p q lam E₂ x (qIter p q lam E₁ x m) := hmono (ih h12)
    have h2 : qMap p q lam E₂ x (qIter p q lam E₁ x m) ≤
        qMap p q lam E₁ x (qIter p q lam E₁ x m) :=
      pruferIter_antitone_E ((p : ℝ) / (q : ℝ)) lam q x (qIter p q lam E₁ x m) h12
    linarith

/-- The asymptotic rotation number `rotQ` is the limit of `m ↦ qIter … m / m`. -/
theorem tendsto_qIter_div (p : ℤ) (q : ℕ) (lam E x : ℝ) (hq : 1 ≤ q) :
    Tendsto (fun m : ℕ => qIter p q lam E x m / (m : ℝ)) atTop (𝓝 (rotQ p q lam E x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun m => norm_nonneg _) ?_
    tendsto_one_div_atTop_nhds_zero_nat
  filter_upwards [eventually_ge_atTop 1] with m hm
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact rotQ_rate p q lam E x hq hm

theorem rotQ_antitone (p : ℤ) (q : ℕ) (lam x : ℝ) (hq : 1 ≤ q) :
    Antitone (fun E : ℝ => Work.TMC14Core.rotQ p q lam E x) := by
  intro E₁ E₂ h12
  exact le_of_tendsto_of_tendsto' (tendsto_qIter_div p q lam E₂ x hq)
    (tendsto_qIter_div p q lam E₁ x hq)
    (fun m => div_le_div_of_nonneg_right (qIter_antitone_E p q lam x m h12)
      (Nat.cast_nonneg m))

end Work.TMC14Core
