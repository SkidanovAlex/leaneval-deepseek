/-
# Area 4 / HB §11–§12 — assembly lemmas of the parent (area4) proof

Namespace `Work.LinnikAreas.Density4`.  Bookkeeping that connects the delegated analytic pieces
to the frozen contract:

* `Lapl_antitone` — the Laplace transform `Lapl x₀ f` is antitone in its argument when `f ≥ 0`
  (hypothesis `hFanti` of `hb_lemma12_1`, i.e. HB's `F(-λ₁) ≥ F(λ-λ₁)` for `0 ≤ λ₁ ≤ λ`);
* `lamOf_pos`, `lamChar_le_lamMax` — elementary facts about the frozen quantities;
* `Ncount_le_of_lt`, `exists_eps_bnd13` — the closing integrality step of HB §12:
  Lemma 12.1 gives `N(λ) ≤ bnd13 λ λ₁ + ε`, `table13_cert` gives `bnd13 λ λ₁ < N₀ + 1`, so
  `N ≤ N₀`.

Remark on `wHB`.  `wHB 0 = 0/(1-1) = 0` by Lean's `0/0 = 0` convention, so `wHB` is *not*
antitone on `[0,∞)` (it jumps up from `0` at `0+`).  The contract's `DensityCert.(D1)` sums
`wHB (lamChar χ)` over the characters that have a zero with `λ ≤ lamMax q`; for such a character
`lamChar χ ≤ lamMax q` (`lamChar_le_lamMax`), so the analytic estimate of HB §11 must be applied
to *minimising* zeros (`lamChar_attained`), not to arbitrary ones — the transfer from an arbitrary
zero would go in the wrong direction.
-/
import Mathlib
import Submission.Work.LinnikContract.Areas
import Submission.Work.LinnikAreas.Density4.Defs
import Submission.Work.LinnikAreas.Density4.TestFun

open scoped BigOperators
noncomputable section

namespace Work.LinnikAreas.Density4

open Work.LinnikContract

/-- The Laplace transform `Lapl x₀ f z = ∫₀^{x₀} e^{-zt} f(t) dt` is antitone in `z` when `f ≥ 0`
and `0 ≤ x₀`.  This is the monotonicity `hFanti` required by `hb_lemma12_1`. -/
lemma Lapl_antitone {x₀ : ℝ} (hx₀ : 0 ≤ x₀) {f : ℝ → ℝ} (hfcont : Continuous f)
    (hf : ∀ t, 0 ≤ f t) {a b : ℝ} (hab : a ≤ b) :
    Lapl x₀ f b ≤ Lapl x₀ f a := by
  rw [Lapl, Lapl]
  refine intervalIntegral.integral_mono_on hx₀ ?_ ?_ ?_
  · exact (Continuous.intervalIntegrable (by fun_prop) 0 x₀)
  · exact (Continuous.intervalIntegrable (by fun_prop) 0 x₀)
  · intro t ht
    have h1 : Real.exp (-(b * t)) ≤ Real.exp (-(a * t)) :=
      Real.exp_le_exp.mpr (by nlinarith [ht.1])
    exact mul_le_mul_of_nonneg_right h1 (hf t)

/-- `lamOf q ρ > 0` when `Re ρ < 1` and `q ≥ 2`. -/
lemma lamOf_pos {q : ℕ} [NeZero q] (hq : 2 ≤ q) {ρ : ℂ} (hre : ρ.re < 1) : 0 < lamOf q ρ := by
  rw [lamOf]
  exact mul_pos (by linarith) (Real.log_pos (by exact_mod_cast hq))

/-- A character with a zero in the working region of `λ ≤ lamMax q` has `lamChar χ ≤ lamMax q`
(this is what makes the minimising zero admissible in HB's §11). -/
lemma lamChar_le_lamMax {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (h : ∃ ρ, IsZ χ ρ ∧ lamOf q ρ ≤ lamMax q) : lamChar χ ≤ lamMax q := by
  obtain ⟨ρ, hρ, hle⟩ := h
  exact le_trans (lamChar_le_of_isZ hq hρ) hle

/-- The integrality step of HB §12: `N < N₀ + 1` implies `N ≤ N₀` for natural `N`. -/
lemma Ncount_le_of_lt {q : ℕ} [NeZero q] {lam : ℝ} {N₀ : ℕ}
    (h : ((Ncount q lam : ℕ) : ℝ) < (N₀ : ℝ) + 1) : Ncount q lam ≤ N₀ := by
  have h' : Ncount q lam < N₀ + 1 := by exact_mod_cast h
  omega

/-- `bnd13 λ λ₁ < N₀ + 1` leaves room for the `ε > 0` of HB's Lemma 12.1. -/
lemma exists_eps_bnd13 {lam lam1 : ℝ} {N₀ : ℕ} (h : bnd13 lam lam1 < (N₀ : ℝ) + 1) :
    ∃ ε : ℝ, 0 < ε ∧ bnd13 lam lam1 + ε < (N₀ : ℝ) + 1 :=
  ⟨((N₀ : ℝ) + 1 - bnd13 lam lam1) / 2, by linarith, by linarith⟩

end Work.LinnikAreas.Density4
