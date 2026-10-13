/-
# `Work.FTS.PhiStar.FlatWAux.Expansion` — the `1/λ_m`-expansion of the radial Green function

The radial mode solution `radGreen α m c` of `-α²z²a'' - α(5+α)za' + λ_m a = c` satisfies the
resolvent identity `λ_m·radGreen α m c = c + α·𝒜(radGreen α m c)` with
`𝒜 = αz²∂² + (5+α)z∂`, and `𝒜` commutes with `radGreen α m` (`RadGreenActA`).  Hence

`λ_m·radGreen α m c = c + α·radGreen α m (𝒜 c)`,

and iterating `J` times:

`radGreen α m c = Σ_{j<J} (α^j/λ_m^{j+1})·(𝒜^j c) + (α^J/λ_m^J)·radGreen α m (𝒜^J c)`.

This file contains the iterates `Ajit α j c = 𝒜^j c` (`Ajit α j (phiA α) = phiAj (j+1) α`), the
one-step identity `radGreen_step` (from `Series.radGreen_resolvent` and `RadGreenActA`) and the
purely algebraic `radGreen_expansion`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.StarDefs
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Radial.radGreen_solves
import Submission.Work.FTS.PhiStar.RadGreenActA
import Submission.Work.FTS.PhiStar.Series.ResolventSetup

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWAux

set_option autoImplicit false

/-- The iterates `𝒜^j c` of `𝒜 a = α z² a'' + (5+α) z a'`.  `Ajit α j (phiA α) = phiAj (j+1) α`. -/
def Ajit (α : ℝ) : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, c => c
  | (j + 1), c => fun z =>
      α * z ^ 2 * iteratedDeriv 2 (Ajit α j c) z + (5 + α) * z * deriv (Ajit α j c) z

@[simp] theorem Ajit_zero (α : ℝ) (c : ℝ → ℝ) : Ajit α 0 c = c := rfl

theorem Ajit_succ (α : ℝ) (j : ℕ) (c : ℝ → ℝ) :
    Ajit α (j + 1) c = fun z =>
      α * z ^ 2 * iteratedDeriv 2 (Ajit α j c) z + (5 + α) * z * deriv (Ajit α j c) z := rfl

/-- `Ajit α j (phiA α) = phiAj (j+1) α`. -/
theorem Ajit_phiA (α : ℝ) (j : ℕ) :
    Ajit α j (Work.FTS.VocabO.phiA α) = Work.FTS.PhiStar.phiAj (j + 1) α := by
  induction j with
  | zero =>
      funext z
      rw [Ajit_zero]
      rfl
  | succ j ih =>
      rw [Ajit_succ]
      have h2 : iteratedDeriv 2 (Ajit α j (Work.FTS.VocabO.phiA α))
          = iteratedDeriv 2 (Work.FTS.PhiStar.phiAj (j + 1) α) := by rw [ih]
      have h1 : deriv (Ajit α j (Work.FTS.VocabO.phiA α))
          = deriv (Work.FTS.PhiStar.phiAj (j + 1) α) := by rw [ih]
      simp only [h2, h1]
      rfl

/-- `Radial.lamR` and `Gegenbauer.lam` are the same function. -/
theorem lamR_eq_lam (m : ℕ) :
    Work.FTS.PhiStar.Radial.lamR m = Work.FTS.PhiStar.Gegenbauer.lam m :=
  rfl

theorem lamR_ne_zero {m : ℕ} (hm : 1 ≤ m) : Work.FTS.PhiStar.Radial.lamR m ≠ 0 := by
  rw [lamR_eq_lam]
  simp only [Work.FTS.PhiStar.Gegenbauer.lam]
  have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  positivity

/-- **The one-step resolvent identity**: `radGreen α m c = c/λ_m + (α/λ_m)·radGreen α m (𝒜 c)`. -/
theorem radGreen_step {α : ℝ} (m : ℕ) (hα : 0 < α) (hα5 : α ≤ 1 / 5) (hm : 1 ≤ m)
    {c : ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A) (hc : ContDiffOn ℝ 2 c (Set.Ioi 0))
    (hb : ∀ k : ℕ, k ≤ 2 → ∀ t : ℝ, 0 < t →
      |iteratedDeriv k c t| ≤ A / (1 + t ^ (k + 1)))
    (hc0 : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn
      (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) (Set.Ioo 0 1))
    (h0' : MeasureTheory.IntegrableOn
      (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn
      (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1)) :
    ∀ z : ℝ, 0 < z → Work.FTS.PhiStar.Radial.radGreen α m c z
      = c z / Work.FTS.PhiStar.Radial.lamR m
        + (α / Work.FTS.PhiStar.Radial.lamR m)
            * Work.FTS.PhiStar.Radial.radGreen α m (Ajit α 1 c) z := by
  intro z hz
  have hres := Work.FTS.PhiStar.Series.radGreen_resolvent α m c hz hα hc0 h0 h0' hinf
  have hact := RadGreenActA (α := α) m hα hα5 hm hA hc hb z hz
  have hstep : Work.FTS.PhiStar.Radial.radGreen α m (Ajit α 1 c) z
      = α * z ^ 2 * iteratedDeriv 2 (Work.FTS.PhiStar.Radial.radGreen α m c) z
        + (5 + α) * z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z := by
    rw [Ajit_succ]
    exact hact
  have hite : iteratedDeriv 2 (Work.FTS.PhiStar.Radial.radGreen α m c) z
      = deriv (deriv (Work.FTS.PhiStar.Radial.radGreen α m c)) z := by
    simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  have hkey : Work.FTS.PhiStar.Radial.lamR m
      * Work.FTS.PhiStar.Radial.radGreen α m c z
      = c z + α * Work.FTS.PhiStar.Radial.radGreen α m (Ajit α 1 c) z := by
    rw [hres, hstep, hite]
    ring
  have hne := lamR_ne_zero hm
  field_simp
  linarith [hkey]

/-- **The `J`-fold expansion of the radial Green function** (algebraic part; the one-step
identity is an explicit hypothesis). -/
theorem radGreen_expansion {α : ℝ} (m : ℕ) (c : ℝ → ℝ) (J : ℕ) {z : ℝ}
    (hlam : Work.FTS.PhiStar.Radial.lamR m ≠ 0)
    (hstep : ∀ j : ℕ, j ≤ J → Work.FTS.PhiStar.Radial.radGreen α m (Ajit α j c) z
      = (Ajit α j c) z / Work.FTS.PhiStar.Radial.lamR m
        + (α / Work.FTS.PhiStar.Radial.lamR m) * Work.FTS.PhiStar.Radial.radGreen α m
            (Ajit α (j + 1) c) z) :
    Work.FTS.PhiStar.Radial.radGreen α m c z
      = (∑ j ∈ Finset.range J,
          (α ^ j / (Work.FTS.PhiStar.Radial.lamR m) ^ (j + 1)) * Ajit α j c z)
        + (α ^ J / (Work.FTS.PhiStar.Radial.lamR m) ^ J)
            * Work.FTS.PhiStar.Radial.radGreen α m (Ajit α J c) z := by
  induction J with
  | zero => simp
  | succ J ih =>
      have h1 := ih (fun j hj => hstep j (le_trans hj (Nat.le_succ J)))
      have h2 := hstep J (Nat.le_succ J)
      rw [h1, h2, Finset.sum_range_succ]
      have key : (α ^ J / Work.FTS.PhiStar.Radial.lamR m ^ J)
            * ((Ajit α J c) z / Work.FTS.PhiStar.Radial.lamR m
              + (α / Work.FTS.PhiStar.Radial.lamR m)
                * Work.FTS.PhiStar.Radial.radGreen α m (Ajit α (J + 1) c) z)
          = (α ^ J / Work.FTS.PhiStar.Radial.lamR m ^ (J + 1)) * (Ajit α J c) z
            + (α ^ (J + 1) / Work.FTS.PhiStar.Radial.lamR m ^ (J + 1))
                * Work.FTS.PhiStar.Radial.radGreen α m (Ajit α (J + 1) c) z := by
        field_simp
        ring
      rw [key]
      ring

end Work.FTS.PhiStar.FlatWAux
