import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Existence.E1_E2_contDiff

namespace Work.OddBridge

open scoped ContDiff

theorem contDiffOn_Q_Ioo (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hmid : ∀ s ∈ Set.Ioo (0 : ℝ) 1,
      ∀ t ∈ Set.Icc (-(Commons.Geometry.Ulam.profileX 1)) (Commons.Geometry.Ulam.profileX 1),
      0 < Work.OddVolterra.psi h Commons.Geometry.Ulam.semicircle s t) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Work.OddVolterra.Q n h) (Set.Ioo (0:ℝ) 1) := by
  -- The two inhomogeneities `E₁`, `E₂` are `C^∞` on `(0,1)`.
  obtain ⟨hE1, hE2⟩ := Work.OddVolterra.Existence.E1_E2_contDiff n hn hh hmid
  -- The ball right-hand side `momentRHS n` is `C^∞` on all of `ℝ`.
  have hmr : ContDiff ℝ (⊤ : ℕ∞) (Work.OddVolterra.momentRHS n) := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => 1 + s ^ 2) := by fun_prop
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => Real.sqrt (1 + s ^ 2)) :=
      ContDiff.sqrt h1 (fun x => by positivity)
    have h3 : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => (Real.sqrt (1 + s ^ 2))⁻¹) :=
      ContDiff.inv h2 (fun x => by positivity)
    unfold Work.OddVolterra.momentRHS
    exact ContDiff.mul contDiff_const h3
  -- Hence every iterated derivative of it is `C^∞` as well.
  have hRHS : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun s : ℝ => iteratedDeriv (n + 1) (Work.OddVolterra.momentRHS n) s)
      (Set.Ioo (0:ℝ) 1) := by
    rw [iteratedDeriv_eq_iterate]
    exact (ContDiff.iterate_deriv (n + 1) hmr).contDiffOn
  have h0 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun s : ℝ => - Work.OddVolterra.E1 n h s
        + iteratedDeriv (n + 1) (Work.OddVolterra.momentRHS n) s) (Set.Ioo (0:ℝ) 1) :=
    (hE1.neg).add hRHS
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun s : ℝ => - Work.OddVolterra.E2 n h s) (Set.Ioo (0:ℝ) 1) := hE2.neg
  -- Assemble the two components of `Q n h : ℝ → (Fin 2 → ℝ)`.
  rw [contDiffOn_pi]
  intro i
  fin_cases i
  · simpa [Work.OddVolterra.Q] using h0
  · simpa [Work.OddVolterra.Q] using h1

end Work.OddBridge
