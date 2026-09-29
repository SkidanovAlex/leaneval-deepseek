import Mathlib
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.Cocycle.frob_mul_le
import Submission.Work.TMC7Core.Cocycle.frob_add_le
import Submission.Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one
import Submission.Work.TMC7Core.Scale.frob_tmC_le
import Submission.Work.TMC7Core.Scale.frob_matProd_le
import Submission.Work.TMC7Core.Scale.frob_matProd_sub_le
import Submission.Work.TMC7Core.Scale.frob_tmC_sub_le
import Submission.Work.TMC7Core.Scale.lyapAvg_lipschitz

/-!
# Local Lipschitz continuity of `E ↦ log ‖A_k(E, x)‖_F`

For fixed `α, λ, E₀, k` the map `E ↦ log (frob (iterC α lam E k x))` is Lipschitz on the
closed unit ball `‖E - E₀‖ ≤ 1`, uniformly in `x`.

The two ingredients are already available:

* `frob_matProd_sub_le` (stability of ordered products): if the individual transfer
  matrices of two energies are uniformly bounded by `M` and agree to within `D`, the
  length-`k` products differ by at most `k M^k D`; here `D = max 1 (4π|λ|)·‖E - E₀‖`
  by `frob_tmC_sub_le`;
* `abs_log_sub_log_le` together with `abs_frob_sub_le`: `log` is `1`-Lipschitz on
  `[1, ∞)` and every iterate has Frobenius norm `≥ √2` (`frob_sqrt_two_le_of_det_one`,
  `det_iterC`).
-/

namespace Work.TMLECore

theorem log_frob_iterC_energy_cont (α lam : ℝ) (E₀ : ℂ) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : ℂ) (x : ℝ), ‖E - E₀‖ ≤ 1 →
      |Real.log (Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E k x))
        - Real.log (Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E₀ k x))| ≤ C * ‖E - E₀‖ := by
  -- Constants: a uniform bound `M` on the transfer matrices near `E₀`, and the
  -- Lipschitz constant `D` of `y ↦ tmC lam · y` in the energy variable.
  set c : ℝ := ‖E₀‖ + 1 + 2 * |lam| with hc
  set M : ℝ := Real.sqrt (c ^ 2 + 2) with hMdef
  set D : ℝ := max 1 (4 * Real.pi * |lam|) with hDdef
  have hc_nonneg : 0 ≤ c := by rw [hc]; positivity
  have hM_two : Real.sqrt 2 ≤ M := by
    rw [hMdef]
    apply Real.sqrt_le_sqrt
    nlinarith
  have hD_pos : 0 < D := lt_of_lt_of_le one_pos (le_max_left _ _)
  refine ⟨max 1 ((k : ℝ) * M ^ k * D), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro E x hE
  -- Bound on `‖E‖` inside the unit ball, and hence on the transfer matrices.
  have hE0 : ‖E‖ ≤ ‖E₀‖ + 1 := by
    have h := norm_add_le (E - E₀) E₀
    have heq : (E - E₀) + E₀ = E := by ring
    rw [heq] at h
    linarith
  have hME : ∀ y : ℝ, Work.TMC7Core.frob (Work.TMC7Core.tmC lam E y) ≤ M := by
    intro y
    rw [hMdef]
    refine le_trans (Work.TMC7Core.Scale.frob_tmC_le lam E y) (Real.sqrt_le_sqrt ?_)
    have h1 : 0 ≤ ‖E‖ + 2 * |lam| := by positivity
    have h3 : ‖E‖ + 2 * |lam| ≤ c := by rw [hc]; linarith
    nlinarith [h1, hc_nonneg, h3]
  have hM0 : ∀ y : ℝ, Work.TMC7Core.frob (Work.TMC7Core.tmC lam E₀ y) ≤ M := by
    intro y
    rw [hMdef]
    refine le_trans (Work.TMC7Core.Scale.frob_tmC_le lam E₀ y) (Real.sqrt_le_sqrt ?_)
    have h1 : 0 ≤ ‖E₀‖ + 2 * |lam| := by positivity
    have h3 : ‖E₀‖ + 2 * |lam| ≤ c := by rw [hc]; linarith
    nlinarith [h1, hc_nonneg, h3]
  have hDn : 0 ≤ D * ‖E - E₀‖ := mul_nonneg hD_pos.le (norm_nonneg _)
  -- Energy-Lipschitz bound for a single transfer matrix, at the frozen angle.
  have hAB : ∀ j : ℕ, Work.TMC7Core.frob
      (Work.TMC7Core.tmC lam E (x + (j : ℝ) * α)
        - Work.TMC7Core.tmC lam E₀ (x + (j : ℝ) * α)) ≤ D * ‖E - E₀‖ := by
    intro j
    have h := Work.TMC7Core.Scale.frob_tmC_sub_le lam E E₀ (x + (j : ℝ) * α) (x + (j : ℝ) * α)
    simp only [sub_self, abs_zero, add_zero] at h
    simpa [hDdef] using h
  -- The product stability estimate.
  have key := Work.TMC7Core.Scale.frob_matProd_sub_le
    (fun j => Work.TMC7Core.tmC lam E (x + (j : ℝ) * α))
    (fun j => Work.TMC7Core.tmC lam E₀ (x + (j : ℝ) * α))
    M (D * ‖E - E₀‖) hM_two hDn (fun j => hME (x + (j : ℝ) * α))
    (fun j => hM0 (x + (j : ℝ) * α)) hAB k
  have hAeq : Work.TMC7Core.matProd (fun j => Work.TMC7Core.tmC lam E (x + (j : ℝ) * α)) k
      = Work.TMC7Core.iterC α lam E k x := (Work.TMC7Core.iterC_eq_matProd α lam E k x).symm
  have hBeq : Work.TMC7Core.matProd (fun j => Work.TMC7Core.tmC lam E₀ (x + (j : ℝ) * α)) k
      = Work.TMC7Core.iterC α lam E₀ k x := (Work.TMC7Core.iterC_eq_matProd α lam E₀ k x).symm
  rw [hAeq, hBeq] at key
  -- Lower bound `√2 ≤ frob` for both iterates, so `log` is `1`-Lipschitz there.
  have hb1 : (1 : ℝ) ≤ Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E k x) :=
    le_trans Real.one_lt_sqrt_two.le
      (Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one (Work.TMC7Core.det_iterC α lam E k x))
  have hb0 : (1 : ℝ) ≤ Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E₀ k x) :=
    le_trans Real.one_lt_sqrt_two.le
      (Work.TMC7Core.Cocycle.frob_sqrt_two_le_of_det_one (Work.TMC7Core.det_iterC α lam E₀ k x))
  have hkey : Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E k x - Work.TMC7Core.iterC α lam E₀ k x)
      ≤ ((k : ℝ) * M ^ k * D) * ‖E - E₀‖ := by
    have heq : (k : ℝ) * M ^ k * (D * ‖E - E₀‖) = ((k : ℝ) * M ^ k * D) * ‖E - E₀‖ := by ring
    rwa [heq] at key
  calc |Real.log (Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E k x))
          - Real.log (Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E₀ k x))|
      ≤ |Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E k x)
          - Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E₀ k x)| :=
        Work.TMC7Core.Scale.abs_log_sub_log_le _ _ hb1 hb0
    _ ≤ Work.TMC7Core.frob (Work.TMC7Core.iterC α lam E k x - Work.TMC7Core.iterC α lam E₀ k x) :=
        Work.TMC7Core.Scale.abs_frob_sub_le _ _
    _ ≤ ((k : ℝ) * M ^ k * D) * ‖E - E₀‖ := hkey
    _ ≤ max 1 ((k : ℝ) * M ^ k * D) * ‖E - E₀‖ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

end Work.TMLECore
