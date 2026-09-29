import Mathlib
import Submission.Work.TMC7Core.Scale.floquet_phase_aux
import Submission.Work.TMC7Core.Defs
import Submission.Work.TMC7Core.Cocycle
import Submission.Work.TMC7Core.FtbAux.floquet_core

/-!
# Floquet theory at rational frequency, general phase: `‖tr A_q(θ)‖ ≤ 2`

If `u ≠ 0` is a polynomially bounded formal solution of the almost Mathieu difference
equation at rational frequency `α = p/q`, *phase* `θ` and energy `E`, then the transfer
matrix over one period, `A_q(θ) = iterC α lam E q θ = S(θ+(q-1)α)⋯S(θ)`, satisfies
`‖tr A_q(θ)‖ ≤ 2`.

The proof is the phase-`θ` analogue of `Work.TMC7Core.FtbAux.floquet_of_genEigen`: the
only phase-dependent input is the block transfer `W (k+1) = A_q(θ) ·ᵥ W k` for
`W k = (u (k q), u (k q - 1))`, which is `Work.TMC7Core.Scale.block_transfer_phase`
(`tmC` is `1`-periodic in its argument, so `S(θ + k q α) = S(θ + k p) = S(θ)`), while the
core linear algebra `orbit_trace_norm_le_two` of `FtbAux.floquet_core` is phase-free.
-/

namespace Work.TMC7Core.Scale

open Work.TMC7Core

theorem floquet_of_genEigen_phase (p : ℤ) (q : ℕ) (hq : 1 ≤ q) (lam θ E : ℝ) (u : ℤ → ℂ)
    (hu : Work.TMC7Core.IsGenEigen ((p : ℝ) / (q : ℝ)) lam θ E u) :
    ‖(Work.TMC7Core.iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q θ).trace‖ ≤ 2 := by
  obtain ⟨hne, hrec, C, hC⟩ := hu
  have hC0 : 0 ≤ C := by
    have h := hC 0
    simp only [Int.cast_zero, abs_zero, add_zero, mul_one] at h
    linarith [norm_nonneg (u 0)]
  set A : Matrix (Fin 2) (Fin 2) ℂ := iterC ((p : ℝ) / (q : ℝ)) lam (E : ℂ) q θ with hA
  set W : ℤ → Fin 2 → ℂ := fun k => ![u (k * q), u (k * q - 1)] with hW
  have hW0 : W 0 ≠ 0 := by
    intro h
    have h1 : u 0 = 0 := by
      have hh := congrFun h 0
      simp only [hW, Pi.zero_apply] at hh
      simpa using hh
    have h2 : u (-1) = 0 := by
      have hh := congrFun h 1
      simp only [hW, Pi.zero_apply] at hh
      simpa using hh
    exact hne (Work.TMC7Core.FtbAux.floquet_vanish ((p : ℝ) / (q : ℝ)) lam θ (E : ℂ) u hrec h1 h2)
  have hdet : A.det = 1 := by rw [hA]; exact det_iterC _ _ _ _ _
  have hstep : ∀ k : ℤ, W (k + 1) = A.mulVec (W k) := by
    intro k
    simpa only [hA, hW] using (block_transfer_phase p q hq lam θ E u hrec k).symm
  have hbnd : ∀ k : ℤ, ‖W k 0‖ ≤ (2 * C * (1 + q)) * (1 + |(k : ℝ)|) ∧
      ‖W k 1‖ ≤ (2 * C * (1 + q)) * (1 + |(k : ℝ)|) := by
    intro k
    obtain ⟨h1, h2⟩ := Work.TMC7Core.FtbAux.floquet_bound q u C hC0 hC k
    exact ⟨by simpa [hW] using h1, by simpa [hW] using h2⟩
  have hmain := Work.TMC7Core.FtbAux.orbit_trace_norm_le_two A W (2 * C * (1 + q)) hdet hstep hW0 hbnd
  rwa [hA] at hmain

end Work.TMC7Core.Scale
