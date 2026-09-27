import Mathlib
import Submission.Work.KT.Defs

/-!
# `Work.KT.Fund.hopf_trace_det` — trace `1` and vanishing determinant of the Hopf projection

The Hopf idempotent `hopfIdem` is the rank-one projection onto the tautological line bundle of
`S² = ℂP¹`, written as `(1 + x·σ)/2` for the Pauli matrices `σ = (σ₁, σ₂, σ₃)` and `x ∈ S²`.
Its entries are therefore

`hopfIdem = 1/2 • [[1 + x₂, x₀ - i x₁], [x₀ + i x₁, 1 - x₂]]`.

Over `C(S², ℂ)` this matrix has:

* trace `= 1`: `(1/2)(1 + x₂) + (1/2)(1 - x₂) = 1`, the rank-one projection has rank one;
* determinant `= 0`: `(1/2)(1 + x₂)·(1/2)(1 - x₂) = (1/2)(x₀ - i x₁)·(1/2)(x₀ + i x₁)`, which
  reduces, via `x₀² + x₁² + x₂² = 1` (`sphere_sq_sum`), to `(1 - x₂²)/4 = (x₀² + x₁²)/4`.

These are the two elementary facts about the generator `H = [hopfIdem]` of `K⁰(S²)` used when
manipulating the Hopf bundle in `K`-theory (rank and determinant of the projection).
-/

namespace Work.KT.Fund

open Matrix

/-- The unit sphere relation `x₀² + x₁² + x₂² = 1` on `S² ⊂ ℝ³`, read in `ℂ`. -/
lemma sphere_sq_sum (x : S2) : ((x.1) 0 : ℂ) ^ 2 + ((x.1) 1 : ℂ) ^ 2 + ((x.1) 2 : ℂ) ^ 2 = 1 := by
  have h := EuclideanSpace.real_norm_sq_eq (x.1)
  rw [Fin.sum_univ_three] at h
  have hn : ‖x.1‖ = 1 := by
    rw [← mem_sphere_zero_iff_norm]
    exact x.2
  rw [hn] at h
  norm_num at h
  have hreal : ((x.1) 0 : ℝ) ^ 2 + ((x.1) 1 : ℝ) ^ 2 + ((x.1) 2 : ℝ) ^ 2 = 1 := by rw [← h]
  have hcast := congrArg (fun r : ℝ => (r : ℂ)) hreal
  push_cast at hcast
  simpa using hcast

/-- The `(0,0)` entry of `hopfIdem` at `x ∈ S²` is `(1 + x₂)/2`. -/
lemma hopfIdem_apply_zero_zero (x : S2) :
    hopfIdem.2 (0 : Fin 2) (0 : Fin 2) x = (1 / 2 : ℂ) * (1 + ((x.1) 2 : ℂ)) := by
  simp [hopfIdem, coordC, Algebra.smul_def]

/-- The `(1,1)` entry of `hopfIdem` at `x ∈ S²` is `(1 - x₂)/2`. -/
lemma hopfIdem_apply_one_one (x : S2) :
    hopfIdem.2 (1 : Fin 2) (1 : Fin 2) x = (1 / 2 : ℂ) * (1 - ((x.1) 2 : ℂ)) := by
  simp [hopfIdem, coordC, Algebra.smul_def]

/-- The `(0,1)` entry of `hopfIdem` at `x ∈ S²` is `(x₀ - i x₁)/2`. -/
lemma hopfIdem_apply_zero_one (x : S2) :
    hopfIdem.2 (0 : Fin 2) (1 : Fin 2) x
      = (1 / 2 : ℂ) * (((x.1) 0 : ℂ) - Complex.I * ((x.1) 1 : ℂ)) := by
  simp [hopfIdem, coordC, Algebra.smul_def]

/-- The `(1,0)` entry of `hopfIdem` at `x ∈ S²` is `(x₀ + i x₁)/2`. -/
lemma hopfIdem_apply_one_zero (x : S2) :
    hopfIdem.2 (1 : Fin 2) (0 : Fin 2) x
      = (1 / 2 : ℂ) * (((x.1) 0 : ℂ) + Complex.I * ((x.1) 1 : ℂ)) := by
  simp [hopfIdem, coordC, Algebra.smul_def]

theorem hopf_trace_det :
    (hopfIdem.2 (0 : Fin 2) (0 : Fin 2) + hopfIdem.2 (1 : Fin 2) (1 : Fin 2) = (1 : C(S2, ℂ))) ∧
      (hopfIdem.2 (0 : Fin 2) (0 : Fin 2) * hopfIdem.2 (1 : Fin 2) (1 : Fin 2)
        = hopfIdem.2 (0 : Fin 2) (1 : Fin 2) * hopfIdem.2 (1 : Fin 2) (0 : Fin 2)) := by
  constructor
  · ext x
    rw [ContinuousMap.add_apply, hopfIdem_apply_zero_zero x, hopfIdem_apply_one_one x,
      ContinuousMap.one_apply]
    ring
  · ext x
    rw [ContinuousMap.mul_apply, ContinuousMap.mul_apply, hopfIdem_apply_zero_zero x,
      hopfIdem_apply_one_one x, hopfIdem_apply_zero_one x, hopfIdem_apply_one_zero x]
    have h := sphere_sq_sum x
    ring_nf
    simp only [Complex.I_sq]
    ring_nf
    linear_combination (-1 / 4 : ℂ) * h

end Work.KT.Fund
