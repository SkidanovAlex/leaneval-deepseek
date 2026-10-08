import Mathlib
import Submission.Work.L2F.Torus.Defs
import Submission.Work.L2F.Mat2.pslMap_eq_one_iff

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Torus

/-- Conjugation in `SL(2,F)` preserves the trace (the matrix of `g⁻¹` is the adjugate of the
matrix of `g`). -/
theorem trace_conj (F : Type*) [Field F] (g x : Matrix.SpecialLinearGroup (Fin 2) F) :
    (((g * x * g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F).trace =
      ((x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace := by
  have hcoe : (((g * x * g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) :
      Matrix (Fin 2) (Fin 2) F) =
      ((g : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (((x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) *
      (((g : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)).adjugate := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv]
  rw [hcoe, Matrix.trace_mul_cycle, Matrix.adjugate_mul, Matrix.SpecialLinearGroup.det_coe]
  simp

/-- The matrix of `-1 • x` in `SL(2,F)` is `-x`. -/
theorem coe_negOne_mul (F : Type*) [Field F] (x : Matrix.SpecialLinearGroup (Fin 2) F) :
    (((Work.L2F.negOne F * x : Matrix.SpecialLinearGroup (Fin 2) F)) : Matrix (Fin 2) (Fin 2) F) =
      -((x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
  rw [Matrix.SpecialLinearGroup.coe_mul,
    show ((Work.L2F.negOne F : Matrix.SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = -1 from rfl, Matrix.neg_mul, Matrix.one_mul]

/-- If the image of `x ∈ SL(2,F)` in `PSL(2,F)` has prime order `r ≠ 2`, then `x` is not
conjugate to `-x`: `g * x * g⁻¹ ≠ -1 * x` for every `g`.

Proof: conjugation preserves the trace, whereas `-x` has trace `-tr x`, so `tr x = 0` (as
`2 ≠ 0`); Cayley–Hamilton then gives `x * x = -1`, whence `(π x)² = 1` and `r ∣ 2`, contradicting
`r ≠ 2`. -/
theorem ne_conj_negOne_mul (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (x g : Matrix.SpecialLinearGroup (Fin 2) F) (r : ℕ) (hr : r.Prime) (hr2 : r ≠ 2)
    (hx : orderOf (Work.PSL2.pslMap F x) = r) :
    g * x * g⁻¹ ≠ Work.L2F.negOne F * x := by
  intro h
  have htr : ((x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace = 0 := by
    set t : F := ((x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace with ht
    have hmat : (((g * x * g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F)) :
        Matrix (Fin 2) (Fin 2) F) =
        ((Work.L2F.negOne F * x : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) := congrArg _ h
    have h1 := trace_conj F g x
    have h2' : (((Work.L2F.negOne F * x : Matrix.SpecialLinearGroup (Fin 2) F)) :
        Matrix (Fin 2) (Fin 2) F).trace =
        -((x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace := by
      rw [coe_negOne_mul, Matrix.trace_neg]
    rw [hmat, h2', ← ht] at h1
    have ht2 : t + t = 0 := by
      have h' := congrArg (fun s : F => s + t) h1
      simpa using h'.symm
    have hzero : (2 : F) * t = 0 := by rw [two_mul]; exact ht2
    exact (mul_eq_zero.mp hzero).resolve_left h2
  have hxx : x * x = Work.L2F.negOne F := by
    apply Subtype.ext
    have hCH := Work.L2F.Mat2.sq_eq_trace_smul_sub_det F
      ((x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
    rw [Matrix.SpecialLinearGroup.det_coe, one_smul, htr, zero_smul, zero_sub] at hCH
    rw [Matrix.SpecialLinearGroup.coe_mul, hCH]
    rfl
  have hsq : (Work.PSL2.pslMap F x) ^ 2 = 1 := by
    rw [pow_two, ← map_mul, hxx]
    exact (Work.L2F.Mat2.pslMap_eq_one_iff F h2 (Work.L2F.negOne F)).mpr (Or.inr rfl)
  have hdvd : r ∣ 2 := by
    rw [← hx]
    exact orderOf_dvd_iff_pow_eq_one.mpr hsq
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd h (Nat.Prime.ne_one hr)
  · exact hr2 h

end Work.L2F.Torus
