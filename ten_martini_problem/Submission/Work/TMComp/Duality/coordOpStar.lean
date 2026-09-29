/-
# The adjoint of a coordinate operator on `ℓ²(ι)`

`Work.TMComp.Duality.coordOp b e K hK0 hK` is the bounded operator on `ℓ²(ι)` with
coordinates `(T f) i = b i * f (e i)`, where `e` is a bijection of the index type `ι`
and `b` is a coefficient function bounded by `K`.  Every operator that occurs in the
suspension of the almost Mathieu cocycle (`s2Sh`, `s2Sh'`, `s2P`, `s2M`) is of this form.

Since `ℓ²(ι)` is a complex Hilbert space, the `star` of the algebra of bounded operators
is the Hilbert-space adjoint (`ContinuousLinearMap.star_eq_adjoint`).  This file computes
it: the adjoint of a coordinate operator is again a coordinate operator, with
coefficients `conj (b (e.symm j))` and permutation `e.symm`.  Equivalently, for every
`f : ℓ²(ι)` and every index `j`,

`(star T) f j = conj (b (e.symm j)) * f (e.symm j)`.

The proof is a direct computation with the inner product of `lp` (`lp.inner_eq_tsum`),
the conjugate-linearity of `inner` on `ℂ` (`RCLike.inner_apply`) and the reindexing of
an absolutely convergent series along a permutation (`Equiv.tsum_eq`).

We also record the elementary identity `conj (ph α n) = ph α (-n)` for the characters
`ph α n = e^{2πi n α}`, which is what identifies the adjoint of `s2P` with `s2M`.
-/
import Mathlib
import Submission.Work.TMComp.Duality.Defs

open scoped ENNReal ComplexConjugate

noncomputable section

namespace Work.TMComp.Duality

variable {ι : Type*} [DecidableEq ι]

/-- The adjoint of the coordinate operator `(T f) i = b i * f (e i)` on `ℓ²(ι)` is the
coordinate operator with coefficients `conj (b (e.symm j))` and permutation `e.symm`. -/
theorem coordOp_star_eq (b : ι → ℂ) (e : ι ≃ ι) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ i, ‖b i‖ ≤ K) :
    star (coordOp b e K hK0 hK) =
      coordOp (fun j => conj (b (e.symm j))) e.symm K hK0
        (fun j => by simpa [RCLike.norm_conj] using hK (e.symm j)) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).mpr ?_).symm
  intro f g
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  simp only [coordOp_coord]
  rw [← Equiv.tsum_eq e.symm (fun i => inner ℂ (f i) (b i * g (e i)))]
  apply tsum_congr
  intro c
  simp only [Equiv.apply_symm_apply, RCLike.inner_apply, map_mul, starRingEnd_self_apply]
  ring

/-- Coordinate form of `coordOp_star_eq`: the adjoint of a coordinate operator is again a
coordinate operator, and its coordinates are computed explicitly. -/
theorem coordOp_star_coord (b : ι → ℂ) (e : ι ≃ ι) (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ i, ‖b i‖ ≤ K) (f : lp (fun _ : ι => ℂ) 2) (j : ι) :
    (star (coordOp b e K hK0 hK)) f j = conj (b (e.symm j)) * f (e.symm j) := by
  rw [coordOp_star_eq, coordOp_coord]

/-- `phR x = e^{2πix}` has conjugate `phR (-x)`. -/
theorem conj_phR (x : ℝ) : conj (phR x) = phR (-x) := by
  have h : conj (phR x) = Complex.exp (conj (↑(2 * Real.pi * x) * Complex.I)) := by
    rw [phR, Complex.exp_conj]
  rw [h, phR]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- The characters satisfy `conj (ph α n) = ph α (-n)`. -/
theorem conj_ph (α : ℝ) (n : ℤ) : conj (ph α n) = ph α (-n) := by
  rw [ph, ph, conj_phR]
  congr 1
  push_cast
  ring

end Work.TMComp.Duality
