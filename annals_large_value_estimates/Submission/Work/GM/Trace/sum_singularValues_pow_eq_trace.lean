import Mathlib
import Submission.Work.GM.Trace.Defs

/-!
# `Σ σᵢ^{2r} = tr((A Aᴴ)^r)` for a complex matrix `A`

This file proves that the `2r`-th powers of the singular values of `Matrix.toEuclideanLin A`
sum to the real part of the trace of `(A Aᴴ)^r`.  It is the trace identity underlying
Guth–Maynard §4 (Lemma 4.4/4.5, Proposition 4.6): the trace expressions `Σ σᵢ^{2}` and
`Σ σᵢ^{6}` are the traces of `A Aᴴ` and `(A Aᴴ)³`.

The proof proceeds in three steps, all proved here:

* `svTrace_sing_pow_eq_re_trace` (`= LinearMap.singularValues` vs `= LinearMap.trace`):
  `Σᵢ σᵢ(T)^{2r} = Re tr((T†T)^r)` for an arbitrary linear map `T` between finite-dimensional
  real/complex inner product spaces.  Here `sq_singularValues_fin` identifies `σᵢ²` with the
  `i`-th eigenvalue of the self-adjoint operator `T†T`, and `trace_eq_sum_inner` applied to the
  eigenbasis `hT.eigenvectorBasis` computes the trace of `(T†T)^r`.
* `svTrace_trace_toEuclideanLin_fin`: the trace of `Matrix.toEuclideanLin B` is `Matrix.trace B`.
* `svTrace_trace_mul_pow_comm`: `tr((A B)^r) = tr((B A)^r)` for matrices, by cyclic invariance
  of the trace (`Matrix.trace_mul_cycle`) — this passes from `Aᴴ A` to `A Aᴴ`.

Paper reference: `REFS/GuthMaynard_2405.20552.txt`, §4.
-/

open Complex Finset Matrix
open scoped BigOperators
set_option autoImplicit false

namespace Work.GM.Trace

open Submission.LargeValues

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Powers of an eigenvector: if `T v = c • v` then `T^r v = c^r • v`. -/
private lemma svTrace_pow_apply_of_apply_eq_smul {E : Type*} [AddCommMonoid E] [Module 𝕜 E]
    {T : E →ₗ[𝕜] E} {v : E} {c : 𝕜} (h : T v = c • v) (r : ℕ) :
    (T^r) v = c^r • v := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    change (T^n) (T v) = c^(n+1) • v
    rw [h, map_smul, ih, smul_smul, ← pow_succ']

/-- **Singular values versus the trace of `(T†T)^r`.**  For a linear map `T` between
finite-dimensional inner product spaces with `finrank 𝕜 E = n`,
`Σ_{i : Fin n} σᵢ(T)^{2r} = Re tr((T†T)^r)`. -/
private lemma svTrace_sing_pow_eq_re_trace {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (T : E →ₗ[𝕜] F) {n : ℕ} (hn : Module.finrank 𝕜 E = n) (r : ℕ) :
    ∑ i : Fin n, T.singularValues i ^ (2 * r)
      = RCLike.re (LinearMap.trace 𝕜 E ((T.adjoint ∘ₗ T)^r)) := by
  have hsym : (T.adjoint ∘ₗ T).IsSymmetric := T.isSymmetric_adjoint_comp_self
  set b := hsym.eigenvectorBasis hn with hbdef
  have hstep : ∀ i : Fin n, (((T.adjoint ∘ₗ T)^r) (b i))
      = ((hsym.eigenvalues hn i : 𝕜))^r • b i := by
    intro i
    rw [hbdef]
    exact svTrace_pow_apply_of_apply_eq_smul (hsym.apply_eigenvectorBasis hn i) r
  have htr : RCLike.re (LinearMap.trace 𝕜 E ((T.adjoint ∘ₗ T)^r))
      = ∑ i : Fin n, (hsym.eigenvalues hn i)^r := by
    rw [LinearMap.trace_eq_sum_inner ((T.adjoint ∘ₗ T)^r) b, map_sum RCLike.re]
    apply Finset.sum_congr rfl
    intro i _
    rw [hstep i, inner_smul_right]
    have hone : inner 𝕜 (b i) (b i) = 1 := by
      rw [(orthonormal_iff_ite.mp b.orthonormal) i i]; simp
    rw [hone, mul_one, ← RCLike.ofReal_pow]
    exact RCLike.ofReal_re_ax _
  rw [htr]
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_mul]
  congr 1
  exact LinearMap.sq_singularValues_fin T hn i

/-- The trace of `Matrix.toEuclideanLin B`, for `B` square of size `N + 1`. -/
private lemma svTrace_trace_toEuclideanLin_fin (N : ℕ)
    (B : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ) :
    LinearMap.trace ℂ (EuclideanSpace ℂ (Fin (N + 1))) (Matrix.toEuclideanLin B)
      = Matrix.trace B := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal]
  exact Matrix.trace_toLin_eq B _

/-- `(A * B)^k * A = A * (B * A)^k`; the "shuffle" identity behind cyclic invariance. -/
private lemma svTrace_pow_mul_tail {R : Type*} [Semiring R] {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n R) (B : Matrix n m R) (k : ℕ) :
    (A * B)^k * A = A * (B * A)^k := by
  induction k with
  | zero => simp
  | succ j ih =>
    conv_lhs => rw [pow_succ]
    rw [show ((A*B)^j * (A*B)) * A = ((A*B)^j * A) * (B*A) from by
      simp only [Matrix.mul_assoc]]
    rw [ih]
    conv_rhs => rw [pow_succ]
    rw [Matrix.mul_assoc]

/-- Cyclic invariance of the trace of a power: `tr((A B)^r) = tr((B A)^r)` for `1 ≤ r`. -/
private lemma svTrace_trace_mul_pow_comm {R : Type*} [CommSemiring R] {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n R) (B : Matrix n m R) {r : ℕ} (hr : 1 ≤ r) :
    Matrix.trace ((A * B)^r) = Matrix.trace ((B * A)^r) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  rw [show (A*B)^(k+1) = A * (B*(A*B)^k) from by
        rw [pow_succ']; simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
  congr 1
  rw [Matrix.mul_assoc, svTrace_pow_mul_tail, ← Matrix.mul_assoc, ← pow_succ']

/-- The general form of the target identity: for any complex matrix `A` with `N + 1` columns,
`Σᵢ σᵢ(M_A)^{2r} = Re tr((A Aᴴ)^r)`. -/
theorem sum_singularValues_pow_eq_trace_gen {m : Type*} [Fintype m] [DecidableEq m]
    (N : ℕ) (A : Matrix m (Fin (N + 1)) ℂ) {r : ℕ} (hr : 1 ≤ r) :
    ∑ i : Fin (N + 1), (Matrix.toEuclideanLin A).singularValues i ^ (2 * r)
      = (Matrix.trace ((A * A.conjTranspose)^r)).re := by
  have hn : Module.finrank ℂ (EuclideanSpace ℂ (Fin (N + 1))) = N + 1 := by
    rw [finrank_euclideanSpace, Fintype.card_fin]
  have hpow : (LinearMap.adjoint (Matrix.toEuclideanLin A) ∘ₗ Matrix.toEuclideanLin A)^r
      = Matrix.toEuclideanLin ((A.conjTranspose * A)^r) := by
    have hmul : LinearMap.adjoint (Matrix.toEuclideanLin A) ∘ₗ Matrix.toEuclideanLin A
        = Matrix.toEuclideanLin (A.conjTranspose * A) := by
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint A]
      exact (Matrix.toLpLin_mul_same 2 A.conjTranspose A).symm
    rw [hmul]
    exact (Matrix.toLpLin_pow 2 (A.conjTranspose * A) r).symm
  have htrace : LinearMap.trace ℂ (EuclideanSpace ℂ (Fin (N + 1)))
        ((LinearMap.adjoint (Matrix.toEuclideanLin A) ∘ₗ Matrix.toEuclideanLin A)^r)
      = Matrix.trace ((A * A.conjTranspose)^r) := by
    rw [hpow, svTrace_trace_toEuclideanLin_fin N ((A.conjTranspose * A)^r)]
    exact svTrace_trace_mul_pow_comm A.conjTranspose A hr
  rw [svTrace_sing_pow_eq_re_trace (Matrix.toEuclideanLin A) hn r, htrace]
  rfl

/-- For a complex matrix `A` (here `A = Submission.LargeValues.MWmat N W`) and `1 ≤ r`, the `2r`-th
powers of the singular values of the linear map `Matrix.toEuclideanLin A` sum to the real trace of
`(A A*)^r`.

Suggested route: `LinearMap.sq_singularValues_fin` identifies `σ_i²` with the `i`-th eigenvalue of
`T†T` (`T = Matrix.toEuclideanLin A`), and `LinearMap.trace_eq_sum_inner` applied to the orthonormal
eigenbasis `hT.eigenvectorBasis` gives `∑_i (eigenvalue_i)^r = tr((T†T)^r)`; then
`Matrix.toEuclideanLin_conjTranspose_eq_adjoint` and cyclic invariance of the trace
(`LinearMap.trace_comp_comm`) identify `tr((T†T)^r)` with `(Matrix.trace ((A*Aᴴ)^r)).re`. -/
theorem sum_singularValues_pow_eq_trace (N : ℕ) (W : Finset ℝ) {r : ℕ} (hr : 1 ≤ r) :
    ∑ i : Fin (N + 1),
        (Matrix.toEuclideanLin (Submission.LargeValues.MWmat N W)).singularValues i ^ (2 * r)
      = (Matrix.trace ((Submission.LargeValues.MWmat N W *
          (Submission.LargeValues.MWmat N W).conjTranspose) ^ r)).re :=
  sum_singularValues_pow_eq_trace_gen N (Submission.LargeValues.MWmat N W) hr

end Work.GM.Trace
