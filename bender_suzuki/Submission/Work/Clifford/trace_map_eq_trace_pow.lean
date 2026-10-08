import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

/-!
# `Work.Clifford.trace_map_eq_trace_pow`

Let `M` be a complex matrix with `M ^ r = 1` (`r > 0`), so that every eigenvalue of `M` is an
`r`-th root of unity.  Let `ζ` be a primitive `n`-th root of unity with `r ∣ n`, and let
`σ : ℂ ≃+* ℂ` be a field automorphism satisfying `σ ζ = ζ ^ k`.  Then `σ` acts on the `r`-th
roots of unity as the `k`-th power map, and

  `(M.map σ).trace = (M ^ k).trace`,

i.e. the Galois twist `M ↦ σ · M` of `M` has the same trace as the `k`-th power of `M`.

The proof: `(M.map σ).trace = σ (M.trace)`.  Since `M ^ r = 1`, the endomorphism `T = M.toLin'`
is diagonalizable (its minimal polynomial divides the squarefree polynomial `X ^ r - 1`), so
choosing an eigenbasis `b` of `T`, the trace of `T` is the sum of the eigenvalues and the trace
of `T ^ k` is the sum of their `k`-th powers.  For each eigenvalue `μ` (an `r`-th root of unity,
hence an `n`-th root of unity) one has `σ μ = μ ^ k`.
-/

noncomputable section

open Polynomial Module

namespace Work.Clifford

/-- If `μ ^ n = 1`, `ζ` is a primitive `n`-th root of unity and `σ ζ = ζ ^ k`, then
`σ μ = μ ^ k`. -/
theorem aut_apply_eq_pow_of_pow_eq_one {n k : ℕ} (hn : 0 < n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) (σ : ℂ ≃+* ℂ) (hσ : σ ζ = ζ ^ k) {μ : ℂ}
    (hμ : μ ^ n = 1) : σ μ = μ ^ k := by
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨j, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ
  rw [map_pow, hσ, ← pow_mul, ← pow_mul, mul_comm]

/-- For an endomorphism `T` of a finite-dimensional complex vector space with `T ^ r = 1`
(`r > 0`), and `σ : ℂ ≃+* ℂ` acting on the `r`-th roots of unity as `μ ↦ μ ^ k`, the trace of
`T ^ k` is the image under `σ` of the trace of `T`. -/
theorem trace_sigma_eq_trace_pow {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] {r n k : ℕ} (hr : 0 < r) (hn : 0 < n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) (hrn : r ∣ n) (σ : ℂ ≃+* ℂ) (hσ : σ ζ = ζ ^ k)
    (T : V →ₗ[ℂ] V) (hT : T ^ r = 1) :
    σ (LinearMap.trace ℂ V T) = LinearMap.trace ℂ V (T ^ k) := by
  have hsq : Squarefree ((X ^ r - 1 : ℂ[X])) := by
    rw [show (X ^ r - 1 : ℂ[X]) = X ^ r - C (1 : ℂ) by simp]
    exact (separable_X_pow_sub_C (1 : ℂ) (by exact_mod_cast hr.ne') one_ne_zero).squarefree
  have hae : aeval T (X ^ r - 1 : ℂ[X]) = 0 := by
    rw [map_sub, map_pow, aeval_X, map_one, hT, sub_self]
  have hiss : Module.End.IsSemisimple T := Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq hae
  classical
  let ed := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (Module.End.eigenspaces_iSupIndep T) hiss.iSup_eigenspace_eq_top
  let I := (μ : ℂ) × Fin (finrank ℂ (Module.End.eigenspace T μ))
  let b : Basis I ℂ V := ed.collectedBasis fun μ => finBasis ℂ (Module.End.eigenspace T μ)
  haveI : Fintype I := FiniteDimensional.fintypeBasisIndex b
  have hbv (i : I) : T (b i) = i.1 • b i :=
    Module.End.mem_eigenspace_iff.mp (ed.collectedBasis_mem _ i)
  have hmat : LinearMap.toMatrix b b T = Matrix.diagonal (fun i : I => i.1) := by
    ext i j
    rw [LinearMap.toMatrix_apply, hbv j, Matrix.diagonal_apply]
    simp only [map_smul, Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one]
    split_ifs with h
    · rw [h, Finsupp.single_eq_same]
    · rw [Finsupp.single_eq_of_ne h]
  have htraceT : LinearMap.trace ℂ V T = ∑ i : I, (i.1 : ℂ) := by
    rw [LinearMap.trace_eq_matrix_trace ℂ b T, hmat, Matrix.trace_diagonal]
  have hpowmat : ∀ s : ℕ, LinearMap.toMatrix b b (T ^ s) = (LinearMap.toMatrix b b T) ^ s := by
    intro s; induction s with
    | zero => simp
    | succ s ih => rw [pow_succ', pow_succ', LinearMap.toMatrix_mul, ih]
  have htraceTk : LinearMap.trace ℂ V (T ^ k) = ∑ i : I, (i.1 : ℂ) ^ k := by
    rw [LinearMap.trace_eq_matrix_trace ℂ b (T ^ k), hpowmat k, hmat, Matrix.diagonal_pow,
      Matrix.trace_diagonal]
    simp
  rw [htraceT, htraceTk, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply aut_apply_eq_pow_of_pow_eq_one hn hζ σ hσ
  have hev : Module.End.HasEigenvector T i.1 (b i) :=
    ⟨ed.collectedBasis_mem _ i, b.ne_zero i⟩
  have hp : (T ^ r) (b i) = i.1 ^ r • b i := hev.pow_apply r
  have hp2 : i.1 ^ r • b i = b i := by
    rw [← hp, hT]; rfl
  have hzero : (i.1 ^ r - 1) • b i = 0 := by rw [sub_smul, hp2, one_smul, sub_self]
  have hlamr : i.1 ^ r = 1 := by
    rcases smul_eq_zero.mp hzero with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h (b.ne_zero i)
  obtain ⟨d, hd⟩ := hrn
  rw [hd, pow_mul, hlamr, one_pow]

/-- Let `M` be a complex matrix with `M ^ r = 1` (`r > 0`).  Let `ζ` be a primitive `n`-th root of
unity with `r ∣ n`, and let `σ : ℂ ≃+* ℂ` satisfy `σ ζ = ζ ^ k`.  Then
`(M.map σ).trace = (M ^ k).trace`. -/
theorem trace_map_eq_trace_pow {m r n k : ℕ} (hr : 0 < r) (hn : 0 < n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) (hrn : r ∣ n) (σ : ℂ ≃+* ℂ) (hσ : σ ζ = ζ ^ k)
    (M : Matrix (Fin m) (Fin m) ℂ) (hM : M ^ r = 1) :
    (M.map σ).trace = (M ^ k).trace := by
  have htrace_map : (M.map σ).trace = σ M.trace := by
    simp [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
  have heq : ∀ A : Matrix (Fin m) (Fin m) ℂ, Matrix.toLinAlgEquiv' A = Matrix.toLin' A :=
    fun A => LinearMap.ext fun x => by simp [Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply]
  have hpow : (Matrix.toLin' M) ^ k = Matrix.toLin' (M ^ k) := by
    rw [← heq M, ← map_pow Matrix.toLinAlgEquiv' M k, heq (M ^ k)]
  have hTr : (Matrix.toLin' M) ^ r = 1 := by
    rw [← heq M, ← map_pow Matrix.toLinAlgEquiv' M r, hM, map_one]
  rw [htrace_map]
  have key := trace_sigma_eq_trace_pow hr hn hζ hrn σ hσ (Matrix.toLin' M) hTr
  rw [← Matrix.trace_toLin'_eq M, key, hpow, Matrix.trace_toLin'_eq (M ^ k)]

end Work.Clifford
