import Mathlib
import Submission.Work.TMC14Core.zero_aux

/-!
# `disc_zero_abs`: the graded half-product trace identity

For `a ζ u : ℂ`, `ζ` a primitive `2N`-th root of unity and `u ≠ 0`, the transfer matrices
`S2 x = !![x, -1; 1, 0]` of the energy-zero almost Mathieu cocycle with arguments
`x t = (a/2) * (u * ζ^t + (u * ζ^t)⁻¹)` satisfy
`tr (S2 (x 0) * ⋯ * S2 (x (N-1)) * sz) = ∏ t, x t`.

The proof is the "grading" argument: `u * S2 (x t)` is the value at `X = u` of the polynomial
matrix `Mpol t = !![C (a/2 * ζ^t) X² + C (a/2 * (ζ^t)⁻¹), -X; X, 0]`, whose product has
entries of degree `≤ 2N`.  The substitution `X ↦ ζ X` maps the `N`-fold product to `ζ^N`
times a cyclic rotation of itself, so the supertrace `Tpoly` is invariant under `X ↦ ζ X` and
therefore has only the two coefficients `X^0` and `X^{2N}`; these are computed from the value
at `X = 0` and from the reciprocal identity `Tpoly_{ζ⁻¹}(X) = X^{2N} Tpoly_ζ(X⁻¹)`.
-/

open Polynomial Matrix
open scoped BigOperators

noncomputable section

namespace Work.TMC14Core

namespace DZ

/-! ## 1. Definitions -/

/-- The `t`-th linear factor `(a/2) ζ^t X² + (a/2) (ζ^t)⁻¹` of the graded product. -/
def grFactor (a ζ : ℂ) (t : ℕ) : ℂ[X] := C (a / 2 * ζ ^ t) * X ^ 2 + C (a / 2 * (ζ ^ t)⁻¹)

/-- `X` times the `t`-th transfer matrix, as a polynomial matrix. -/
def Mpol (a ζ : ℂ) (t : ℕ) : Matrix (Fin 2) (Fin 2) ℂ[X] := !![grFactor a ζ t, -X; X, 0]

/-- `sz = diag(1,-1)` as a polynomial matrix. -/
def szp : Matrix (Fin 2) (Fin 2) ℂ[X] := !![1, 0; 0, -1]

/-- The ordered product `f 0 * ⋯ * f (n-1)` of polynomial matrices. -/
def gprod (f : ℕ → Matrix (Fin 2) (Fin 2) ℂ[X]) : ℕ → Matrix (Fin 2) (Fin 2) ℂ[X]
  | 0 => 1
  | n + 1 => gprod f n * f n

/-- The graded product `Mpol 0 * ⋯ * Mpol (N-1)`. -/
def Pmat (a ζ : ℂ) (N : ℕ) : Matrix (Fin 2) (Fin 2) ℂ[X] := gprod (Mpol a ζ) N

/-- The supertrace of the graded product. -/
def Tpoly (a ζ : ℂ) (N : ℕ) : ℂ[X] := ((Pmat a ζ N) * szp).trace

/-- The product of the linear factors `grFactor`. -/
def Rpoly (a ζ : ℂ) (N : ℕ) : ℂ[X] := ∏ t ∈ Finset.range N, grFactor a ζ t

/-! ## 2. Entries -/

@[simp] theorem Mpol_apply_zero_zero (a ζ : ℂ) (t : ℕ) : (Mpol a ζ t) 0 0 = grFactor a ζ t := rfl

@[simp] theorem Mpol_apply_zero_one (a ζ : ℂ) (t : ℕ) : (Mpol a ζ t) 0 1 = -X := rfl

@[simp] theorem Mpol_apply_one_zero (a ζ : ℂ) (t : ℕ) : (Mpol a ζ t) 1 0 = X := rfl

@[simp] theorem Mpol_apply_one_one (a ζ : ℂ) (t : ℕ) : (Mpol a ζ t) 1 1 = 0 := rfl

@[simp] theorem szp_apply_zero_zero : szp 0 0 = 1 := rfl

@[simp] theorem szp_apply_zero_one : szp 0 1 = 0 := rfl

@[simp] theorem szp_apply_one_zero : szp 1 0 = 0 := rfl

@[simp] theorem szp_apply_one_one : szp 1 1 = -1 := rfl

@[simp] theorem Pmat_zero (a ζ : ℂ) : Pmat a ζ 0 = 1 := rfl

@[simp] theorem Pmat_succ (a ζ : ℂ) (N : ℕ) :
    Pmat a ζ (N + 1) = Pmat a ζ N * Mpol a ζ N := rfl

@[simp] theorem gprod_zero (f : ℕ → Matrix (Fin 2) (Fin 2) ℂ[X]) : gprod f 0 = 1 := rfl

@[simp] theorem gprod_succ (f : ℕ → Matrix (Fin 2) (Fin 2) ℂ[X]) (n : ℕ) :
    gprod f (n + 1) = gprod f n * f n := rfl

theorem gprod_add (f : ℕ → Matrix (Fin 2) (Fin 2) ℂ[X]) (m n : ℕ) :
    gprod f (m + n) = gprod f m * gprod (fun k => f (m + k)) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show m + (n + 1) = (m + n) + 1 by omega, gprod_succ, ih, gprod_succ, mul_assoc]

/-! ## 3. Degree bounds -/

theorem grFactor_natDegree (a ζ : ℂ) (t : ℕ) : (grFactor a ζ t).natDegree ≤ 2 := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [grFactor, coeff_add, coeff_C_mul_X_pow, coeff_C]
  simp [show m ≠ 2 by omega, show m ≠ 0 by omega]

theorem Mpol_natDegree (a ζ : ℂ) (t : ℕ) (i j : Fin 2) : ((Mpol a ζ t) i j).natDegree ≤ 2 := by
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceEq, reduceIte]
  · rw [Mpol_apply_zero_zero]
    exact grFactor_natDegree a ζ t
  · rw [Mpol_apply_zero_one, natDegree_neg, natDegree_X]; norm_num
  · rw [Mpol_apply_one_zero, natDegree_X]; norm_num
  · rw [Mpol_apply_one_one, natDegree_zero]; norm_num

theorem szp_natDegree (i j : Fin 2) : (szp i j).natDegree ≤ 0 := by
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceEq, reduceIte]
  · rw [szp_apply_zero_zero]; simp
  · rw [szp_apply_zero_one]; simp
  · rw [szp_apply_one_zero]; simp
  · rw [szp_apply_one_one]; simp

theorem Pmat_natDegree (a ζ : ℂ) : ∀ (N : ℕ) (i j : Fin 2),
    ((Pmat a ζ N) i j).natDegree ≤ 2 * N := by
  intro N
  induction N with
  | zero =>
    intro i j
    rw [Pmat_zero, Matrix.one_apply]
    split <;> simp
  | succ n ih =>
    intro i j
    rw [Pmat_succ, Matrix.mul_apply, Fin.sum_univ_two]
    refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_) <;>
      refine le_trans natDegree_mul_le ?_ <;>
      have h1 := ih i 0 <;> have h2 := ih i 1 <;>
      have h3 := Mpol_natDegree a ζ n 0 j <;> have h4 := Mpol_natDegree a ζ n 1 j <;>
      omega

theorem Tpoly_natDegree (a ζ : ℂ) (N : ℕ) : (Tpoly a ζ N).natDegree ≤ 2 * N := by
  rw [Tpoly, Matrix.trace_fin_two]
  refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_) <;>
    rw [Matrix.mul_apply, Fin.sum_univ_two] <;>
    refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_) <;>
    refine le_trans natDegree_mul_le ?_ <;>
    have h1 := Pmat_natDegree a ζ N 0 0 <;>
    have h2 := Pmat_natDegree a ζ N 0 1 <;>
    have h3 := Pmat_natDegree a ζ N 1 0 <;>
    have h4 := Pmat_natDegree a ζ N 1 1 <;>
    have h5 := szp_natDegree 0 0 <;> have h6 := szp_natDegree 1 1 <;>
    have h7 := szp_natDegree 0 1 <;> have h8 := szp_natDegree 1 0 <;>
    omega

/-! ## 4. Products, scaling and ring homomorphisms -/

theorem gprod_map (φ : ℂ[X] →+* ℂ) (f : ℕ → Matrix (Fin 2) (Fin 2) ℂ[X]) (N : ℕ) :
    φ.mapMatrix (gprod f N) = mprod (fun t => φ.mapMatrix (f t)) N := by
  induction N with
  | zero => rw [gprod_zero, mprod_zero]; simp [RingHom.mapMatrix]
  | succ n ih => rw [gprod_succ, mprod_succ, map_mul, ih]

theorem mprod_mul_smul_const (c : ℂ) (M : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (N : ℕ) :
    mprod (fun t => c • M t) N = c ^ N • mprod M N := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [mprod_succ, mprod_succ, ih, Matrix.smul_mul, Matrix.mul_smul, smul_smul, pow_succ]

/-! ## 5. Evaluation of the graded product -/

theorem evalRingHom_apply_eval (u : ℂ) (p : ℂ[X]) :
    (Polynomial.evalRingHom u) p = p.eval u := rfl

theorem mapMatrix_apply_entry (φ : ℂ[X] →+* ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ[X])
    (i j : Fin 2) : (φ.mapMatrix M) i j = φ (M i j) := by
  rw [RingHom.mapMatrix_apply, Matrix.map_apply]

theorem mapMatrix_trace (φ : ℂ[X] →+* ℂ) (M : Matrix (Fin 2) (Fin 2) ℂ[X]) :
    (φ.mapMatrix M).trace = φ M.trace := by
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two, mapMatrix_apply_entry,
    mapMatrix_apply_entry, map_add]

theorem mapMatrix_eval_szp (u : ℂ) : (Polynomial.evalRingHom u).mapMatrix szp = sz := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceEq, reduceIte] <;>
    simp [szp, sz, RingHom.mapMatrix, Matrix.map_apply]

/-- The supertrace of the graded product, evaluated at `u`, is a product of complex matrices. -/
theorem Tpoly_eval_eq (a ζ : ℂ) (N : ℕ) (u : ℂ) :
    (Tpoly a ζ N).eval u
      = ((mprod (fun t => (Polynomial.evalRingHom u).mapMatrix (Mpol a ζ t)) N) * sz).trace := by
  rw [show (Tpoly a ζ N).eval u
      = (Polynomial.evalRingHom u) ((Pmat a ζ N * szp).trace) from rfl,
    ← mapMatrix_trace, map_mul, show Pmat a ζ N = gprod (Mpol a ζ) N from rfl,
    gprod_map, mapMatrix_eval_szp]

/-- `u` times the transfer matrix of the `t`-th step is the value of `Mpol t` at `X = u`. -/
theorem Mpol_eval_eq_smul (a ζ : ℂ) (t : ℕ) {u : ℂ} (hu : u ≠ 0) (hζ : ζ ≠ 0) :
    (Polynomial.evalRingHom u).mapMatrix (Mpol a ζ t)
      = u • S2 ((a / 2) * (u * ζ ^ t + (u * ζ ^ t)⁻¹)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceEq, reduceIte]
  · simp [mapMatrix_apply_entry, Mpol, grFactor, S2, Matrix.of_apply,
      Matrix.smul_apply, smul_eq_mul, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Matrix.empty_val', Fin.isValue, ge_iff_le]
    have hzt : ζ ^ t ≠ 0 := pow_ne_zero _ hζ
    field_simp
  · simp [mapMatrix_apply_entry, Mpol, S2, Matrix.of_apply, Matrix.smul_apply,
      smul_eq_mul, Polynomial.eval_neg, Polynomial.eval_X, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Matrix.empty_val', Fin.isValue, ge_iff_le]
  · simp [mapMatrix_apply_entry, Mpol, S2, Matrix.of_apply, Matrix.smul_apply,
      smul_eq_mul, Polynomial.eval_X, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Matrix.empty_val', Fin.isValue, ge_iff_le]
  · simp [mapMatrix_apply_entry, Mpol, S2, Matrix.of_apply, Matrix.smul_apply,
      Polynomial.eval_zero, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.empty_val',
      Fin.isValue, ge_iff_le]

/-- The bridge: `Tpoly` at `u` is `u^N` times the supertrace of the half-product. -/
theorem Tpoly_eval_ne_zero (a ζ : ℂ) (N : ℕ) {u : ℂ} (hu : u ≠ 0) (hζ : ζ ≠ 0) :
    (Tpoly a ζ N).eval u
      = u ^ N * ((mprod (fun t => S2 ((a / 2) * (u * ζ ^ t + (u * ζ ^ t)⁻¹))) N) * sz).trace := by
  rw [Tpoly_eval_eq]
  have hfun : (fun t => (Polynomial.evalRingHom u).mapMatrix (Mpol a ζ t))
      = (fun t => u • S2 ((a / 2) * (u * ζ ^ t + (u * ζ ^ t)⁻¹))) := by
    funext t
    exact Mpol_eval_eq_smul a ζ t hu hζ
  rw [hfun, mprod_mul_smul_const, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

/-! ## 6. Substitution, invariance and the shift -/

/-- The substitution `X ↦ ζ X` shifts the index of the graded factors. -/
theorem Mpol_subst (a ζ : ℂ) (t : ℕ) (u : ℂ) (hζ : ζ ≠ 0) :
    (Polynomial.evalRingHom (ζ * u)).mapMatrix (Mpol a ζ t)
      = ζ • (Polynomial.evalRingHom u).mapMatrix (Mpol a ζ (t + 1)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceEq, reduceIte]
  · simp [mapMatrix_apply_entry, Mpol, grFactor, Matrix.of_apply,
      Matrix.smul_apply, smul_eq_mul, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Matrix.empty_val', Fin.isValue, ge_iff_le]
    have hzt : ζ ^ t ≠ 0 := pow_ne_zero _ hζ
    have hzt1 : ζ ^ (t + 1) ≠ 0 := pow_ne_zero _ hζ
    field_simp
    ring
  · simp [mapMatrix_apply_entry, Mpol, Matrix.of_apply, Matrix.smul_apply,
      smul_eq_mul, Polynomial.eval_neg, Polynomial.eval_X, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Matrix.empty_val', Fin.isValue, ge_iff_le]
  · simp [mapMatrix_apply_entry, Mpol, Matrix.of_apply, Matrix.smul_apply,
      smul_eq_mul, Polynomial.eval_X, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Matrix.empty_val', Fin.isValue, ge_iff_le]
  · simp [mapMatrix_apply_entry, Mpol, Matrix.of_apply, Matrix.smul_apply,
      Polynomial.eval_zero, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.empty_val',
      Fin.isValue, ge_iff_le]

/-- `sz`-conjugation of a `2 × 2` matrix, entrywise. -/
theorem sz_mul_sz_apply (A : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    (sz * A * sz) i j = sz i i * A i j * sz j j := by
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, sz, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one,
      Matrix.head_fin_const, Matrix.empty_val', Fin.isValue, Fin.zero_eta, Fin.mk_one] <;>
    ring

/-- The last graded factor is the `sz`-conjugate of the first, up to sign, when `ζ^N = -1`. -/
theorem Mpol_last (a ζ : ℂ) (N : ℕ) (hζN : ζ ^ N = -1) (u : ℂ) (hζ : ζ ≠ 0) :
    (Polynomial.evalRingHom u).mapMatrix (Mpol a ζ N)
      = -(sz * (Polynomial.evalRingHom u).mapMatrix (Mpol a ζ 0) * sz) := by
  have hζNinv : (ζ ^ N)⁻¹ = -1 := by rw [hζN]; norm_num
  ext i j
  rw [Matrix.neg_apply, sz_mul_sz_apply]
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceEq, reduceIte] <;>
    simp only [mapMatrix_apply_entry, Mpol_apply_zero_zero, Mpol_apply_zero_one,
      Mpol_apply_one_zero, Mpol_apply_one_one, evalRingHom_apply_eval] <;>
    simp [grFactor, sz, RingHom.mapMatrix, Matrix.map_apply, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_neg, hζN, hζNinv] <;>
    ring

/-- The `sz`-twisted trace of a shifted half-product, when the last factor is the
`sz`-conjugate of the first one. -/
theorem mprod_shift_trace (M : ℕ → Matrix (Fin 2) (Fin 2) ℂ) (n : ℕ)
    (hM : M (n + 1) = -(sz * M 0 * sz)) :
    ((mprod (fun t => M (t + 1)) (n + 1)) * sz).trace
      = -(((mprod M (n + 1)) * sz).trace) := by
  have h1 : mprod (fun t => M (t + 1)) (n + 1) = mprod (fun t => M (t + 1)) n * M (n + 1) := by
    rw [mprod_succ]
  have h2 : mprod M (n + 1) = M 0 * mprod (fun t => M (t + 1)) n := by
    have h := mprod_add M 1 n
    rw [mprod_succ, mprod_zero, Matrix.one_mul] at h
    rw [show 1 + n = n + 1 by omega] at h
    rw [h]
    congr 1
    congr 1
    funext k
    rw [Nat.add_comm]
  rw [h1, h2, hM]
  have hL : mprod (fun t => M (t + 1)) n * -(sz * M 0 * sz) * sz
      = -(mprod (fun t => M (t + 1)) n * sz * M 0) := by
    rw [Matrix.mul_neg, Matrix.neg_mul]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [sz_mul_sz, Matrix.mul_one]
  rw [hL, Matrix.trace_neg, neg_inj]
  rw [show mprod (fun t => M (t + 1)) n * sz * M 0
      = (mprod (fun t => M (t + 1)) n * sz) * M 0 from rfl,
    Matrix.trace_mul_comm, Matrix.mul_assoc]

/-- The supertrace of the graded half-product is invariant under `X ↦ ζ X`. -/
theorem Tpoly_eval_zeta_mul (a ζ : ℂ) (N : ℕ) (hN : 0 < N) (hζN : ζ ^ N = -1) (u : ℂ) :
    (Tpoly a ζ N).eval (ζ * u) = (Tpoly a ζ N).eval u := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hζ : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.succ_ne_zero n)] at hζN
    exact absurd hζN (by norm_num)
  rw [Tpoly_eval_eq (u := ζ * u), Tpoly_eval_eq (u := u)]
  have hfun : (fun t => (Polynomial.evalRingHom (ζ * u)).mapMatrix (Mpol a ζ t))
      = (fun t => ζ • (Polynomial.evalRingHom u).mapMatrix (Mpol a ζ (t + 1))) := by
    funext t
    exact Mpol_subst a ζ t u hζ
  rw [hfun, mprod_mul_smul_const, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    mprod_shift_trace (fun s => (Polynomial.evalRingHom u).mapMatrix (Mpol a ζ s)) n
      (Mpol_last a ζ (n + 1) hζN u hζ)]
  rw [hζN]
  ring

/-! ## 7. Polynomial auxiliaries -/

/-- A polynomial over `ℂ` vanishing at every nonzero complex number is zero. -/
theorem eq_zero_of_eval_eq_zero_of_ne_zero (p : ℂ[X]) (h : ∀ u : ℂ, u ≠ 0 → p.eval u = 0) :
    p = 0 := by
  by_contra hp
  have hfin : (Set.univ \ {0} : Set ℂ).Finite :=
    (Polynomial.finite_setOf_isRoot hp).subset (by
      intro u hu
      have hu0 : u ≠ 0 := by simpa using hu.2
      exact h u hu0)
  exact ((Set.infinite_univ.diff (Set.finite_singleton (0 : ℂ)))).not_finite hfin

/-- Coefficients of the substitution `X ↦ c X`. -/
theorem coeff_comp_C_mul_X (p : ℂ[X]) (c : ℂ) (m : ℕ) :
    (p.comp (C c * X)).coeff m = p.coeff m * c ^ m := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [Polynomial.add_comp, coeff_add, hp, hq, coeff_add]; ring
  | monomial k a =>
    rw [Polynomial.monomial_comp, mul_pow, ← Polynomial.C_pow, ← mul_assoc, ← Polynomial.C_mul,
      coeff_C_mul_X_pow, coeff_monomial]
    by_cases h : k = m
    · rw [if_pos h, if_pos h.symm, h]
    · have h' : ¬ (m = k) := fun hh => h hh.symm
      rw [if_neg h', if_neg h]; ring

/-- A polynomial of degree at most `n` invariant under `X ↦ ζ X`, `ζ` a primitive `n`-th
root of unity, is the sum of its constant and its `X^n` terms. -/
theorem poly_two_coeff (n : ℕ) (hn : 0 < n) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ n)
    (p : ℂ[X]) (hdeg : p.natDegree ≤ n) (hfix : ∀ z : ℂ, p.eval (ζ * z) = p.eval z) :
    p = Polynomial.C (p.coeff 0) + Polynomial.C (p.coeff n) * Polynomial.X ^ n := by
  have hzeta : (C ζ * X).eval (0 : ℂ) = 0 := by simp
  have hq : p.comp (C ζ * X) = p := by
    apply Polynomial.funext
    intro z
    have hz : (C ζ * X).eval z = ζ * z := by simp
    rw [Polynomial.eval_comp, hz]
    exact hfix z
  have hcoeff : ∀ m, 0 < m → m < n → p.coeff m = 0 := by
    intro m hm0 hmn
    have h := congrArg (fun q : ℂ[X] => q.coeff m) hq
    rw [coeff_comp_C_mul_X] at h
    have hz : ζ ^ m ≠ 1 := by
      intro h1
      have hd := (hζ.pow_eq_one_iff_dvd m).mp h1
      have hle := Nat.le_of_dvd hm0 hd
      omega
    have h2 : p.coeff m * (ζ ^ m - 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · exact absurd (sub_eq_zero.mp h3) hz
  refine Polynomial.ext fun m => ?_
  simp only [coeff_add, coeff_C, coeff_C_mul_X_pow]
  by_cases h0 : m = 0
  · rw [h0]
    simp [show (0 : ℕ) ≠ n by omega]
  by_cases hn' : m = n
  · rw [hn']
    simp [show n ≠ 0 by omega]
  have hL : p.coeff m = 0 := by
    by_cases hlt : m < n
    · exact hcoeff m (Nat.pos_of_ne_zero h0) hlt
    · exact coeff_eq_zero_of_natDegree_lt (by omega)
  rw [hL]
  simp [h0, hn']

/-- `∏_{t<n} (1 + v η^t) = 1 - (-v)^n` for `η` a primitive `n`-th root of unity. -/
theorem prod_one_add_mul_pow (n : ℕ) (hn : 0 < n) (η v : ℂ) (hη : IsPrimitiveRoot η n) :
    ∏ t ∈ Finset.range n, (1 + v * η ^ t) = 1 - (-v) ^ n := by
  have hroot : ∀ u : ℂ, u ≠ 0 →
      (∏ t ∈ Finset.range n, (1 + u * η ^ t)) - (1 - (-u) ^ n) = 0 := by
    intro u hu
    have hprod : ∏ t ∈ Finset.range n, (u⁻¹ + η ^ t) = (u⁻¹) ^ n - (-1) ^ n := by
      have h := X_pow_sub_C_eq_prod hη hn (α := (1 : ℂ)) (a := (1 : ℂ)) (one_pow n)
      have h2 := congrArg (fun p : ℂ[X] => p.eval (-u⁻¹)) h
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C, Polynomial.eval_prod, Polynomial.eval_one, mul_one] at h2
      have h3 : ∏ x ∈ Finset.range n, (-u⁻¹ - η ^ x)
          = (-1) ^ n * ∏ x ∈ Finset.range n, (u⁻¹ + η ^ x) := by
        rw [show (∏ x ∈ Finset.range n, (-u⁻¹ - η ^ x))
            = ∏ x ∈ Finset.range n, (-(u⁻¹ + η ^ x)) from
              Finset.prod_congr rfl (fun x _ => by ring)]
        rw [Finset.prod_neg, Finset.card_range]
      rw [h3] at h2
      have h4 : (-u⁻¹) ^ n = (-1) ^ n * (u⁻¹) ^ n := by rw [neg_pow]
      rw [h4] at h2
      have hsq : ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n) = 1 := by
        rw [← mul_pow]; norm_num
      have h8 := congrArg (fun w : ℂ => ((-1 : ℂ) ^ n) * w) h2
      rw [mul_sub, mul_one] at h8
      rw [← mul_assoc, hsq, one_mul] at h8
      rw [← mul_assoc, hsq, one_mul] at h8
      exact h8.symm
    have hmain : ∏ t ∈ Finset.range n, (1 + u * η ^ t)
        = u ^ n * ∏ t ∈ Finset.range n, (u⁻¹ + η ^ t) := by
      rw [show (∏ t ∈ Finset.range n, (1 + u * η ^ t))
          = ∏ t ∈ Finset.range n, (u * (u⁻¹ + η ^ t)) from
            Finset.prod_congr rfl (fun t _ => by field_simp)]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    rw [hmain, hprod, mul_sub,
      show u ^ n * (u⁻¹) ^ n = 1 by rw [← mul_pow, mul_inv_cancel₀ hu, one_pow],
      show u ^ n * (-1) ^ n = (-u) ^ n by rw [neg_pow]; ring]
    ring
  rcases eq_or_ne v 0 with rfl | hv
  · simp [zero_pow (Nat.pos_iff_ne_zero.mp hn)]
  · exact sub_eq_zero.mp (hroot v hv)

/-- The `ℂ[X]` form of `prod_one_add_mul_pow`, used for `Rpoly`. -/
theorem prod_one_add_mul_pow_CX (n : ℕ) (hn : 0 < n) (η : ℂ) (hη : IsPrimitiveRoot η n) :
    ∏ t ∈ Finset.range n, (1 + C (η ^ t) * X ^ 2) = 1 - (-(X ^ 2)) ^ n := by
  apply Polynomial.funext
  intro z
  rw [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow,
    Polynomial.eval_neg, Polynomial.eval_pow, Polynomial.eval_X]
  rw [← prod_one_add_mul_pow n hn η (z ^ 2) hη]
  refine Finset.prod_congr rfl (fun t _ => ?_)
  rw [Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X]
  ring

/-! ## 8. The two extreme coefficients of `Tpoly` -/

/-- The rank-one projection `!![1,0;0,0]`. -/
def E2 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

theorem E2_mul_E2 : E2 * E2 = E2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceEq, reduceIte] <;>
    simp [E2, Matrix.mul_apply, Fin.sum_univ_two]

theorem trace_E2_sz : (E2 * sz).trace = 1 := by
  rw [Matrix.trace_fin_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two]
  simp [E2, sz]

theorem E2_pow (N : ℕ) (hN : 0 < N) : E2 ^ N = E2 := by
  cases N with
  | zero => omega
  | succ n =>
    clear hN
    induction n with
    | zero => simp
    | succ k ih => rw [pow_succ, ih, E2_mul_E2]

theorem mprod_smul_E2 (c : ℕ → ℂ) (N : ℕ) :
    mprod (fun t => c t • E2) N = (∏ t ∈ Finset.range N, c t) • E2 ^ N := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [mprod_succ, ih, Finset.prod_range_succ, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      pow_succ]

theorem eval_zero_Mpol (a ζ : ℂ) (t : ℕ) :
    (Polynomial.evalRingHom 0).mapMatrix (Mpol a ζ t) = ((a / 2) * (ζ ^ t)⁻¹) • E2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceEq, reduceIte] <;>
    simp [mapMatrix_apply_entry, Mpol, grFactor, E2, Matrix.smul_apply, smul_eq_mul,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]

/-- The value at `X = 0` of the supertrace of the graded product. -/
theorem Tpoly_eval_zero (a ζ : ℂ) (N : ℕ) (hN : 0 < N) :
    (Tpoly a ζ N).eval 0 = (a / 2) ^ N * ∏ t ∈ Finset.range N, (ζ ^ t)⁻¹ := by
  rw [Tpoly_eval_eq (u := 0)]
  have hfun : (fun t => (Polynomial.evalRingHom 0).mapMatrix (Mpol a ζ t))
      = (fun t => ((a / 2) * (ζ ^ t)⁻¹) • E2) := by
    funext t
    exact eval_zero_Mpol a ζ t
  rw [hfun, mprod_smul_E2, E2_pow N hN, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    trace_E2_sz, mul_one, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]

/-! ## 9. The reciprocal identity and the top coefficient -/

/-- `∏_{t<N} η^t = (-1)^(N+1)` for a primitive `N`-th root of unity `η`. -/
theorem prod_prim_root_pow (N : ℕ) (hN : 0 < N) (η : ℂ) (hη : IsPrimitiveRoot η N) :
    ∏ t ∈ Finset.range N, η ^ t = (-1) ^ (N + 1) := by
  have h := X_pow_sub_C_eq_prod hη hN (α := (1 : ℂ)) (a := (1 : ℂ)) (one_pow N)
  have h2 := congrArg (fun p : ℂ[X] => p.eval 0) h
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_prod, Polynomial.eval_one, mul_one] at h2
  have h3 : ∏ i ∈ Finset.range N, (0 - η ^ i) = (-1) ^ N * ∏ i ∈ Finset.range N, η ^ i := by
    rw [show (∏ i ∈ Finset.range N, (0 - η ^ i))
        = ∏ i ∈ Finset.range N, (-(η ^ i)) from
          Finset.prod_congr rfl (fun i _ => by ring)]
    rw [Finset.prod_neg, Finset.card_range]
  rw [h3, zero_pow (Nat.pos_iff_ne_zero.mp hN)] at h2
  have hsq : ((-1 : ℂ) ^ N) * ((-1 : ℂ) ^ N) = 1 := by rw [← mul_pow]; norm_num
  have h4 := congrArg (fun w : ℂ => ((-1 : ℂ) ^ N) * w) h2
  rw [← mul_assoc, hsq, one_mul] at h4
  have h5 : ((-1 : ℂ) ^ N) * ((0 : ℂ) - 1) = -((-1 : ℂ) ^ N) := by ring
  rw [h5] at h4
  rw [← h4, pow_succ]
  ring

/-- For `ζ` a primitive `2N`-th root of unity and `N > 0`, `ζ^N = -1`. -/
theorem prim_root_pow_eq_neg_one {N : ℕ} (hN : 0 < N) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (2 * N)) : ζ ^ N = -1 := by
  have h1 : (ζ ^ N) ^ 2 = 1 := by
    rw [← pow_mul, show N * 2 = 2 * N by ring]
    exact hζ.pow_eq_one
  have h2 : ζ ^ N ≠ 1 := by
    intro h
    have hd := (hζ.pow_eq_one_iff_dvd N).mp h
    have hle := Nat.le_of_dvd hN hd
    omega
  rcases sq_eq_one_iff.mp h1 with h | h
  · exact absurd h h2
  · exact h

/-- The reciprocal relation for the graded factors at `X = u` and `X = u⁻¹`. -/
theorem Mpol_recip (a ζ : ℂ) (t : ℕ) {u : ℂ} (hu : u ≠ 0) :
    (Polynomial.evalRingHom u).mapMatrix (Mpol a ζ t)
      = u ^ 2 • (Polynomial.evalRingHom u⁻¹).mapMatrix (Mpol a ζ⁻¹ t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceEq, reduceIte] <;>
    simp [mapMatrix_apply_entry, Mpol, grFactor, Matrix.smul_apply, smul_eq_mul,
      Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X, inv_pow] <;>
    field_simp <;>
    ring

/-- `Tpoly` satisfies the reciprocal identity `Tpoly_ζ(u) = u^{2N} Tpoly_{ζ⁻¹}(u⁻¹)`. -/
theorem Tpoly_recip (a ζ : ℂ) (N : ℕ) {u : ℂ} (hu : u ≠ 0) :
    (Tpoly a ζ N).eval u = u ^ (2 * N) * (Tpoly a ζ⁻¹ N).eval u⁻¹ := by
  rw [Tpoly_eval_eq (u := u), Tpoly_eval_eq (u := u⁻¹)]
  have hfun : (fun t => (Polynomial.evalRingHom u).mapMatrix (Mpol a ζ t))
      = (fun t => u ^ 2 • (Polynomial.evalRingHom u⁻¹).mapMatrix (Mpol a ζ⁻¹ t)) := by
    funext t
    exact Mpol_recip a ζ t hu
  rw [hfun, mprod_mul_smul_const, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, ← pow_mul]

/-- The constant coefficient of a polynomial is its value at zero. -/
theorem coeff_zero_eq_eval_zero_CX (p : ℂ[X]) : p.coeff 0 = p.eval 0 := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_self p.natDegree)]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b _ hb
    rw [zero_pow hb]; ring
  · intro h0
    simp at h0

/-- The coefficient of `X^{2N}` of `Tpoly`. -/
theorem Tpoly_coeff_top (a ζ : ℂ) (N : ℕ) (hN : 0 < N) (hζ : IsPrimitiveRoot ζ (2 * N)) :
    (Tpoly a ζ N).coeff (2 * N) = (a / 2) ^ N * ∏ t ∈ Finset.range N, ζ ^ t := by
  have hζN : ζ ^ N = -1 := prim_root_pow_eq_neg_one hN hζ
  have hζ' : IsPrimitiveRoot ζ⁻¹ (2 * N) := hζ.inv
  have hζN' : (ζ⁻¹) ^ N = -1 := prim_root_pow_eq_neg_one hN hζ'
  have hsupp : Tpoly a ζ N
      = C ((Tpoly a ζ N).coeff 0) + C ((Tpoly a ζ N).coeff (2 * N)) * X ^ (2 * N) :=
    poly_two_coeff (2 * N) (by omega) ζ hζ (Tpoly a ζ N) (Tpoly_natDegree a ζ N)
      (fun z => Tpoly_eval_zeta_mul a ζ N hN hζN z)
  have hsupp' : Tpoly a ζ⁻¹ N
      = C ((Tpoly a ζ⁻¹ N).coeff 0) + C ((Tpoly a ζ⁻¹ N).coeff (2 * N)) * X ^ (2 * N) :=
    poly_two_coeff (2 * N) (by omega) ζ⁻¹ hζ' (Tpoly a ζ⁻¹ N) (Tpoly_natDegree a ζ⁻¹ N)
      (fun z => Tpoly_eval_zeta_mul a ζ⁻¹ N hN hζN' z)
  have hpoly : (C ((Tpoly a ζ N).coeff 0) + C ((Tpoly a ζ N).coeff (2 * N)) * X ^ (2 * N))
      - (C ((Tpoly a ζ⁻¹ N).coeff (2 * N)) + C ((Tpoly a ζ⁻¹ N).coeff 0) * X ^ (2 * N))
      = 0 := by
    apply eq_zero_of_eval_eq_zero_of_ne_zero
    intro u hu
    simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    have hrec := Tpoly_recip a ζ N hu
    rw [hsupp] at hrec
    rw [hsupp'] at hrec
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X] at hrec
    rw [hrec]
    have h2N : u ^ (2 * N) * (u⁻¹) ^ (2 * N) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hu, one_pow]
    linear_combination ((Tpoly a ζ⁻¹ N).coeff (2 * N)) * h2N
  have hp : C ((Tpoly a ζ N).coeff 0) + C ((Tpoly a ζ N).coeff (2 * N)) * X ^ (2 * N)
      = C ((Tpoly a ζ⁻¹ N).coeff (2 * N)) + C ((Tpoly a ζ⁻¹ N).coeff 0) * X ^ (2 * N) :=
    sub_eq_zero.mp hpoly
  have hcoeff : (Tpoly a ζ N).coeff (2 * N) = (Tpoly a ζ⁻¹ N).coeff 0 := by
    have hA : (2 * N : ℕ) ≠ 0 := by omega
    have h2 := congrArg (fun p : ℂ[X] => p.coeff (2 * N)) hp
    have hL : (C ((Tpoly a ζ N).coeff 0) + C ((Tpoly a ζ N).coeff (2 * N)) * X ^ (2 * N)).coeff (2 * N)
        = (Tpoly a ζ N).coeff (2 * N) := by
      simp [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X_pow, hA]
    have hR : (C ((Tpoly a ζ⁻¹ N).coeff (2 * N)) + C ((Tpoly a ζ⁻¹ N).coeff 0) * X ^ (2 * N)).coeff (2 * N)
        = (Tpoly a ζ⁻¹ N).coeff 0 := by
      simp [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul_X_pow, hA]
    rw [hL, hR] at h2
    exact h2
  rw [hcoeff, coeff_zero_eq_eval_zero_CX, Tpoly_eval_zero a ζ⁻¹ N hN]
  congr 1
  refine Finset.prod_congr rfl (fun t _ => ?_)
  rw [inv_pow, inv_inv]

/-! ## 10. The half-product trace identity -/

theorem half_trace_gen (N : ℕ) (hN : 0 < N) (a ζ u : ℂ) (hζ : IsPrimitiveRoot ζ (2 * N))
    (hu : u ≠ 0) :
    ((mprod (fun t => S2 ((a / 2) * (u * ζ ^ t + (u * ζ ^ t)⁻¹))) N) * sz).trace
      = ∏ t ∈ Finset.range N, ((a / 2) * (u * ζ ^ t + (u * ζ ^ t)⁻¹)) := by
  have hζN : ζ ^ N = -1 := prim_root_pow_eq_neg_one hN hζ
  have hζne : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.pos_iff_ne_zero.mp hN)] at hζN
    exact absurd hζN (by norm_num)
  have hζ2 : IsPrimitiveRoot (ζ ^ 2) N := hζ.pow (by omega) (show 2 * N = 2 * N from rfl)
  have hsupp : Tpoly a ζ N
      = C ((Tpoly a ζ N).coeff 0) + C ((Tpoly a ζ N).coeff (2 * N)) * X ^ (2 * N) :=
    poly_two_coeff (2 * N) (by omega) ζ hζ (Tpoly a ζ N) (Tpoly_natDegree a ζ N)
      (fun z => Tpoly_eval_zeta_mul a ζ N hN hζN z)
  have hbridge : u ^ N * ((mprod (fun t => S2 ((a / 2) * (u * ζ ^ t + (u * ζ ^ t)⁻¹))) N) * sz).trace
      = (a / 2) ^ N * (∏ t ∈ Finset.range N, (ζ ^ t)⁻¹)
        + (a / 2) ^ N * (∏ t ∈ Finset.range N, ζ ^ t) * u ^ (2 * N) := by
    rw [← Tpoly_eval_ne_zero a ζ N hu hζne, hsupp]
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X]
    rw [coeff_zero_eq_eval_zero_CX, Tpoly_eval_zero a ζ N hN, Tpoly_coeff_top a ζ N hN hζ]
  have hWV : (∏ t ∈ Finset.range N, ζ ^ t) * (∏ t ∈ Finset.range N, (ζ ^ t)⁻¹) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one (fun t _ => ?_)
    exact mul_inv_cancel₀ (pow_ne_zero t hζne)
  have hW2 : (∏ t ∈ Finset.range N, ζ ^ t) ^ 2 = -((-1 : ℂ) ^ N) := by
    have h1 : (∏ t ∈ Finset.range N, ζ ^ t) ^ 2 = ∏ t ∈ Finset.range N, (ζ ^ 2) ^ t := by
      rw [sq, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun t _ => ?_)
      rw [← pow_mul]
      ring_nf
    rw [h1, prod_prim_root_pow N hN (ζ ^ 2) hζ2, pow_succ]
    ring
  have hW : (∏ t ∈ Finset.range N, ζ ^ t) = -((-1 : ℂ) ^ N) * ∏ t ∈ Finset.range N, (ζ ^ t)⁻¹ := by
    calc (∏ t ∈ Finset.range N, ζ ^ t)
        = (∏ t ∈ Finset.range N, ζ ^ t) ^ 2 * (∏ t ∈ Finset.range N, (ζ ^ t)⁻¹) := by
          rw [sq, mul_assoc, hWV, mul_one]
      _ = -((-1 : ℂ) ^ N) * ∏ t ∈ Finset.range N, (ζ ^ t)⁻¹ := by rw [hW2]
  have hmain : u ^ N * ∏ t ∈ Finset.range N, ((a / 2) * (u * ζ ^ t + (u * ζ ^ t)⁻¹))
      = (a / 2) ^ N * (∏ t ∈ Finset.range N, (ζ ^ t)⁻¹)
        + (a / 2) ^ N * (∏ t ∈ Finset.range N, ζ ^ t) * u ^ (2 * N) := by
    have hU : u ^ N * ∏ t ∈ Finset.range N, ((a / 2) * (u * ζ ^ t + (u * ζ ^ t)⁻¹))
        = (a / 2) ^ N * ∏ t ∈ Finset.range N, (u ^ 2 * ζ ^ t + (ζ ^ t)⁻¹) := by
      have h1 : u ^ N = ∏ t ∈ Finset.range N, u := by
        rw [Finset.prod_const, Finset.card_range]
      rw [h1, ← Finset.prod_mul_distrib]
      rw [show (∏ t ∈ Finset.range N, (u * ((a / 2) * (u * ζ ^ t + (u * ζ ^ t)⁻¹))))
          = ∏ t ∈ Finset.range N, ((a / 2) * (u ^ 2 * ζ ^ t + (ζ ^ t)⁻¹)) from
            Finset.prod_congr rfl (fun t _ => by
              have hzt : ζ ^ t ≠ 0 := pow_ne_zero t hζne
              rw [_root_.mul_inv_rev]
              field_simp)]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    rw [hU]
    have hV : ∏ t ∈ Finset.range N, (u ^ 2 * ζ ^ t + (ζ ^ t)⁻¹)
        = (∏ t ∈ Finset.range N, (ζ ^ t)⁻¹)
          * ∏ t ∈ Finset.range N, (1 + u ^ 2 * (ζ ^ 2) ^ t) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl (fun t _ => ?_)
      have hzt : ζ ^ t ≠ 0 := pow_ne_zero t hζne
      rw [show (ζ ^ 2) ^ t = (ζ ^ t) ^ 2 by rw [← pow_mul]; ring_nf]
      field_simp
      ring
    rw [hV, prod_one_add_mul_pow N hN (ζ ^ 2) (u ^ 2) hζ2, hW, neg_pow, ← pow_mul]
    ring
  have hfin : u ^ N * ∏ t ∈ Finset.range N, ((a / 2) * (u * ζ ^ t + (u * ζ ^ t)⁻¹))
      = u ^ N * ((mprod (fun t => S2 ((a / 2) * (u * ζ ^ t + (u * ζ ^ t)⁻¹))) N) * sz).trace := by
    rw [hmain, hbridge]
  exact (mul_left_cancel₀ (pow_ne_zero N hu) hfin).symm

end DZ

end Work.TMC14Core
