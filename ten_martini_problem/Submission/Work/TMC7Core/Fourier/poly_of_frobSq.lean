import Mathlib
import Submission.Work.TMC7Core.Trig.frobSq_eq_iterZ
import Submission.Work.TMC7Core.Trig.iterPoly_eval
import Submission.Work.TMC7Core.Trig.iterPoly_natDegree

/-!
# `frobSq` is the squared modulus of a polynomial on the unit circle

`frobSq α lam E N x = ∑_{i,j} ‖A_N(x)_{ij}‖²` is a real trigonometric polynomial in
`x` of degree `≤ 2N`.  Here we promote it to a genuine *complex* polynomial in
`z = e^{2πix}`: there is `Q ∈ ℂ[X]` with `natDegree Q ≤ 4N` and

`‖Q(e^{2πix})‖ = frobSq α lam E N x`  for every `x : ℝ`.

The construction uses the polynomial cocycle `iterPoly α lam E N`, whose entries
satisfy `(iterPoly α lam E N i j).eval z = iterZ α lam E N z i j` on the unit circle
(`iterPoly_eval`).  On `‖z‖ = 1` one has `‖w‖² = w · conj w` and `conj w = star w`,
so we build, for a polynomial `p` of degree `≤ d`, the *conjugate-reverse*
`revConj d p = ∑_{k≤d} conj(p.coeff k) X^{d-k}`, which satisfies
`(revConj d p).eval z = z^d · conj (p.eval z)` when `‖z‖ = 1`.  Then

`Q = ∑_{i,j} p_{ij} · revConj (2N) p_{ij}`

has degree `≤ 4N` and `Q(z) = z^{2N} ∑_{i,j} ‖p_{ij}(z)‖²`, whence the norm of the
right-hand side is the wanted real quantity.
-/

namespace Work.TMC7Core.Fourier

open Polynomial

noncomputable section

/-- Coefficientwise conjugate followed by reversal at degree `d`:
`revConj d p = ∑_{k ≤ d} conj (p.coeff k) · X^{d-k}`.  Its degree is `≤ d`. -/
def revConj (d : ℕ) (p : Polynomial ℂ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range (d + 1), Polynomial.C (star (p.coeff k)) * Polynomial.X ^ (d - k)

/-- `revConj d p` has degree at most `d`. -/
lemma revConj_natDegree (d : ℕ) (p : Polynomial ℂ) : (revConj d p).natDegree ≤ d := by
  rw [revConj]
  refine Polynomial.natDegree_sum_le_of_forall_le (Finset.range (d + 1))
    (fun k => Polynomial.C (star (p.coeff k)) * Polynomial.X ^ (d - k)) (fun k hk => ?_)
  exact (Polynomial.natDegree_C_mul_X_pow_le (star (p.coeff k)) (d - k)).trans (Nat.sub_le _ _)

/-- A polynomial of degree `≤ d` is the sum of its monomials up to `d`. -/
lemma eval_eq_sum_range (p : Polynomial ℂ) (z : ℂ) (d : ℕ) (hp : p.natDegree ≤ d) :
    p.eval z = ∑ k ∈ Finset.range (d + 1), p.coeff k * z ^ k := by
  conv_lhs => rw [Polynomial.as_sum_range' p (d + 1) (Nat.lt_succ_of_le hp)]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial]

/-- On the unit circle, `revConj` realises `z ↦ z^d · conj (p z)`. -/
lemma revConj_eval (d : ℕ) (p : Polynomial ℂ) (z : ℂ) (hz : ‖z‖ = 1) (hp : p.natDegree ≤ d) :
    (revConj d p).eval z = z ^ d * star (p.eval z) := by
  have hzz : z * star z = 1 := by
    have h := Complex.mul_conj z
    rw [Complex.normSq_eq_norm_sq, hz] at h
    simp at h
    simpa [Complex.star_def] using h
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; exact zero_ne_one hz
  have hkey : ∀ k ∈ Finset.range (d + 1), z ^ d * star z ^ k = z ^ (d - k) := by
    intro k hk
    have hk' : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    apply mul_right_cancel₀ (pow_ne_zero k hz0)
    calc z ^ d * star z ^ k * z ^ k
        = z ^ d * (star z * z) ^ k := by rw [mul_pow]; ring
      _ = z ^ d * (z * star z) ^ k := by rw [mul_comm (star z) z]
      _ = z ^ d * 1 := by rw [hzz, one_pow]
      _ = z ^ (d - k) * z ^ k := by rw [mul_one, ← pow_add, Nat.sub_add_cancel hk']
  have hrev : (revConj d p).eval z
      = ∑ k ∈ Finset.range (d + 1), star (p.coeff k) * z ^ (d - k) := by
    rw [revConj, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    simp [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow]
  rw [hrev, eval_eq_sum_range p z d hp, star_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [star_mul, star_pow, ← hkey k hk]
  ring

/-- The norm of a nonnegative real, viewed in `ℂ`. -/
lemma norm_ofReal_of_nonneg (s : ℝ) (hs : 0 ≤ s) : ‖((s : ℝ) : ℂ)‖ = s := by
  rw [Complex.norm_def, Complex.normSq_ofReal]
  exact Real.sqrt_mul_self hs

/-- The entry of `iterPoly α lam E N` evaluated at `z` is the corresponding entry of
the algebraic cocycle `iterZ α lam E N z`. -/
lemma iterPoly_eval_entry (α lam : ℝ) (E : ℂ) (N : ℕ) (z : ℂ) (i j : Fin 2) :
    (Work.TMC7Core.iterPoly α lam E N i j).eval z = Work.TMC7Core.iterZ α lam E N z i j := by
  have h := congrFun (congrFun (Work.TMC7Core.Trig.iterPoly_eval α lam E N z) i) j
  simpa only [Matrix.map_apply] using h

theorem poly_of_frobSq (α lam : ℝ) (E : ℂ) (N : ℕ) :
    ∃ Q : Polynomial ℂ, Q.natDegree ≤ 4 * N ∧
      ∀ x : ℝ, ‖Polynomial.eval (Complex.exp (2 * Real.pi * Complex.I * x)) Q‖
        = Work.TMC7Core.frobSq α lam E N x := by
  refine ⟨∑ i : Fin 2, ∑ j : Fin 2,
    Work.TMC7Core.iterPoly α lam E N i j * revConj (2 * N) (Work.TMC7Core.iterPoly α lam E N i j),
    ?_, ?_⟩
  · -- degree bound: each summand has degree `≤ 2N + 2N = 4N`
    refine Polynomial.natDegree_sum_le_of_forall_le _ (fun i => ∑ j : Fin 2,
      Work.TMC7Core.iterPoly α lam E N i j * revConj (2 * N) (Work.TMC7Core.iterPoly α lam E N i j)) ?_
    intro i _
    refine Polynomial.natDegree_sum_le_of_forall_le _ (fun j =>
      Work.TMC7Core.iterPoly α lam E N i j * revConj (2 * N) (Work.TMC7Core.iterPoly α lam E N i j)) ?_
    intro j _
    exact (Polynomial.natDegree_mul_le_of_le (Work.TMC7Core.Trig.iterPoly_natDegree α lam E N i j)
      (revConj_natDegree (2 * N) _)).trans (by omega)
  · intro x
    set z : ℂ := Complex.exp (2 * Real.pi * Complex.I * x) with hzdef
    have hzn : ‖z‖ = 1 := by rw [hzdef, Complex.norm_exp]; simp [Complex.mul_re]
    have hentry : ∀ i j : Fin 2, (Work.TMC7Core.iterPoly α lam E N i j).eval z
        = Work.TMC7Core.iterZ α lam E N z i j := iterPoly_eval_entry α lam E N z
    have hww : ∀ i j : Fin 2, Work.TMC7Core.iterZ α lam E N z i j
        * star (Work.TMC7Core.iterZ α lam E N z i j)
        = ((‖Work.TMC7Core.iterZ α lam E N z i j‖ ^ 2 : ℝ) : ℂ) := by
      intro i j
      have h := Complex.mul_conj (Work.TMC7Core.iterZ α lam E N z i j)
      rw [Complex.normSq_eq_norm_sq] at h
      simpa [Complex.star_def] using h
    have hQ : Polynomial.eval z (∑ i : Fin 2, ∑ j : Fin 2,
        Work.TMC7Core.iterPoly α lam E N i j * revConj (2 * N) (Work.TMC7Core.iterPoly α lam E N i j))
        = ∑ i : Fin 2, ∑ j : Fin 2, z ^ (2 * N)
            * ((‖Work.TMC7Core.iterZ α lam E N z i j‖ ^ 2 : ℝ) : ℂ) := by
      rw [Polynomial.eval_finsetSum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Polynomial.eval_finsetSum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Polynomial.eval_mul,
        revConj_eval (2 * N) _ z hzn (Work.TMC7Core.Trig.iterPoly_natDegree α lam E N i j), hentry i j]
      rw [← hww i j]
      ring
    rw [hQ, show (∑ i : Fin 2, ∑ j : Fin 2, z ^ (2 * N)
            * ((‖Work.TMC7Core.iterZ α lam E N z i j‖ ^ 2 : ℝ) : ℂ))
          = z ^ (2 * N) * (∑ i : Fin 2, ∑ j : Fin 2,
              ((‖Work.TMC7Core.iterZ α lam E N z i j‖ ^ 2 : ℝ) : ℂ)) from by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.mul_sum]]
    rw [norm_mul, norm_pow, hzn, one_pow, one_mul]
    rw [show (∑ i : Fin 2, ∑ j : Fin 2, ((‖Work.TMC7Core.iterZ α lam E N z i j‖ ^ 2 : ℝ) : ℂ))
        = ((∑ i : Fin 2, ∑ j : Fin 2, ‖Work.TMC7Core.iterZ α lam E N z i j‖ ^ 2 : ℝ) : ℂ) from by
      push_cast
      rfl]
    rw [norm_ofReal_of_nonneg _
      (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)))]
    rw [Work.TMC7Core.Trig.frobSq_eq_iterZ, ← hzdef]

end

end Work.TMC7Core.Fourier
