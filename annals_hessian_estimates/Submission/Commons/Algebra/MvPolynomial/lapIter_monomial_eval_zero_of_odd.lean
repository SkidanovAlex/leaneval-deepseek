import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

/-!
# The iterated Laplacian annihilates a monomial of even total degree that has
an odd exponent.

`lapIter_monomial_eval_zero_of_odd`: if `e : Fin n →₀ ℕ` has total weight
`2m` (so the monomial `∏ xᵢ^eᵢ` has degree `2m`) but some exponent `e i` is
odd, then applying `m` iterations of the Laplacian
`Q ↦ ∑ i, ∂ᵢ ∂ᵢ Q` to the monomial and evaluating at `0` gives `0`.
-/

noncomputable section
open scoped BigOperators
open MvPolynomial

namespace Commons.Algebra.MvPolynomial

private abbrev P (n : ℕ) := MvPolynomial (Fin n) ℝ

/-- Total degree (sum of exponents) of a monomial exponent vector. -/
private def wt {n : ℕ} (e : Fin n →₀ ℕ) : ℕ :=
  ∑ i : Fin n, e i

/-- Exponent vector obtained from `e` by removing two units at coordinate `i`
(as produced by applying `∂ᵢ²` to the monomial with exponent `e`). -/
private def tsub2 {n : ℕ} (e : Fin n →₀ ℕ) (i : Fin n) : Fin n →₀ ℕ :=
  (e - (Finsupp.single i 1)) - (Finsupp.single i 1)

/-- The coefficient `e i * (e i - 1)` vanishes unless `e i ≥ 2`. -/
private lemma coeff_of_lt_two {n : ℕ} (e : Fin n →₀ ℕ) (i : Fin n) (h : e i ≤ 1) :
    ((e i * (e i - 1) : ℕ) : ℝ) = 0 := by
  have h01 : e i = 0 ∨ e i = 1 := by omega
  rcases h01 with h0 | h1
  · simp [h0]
  · simp [h1]

/-- At coordinate `i` the twice-subtracted exponent is `e i - 2`. -/
private lemma tsub2_apply_self {n : ℕ} (e : Fin n →₀ ℕ) (i : Fin n) :
    (((tsub2 e i) : Fin n →₀ ℕ) i) = e i - 2 := by
  unfold tsub2
  simp
  omega

/-- Away from coordinate `i` the twice-subtracted exponent is unchanged. -/
private lemma tsub2_apply_of_ne {n : ℕ} (e : Fin n →₀ ℕ) (i : Fin n) {j : Fin n}
    (hji : j ≠ i) : (((tsub2 e i) : Fin n →₀ ℕ) j) = e j := by
  unfold tsub2
  simp [hji]

/-- Removing two units from coordinate `i` (which is legal when `2 ≤ e i`)
lowers the total weight by two. -/
private lemma wt_tsub2 {n : ℕ} (e : Fin n →₀ ℕ) (i : Fin n) (hi : 2 ≤ e i) :
    wt (tsub2 e i) = wt e - 2 := by
  unfold wt
  calc
    (∑ j : Fin n, (((tsub2 e i) : Fin n →₀ ℕ) j))
        = (∑ j ∈ (Finset.univ.erase i), (((tsub2 e i) : Fin n →₀ ℕ) j)) + (((tsub2 e i) : Fin n →₀ ℕ) i) := by
            exact (Finset.sum_erase_add (Finset.univ) (fun j : Fin n => (((tsub2 e i) : Fin n →₀ ℕ) j)) (Finset.mem_univ i)).symm
    _ = (∑ j ∈ (Finset.univ.erase i), e j) + (e i - 2) := by
            rw [tsub2_apply_self]
            apply congrArg (fun x => x + (e i - 2))
            apply Finset.sum_congr rfl
            intro j hj
            exact tsub2_apply_of_ne e i ((Finset.mem_erase.mp hj).1)
    _ = wt e - 2 := by
            have hs2 : (∑ j ∈ (Finset.univ.erase i), e j) + e i = wt e :=
              Finset.sum_erase_add (Finset.univ) (fun j : Fin n => e j) (Finset.mem_univ i)
            omega

/-- An odd exponent survives the removal of two units from coordinate `i`. -/
private lemma odd_tsub2 {n : ℕ} (e : Fin n →₀ ℕ) (i : Fin n) (hi : 2 ≤ e i)
    (hodd : ∃ j : Fin n, Odd (e j)) : ∃ j : Fin n, Odd (((tsub2 e i) : Fin n →₀ ℕ) j) := by
  rcases hodd with ⟨j, hj⟩
  by_cases hji : j = i
  · subst j
    refine ⟨i, ?_⟩
    rw [tsub2_apply_self]
    rcases hj with ⟨t, ht⟩
    refine ⟨t - 1, ?_⟩
    omega
  · refine ⟨j, ?_⟩
    rw [tsub2_apply_of_ne e i hji]
    exact hj

/-- The Laplacian as an `ℝ`-linear endomorphism of the polynomial ring. -/
private noncomputable def lapEnd (n : ℕ) : Module.End ℝ (P n) :=
  ∑ i : Fin n, ((pderiv (R := ℝ) i : P n →ₗ[ℝ] P n).comp (pderiv (R := ℝ) i : P n →ₗ[ℝ] P n))

private lemma lapEnd_apply (n : ℕ) (Q : P n) :
    lapEnd n Q = ∑ i : Fin n, pderiv i (pderiv i Q) := by
  simp [lapEnd]

/-- Applying the Laplacian to the monomial `x^e` removes two units from one
coordinate in all possible ways. -/
private lemma lap_monomial {n : ℕ} (e : Fin n →₀ ℕ) :
    lapEnd n (monomial e (1 : ℝ)) =
      ∑ i : Fin n, ((e i * (e i - 1) : ℕ) : ℝ) • monomial (tsub2 e i) (1 : ℝ) := by
  rw [lapEnd_apply]
  simp [smul_monomial, tsub2]

/-- The iterated Laplacian kills every monomial whose total degree is exactly
`2m` but which has an odd exponent.  (This is the stronger polynomial-identity
version of the requested statement; evaluating it at `0` is then trivial.) -/
private lemma end_pow_monomial_odd_zero (n : ℕ) : ∀ (m : ℕ) (e : Fin n →₀ ℕ),
    wt e = 2 * m → (∃ j : Fin n, Odd (e j)) → ((lapEnd n) ^ m) (monomial e (1 : ℝ)) = 0 := by
  intro m
  induction m with
  | zero =>
      intro e hw hodd
      have hw0 : wt e = 0 := by simpa using hw
      have hzero : ∀ j : Fin n, e j = 0 := by
        intro j
        have := (Finset.sum_eq_zero_iff_of_nonneg (s := (Finset.univ : Finset (Fin n))) (f := e)
          (fun i hi => Nat.zero_le _)).mp hw0
        exact this j (Finset.mem_univ j)
      exfalso
      rcases hodd with ⟨j, hj⟩
      have hzeroj : e j = 0 := hzero j
      simp [hzeroj] at hj
  | succ k ih =>
      intro e hw hodd
      calc
        ((lapEnd n) ^ (k + 1)) (monomial e (1 : ℝ))
            = ((lapEnd n) ^ k) ((lapEnd n) (monomial e (1 : ℝ))) := by
                rw [pow_succ]
                simp
        _ = ((lapEnd n) ^ k) (∑ i : Fin n,
              ((e i * (e i - 1) : ℕ) : ℝ) • monomial (tsub2 e i) (1 : ℝ)) := by
                rw [lap_monomial]
        _ = ∑ i : Fin n, ((e i * (e i - 1) : ℕ) : ℝ) •
              ((lapEnd n) ^ k) (monomial (tsub2 e i) (1 : ℝ)) := by
                simp [map_sum, map_smul]
        _ = ∑ i : Fin n, (0 : P n) := by
                apply Finset.sum_congr rfl
                intro i hi
                by_cases hbig : 2 ≤ e i
                · have hw' : wt (tsub2 e i) = 2 * k := by
                    have hwts := wt_tsub2 e i hbig
                    omega
                  have ho' : ∃ j : Fin n, Odd (((tsub2 e i) : Fin n →₀ ℕ) j) :=
                    odd_tsub2 e i hbig hodd
                  have hz := ih (tsub2 e i) hw' ho'
                  simp [hz]
                · have hle : e i ≤ 1 := by omega
                  have hc : ((e i * (e i - 1) : ℕ) : ℝ) = 0 := coeff_of_lt_two e i hle
                  simp [hc]
        _ = 0 := by simp

/-- If `e` has total weight `2m` and one of its exponents is odd, then `m`
iterations of the Laplacian, applied to the monomial `x^e` and evaluated at
zero, vanish. -/
theorem lapIter_monomial_eval_zero_of_odd
    {n : ℕ} {m : ℕ} (e : Fin n →₀ ℕ)
    (hw : (Finset.univ.sum (fun i : Fin n => e i)) = 2 * m)
    (hodd : ∃ i : Fin n, Odd (e i)) :
    MvPolynomial.eval (fun _ : Fin n => (0 : ℝ))
      ((fun Q : MvPolynomial (Fin n) ℝ =>
          Finset.univ.sum (fun i : Fin n => MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)))^[m]
        (MvPolynomial.monomial e (1 : ℝ))) = 0 := by
  classical
  have hfun : (fun Q : MvPolynomial (Fin n) ℝ =>
          Finset.univ.sum (fun i : Fin n => MvPolynomial.pderiv i (MvPolynomial.pderiv i Q)))
        = fun Q => lapEnd n Q := by
    funext Q
    exact (lapEnd_apply n Q).symm
  rw [hfun]
  rw [← Module.End.pow_apply (lapEnd n) m]
  have hzero := end_pow_monomial_odd_zero n m e hw hodd
  rw [hzero]
  simp

end Commons.Algebra.MvPolynomial