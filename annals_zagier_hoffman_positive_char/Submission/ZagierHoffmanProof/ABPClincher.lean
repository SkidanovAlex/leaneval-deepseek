import Submission.ZagierHoffmanProof.ABPGauss
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# The Liouville (clincher) inequality for roots of integral polynomials

This is ABP's `Lemma:Clincher` in the case `[K₀ : k] = 1` (the case relevant for the
Zagier–Hoffman application, where the base field is `k = F_q(θ)` itself).

If `f ∈ K[z]` is a nonzero polynomial all of whose **nonzero** coefficients are integral
(`1 ≤ v a`) and bounded by `A` (`v a ≤ A`), and `lam ≠ 0` is a root of `f`, then

  `1 ≤ A * v lam`,   i.e.  `|lam| ≥ 1/A`.

Proof: let `n` be the order of vanishing of `f` at `0` and write the relation `f(lam) = 0` as

  `aₙ lamⁿ = - ∑_{i ≠ n} aᵢ lamⁱ`.

If `|lam| < 1`, all terms on the right have `v = v(aᵢ) v(lam)ⁱ ≤ A v(lam)^{n+1}`, while the left-hand
side is `≥ v(lam)ⁿ`; cancelling the nonzero factor `v(lam)ⁿ` gives `1 ≤ A v lam`.  (If `|lam| ≥ 1` the
statement is trivial since `A ≥ 1`.)  No `q`-th roots are involved: the lemma is stated for an
arbitrary polynomial.
-/

set_option autoImplicit false
open Polynomial
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

/-- ★★★ **The Liouville/clincher inequality**: a nonzero root of a polynomial whose nonzero
coefficients are integral and bounded by `A` satisfies `1 ≤ A * v lam`. -/
theorem clincher {f : Polynomial K} {A : Γ₀} (hf : f ≠ 0)
    (hint : ∀ i, f.coeff i ≠ 0 → 1 ≤ Valued.v (f.coeff i))
    (hbound : ∀ i, Valued.v (f.coeff i) ≤ A)
    {lam : K} (hlam0 : lam ≠ 0) (hroot : f.eval lam = 0) :
    1 ≤ A * Valued.v lam := by
  have hlamne : Valued.v lam ≠ 0 := (Valuation.ne_zero_iff Valued.v).mpr hlam0
  have hex : ∃ j, f.coeff j ≠ 0 := by
    by_contra h
    refine hf (Polynomial.ext fun n => ?_)
    exact not_not.mp (not_exists.mp h n)
  have hA1 : 1 ≤ A := by
    obtain ⟨j, hj⟩ := hex
    exact le_trans (hint j hj) (hbound j)
  rcases lt_or_ge (Valued.v lam) 1 with hlt | hge
  · set n := f.natTrailingDegree with hn
    have hcn : f.coeff n ≠ 0 := Polynomial.coeff_natTrailingDegree_ne_zero.mpr hf
    have hltn : n ≤ f.natDegree := Polynomial.natTrailingDegree_le_natDegree f
    have hmem : n ∈ Finset.range (f.natDegree + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le hltn)
    have hsum : ∑ i ∈ Finset.range (f.natDegree + 1), f.coeff i * lam ^ i = 0 := by
      rw [← Polynomial.eval_eq_sum_range lam]; exact hroot
    have hsplit : f.coeff n * lam ^ n
        = - ∑ i ∈ (Finset.range (f.natDegree + 1)).erase n, f.coeff i * lam ^ i := by
      have h := Finset.sum_erase_add (Finset.range (f.natDegree + 1))
        (fun i => f.coeff i * lam ^ i) hmem
      rw [hsum] at h
      exact eq_neg_of_add_eq_zero_right h
    have hbdd : Valued.v (f.coeff n * lam ^ n) ≤ A * (Valued.v lam) ^ (n + 1) := by
      rw [hsplit, Valuation.map_neg]
      refine Valuation.map_sum_le Valued.v (fun i hi => ?_)
      rw [Valuation.map_mul, Valuation.map_pow]
      rcases lt_trichotomy i n with hlt' | heq | hgt'
      · rw [Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hlt', map_zero (Valued.v), zero_mul]
        exact zero_le
      · exact absurd heq (Finset.mem_erase.mp hi).1
      · have hi1 : n + 1 ≤ i := by omega
        calc Valued.v (f.coeff i) * (Valued.v lam) ^ i
            ≤ A * (Valued.v lam) ^ i := mul_le_mul_left (hbound i) _
          _ ≤ A * (Valued.v lam) ^ (n + 1) :=
              mul_le_mul_right (pow_le_pow_of_le_one zero_le hlt.le hi1) A
    have h1 : (Valued.v lam) ^ n ≤ Valued.v (f.coeff n * lam ^ n) := by
      rw [Valuation.map_mul, Valuation.map_pow]
      simpa using mul_le_mul_left (hint n hcn) ((Valued.v lam) ^ n)
    have h2 : (Valued.v lam) ^ n ≤ A * (Valued.v lam) ^ n * Valued.v lam := by
      calc (Valued.v lam) ^ n ≤ Valued.v (f.coeff n * lam ^ n) := h1
        _ ≤ A * (Valued.v lam) ^ (n + 1) := hbdd
        _ = A * (Valued.v lam) ^ n * Valued.v lam := by
            rw [pow_succ, mul_assoc]
    have hne : (Valued.v lam) ^ n ≠ 0 := pow_ne_zero n hlamne
    have h3 : (1 : Γ₀) ≤ A * (Valued.v lam) ^ n * Valued.v lam * ((Valued.v lam) ^ n)⁻¹ := by
      calc (1 : Γ₀) = (Valued.v lam) ^ n * ((Valued.v lam) ^ n)⁻¹ := (mul_inv_cancel₀ hne).symm
        _ ≤ A * (Valued.v lam) ^ n * Valued.v lam * ((Valued.v lam) ^ n)⁻¹ :=
            mul_le_mul_left h2 _
    have hsimp : A * (Valued.v lam) ^ n * Valued.v lam * ((Valued.v lam) ^ n)⁻¹
        = A * Valued.v lam := by
      rw [mul_assoc (A * (Valued.v lam) ^ n), mul_mul_mul_comm, mul_inv_cancel₀ hne, mul_one]
    rwa [hsimp] at h3
  · exact le_trans hA1 (le_mul_of_one_le_right zero_le hge)

end ZagierHoffmanPositiveChar
