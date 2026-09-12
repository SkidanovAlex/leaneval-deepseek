import Mathlib

/-!
# Complex Chebyshev growth at Joukowski points

Theorem `Submission.ChebGrowth.cheb_growth`: a degree-≤-`n` complex polynomial
`P` bounded by `M` on the real segment `[-1,1]` is bounded by `M · ‖ζ‖^n`
at the complex point `(ζ + ζ⁻¹)/2`, whenever `1 ≤ ‖ζ‖`.

The proof uses the standard companion-polynomial argument.

Let `a_k := P.coeff k` and set

    F(X) := ∑ k ∈ range (n+1),  C (a k / 2^k) · (X² + 1)^k · X^(n-k).

For `ζ ≠ 0` we prove the key identity `F.eval ζ = ζ^n · P.eval ((ζ+ζ⁻¹)/2)`
(`chebF_eval`).  On the unit circle `(ζ + ζ⁻¹)/2 = ζ.re ∈ [-1,1]`, hence
`‖F.eval ζ‖ ≤ M` there (`unit_circle`); by the maximum modulus principle the
same bound holds on the closed unit disk (`disk_bound`).  Finally, for
`1 ≤ ‖ζ‖`, writing `ξ = ζ⁻¹` (so `‖ξ‖ ≤ 1`), the identity at `ξ` gives
`P.eval ((ζ+ζ⁻¹)/2) = ζ^n · F.eval ξ` (`main_aux`), whose norm is at most
`‖ζ‖^n · M`.
-/

noncomputable section

open scoped Polynomial Real BigOperators ComplexConjugate

namespace Submission.ChebGrowth

open Polynomial Metric

/-- The companion polynomial `F` of `P` (of degree `≤ 2n`):
`F(X) = ∑ k < n+1, (P.coeff k / 2^k) (X² + 1)^k X^(n-k)`.

For `ζ ≠ 0` it satisfies `F.eval ζ = ζ^n · P.eval ((ζ + ζ⁻¹) / 2)`
(see `chebF_eval`). -/
def chebF (n : ℕ) (P : ℂ[X]) : ℂ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    Polynomial.C ((P.coeff k) / (2 : ℂ) ^ k) * (X ^ 2 + 1) ^ k * X ^ (n - k)

/-- Expansion of `F.eval ζ` as the corresponding scalar sum. -/
lemma chebF_eval_term (n : ℕ) (P : ℂ[X]) (ζ : ℂ) :
    (chebF n P).eval ζ =
      ∑ k ∈ Finset.range (n + 1), ((P.coeff k) / (2 : ℂ) ^ k) * (ζ^2+1)^k * ζ^(n-k) := by
  calc
    (chebF n P).eval ζ
        = (Finset.range (n+1)).sum
            (fun k => (Polynomial.C ((P.coeff k) / (2 : ℂ) ^ k) * (X ^ 2 + 1) ^ k
              * X ^ (n - k)).eval ζ) := by
          rw [chebF]
          exact map_sum (Polynomial.evalRingHom ζ)
            (fun k => Polynomial.C ((P.coeff k) / (2:ℂ)^k) * (X^2+1)^k * X^(n-k))
            (Finset.range (n+1))
    _ = ∑ k ∈ Finset.range (n + 1), ((P.coeff k) / (2 : ℂ) ^ k) * (ζ^2+1)^k * ζ^(n-k) := by
          apply Finset.sum_congr rfl
          intro k hk
          simp

/-- Termwise algebraic identity used inside `chebF_eval`. -/
lemma term_identity (a : ℂ) (ζ : ℂ) (hζ : ζ ≠ 0) (k n : ℕ) (hk : k ≤ n) :
    (a / (2:ℂ)^k) * (ζ^2+1)^k * ζ^(n-k) = ζ^n * (a * (((ζ + ζ⁻¹) / 2)^k)) := by
  have hy : (ζ + ζ⁻¹) / 2 = (ζ^2 + 1) / (2 * ζ) := by
    field_simp [hζ]
  have hk' : k + (n - k) = n := by omega
  have hpow : ζ^k * ζ^(n-k) = ζ^n := by
    rw [← pow_add, hk']
  rw [hy]
  rw [div_pow, mul_pow]
  field_simp [hζ]
  ring_nf
  calc
    a * ζ ^ k * ζ ^ (n - k) * (1 + ζ ^ 2) ^ k
        = a * (ζ ^ k * ζ ^ (n - k)) * (1 + ζ ^ 2) ^ k := by ring
    _ = a * ζ ^ n * (1 + ζ ^ 2) ^ k := by rw [hpow]
    _ = a * ζ ^ n * (1 + ζ ^ 2) ^ k := by ring

/-- Companion identity: for `ζ ≠ 0`,
`F.eval ζ = ζ^n · P.eval ((ζ + ζ⁻¹) / 2)` whenever `P.natDegree ≤ n`. -/
lemma chebF_eval (n : ℕ) (P : ℂ[X]) (ζ : ℂ) (hζ : ζ ≠ 0) (hdeg : P.natDegree ≤ n) :
    (chebF n P).eval ζ = ζ ^ n * P.eval ((ζ + ζ⁻¹) / 2) := by
  let y : ℂ := (ζ + ζ⁻¹) / 2
  calc
    (chebF n P).eval ζ
        = ∑ k ∈ Finset.range (n + 1), ((P.coeff k) / (2 : ℂ) ^ k) * (ζ^2+1)^k * ζ^(n-k) := by
            exact chebF_eval_term n P ζ
    _ = ∑ k ∈ Finset.range (n + 1), ζ^n * (P.coeff k * y^k) := by
            apply Finset.sum_congr rfl
            intro k hk
            have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
            rw [term_identity (P.coeff k) ζ hζ k n hkn]
    _ = ζ^n * (∑ k ∈ Finset.range (n + 1), P.coeff k * y^k) := by
            rw [← Finset.mul_sum]
    _ = ζ^n * P.eval y := by
            congr 1
            rw [Polynomial.eval_eq_sum_range' (n := n + 1) (Nat.lt_succ_of_le hdeg)]

/-- On the unit circle `F` is bounded by `M`. -/
lemma unit_circle (n : ℕ) (P : ℂ[X]) (hdeg : P.natDegree ≤ n) {M : ℝ}
    (hP : ∀ t : ℝ, t ∈ Set.Icc (-1 : ℝ) 1 → ‖P.eval (t : ℂ)‖ ≤ M) :
    ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖(chebF n P).eval ζ‖ ≤ M := by
  intro ζ hnorm
  have hζ0 : ζ ≠ 0 := by
    intro hz
    rw [hz] at hnorm
    norm_num at hnorm
  have hinv : ζ⁻¹ = conj ζ := Complex.inv_eq_conj hnorm
  have hy : ((ζ + ζ⁻¹) / 2) = (ζ.re : ℂ) := by
    rw [hinv]
    rw [← Complex.re_eq_add_conj ζ]
  have hmem : ζ.re ∈ Set.Icc (-1 : ℝ) 1 := by
    have hle : |ζ.re| ≤ 1 := by
      simpa [hnorm] using Complex.abs_re_le_norm ζ
    exact (abs_le.mp hle)
  calc
    ‖(chebF n P).eval ζ‖ = ‖ζ^n * P.eval ((ζ + ζ⁻¹) / 2)‖ := by
        rw [chebF_eval n P ζ hζ0 hdeg]
    _ = ‖ζ^n‖ * ‖P.eval ((ζ + ζ⁻¹) / 2)‖ := by rw [norm_mul]
    _ = ‖P.eval ((ζ + ζ⁻¹) / 2)‖ := by simp [hnorm]
    _ = ‖P.eval ((ζ.re : ℂ))‖ := by rw [hy]
    _ ≤ M := hP ζ.re hmem

/-- Maximum modulus on the closed unit disk: `F` is bounded by `M` on
`closedBall 0 1`, because it is bounded by `M` on the unit circle. -/
lemma disk_bound (n : ℕ) (P : ℂ[X]) (hdeg : P.natDegree ≤ n) {M : ℝ}
    (hP : ∀ t : ℝ, t ∈ Set.Icc (-1 : ℝ) 1 → ‖P.eval (t : ℂ)‖ ≤ M) :
    ∀ ξ : ℂ, ‖ξ‖ ≤ 1 → ‖(chebF n P).eval ξ‖ ≤ M := by
  intro ξ hξ
  have hd : DiffContOnCl ℂ (fun z : ℂ => (chebF n P).eval z) (Metric.ball (0 : ℂ) 1) := by
    refine DifferentiableOn.diffContOnCl_ball (U := (Set.univ : Set ℂ)) ?_ ?_
    · exact (chebF n P).differentiableOn
    · intro x hx
      trivial
  refine Complex.norm_le_of_forall_mem_frontier_norm_le
    (f := fun z : ℂ => (chebF n P).eval z) (U := Metric.ball (0 : ℂ) 1) (C := M)
    Metric.isBounded_ball hd ?_ ?_
  · intro z hz
    exact unit_circle n P hdeg hP z (by
      have hn := (mem_sphere_iff_norm).mp (Metric.frontier_ball_subset_sphere hz)
      simpa using hn)
  · have hξc : ξ ∈ Metric.closedBall (0 : ℂ) 1 := by
      rw [Metric.mem_closedBall]
      simpa using hξ
    rwa [closure_ball (0 : ℂ) one_ne_zero]

/-- Inversion identity: for `ζ ≠ 0` and `P.natDegree ≤ n`,
`ζ^n · F.eval (ζ⁻¹) = P.eval ((ζ + ζ⁻¹) / 2)`. -/
lemma main_aux (n : ℕ) (P : ℂ[X]) (hdeg : P.natDegree ≤ n) (ζ : ℂ) (hζ : ζ ≠ 0) :
    ζ ^ n * (chebF n P).eval (ζ⁻¹) = P.eval ((ζ + ζ⁻¹) / 2) := by
  rw [chebF_eval n P (ζ⁻¹) (inv_ne_zero hζ) hdeg]
  have hpow : ζ^n * (ζ⁻¹)^n = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hζ]
    simp
  rw [← mul_assoc, hpow]
  simp
  congr 1
  rw [add_comm]

/-- **Chebyshev growth at Joukowski points.**  A degree-≤-n polynomial
bounded by `M` on the real segment `[-1,1]` is bounded by `M·‖ζ‖^n` at
the complex point `(ζ+ζ⁻¹)/2`, whenever `1 ≤ ‖ζ‖`. -/
theorem cheb_growth {n : ℕ} {P : ℂ[X]} (hdeg : P.natDegree ≤ n)
    {M : ℝ} (hM : 0 ≤ M)
    (hP : ∀ t : ℝ, t ∈ Set.Icc (-1 : ℝ) 1 → ‖P.eval (t : ℂ)‖ ≤ M) :
    ∀ ζ : ℂ, 1 ≤ ‖ζ‖ → ‖P.eval ((ζ + ζ⁻¹) / 2)‖ ≤ M * ‖ζ‖ ^ n := by
  intro ζ hz1
  by_cases hζ0 : ζ = 0
  · exfalso
    rw [hζ0] at hz1
    norm_num at hz1
  · have hξ : ‖ζ⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact (inv_le_one₀ (lt_of_lt_of_le zero_lt_one hz1)).2 hz1
    have hFb : ‖(chebF n P).eval (ζ⁻¹)‖ ≤ M := disk_bound n P hdeg hP (ζ⁻¹) hξ
    calc
      ‖P.eval ((ζ + ζ⁻¹) / 2)‖ = ‖ζ^n * (chebF n P).eval (ζ⁻¹)‖ := by
          rw [← main_aux n P hdeg ζ hζ0]
      _ = ‖ζ^n‖ * ‖(chebF n P).eval (ζ⁻¹)‖ := by rw [norm_mul]
      _ = ‖ζ‖^n * ‖(chebF n P).eval (ζ⁻¹)‖ := by rw [norm_pow]
      _ ≤ ‖ζ‖^n * M := by
          exact mul_le_mul_of_nonneg_left hFb (pow_nonneg (norm_nonneg ζ) n)
      _ = M * ‖ζ‖ ^ n := by ring

end Submission.ChebGrowth

end
