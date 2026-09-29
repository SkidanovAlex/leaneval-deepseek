import Mathlib
import Submission.Work.A14.defs

/-!
# A14D: the cleared polynomial chain of `∂_y^k` for the operator `L_Z`

`L_Z y = (P y')' + R y` with `P = z(1−z)(1−9z) = z − 10z² + 9z³` and `R = 9z − 3` is the
Zagier operator of the `x`-side design (`REFS/design/a14`).  The `y`-derivative is
`∂_y = (1/y') ∂_x`, `y = z²/(z−1)`, `y' = (z²−2z)/(z−1)²`, so that

  `∂_y f = ρ · f'`,   `ρ = rhos = (X−1)²/(X²−2X)`.

The class chain of `∂_y^k` in the `P`-branch module `ℚ(X)e₀ ⊕ ℚ(X)e₁` is `clsZ k`
(`Work.A14D.clsZ`), obtained from the derivation `dZ` of `Work.A14.defs`.  This file supplies the
*cleared* form of that chain: polynomials `D_k, A_k, B_k` over `ℚ` with

  `algebraMap A_k = algebraMap D_k * (clsZ k).1`,  `algebraMap B_k = algebraMap D_k * (clsZ k).2`

and, for any holomorphic solution `y9` of `L_Z` on a disc around `1/9`,

  `D_k z · (∂_y^k y9)(z) = A_k z · y9 z + B_k z · (∂y9)(z)`.

The recursion is the one obtained by clearing the denominators in
`(u,v) ↦ (ρ(u' − v·R/P), ρ(u + v' − v·P'/P))`; the denominator is `D_k = (P·W)^{2^k−1}` with
`W = X² − 2X`.
-/

namespace Work.A14D

open Polynomial Complex Metric
open scoped Topology

noncomputable section

/-! ## 0. The polynomial data of `L_Z` -/

/-- `P = X − 10X² + 9X³ = X(1−X)(1−9X)`, the `y''`-coefficient of `L_Z`, over `ℚ`.
(`Work.A14D.PZQ` is its image in `ℚ(X)`.) -/
def pZq : Polynomial ℚ := X - 10 * X ^ 2 + 9 * X ^ 3

/-- `P' = 1 − 20X + 27X²`. -/
def pZq' : Polynomial ℚ := 1 - 20 * X + 27 * X ^ 2

/-- `R = −3 + 9X`. -/
def rZq : Polynomial ℚ := -3 + 9 * X

/-- `X − 1`: the numerator of `rhos`. -/
def rXq : Polynomial ℚ := X - 1

/-- `X² − 2X = X(X−2)`: the denominator of `rhos` (and of `∂_y`). -/
def wXq : Polynomial ℚ := X ^ 2 - 2 * X

/-! ## 1. Evaluation of the polynomial data at a complex point -/

@[simp] lemma pZq_eval₂ (z : ℂ) : pZq.eval₂ (algebraMap ℚ ℂ) z = PZ z := by
  simp only [pZq, PZ, Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_ofNat]
  ring

@[simp] lemma pZq'_eval₂ (z : ℂ) : pZq'.eval₂ (algebraMap ℚ ℂ) z = PZ' z := by
  simp only [pZq', PZ', Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_one, Polynomial.eval₂_ofNat]

@[simp] lemma rZq_eval₂ (z : ℂ) : rZq.eval₂ (algebraMap ℚ ℂ) z = RZ z := by
  simp only [rZq, RZ, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_X, Polynomial.eval₂_ofNat, Polynomial.eval₂_neg]
  ring

@[simp] lemma rXq_eval₂ (z : ℂ) : rXq.eval₂ (algebraMap ℚ ℂ) z = z - 1 := by
  simp only [rXq, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_one]

@[simp] lemma wXq_eval₂ (z : ℂ) : wXq.eval₂ (algebraMap ℚ ℂ) z = z ^ 2 - 2 * z := by
  simp only [wXq, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_ofNat]

lemma pZq_ne_zero : pZq ≠ 0 := by
  intro h
  have h2 : pZq.eval 2 = 0 := by rw [h]; simp
  norm_num [pZq] at h2

lemma wXq_ne_zero : wXq ≠ 0 := by
  intro h
  have h2 : wXq.eval 3 = 0 := by rw [h]; simp
  norm_num [wXq] at h2

lemma rXq_ne_zero : rXq ≠ 0 := by
  intro h
  have h2 : rXq.eval 0 = 0 := by rw [h]; simp
  norm_num [rXq] at h2

/-! ## 2. The same data inside `ℚ(X)` -/

lemma PZQ_eq : PZQ = algebraMap (Polynomial ℚ) (RatFunc ℚ) pZq := by
  simp only [PZQ, pZq, xQ', map_sub, map_add, map_mul, map_pow, map_ofNat, RatFunc.algebraMap_X]

lemma PZQ'_eq : PZQ' = algebraMap (Polynomial ℚ) (RatFunc ℚ) pZq' := by
  simp only [PZQ', pZq', xQ', map_sub, map_add, map_mul, map_pow, map_one, map_ofNat,
    RatFunc.algebraMap_X]

lemma RZQ_eq : RZQ = algebraMap (Polynomial ℚ) (RatFunc ℚ) rZq := by
  simp only [RZQ, rZq, xQ', map_neg, map_add, map_mul, map_ofNat, RatFunc.algebraMap_X]

lemma rhos_eq : rhos = (algebraMap (Polynomial ℚ) (RatFunc ℚ) rXq) ^ 2
    / algebraMap (Polynomial ℚ) (RatFunc ℚ) wXq := by
  simp only [rhos, rXq, wXq, xQ', map_sub, map_add, map_mul, map_pow, map_ofNat, map_one,
    RatFunc.algebraMap_X]

/-! ## 3. The cleared chain -/

/-- One step of the cleared chain: `(D,A,B) ↦ (D²PW, ρ_num·[ ... ], ρ_num·[ ... ])`. -/
def chainStepZ (D A B : Polynomial ℚ) :
    Polynomial ℚ × Polynomial ℚ × Polynomial ℚ :=
  (D ^ 2 * pZq * wXq,
   rXq ^ 2 * (D * pZq * A.derivative - pZq * D.derivative * A - D * B * rZq),
   rXq ^ 2 * (D * pZq * (A + B.derivative) - D * B * pZq' - pZq * D.derivative * B))

/-- The cleared chain `(D_k, A_k, B_k)` of the class of `∂_y^k`. -/
def chainZ : ℕ → Polynomial ℚ × Polynomial ℚ × Polynomial ℚ
  | 0 => (1, 1, 0)
  | (k + 1) => chainStepZ (chainZ k).1 (chainZ k).2.1 (chainZ k).2.2

/-- The common denominator `D_k`. -/
def DZpoly (k : ℕ) : Polynomial ℚ := (chainZ k).1

/-- The `y9`-coefficient `A_k`. -/
def AZpoly (k : ℕ) : Polynomial ℚ := (chainZ k).2.1

/-- The `y9'`-coefficient `B_k`. -/
def BZpoly (k : ℕ) : Polynomial ℚ := (chainZ k).2.2

@[simp] lemma chainZ_zero : chainZ 0 = (1, 1, 0) := rfl

@[simp] lemma chainZ_succ (k : ℕ) :
    chainZ (k + 1) = chainStepZ (chainZ k).1 (chainZ k).2.1 (chainZ k).2.2 := rfl

@[simp] lemma DZpoly_zero : DZpoly 0 = 1 := rfl
@[simp] lemma AZpoly_zero : AZpoly 0 = 1 := rfl
@[simp] lemma BZpoly_zero : BZpoly 0 = 0 := rfl

@[simp] lemma DZpoly_succ (k : ℕ) : DZpoly (k + 1) = DZpoly k ^ 2 * pZq * wXq := rfl

@[simp] lemma AZpoly_succ (k : ℕ) :
    AZpoly (k + 1) = rXq ^ 2 * (DZpoly k * pZq * (AZpoly k).derivative
      - pZq * (DZpoly k).derivative * AZpoly k - DZpoly k * BZpoly k * rZq) := rfl

@[simp] lemma BZpoly_succ (k : ℕ) :
    BZpoly (k + 1) = rXq ^ 2 * (DZpoly k * pZq * (AZpoly k + (BZpoly k).derivative)
      - DZpoly k * BZpoly k * pZq' - pZq * (DZpoly k).derivative * BZpoly k) := rfl

/-- `D_k` is the `(P·W)`-power predicted by the recursion. -/
lemma DZpoly_eq (k : ℕ) : DZpoly k = (pZq * wXq) ^ (2 ^ k - 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [DZpoly_succ, ih, show 2 ^ (k + 1) - 1 = (2 ^ k - 1) * 2 + 1 from by
        have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        omega]
      ring

lemma DZpoly_ne_zero (k : ℕ) : DZpoly k ≠ 0 := by
  rw [DZpoly_eq]
  exact pow_ne_zero _ (mul_ne_zero pZq_ne_zero wXq_ne_zero)

/-- `D_k` does not vanish at a point where neither `P` nor `W = X²−2X` vanishes. -/
lemma DZpoly_eval₂_ne_zero (k : ℕ) {z : ℂ}
    (hp : pZq.eval₂ (algebraMap ℚ ℂ) z ≠ 0) (hw : wXq.eval₂ (algebraMap ℚ ℂ) z ≠ 0) :
    (DZpoly k).eval₂ (algebraMap ℚ ℂ) z ≠ 0 := by
  rw [DZpoly_eq, Polynomial.eval₂_pow, Polynomial.eval₂_mul]
  exact pow_ne_zero _ (mul_ne_zero hp hw)

/-! ## 4. Evaluated recursion, in the shape used by the analytic induction -/

lemma DZpoly_eval₂_succ (k : ℕ) (z : ℂ) :
    (DZpoly (k + 1)).eval₂ (algebraMap ℚ ℂ) z
      = (DZpoly k).eval₂ (algebraMap ℚ ℂ) z ^ 2 * (pZq).eval₂ (algebraMap ℚ ℂ) z
        * (z ^ 2 - 2 * z) := by
  rw [DZpoly_succ, Polynomial.eval₂_mul, Polynomial.eval₂_mul, Polynomial.eval₂_pow, wXq_eval₂]

lemma AZpoly_eval₂_succ (k : ℕ) (z : ℂ) :
    (AZpoly (k + 1)).eval₂ (algebraMap ℚ ℂ) z
      = (z - 1) ^ 2
        * ((DZpoly k).eval₂ (algebraMap ℚ ℂ) z * (pZq).eval₂ (algebraMap ℚ ℂ) z
            * (AZpoly k).derivative.eval₂ (algebraMap ℚ ℂ) z
          - (pZq).eval₂ (algebraMap ℚ ℂ) z * (DZpoly k).derivative.eval₂ (algebraMap ℚ ℂ) z
            * (AZpoly k).eval₂ (algebraMap ℚ ℂ) z
          - (DZpoly k).eval₂ (algebraMap ℚ ℂ) z * (BZpoly k).eval₂ (algebraMap ℚ ℂ) z
            * (rZq).eval₂ (algebraMap ℚ ℂ) z) := by
  simp only [AZpoly_succ, Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    rXq_eval₂]

lemma BZpoly_eval₂_succ (k : ℕ) (z : ℂ) :
    (BZpoly (k + 1)).eval₂ (algebraMap ℚ ℂ) z
      = (z - 1) ^ 2
        * ((DZpoly k).eval₂ (algebraMap ℚ ℂ) z * (pZq).eval₂ (algebraMap ℚ ℂ) z
            * ((AZpoly k).eval₂ (algebraMap ℚ ℂ) z
              + (BZpoly k).derivative.eval₂ (algebraMap ℚ ℂ) z)
          - (DZpoly k).eval₂ (algebraMap ℚ ℂ) z * (BZpoly k).eval₂ (algebraMap ℚ ℂ) z
            * (pZq').eval₂ (algebraMap ℚ ℂ) z
          - (pZq).eval₂ (algebraMap ℚ ℂ) z * (DZpoly k).derivative.eval₂ (algebraMap ℚ ℂ) z
            * (BZpoly k).eval₂ (algebraMap ℚ ℂ) z) := by
  simp only [BZpoly_succ, Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_add,
    Polynomial.eval₂_pow, rXq_eval₂]

/-! ## 5. The chain as the clearance of `dZ` -/

@[simp] lemma dZ_fst (uv : RatFunc ℚ × RatFunc ℚ) :
    (dZ uv).1 = rhos * (Submission.CDT.dRat uv.1 - uv.2 * RZQ / PZQ) := rfl

@[simp] lemma dZ_snd (uv : RatFunc ℚ × RatFunc ℚ) :
    (dZ uv).2 = rhos * (uv.1 + Submission.CDT.dRat uv.2 - uv.2 * PZQ' / PZQ) := rfl

@[simp] lemma clsZ_eq (k : Fin 4) : clsZ k = (dZ^[(k : ℕ)]) (1, 0) := rfl

@[simp] lemma dyC_eq (z : ℂ) : dyC z = (z ^ 2 - 2 * z) / (z - 1) ^ 2 := rfl

/-! ## 6. Geometry of `ball ninth δ` for `δ ≤ 1/20`

All the points at which the polynomial data of the chain can degenerate are outside the disc. -/

lemma ninth_norm : ‖ninth‖ = 1 / 9 := by
  simp [ninth]

lemma norm_one_sub_ninth : ‖(1 : ℂ) - ninth‖ = 8 / 9 := by
  rw [show (1 : ℂ) - ninth = ((8 / 9 : ℝ) : ℂ) by simp [ninth]; norm_num]
  simp

lemma norm_two_sub_ninth : ‖(2 : ℂ) - ninth‖ = 17 / 9 := by
  rw [show (2 : ℂ) - ninth = ((17 / 9 : ℝ) : ℂ) by simp [ninth]; norm_num]
  simp

lemma ne_zero_of_mem_ball_ninth {z : ℂ} {δ : ℝ} (hδ : δ ≤ 1 / 20)
    (hz : z ∈ ball ninth δ) : z ≠ 0 := by
  intro h
  subst h
  rw [Metric.mem_ball, Complex.dist_eq, zero_sub, norm_neg, ninth_norm] at hz
  linarith

lemma ne_one_of_mem_ball_ninth {z : ℂ} {δ : ℝ} (hδ : δ ≤ 1 / 20)
    (hz : z ∈ ball ninth δ) : z ≠ 1 := by
  intro h
  subst h
  rw [Metric.mem_ball, Complex.dist_eq, norm_one_sub_ninth] at hz
  linarith

lemma ne_two_of_mem_ball_ninth {z : ℂ} {δ : ℝ} (hδ : δ ≤ 1 / 20)
    (hz : z ∈ ball ninth δ) : z ≠ 2 := by
  intro h
  subst h
  rw [Metric.mem_ball, Complex.dist_eq, norm_two_sub_ninth] at hz
  linarith

lemma sq_sub_two_ne_zero_of_mem_ball_ninth {z : ℂ} {δ : ℝ} (hδ : δ ≤ 1 / 20)
    (hz : z ∈ ball ninth δ) : z ^ 2 - 2 * z ≠ 0 := by
  intro h
  have h' : z * (z - 2) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h' with h0 | h2
  · exact ne_zero_of_mem_ball_ninth hδ hz h0
  · exact ne_two_of_mem_ball_ninth hδ hz (sub_eq_zero.mp h2)

lemma PZ_ne_zero_of_mem_ball_ninth {z : ℂ} {δ : ℝ} (hδ : δ ≤ 1 / 20)
    (hz : z ∈ ball ninth δ) (hz9 : z ≠ ninth) : PZ z ≠ 0 := by
  intro h
  rw [PZ] at h
  have hfac : z * (1 - z) * (1 - 9 * z) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hfac with h1 | h3
  · rcases mul_eq_zero.mp h1 with h0 | h1'
    · exact ne_zero_of_mem_ball_ninth hδ hz h0
    · exact ne_one_of_mem_ball_ninth hδ hz (by linear_combination (-1 : ℂ) * h1')
  · have hz9' : z - ninth = 0 := by
      rw [ninth]; linear_combination (-(1 / 9)) * h3
    exact hz9 (sub_eq_zero.mp hz9')

end

end Work.A14D
