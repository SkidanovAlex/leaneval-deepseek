import Mathlib
import Submission.RS
import Submission.Sec3Defs
import Submission.Sec3H_defs
import Submission.Sec3_c_bridge

/-! Support expansion of the cosine polynomial `c(θ) = Re(z^T P_t(z) +
z^{2T} Q_t(z))`, `z = e^{2iθ}`, `T = 2^(t+10)` (paper arXiv:1907.09464v1 §3):

    c(θ) = Σ_{r < 2^t} a_r·cos(2·(T+r)·θ) + Σ_{r < 2^t} b_r·cos(2·(2T+r)·θ)

where `a_r := (coeff (P t) r).re ∈ {±1}`, `b_r := (coeff (Q t) r).re ∈ {±1}`.
The frequencies `2·(T+r)`, `2·(2T+r)` are EVEN, which gives the symmetries
`c(θ+π) = c(θ)`, `c(π−θ) = c(θ)`, `c(−θ) = c(θ)` (`cos` is even, and
`cos(k(π±θ)) = cos(kθ)` for even integers `k`), and periodicity
`c(θ + 2π) = c(θ)`.

Also the complex form `c(θ) = Re( Σ_{r<2^t} c_r·w^{T+r} + Σ_{r<2^t} d_r·w^{2T+r} )`
with `w = e^{2iθ}` (coefficients ±1), used for the root-count lemma. -/

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex

set_option autoImplicit false

namespace Submission
namespace Sec3

/-- `m_t := 2^(t+11) + 2^t − 1` (the paper's `γn` for the constructed n). -/
def m_t (t : ℕ) : ℕ := 2 ^ (t + 11) + 2 ^ t - 1

/-! ## Internal helpers (own namespace, to avoid collisions). -/

namespace CosExpandAux

/-- real part of `e^{ix}`. -/
lemma eθ_re (x : ℝ) : (eθ x).re = Real.cos x := by
  unfold eθ
  rw [Complex.exp_ofReal_mul_I]
  rw [Complex.add_re]
  rw [Complex.ofReal_re]
  have hmul : (↑(Real.sin x) * Complex.I).re = 0 := by
    rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [hmul]
  simp

/-- imag part of `e^{ix}`. -/
lemma eθ_im (x : ℝ) : (eθ x).im = Real.sin x := by
  unfold eθ
  rw [Complex.exp_ofReal_mul_I]
  rw [Complex.add_im]
  rw [Complex.ofReal_im]
  have hmul : (↑(Real.sin x) * Complex.I).im = Real.sin x := by
    rw [Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [hmul]
  simp

/-- real part of `zθ^n = e^{2inθ}`. -/
lemma re_zθ_pow (n : ℕ) (θ : ℝ) :
    ((zθ θ) ^ n).re = Real.cos (2 * (n : ℝ) * θ) := by
  unfold zθ
  rw [← Sec3BridgeAux.eθ_nat_mul n (2 * θ)]
  rw [eθ_re]
  congr 1
  ring

/-- coefficients of `P t` have zero imaginary part (they are ±1 below degree
`2^t`, and zero above). -/
lemma coeff_P_im (t r : ℕ) : ((RudinShapiro.P t).coeff r).im = 0 := by
  by_cases hr : r < 2 ^ t
  · rcases (RudinShapiro.P_coeff_mem t r hr) with h | h <;> rw [h] <;> norm_num
  · have hge : 2 ^ t ≤ r := le_of_not_gt hr
    rw [RudinShapiro.coeff_P_ge t r hge]
    norm_num

/-- coefficients of `Q t` have zero imaginary part. -/
lemma coeff_Q_im (t r : ℕ) : ((RudinShapiro.Q t).coeff r).im = 0 := by
  by_cases hr : r < 2 ^ t
  · rcases (RudinShapiro.Q_coeff_mem t r hr) with h | h <;> rw [h] <;> norm_num
  · have hge : 2 ^ t ≤ r := le_of_not_gt hr
    rw [RudinShapiro.coeff_Q_ge t r hge]
    norm_num

/-- real part of `a · zθ^n` when `a` has zero imaginary part. -/
lemma re_mul_zθ_pow (a : ℂ) (n : ℕ) (θ : ℝ) (ha : a.im = 0) :
    (a * (zθ θ) ^ n).re = a.re * Real.cos (2 * (n : ℝ) * θ) := by
  rw [Complex.mul_re]
  rw [ha]
  rw [re_zθ_pow n θ]
  ring

/-- `real part` is additive over finite sums. -/
lemma sum_re (s : Finset ℕ) (f : ℕ → ℂ) :
    ((∑ r ∈ s, f r).re) = ∑ r ∈ s, (f r).re := by
  exact (map_sum Complex.reAddGroupHom f s)

/-- `natDegree (P t) < 2^t`. -/
lemma P_natDegree_lt (t : ℕ) : (RudinShapiro.P t).natDegree < 2 ^ t := by
  have hle := RudinShapiro.P_natDegree_le t
  have h2 : 2 ^ t - 1 < 2 ^ t := by
    have hpos : 0 < 2 ^ t := RudinShapiro.two_pow_pos t
    omega
  omega

/-- `natDegree (Q t) < 2^t`. -/
lemma Q_natDegree_lt (t : ℕ) : (RudinShapiro.Q t).natDegree < 2 ^ t := by
  have hle := RudinShapiro.Q_natDegree_le t
  have h2 : 2 ^ t - 1 < 2 ^ t := by
    have hpos : 0 < 2 ^ t := RudinShapiro.two_pow_pos t
    omega
  omega

/-- Multiplying the evaluation of a degree-`< n` polynomial by `z^A` expands
to the sum over `r < n` of `coeff r · z^(A+r)`. -/
lemma zpow_mul_eval_eq_sum (p : ℂ[X]) (n A : ℕ) (z : ℂ) (hn : p.natDegree < n) :
    z ^ A * p.eval z = ∑ r ∈ Finset.range n, p.coeff r * z ^ (A + r) := by
  rw [Polynomial.eval_eq_sum_range' hn z]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  calc
    z ^ A * (p.coeff r * z ^ r) = p.coeff r * (z ^ A * z ^ r) := by ring
    _ = p.coeff r * z ^ (A + r) := by rw [pow_add]

/-- The complex combination `cval` expanded as two finite sums
(`w := zθ θ`, exponents `T+r` and `2T+r`, `T := Sec3H.T t`). -/
lemma cval_eq_sum (t : ℕ) (θ : ℝ) :
    cval t θ =
      (∑ r ∈ Finset.range (2 ^ t),
          (RudinShapiro.P t).coeff r * (zθ θ) ^ (Sec3H.T t + r)) +
      (∑ r ∈ Finset.range (2 ^ t),
          (RudinShapiro.Q t).coeff r * (zθ θ) ^ (2 * Sec3H.T t + r)) := by
  unfold cval Sec3H.T
  dsimp
  rw [zpow_mul_eval_eq_sum (p := RudinShapiro.P t) (n := 2 ^ t) (A := 2 ^ (t + 10))
      (z := zθ θ) (hn := P_natDegree_lt t)]
  rw [zpow_mul_eval_eq_sum (p := RudinShapiro.Q t) (n := 2 ^ t) (A := 2 * 2 ^ (t + 10))
      (z := zθ θ) (hn := Q_natDegree_lt t)]

/-- The real part of the first (`P`-)block is the cosine sum over
frequencies `T + r`. -/
lemma re_block_P (t : ℕ) (θ : ℝ) :
    ((∑ r ∈ Finset.range (2 ^ t),
        (RudinShapiro.P t).coeff r * (zθ θ) ^ (Sec3H.T t + r)).re) =
      ∑ r ∈ Finset.range (2 ^ t),
        ((RudinShapiro.P t).coeff r).re * Real.cos (2 * ((Sec3H.T t + r : ℕ) : ℝ) * θ) := by
  rw [sum_re]
  apply Finset.sum_congr rfl
  intro r hr
  exact re_mul_zθ_pow ((RudinShapiro.P t).coeff r) (Sec3H.T t + r) θ (coeff_P_im t r)

/-- The real part of the second (`Q`-)block is the cosine sum over
frequencies `2T + r`. -/
lemma re_block_Q (t : ℕ) (θ : ℝ) :
    ((∑ r ∈ Finset.range (2 ^ t),
        (RudinShapiro.Q t).coeff r * (zθ θ) ^ (2 * Sec3H.T t + r)).re) =
      ∑ r ∈ Finset.range (2 ^ t),
        ((RudinShapiro.Q t).coeff r).re * Real.cos (2 * ((2 * Sec3H.T t + r : ℕ) : ℝ) * θ) := by
  rw [sum_re]
  apply Finset.sum_congr rfl
  intro r hr
  exact re_mul_zθ_pow ((RudinShapiro.Q t).coeff r) (2 * Sec3H.T t + r) θ (coeff_Q_im t r)

end CosExpandAux

/-- Cosine expansion of `c` over the two Rudin-Shapiro blocks. -/
lemma c_eq_cos_sum (t : ℕ) (θ : ℝ) :
    c t θ =
      (∑ r ∈ Finset.range (2 ^ t),
          ((RudinShapiro.P t).coeff r).re * Real.cos (2 * ((Sec3H.T t + r : ℕ) : ℝ) * θ)) +
      (∑ r ∈ Finset.range (2 ^ t),
          ((RudinShapiro.Q t).coeff r).re * Real.cos (2 * ((2 * Sec3H.T t + r : ℕ) : ℝ) * θ)) := by
  unfold c
  rw [CosExpandAux.cval_eq_sum t θ]
  rw [Complex.add_re]
  rw [CosExpandAux.re_block_P t θ]
  rw [CosExpandAux.re_block_Q t θ]

/-- The cosine coefficients are ±1 (real parts of the RS coefficients),
for indices inside the degree range `r < 2^t`. -/
lemma coeff_cos_mem (t : ℕ) (r : ℕ) (hr : r < 2 ^ t) :
    ((RudinShapiro.P t).coeff r).re = 1 ∨ ((RudinShapiro.P t).coeff r).re = -1 := by
  rcases (RudinShapiro.P_coeff_mem t r hr) with h | h
  · left; rw [h]; norm_num
  · right; rw [h]; norm_num

lemma coeff_cosQ_mem (t : ℕ) (r : ℕ) (hr : r < 2 ^ t) :
    ((RudinShapiro.Q t).coeff r).re = 1 ∨ ((RudinShapiro.Q t).coeff r).re = -1 := by
  rcases (RudinShapiro.Q_coeff_mem t r hr) with h | h
  · left; rw [h]; norm_num
  · right; rw [h]; norm_num

/-- Complex form: `c(θ) = Re(Σ_r (P.coeff r)·w^(T+r) + Σ_r (Q.coeff r)·w^(2T+r))`
with `w = e^{2iθ}`. -/
lemma c_eq_re_complex_sum (t : ℕ) (θ : ℝ) :
    (Sec3.c t θ : ℂ) =
      ((∑ r ∈ Finset.range (2 ^ t),
          (RudinShapiro.P t).coeff r * (zθ θ) ^ (Sec3H.T t + r)) +
        (∑ r ∈ Finset.range (2 ^ t),
          (RudinShapiro.Q t).coeff r * (zθ θ) ^ (2 * Sec3H.T t + r))).re := by
  unfold c
  rw [CosExpandAux.cval_eq_sum t θ]

/-- Degree bound: all frequencies `k` appearing in the complex form of `c`
satisfy `k ≤ 2·m_t` (with `m_t := 2^(t+11)+2^t−1`, loose). -/
lemma freq_bound {t r k : ℕ} (hr : r < 2 ^ t) :
    k = Sec3H.T t + r ∨ k = 2 * Sec3H.T t + r → k ≤ 2 * m_t t := by
  intro h
  have hT1 : 2 ^ (t + 10) ≤ 2 ^ (t + 11) := by
    exact pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (by omega : t + 10 ≤ t + 11)
  have hrm : r ≤ 2 ^ t - 1 := by omega
  have hmt_nonneg : 0 ≤ 2 ^ (t + 11) + 2 ^ t - 1 := by
    have h1 : 1 ≤ 2 ^ t := RudinShapiro.two_pow_ge_one t
    omega
  rcases h with h | h
  · rw [h]
    unfold m_t Sec3H.T
    omega
  · rw [h]
    unfold m_t Sec3H.T
    omega

end Sec3
end Submission
