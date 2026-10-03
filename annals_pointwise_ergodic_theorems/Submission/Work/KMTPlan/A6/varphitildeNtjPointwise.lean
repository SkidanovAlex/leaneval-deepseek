/-
# Pointwise bound of the modified `g`-side bump `φ̃_{N,k,j}` and its non-vanishing transfer

The modified `g`-side bump of §6/§8 (KMT (tpntj)) is

  `φ̃_{N,k,j}(t)(ξ) = (2^{-dk} N^d ξ)^j φ̃_{N,k}(t)(ξ)`,  `d = P.natDegree`,

the product of the (modulated) bump `φ̃_{N,k}(t)` with a power of the frequency variable.  Two
elementary facts about it are used by the §8 large-scale estimate:

* for the twists `j ∈ {-1,0,1}` actually occurring, and outside the paper's forbidden pair
  `(k,j) = (0,-1)` where the weight `(2^{-dk}N^dξ)^{-1}` is singular at the origin, the modified
  bump is *uniformly bounded* by a constant `Cb` depending only on `P`, for every `N ≥ 1`, every
  `t`, and every `ξ`;
* a nonzero value of the modified bump forces the *unmodified* bump `φ̃_{N,k}(t)` to be nonzero at
  the same point (the weight is a factor).

Both are immediate from the factorisation once one knows that `‖φ̃_{N,k}(t)‖ ≤ 1` and the
two-sided support of `φ̃_N`: a nonzero value of `φ̃_N(ξ)` forces
`2^{d(Log N - k)}|ξ| ≤ 1`, and, when `k ≥ 1`, even `2^{-(d+1)} < 2^{d(Log N - k)}|ξ|`.  Since
`2^{Log N} ≤ 2N` (with `Log N = ⌊log₂ N⌋` the *floored* logarithm), the weight
`2^{-dk}N^d ξ` is at most `2^d · 2^{d(Log N-k)}|ξ| ≤ 2^d` for `j ≥ 0`, and at least
`2^{-(2d+1)}` in modulus for `j = -1`.  Hence the uniform bound `Cb = 2^{2d+1}`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.lowModRandL2Gh

namespace Work.KMTPlan.A6

/-- **The pointwise bound of the modified `g`-side bump `φ̃_{N,k,j}` and the transfer of
non-vanishing to the unmodified bump `φ̃_{N,k}`.**

For every polynomial `P` of degree `≥ 2` there is a constant `Cb > 0` — namely `2^{2d+1}` with
`d = P.natDegree` — such that for every `N ≥ 1`, every heights `k`, every twist `j ∈ {-1,0,1}`
different from the forbidden pair `(k,j) = (0,-1)`, every `t` and every frequency `ξ`,

  `‖φ̃_{N,k,j}(t)(ξ)‖ ≤ Cb`,

and moreover `φ̃_{N,k,j}(t)(ξ) ≠ 0` implies `φ̃_{N,k}(t)(ξ) ≠ 0`. -/
theorem varphitildeNtjPointwise (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) :
    (∃ Cb : ℝ, 0 < Cb ∧ ∀ (N k : ℕ) (j : ℤ) (t : ℝ),
        j ∈ ({-1, 0, 1} : Finset ℤ) → ¬ (k = 0 ∧ j = -1) → 1 ≤ N →
        ∀ ξ : ℝ, ‖Work.KMTPlan.A6.varphitildeNtj P N k j t ξ‖ ≤ Cb) ∧
      (∀ (N k : ℕ) (j : ℤ) (t ξ : ℝ),
        Work.KMTPlan.A6.varphitildeNtj P N k j t ξ ≠ 0 →
        Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t ξ ≠ 0) := by
  have hd1 : 1 ≤ P.natDegree := by omega
  refine ⟨⟨(2 : ℝ) ^ (2 * P.natDegree + 1), by positivity, ?_⟩, ?_⟩
  · -- the uniform bound, from the pointwise bound proved in `lowModRandL2Gh`
    intro N k j t hj hkj hN ξ
    have h : k ≠ 0 ∨ 0 ≤ j := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨hk0, hjneg⟩ := hcon
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with h1 | h1 | h1
      · exact hkj ⟨hk0, h1⟩
      · omega
      · omega
    exact varphitildeNtj_pointwise P hd1 N k j t ξ hN hj h
  · -- the transfer of non-vanishing, from the factorisation of the modified bump
    intro N k j t ξ h h0
    refine h ?_
    rw [varphitildeNtj_eq_gWeight_mul P N k j t ξ, h0, mul_zero]

end Work.KMTPlan.A6
