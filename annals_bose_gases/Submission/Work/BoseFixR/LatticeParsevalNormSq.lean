import Mathlib.Analysis.Complex.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixR

/-- The squared norm of a finite sum of complex numbers, written as the real part
of the double sum `∑_{k,k'} A k * conj (A k')`.

Indeed `∑_{k,k'} A k * conj (A k') = (∑_k A k) * conj (∑_k A k) = ‖∑_k A k‖²`. -/
theorem LatticeParsevalNormSq {ι : Type*} [Fintype ι] [DecidableEq ι] (K : Finset ι)
    (A : ι → ℂ) :
    ‖∑ k ∈ K, A k‖ ^ 2 = (∑ k ∈ K, ∑ k' ∈ K, A k * star (A k')).re := by
  have hsum : (∑ k ∈ K, ∑ k' ∈ K, A k * star (A k'))
      = (∑ k ∈ K, A k) * star (∑ k ∈ K, A k) := by
    rw [show star (∑ k ∈ K, A k) = ∑ k ∈ K, star (A k) from by simp,
      ← Finset.sum_mul_sum]
  rw [hsum]
  show ‖∑ k ∈ K, A k‖ ^ 2 = ((∑ k ∈ K, A k) * (starRingEnd ℂ) (∑ k ∈ K, A k)).re
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

end Work.BoseFixR
