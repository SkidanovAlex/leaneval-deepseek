import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.BigOperators

namespace Commons.Analysis.Walsh

open Finset BigOperators

noncomputable section

/-- Parseval/orthogonality identity for a family `χ` of real-valued complex functions on
`(ZMod 2)^ι` that is orthogonal with squared "norm" `2 ^ Fintype.card ι`: the squared norm
of a linear combination `∑ k, a k * χ k x` summed over all `x` equals `2 ^ card ι` times
`∑ k, ‖a k‖ ^ 2`. -/
theorem sum_normSq_orthogonal_chi {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (χ : κ → (ι → ZMod 2) → ℂ) (a : κ → ℂ)
    (hconj : ∀ k x, (starRingEnd ℂ) (χ k x) = χ k x)
    (horth : ∀ k l, (∑ x : ι → ZMod 2, χ k x * χ l x)
      = if k = l then (2 : ℂ) ^ Fintype.card ι else 0) :
    (∑ x : ι → ZMod 2, ‖∑ k, a k * χ k x‖ ^ 2)
      = (2 : ℝ) ^ Fintype.card ι * ∑ k, ‖a k‖ ^ 2 := by
  classical
  have hsq : ∀ z : ℂ, (Complex.normSq z : ℂ) = z * (starRingEnd ℂ) z :=
    fun z => (Complex.mul_conj z).symm
  have hcomplex :
      (∑ x : ι → ZMod 2, (Complex.normSq (∑ k, a k * χ k x) : ℂ))
        = (2 : ℂ) ^ Fintype.card ι * ∑ k, (Complex.normSq (a k) : ℂ) := by
    have hstar : ∀ x : ι → ZMod 2,
        (starRingEnd ℂ) (∑ k, a k * χ k x)
          = ∑ l, (starRingEnd ℂ) (a l) * χ l x := by
      intro x
      rw [map_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [map_mul, hconj l x]
    have hexpand : ∀ x : ι → ZMod 2,
        (∑ k, a k * χ k x) * (starRingEnd ℂ) (∑ k, a k * χ k x)
          = ∑ k, ∑ l, a k * (starRingEnd ℂ) (a l) * (χ k x * χ l x) := by
      intro x
      rw [hstar x, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    rw [Finset.sum_congr rfl (fun x _ => hsq _),
        Finset.sum_congr rfl (fun k _ => hsq _)]
    rw [Finset.sum_congr rfl (fun x _ => hexpand x)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun k _ => Finset.sum_comm)]
    simp_rw [← Finset.mul_sum]
    simp only [horth]
    have hinner : ∀ k,
        (∑ l, a k * (starRingEnd ℂ) (a l) * (if k = l then (2 : ℂ) ^ Fintype.card ι else 0))
          = a k * (starRingEnd ℂ) (a k) * (2 : ℂ) ^ Fintype.card ι := by
      intro k
      rw [Finset.sum_eq_single k]
      · rw [if_pos rfl]
      · intro l _ hlk
        rw [if_neg (Ne.symm hlk), mul_zero]
      · intro hk; exact absurd (Finset.mem_univ k) hk
    rw [Finset.sum_congr rfl (fun k _ => hinner k), ← Finset.sum_mul, mul_comm]
  have hreal : (∑ x : ι → ZMod 2, Complex.normSq (∑ k, a k * χ k x))
      = (2 : ℝ) ^ Fintype.card ι * ∑ k, Complex.normSq (a k) := by
    apply Complex.ofReal_inj.mp
    rw [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sum,
      Complex.ofReal_ofNat]
    simpa using hcomplex
  calc (∑ x : ι → ZMod 2, ‖∑ k, a k * χ k x‖ ^ 2)
      = ∑ x : ι → ZMod 2, Complex.normSq (∑ k, a k * χ k x) :=
        Finset.sum_congr rfl fun x _ => (Complex.normSq_eq_norm_sq _).symm
    _ = (2 : ℝ) ^ Fintype.card ι * ∑ k, Complex.normSq (a k) := hreal
    _ = (2 : ℝ) ^ Fintype.card ι * ∑ k, ‖a k‖ ^ 2 := by
        congr 1
        exact Finset.sum_congr rfl fun k _ => Complex.normSq_eq_norm_sq (a k)

end

end Commons.Analysis.Walsh