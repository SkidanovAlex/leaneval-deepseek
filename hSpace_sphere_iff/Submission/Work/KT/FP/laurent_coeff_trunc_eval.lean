import Mathlib

namespace Work.KT.FP

open scoped BigOperators

/-- Auxiliary: for `z ≠ 0` and `j : Fin (2*m+1)`, the power `z ^ j` factors as
`z ^ m * z ^ (j - m)` with the shift `(j : ℤ) - (m : ℤ)` in the exponent. -/
private lemma zpow_shift_mul (z : ℂ) (hz : z ≠ 0) (m : ℕ) (j : Fin (2 * m + 1)) (c : ℂ) :
    z ^ (j : ℕ) * c = z ^ m * (c * z ^ ((j : ℤ) - (m : ℤ))) := by
  have h : z ^ (j : ℕ) = z ^ m * z ^ ((j : ℤ) - (m : ℤ)) := by
    rw [← zpow_natCast z m, ← zpow_add₀ hz]
    rw [show (m : ℤ) + ((j : ℤ) - (m : ℤ)) = (j : ℤ) by omega]
    exact (zpow_natCast z (j : ℕ)).symm
  rw [h]; ring

/-- The sum `∑_{j=0}^{2m} z^j c_{j-m}` of the coefficients of `p` (evaluated at `x`),
shifted by `m`, equals `z^m` times the evaluation of the Laurent polynomial `p` at `x` and `z`,
provided all coefficients with `|k| > m` vanish. -/
theorem laurent_coeff_trunc_eval (X : Type) [TopologicalSpace X] (p : LaurentPolynomial C(X, ℂ))
    (m : ℕ) (z : ℂ) (hz : z ≠ 0) (x : X)
    (hpb : ∀ k : ℤ, (m : ℤ) < k ∨ k < -(m : ℤ) → p.coeff k = 0) :
    (∑ j : Fin (2 * m + 1), z ^ (j : ℕ) * (p.coeff ((j : ℤ) - (m : ℤ))) x)
      = z ^ m * (∑ k ∈ p.coeff.support, (p.coeff k) x * z ^ k) := by
  -- Every exponent in the support lies in `[-m, m]`.
  have hsubset : p.coeff.support ⊆ Finset.Icc (-(m : ℤ)) (m : ℤ) := by
    intro k hk
    rw [Finset.mem_Icc]
    by_contra h
    rw [not_and_or] at h
    exact (Finsupp.mem_support_iff.mp hk)
      (hpb k (h.elim (fun h1 => Or.inr (not_le.mp h1)) (fun h2 => Or.inl (not_le.mp h2))))
  -- Conversely the summand vanishes outside the support.
  have hzero : ∀ y ∈ Finset.Icc (-(m : ℤ)) (m : ℤ), y ∉ p.coeff.support →
      (p.coeff y) x * z ^ y = 0 := by
    intro y _ hy
    have h0 : p.coeff y = 0 := by
      by_contra h
      exact hy (Finsupp.mem_support_iff.mpr h)
    simp [h0]
  have hsupp : ∑ k ∈ p.coeff.support, (p.coeff k) x * z ^ k
      = ∑ k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ), (p.coeff k) x * z ^ k :=
    Finset.sum_subset hsubset hzero
  -- The map `j ↦ j - m` runs bijectively over `[-m, m]`.
  have hinj : Set.InjOn (fun j : Fin (2 * m + 1) => (j : ℤ) - (m : ℤ))
      ↑(Finset.univ : Finset (Fin (2 * m + 1))) := by
    intro j _ j' _ h
    change (j : ℤ) - (m : ℤ) = (j' : ℤ) - (m : ℤ) at h
    have h2 : ((j : ℕ) : ℤ) = ((j' : ℕ) : ℤ) := by omega
    exact Fin.ext (Int.ofNat.inj h2)
  have himage : (Finset.univ.image (fun j : Fin (2 * m + 1) => (j : ℤ) - (m : ℤ)))
      = Finset.Icc (-(m : ℤ)) (m : ℤ) := by
    apply Finset.ext
    intro k
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_Icc]
    constructor
    · rintro ⟨j, rfl⟩
      constructor
      · have : (0 : ℤ) ≤ (j : ℤ) := Int.natCast_nonneg _
        omega
      · have hj : ((j : ℕ) : ℤ) ≤ (2 * (m : ℤ)) := by
          have h : j.val < 2 * m + 1 := j.2
          omega
        omega
    · rintro ⟨h1, h2⟩
      refine ⟨⟨(k + (m : ℤ)).toNat, ?_⟩, ?_⟩
      · rw [Int.toNat_lt_of_ne_zero (by omega)]
        omega
      · show ((((k + (m : ℤ)).toNat : ℕ) : ℤ)) - (m : ℤ) = k
        have hk0 : 0 ≤ k + (m : ℤ) := by omega
        have hval : ((k + (m : ℤ)).toNat : ℤ) = k + (m : ℤ) := Int.toNat_of_nonneg hk0
        omega
  have hIcc : ∑ k ∈ Finset.Icc (-(m : ℤ)) (m : ℤ), (p.coeff k) x * z ^ k
      = ∑ j : Fin (2 * m + 1), (p.coeff ((j : ℤ) - (m : ℤ))) x * z ^ ((j : ℤ) - (m : ℤ)) := by
    rw [← himage]
    exact Finset.sum_image hinj
  rw [hsupp, hIcc, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact zpow_shift_mul z hz m j ((p.coeff ((j : ℤ) - (m : ℤ))) x)

end Work.KT.FP
