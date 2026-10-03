import Mathlib
import Submission.Work.ORHughesFree.NaturalExtension.envelopeToeplitz
import Submission.Work.ORHughesFree.SkewLaurentSeriesInstances

namespace Work.ORHughesFree.NaturalExtension

open Matrix

variable {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]

/-- The `N × N` Toeplitz matrix of a skew Laurent series `p`: the `(r, s)` entry is the twist
`τ^r` applied to the coefficient of `t^{s - r}` in `p`. -/
noncomputable def toeplitzSeries (N : ℕ) (p : Work.ORHughesFree.SkewLaurentSeries U) :
    Matrix (Fin N) (Fin N) U :=
  fun r s => (Multiplicative.ofAdd ((r : ℕ) : ℤ)) • p.1 (((s : ℕ) : ℤ) - ((r : ℕ) : ℤ))

@[simp] theorem toeplitzSeries_apply (N : ℕ) (p : Work.ORHughesFree.SkewLaurentSeries U)
    (r s : Fin N) :
    toeplitzSeries N p r s =
      (Multiplicative.ofAdd ((r : ℕ) : ℤ)) • p.1 (((s : ℕ) : ℤ) - ((r : ℕ) : ℤ)) := rfl

theorem toeplitzSeries_zero (N : ℕ) :
    toeplitzSeries (U := U) N (0 : Work.ORHughesFree.SkewLaurentSeries U) = 0 := by
  ext r s
  simp [toeplitzSeries]

theorem toeplitzSeries_add (N : ℕ) (p q : Work.ORHughesFree.SkewLaurentSeries U) :
    toeplitzSeries N (p + q) = toeplitzSeries N p + toeplitzSeries N q := by
  ext r s
  simp only [toeplitzSeries, Matrix.add_apply, Work.ORHughesFree.SkewLaurentSeries.add_apply,
    smul_add]

theorem toeplitzSeries_one (N : ℕ) :
    toeplitzSeries (U := U) N (1 : Work.ORHughesFree.SkewLaurentSeries U) = 1 := by
  ext r s
  rw [Matrix.one_apply]
  by_cases h : r = s
  · subst h
    simp [toeplitzSeries]
  · have hk : ¬ (((s : ℕ) : ℤ) - ((r : ℕ) : ℤ) = 0) := by
      intro h0
      exact h (Fin.ext (by omega))
    simp [toeplitzSeries, hk, h]

/-- **Multiplicativity of the Toeplitz family.**  If `p` and `q` are power series (`p.1 k = 0`
for `k < 0`, and likewise for `q`), then the `N × N` Toeplitz matrix of the product is the product
of the Toeplitz matrices.  (Without the support hypothesis on `q` the statement fails, since the
coefficient of degree `s - r` in `p * q` can receive contributions from arbitrarily negative
intermediate degrees which the finite matrix product does not see.) -/
theorem toeplitzSeries_mul (N : ℕ) {p q : Work.ORHughesFree.SkewLaurentSeries U}
    (hp : ∀ k : ℤ, k < 0 → p.1 k = 0) (hq : ∀ k : ℤ, k < 0 → q.1 k = 0) :
    toeplitzSeries N (p * q) = toeplitzSeries N p * toeplitzSeries N q := by
  classical
  ext r s
  simp only [toeplitzSeries, Matrix.mul_apply]
  set R : ℤ := ((r : ℕ) : ℤ) with hRdef
  set S : ℤ := ((s : ℕ) : ℤ) with hSdef
  have hR0 : 0 ≤ R := by rw [hRdef]; omega
  have hRn : R ≤ (N : ℤ) - 1 := by rw [hRdef]; have := r.isLt; omega
  have hSn : S ≤ (N : ℤ) - 1 := by rw [hSdef]; have := s.isLt; omega
  rw [Work.ORHughesFree.SkewLaurentSeries.mul_apply_of_bounds p q 0 0 hp hq (S - R)]
  simp only [sub_zero]
  rw [Finset.smul_sum]
  let T : ℤ → U := fun v =>
    (Multiplicative.ofAdd R • p.1 v) * (Multiplicative.ofAdd (R + v) • q.1 (S - R - v))
  have hLsum : (∑ k ∈ Finset.Icc 0 (S - R),
        Multiplicative.ofAdd R • (p.1 k * (Multiplicative.ofAdd k • q.1 (S - R - k))))
      = ∑ v ∈ Finset.Icc 0 (S - R), T v :=
    Finset.sum_congr rfl fun k _ => by
      simp only [T]
      rw [smul_mul', ← mul_smul, ← ofAdd_add]
  have hRsum : (∑ u : Fin N,
        (Multiplicative.ofAdd R • p.1 (((u : ℕ) : ℤ) - R)) *
          (Multiplicative.ofAdd ((u : ℕ) : ℤ) • q.1 (S - ((u : ℕ) : ℤ))))
      = ∑ v ∈ Finset.Icc (-R) ((N : ℤ) - 1 - R), T v := by
    rw [show (∑ u : Fin N,
        (Multiplicative.ofAdd R • p.1 (((u : ℕ) : ℤ) - R)) *
          (Multiplicative.ofAdd ((u : ℕ) : ℤ) • q.1 (S - ((u : ℕ) : ℤ))))
        = ∑ u : Fin N, T (((u : ℕ) : ℤ) - R) from
      Finset.sum_congr rfl fun u _ => by
        simp only [T]
        rw [show R + (((u : ℕ) : ℤ) - R) = ((u : ℕ) : ℤ) by ring,
          show S - R - (((u : ℕ) : ℤ) - R) = S - ((u : ℕ) : ℤ) by ring]]
    exact sum_fin_sub_shift_skew N R T
  rw [hLsum, hRsum]
  have hsub1 : Finset.Icc 0 (S - R) ⊆ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro v hv
    rw [Finset.mem_Icc] at hv ⊢
    omega
  have hsub2 : Finset.Icc (-R) ((N : ℤ) - 1 - R) ⊆ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro v hv
    rw [Finset.mem_Icc] at hv ⊢
    omega
  have hvan1 : ∀ x ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      x ∉ Finset.Icc 0 (S - R) → T x = 0 := by
    intro x _ hx
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · simp only [T]; rw [hp x (by omega), smul_zero, zero_mul]
    · simp only [T]; rw [hq (S - R - x) (by omega), smul_zero, mul_zero]
  have hvan2 : ∀ x ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      x ∉ Finset.Icc (-R) ((N : ℤ) - 1 - R) → T x = 0 := by
    intro x _ hx
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · simp only [T]; rw [hp x (by omega), smul_zero, zero_mul]
    · simp only [T]; rw [hq (S - R - x) (by omega), smul_zero, mul_zero]
  rw [Finset.sum_subset hsub1 hvan1, Finset.sum_subset hsub2 hvan2]

end Work.ORHughesFree.NaturalExtension

namespace Work.ORHughesFree.NaturalExtension

open Matrix

/-- Every subring of the skew Laurent series ring whose elements are exactly the power series
(`p.1 m = 0` for `m < 0`) maps to the product of matrix rings `∏_{n ≥ 1} M_n(U)` by the Toeplitz
construction `p ↦ (n ↦ (toeplitzSeries (n+1) p))`. -/
theorem exists_powerSeriesToeplitz {U : Type} [Ring U] [MulSemiringAction (Multiplicative ℤ) U]
    (S : Subring (Work.ORHughesFree.SkewLaurentSeries U))
    (hS : ∀ p : Work.ORHughesFree.SkewLaurentSeries U, p ∈ S ↔ ∀ m : ℤ, m < 0 → p.1 m = 0) :
    ∃ ψ : ↥S →+* Work.ORHughesFree.NaturalExtension.W U,
      ∀ (p : ↥S) (n : ℕ) (r s : Fin (n+1)),
        (ψ p) n r s =
          (Multiplicative.ofAdd ((r : ℕ) : ℤ)) •
            ((p : Work.ORHughesFree.SkewLaurentSeries U).1 (((s : ℕ) : ℤ) - ((r : ℕ) : ℤ))) := by
  classical
  refine ⟨{ toFun := fun p n => toeplitzSeries (n + 1) (p : Work.ORHughesFree.SkewLaurentSeries U)
            map_one' := ?_
            map_mul' := ?_
            map_zero' := ?_
            map_add' := ?_ }, ?_⟩
  · funext n
    rw [Pi.one_apply, Subring.coe_one]
    exact toeplitzSeries_one (n + 1)
  · intro p q
    funext n
    rw [Pi.mul_apply, Subring.coe_mul]
    exact toeplitzSeries_mul (n + 1) ((hS _).mp p.2) ((hS _).mp q.2)
  · funext n
    rw [Pi.zero_apply, Subring.coe_zero]
    exact toeplitzSeries_zero (n + 1)
  · intro p q
    funext n
    rw [Pi.add_apply, Subring.coe_add]
    exact toeplitzSeries_add (n + 1) _ _
  · intro p n r s
    rfl

end Work.ORHughesFree.NaturalExtension
