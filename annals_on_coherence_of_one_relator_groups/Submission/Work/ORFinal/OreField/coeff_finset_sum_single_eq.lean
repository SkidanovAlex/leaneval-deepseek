import Mathlib

namespace Work.ORFinal.OreField

theorem coeff_finset_sum_single_eq {D : Type*} [DivisionRing D]
    [MulSemiringAction (Multiplicative ℤ) D] (N : ℕ) (C : Fin N → D) (k : Fin N) :
    (∑ j : Fin N, SkewMonoidAlgebra.single (Multiplicative.ofAdd ((j : ℕ) : ℤ))
        (Multiplicative.ofAdd ((j : ℕ) : ℤ) • C j)).coeff (Multiplicative.ofAdd ((k : ℕ) : ℤ))
      = Multiplicative.ofAdd ((k : ℕ) : ℤ) • C k := by
  -- `coeff` is (the underlying map of) the additive equivalence `coeffAddEquiv`,
  -- so it commutes with the finite sum, and evaluation of a `Finsupp` sum is the
  -- sum of the evaluations.
  rw [← SkewMonoidAlgebra.coeffAddEquiv_apply,
    _root_.map_sum SkewMonoidAlgebra.coeffAddEquiv]
  simp only [SkewMonoidAlgebra.coeffAddEquiv_apply]
  rw [Finsupp.finsetSum_apply]
  -- Now evaluate each `single`; only the `j = k` term can contribute, because
  -- `Multiplicative.ofAdd ∘ (↑· : Fin N → ℤ)` is injective.
  simp only [SkewMonoidAlgebra.coeff_single_apply]
  rw [show (∑ x : Fin N,
        (if Multiplicative.ofAdd ((x : ℕ) : ℤ) = Multiplicative.ofAdd ((k : ℕ) : ℤ)
          then Multiplicative.ofAdd ((x : ℕ) : ℤ) • C x else 0))
      = ∑ x : Fin N,
          (if x = k then Multiplicative.ofAdd ((x : ℕ) : ℤ) • C x else 0) from by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x = k
    · simp [hx]
    · have hne : Multiplicative.ofAdd ((x : ℕ) : ℤ)
          ≠ Multiplicative.ofAdd ((k : ℕ) : ℤ) := by
        simp only [ne_eq, Multiplicative.ofAdd.injective.eq_iff, Int.ofNat_inj, Fin.val_inj]
        exact hx
      simp [hx, hne]]
  rw [Finset.sum_ite_eq']
  simp

end Work.ORFinal.OreField
