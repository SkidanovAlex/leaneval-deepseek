import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.NumberField

open scoped Classical

/-- **Norm versus embedding, quadratic case.**

Let `K` be a number field of degree `2` over `ℚ` with no real places, i.e. an imaginary
quadratic field.  Then `K` has a single infinite place `w = mk σ`, every embedding `K →+* ℂ`
has the same infinite place, and the product formula reads

`|norm x| = ∏_w w x ^ mult w = (w x)^2 = ‖σ x‖^2`.

So the absolute value of the field norm of `x` is the square of the complex absolute value of
any one of its conjugates. -/
theorem abs_norm_eq_norm_embedding_sq_of_finrank_two {K : Type*} [Field K] [NumberField K]
    (h2 : Module.finrank ℚ K = 2) (h0 : NumberField.InfinitePlace.nrRealPlaces K = 0)
    (σ : K →+* ℂ) (x : K) : |(Algebra.norm ℚ x : ℝ)| = ‖σ x‖ ^ 2 := by
  -- Degree `2` and no real places force exactly one complex place.
  have hrank := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
  have hc : NumberField.InfinitePlace.nrComplexPlaces K = 1 := by
    rw [h2, h0, zero_add] at hrank
    omega
  have hcard : Fintype.card (NumberField.InfinitePlace K) = 1 := by
    rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, h0, hc]
  -- Hence there is at most one infinite place at all.
  haveI : Subsingleton (NumberField.InfinitePlace K) :=
    Fintype.card_le_one_iff_subsingleton.mp (by rw [hcard])
  -- The place of `σ` is complex (there are no real places) and therefore has multiplicity `2`.
  have hmult : NumberField.InfinitePlace.mult (NumberField.InfinitePlace.mk σ) = 2 := by
    have hnr : ¬ NumberField.InfinitePlace.IsReal (NumberField.InfinitePlace.mk σ) := by
      intro hreal
      haveI : IsEmpty {w : NumberField.InfinitePlace K // w.IsReal} :=
        Fintype.card_eq_zero_iff.mp h0
      exact isEmptyElim (⟨NumberField.InfinitePlace.mk σ, hreal⟩ :
        {w : NumberField.InfinitePlace K // w.IsReal})
    exact NumberField.InfinitePlace.IsComplex.mult_eq_two
      (NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hnr)
  -- The product over all places collapses to the single place `mk σ`.
  have heval : (∏ w : NumberField.InfinitePlace K, (w x) ^ NumberField.InfinitePlace.mult w)
      = ‖σ x‖ ^ 2 := by
    rw [Fintype.prod_subsingleton _ (NumberField.InfinitePlace.mk σ), hmult,
      NumberField.InfinitePlace.apply σ x]
  -- The infinite part of the product formula, and the rational/real absolute value bridge.
  have hprod := NumberField.InfinitePlace.prod_eq_abs_norm (K := K) x
  rw [heval] at hprod
  rw [Rat.cast_abs] at hprod
  exact hprod.symm

end Commons.NumberTheory.NumberField