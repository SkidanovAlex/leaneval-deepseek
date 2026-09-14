import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.NumberTheory.Polynomial

theorem mapMahlerMeasure_minpoly_eq_prod_algHom_simple (z : ℂ) (hz : IsIntegral ℤ z)
    [FiniteDimensional ℚ ↥(IntermediateField.adjoin ℚ ({z} : Set ℂ))] :
    Polynomial.mapMahlerMeasure (minpoly ℤ z) (Int.castRingHom ℂ)
      = ∏ χ : (↥(IntermediateField.adjoin ℚ ({z} : Set ℂ)) →ₐ[ℚ] ℂ),
          max 1 ‖χ (IntermediateField.AdjoinSimple.gen ℚ z)‖ := by
  have hzq : IsIntegral ℚ z := hz.tower_top
  -- `minpoly ℤ z`, mapped to `ℂ`, agrees with `minpoly ℚ z`, mapped to `ℂ`.
  have hmap : (minpoly ℤ z).map (Int.castRingHom ℂ) = (minpoly ℚ z).map (algebraMap ℚ ℂ) := by
    have hmin : minpoly ℚ z = (minpoly ℤ z).map (algebraMap ℤ ℚ) :=
      minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hz
    rw [hmin, Polynomial.map_map]
    congr 1
  -- Reduce the Mahler measure to the product over the roots (the leading coefficient is `1`).
  rw [Polynomial.mapMahlerMeasure_eq, hmap,
    Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots,
    ((minpoly.monic hzq).map (algebraMap ℚ ℂ)).leadingCoeff, norm_one, one_mul,
    ← Polynomial.aroots_def]
  -- The minimal polynomial is separable, so all its roots are distinct.
  have haroots_nodup : ((minpoly ℚ z).aroots ℂ).Nodup := by
    rw [Polynomial.nodup_aroots_iff_of_splits (minpoly.ne_zero hzq) (IsAlgClosed.splits _)]
    exact (minpoly.irreducible hzq).separable
  -- Rewrite the multiset product over the roots as the product over the root set.
  have hmult : (((minpoly ℚ z).aroots ℂ).map (fun a => max 1 ‖a‖)).prod
      = ∏ x : {x // x ∈ (minpoly ℚ z).aroots ℂ}, max 1 ‖x.1‖ := by
    calc (((minpoly ℚ z).aroots ℂ).map (fun a => max 1 ‖a‖)).prod
        = ∏ m ∈ ((minpoly ℚ z).aroots ℂ).toFinset,
            (max 1 ‖m‖) ^ (((minpoly ℚ z).aroots ℂ).count m) :=
          Finset.prod_multiset_map_count _ _
      _ = ∏ m ∈ ((minpoly ℚ z).aroots ℂ).toFinset, max 1 ‖m‖ := by
          apply Finset.prod_congr rfl
          intro m hm
          rw [Multiset.count_eq_one_of_mem haroots_nodup (Multiset.mem_toFinset.mp hm),
            pow_one]
      _ = ∏ x : {x // x ∈ (minpoly ℚ z).aroots ℂ}, max 1 ‖x.1‖ :=
          Finset.prod_subtype (p := fun x => x ∈ (minpoly ℚ z).aroots ℂ)
            (((minpoly ℚ z).aroots ℂ).toFinset)
            (fun x => Multiset.mem_toFinset (a := x))
            (fun a => max 1 ‖a‖)
  -- The `ℚ`-algebra maps `ℚ⟮z⟯ → ℂ` correspond bijectively to the roots of `minpoly ℚ z`.
  have hemb : (∏ χ : (↥(IntermediateField.adjoin ℚ ({z} : Set ℂ)) →ₐ[ℚ] ℂ),
        max 1 ‖χ (IntermediateField.AdjoinSimple.gen ℚ z)‖)
      = ∏ x : {x // x ∈ (minpoly ℚ z).aroots ℂ}, max 1 ‖x.1‖ := by
    refine Fintype.prod_equiv
      (IntermediateField.algHomAdjoinIntegralEquiv (F := ℚ) (E := ℂ) (α := z) (K := ℂ) hzq)
      (fun χ => max 1 ‖χ (IntermediateField.AdjoinSimple.gen ℚ z)‖)
      (fun x => max 1 ‖x.1‖) ?_
    intro χ
    have h := IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen (F := ℚ) (E := ℂ)
      (α := z) (K := ℂ) hzq
      (IntermediateField.algHomAdjoinIntegralEquiv (F := ℚ) (E := ℂ) (α := z) (K := ℂ) hzq χ)
    simp only [Equiv.symm_apply_apply] at h
    rw [← h]
  rw [hmult, hemb]

end Commons.NumberTheory.Polynomial