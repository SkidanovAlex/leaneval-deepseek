import Mathlib
import Submission.Commons.NumberTheory.Height.NumberField.mahlerMeasure_minpoly_int_eq_mulHeight1

namespace Commons.NumberTheory.Polynomial

theorem mapMahlerMeasure_minpoly_eq_prod_algHom {K : Type*} [Field K] [Algebra ℚ K]
    [FiniteDimensional ℚ K] [Algebra.IsSeparable ℚ K] {z : K} (hz : IsIntegral ℤ z)
    (hgen : Algebra.adjoin ℚ ({z} : Set K) = ⊤) :
    Polynomial.mapMahlerMeasure (minpoly ℤ z) (Int.castRingHom ℂ)
      = ∏ χ : (K →ₐ[ℚ] ℂ), max 1 ‖χ z‖ := by
  haveI : NumberField K := by
    have hcz : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
    have halg : (‹Algebra ℚ K›) = (DivisionRing.toRatAlgebra : Algebra ℚ K) :=
      Subsingleton.elim _ _
    have hm : (@Algebra.toModule ℚ K _ _ ‹Algebra ℚ K›)
        = (@Algebra.toModule ℚ K _ _ (DivisionRing.toRatAlgebra : Algebra ℚ K)) :=
      congrArg (fun a : Algebra ℚ K => @Algebra.toModule ℚ K _ _ a) halg
    haveI hfd : @FiniteDimensional ℚ K _ _
        (@Algebra.toModule ℚ K _ _ (DivisionRing.toRatAlgebra : Algebra ℚ K)) :=
      cast (congrArg (fun m => @FiniteDimensional ℚ K _ _ m) hm) (‹FiniteDimensional ℚ K›)
    exact { to_charZero := hcz, to_finiteDimensional := hfd }
  have hgenB : @Algebra.adjoin ℚ K _ _ (DivisionRing.toRatAlgebra : Algebra ℚ K)
      ({z} : Set K) = ⊤ := by
    have halg : (‹Algebra ℚ K›) = (DivisionRing.toRatAlgebra : Algebra ℚ K) :=
      Subsingleton.elim _ _
    exact halg ▸ hgen
  have h1 : Polynomial.mapMahlerMeasure (minpoly ℤ z) (Int.castRingHom ℂ)
      = ∏ σ : K →+* ℂ, max 1 ‖σ z‖ := by
    rw [Commons.NumberTheory.Height.NumberField.mapMahlerMeasure_minpoly_int_eq_map_minpoly_rat
          (K := K) hz,
        Commons.NumberTheory.Height.NumberField.mapMahlerMeasure_minpoly_rat_eq_prod_max_one_norm
          (K := K) hgenB]
  rw [h1]
  exact Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ)
        (fun σ : K →+* ℂ => max 1 ‖σ z‖)
        (fun χ : K →ₐ[ℚ] ℂ => max 1 ‖χ z‖)
        (fun σ => by simp [RingHom.equivRatAlgHom_apply])

end Commons.NumberTheory.Polynomial
