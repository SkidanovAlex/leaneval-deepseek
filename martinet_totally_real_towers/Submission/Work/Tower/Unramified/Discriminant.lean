import Mathlib
import Submission.Work.Tower.Unramified.Basic

/-!
# Discriminants and root discriminants of unramified extensions

For a finite extension `L/F` of number fields which is unramified at every finite prime, the
relative different is trivial, so `|discr L| = |discr F| ^ [L : F]` and hence
`rootDiscr L = rootDiscr F`.  We also record the monotonicity of `rootDiscr` along subfields
and the trivial bound `1 ≤ rootDiscr K`.

## Main results

* `Work.Tower.differentIdeal_eq_top_of_isUnramifiedExtensionForallPrimes`;
* `Work.Tower.natAbs_discr_eq_pow_of_isUnramifiedExtensionForallPrimes`;
* `Work.Tower.rootDiscr_eq_of_isUnramifiedExtensionForallPrimes`;
* `Work.Tower.one_le_rootDiscr`, `Work.Tower.rootDiscr_le_of_algebra`.
-/

open NumberField
open scoped Classical nonZeroDivisors

namespace Work
namespace Tower

variable {F L : Type*} [Field F] [Field L] [NumberField F] [NumberField L] [Algebra F L]
    [FiniteDimensional F L]

/-- If `L/F` is unramified at every prime, the relative different `𝔡_{L/F}` is trivial. -/
theorem differentIdeal_eq_top_of_isUnramifiedExtensionForallPrimes
    (h : IsUnramifiedExtensionForallPrimes F L) :
    differentIdeal (𝓞 F) (𝓞 L) = ⊤ := by
  letI : Algebra (FractionRing (𝓞 F)) (FractionRing (𝓞 L)) :=
    FractionRing.liftAlgebra (R := 𝓞 F) (FractionRing (𝓞 L))
  haveI : Algebra.IsSeparable (FractionRing (𝓞 F)) (FractionRing (𝓞 L)) := inferInstance
  rw [← not_ne_iff]
  intro hne
  obtain ⟨M, hMmax, hMle⟩ := Ideal.ne_top_iff_exists_maximal.mp hne
  have hMprime : M.IsPrime := hMmax.isPrime
  have hdvd : M ∣ differentIdeal (𝓞 F) (𝓞 L) := Ideal.dvd_iff_le.mpr hMle
  have hunr : Algebra.IsUnramifiedAt (𝓞 F) M :=
    (Ideal.ramificationIdx_eq_one_iff (R := 𝓞 F) (q := M)).mp (h M hMprime)
  exact (dvd_differentIdeal_iff.mp hdvd) hunr

/-- **The discriminant of an unramified extension.**  If `L/F` is unramified at every prime,
then `|discr L| = |discr F| ^ [L : F]`. -/
theorem natAbs_discr_eq_pow_of_isUnramifiedExtensionForallPrimes
    (h : IsUnramifiedExtensionForallPrimes F L) :
    (discr L).natAbs = (discr F).natAbs ^ Module.finrank F L := by
  have hdiff := differentIdeal_eq_top_of_isUnramifiedExtensionForallPrimes h
  have hmain := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) L (𝓞 L)
  rwa [hdiff, Ideal.absNorm_top, one_mul] at hmain

/-- **The discriminant of an unramified extension**, in `ℤ`. -/
theorem abs_discr_eq_pow_of_isUnramifiedExtensionForallPrimes
    (h : IsUnramifiedExtensionForallPrimes F L) :
    |discr L| = |discr F| ^ Module.finrank F L := by
  rw [← Int.natCast_natAbs, natAbs_discr_eq_pow_of_isUnramifiedExtensionForallPrimes h,
    Int.natCast_pow, Int.natCast_natAbs]

/-- **The root discriminant is unchanged by unramified extensions.** -/
theorem rootDiscr_eq_of_isUnramifiedExtensionForallPrimes
    (h : IsUnramifiedExtensionForallPrimes F L) : rootDiscr L = rootDiscr F := by
  have hdisc : ((|discr L| : ℤ) : ℝ) = ((|discr F| : ℤ) : ℝ) ^ Module.finrank F L := by
    rw [abs_discr_eq_pow_of_isUnramifiedExtensionForallPrimes h, Int.cast_pow]
  have hfinNat : Module.finrank ℚ L = Module.finrank F L * Module.finrank ℚ F := by
    rw [← Module.finrank_mul_finrank ℚ F L, mul_comm]
  have hfin : (Module.finrank ℚ L : ℝ) =
      (Module.finrank F L : ℝ) * (Module.finrank ℚ F : ℝ) := by
    rw [hfinNat, Nat.cast_mul]
  have hpos : (0 : ℝ) ≤ ((|discr F| : ℤ) : ℝ) := by positivity
  have hn : (Module.finrank F L : ℝ) ≠ 0 := by
    exact_mod_cast Module.finrank_pos.ne'
  have hexp : (Module.finrank F L : ℝ) *
      ((Module.finrank F L : ℝ) * (Module.finrank ℚ F : ℝ))⁻¹ =
        ((Module.finrank ℚ F : ℝ))⁻¹ := by
    rw [mul_inv]
    field_simp
  rw [rootDiscr_def, rootDiscr_def]
  rw [show ((|discr L| : ℤ) : ℝ) = ((|discr F| : ℤ) : ℝ) ^ Module.finrank F L from hdisc]
  rw [show ((|discr F| : ℤ) : ℝ) ^ Module.finrank F L =
      ((|discr F| : ℤ) : ℝ) ^ ((Module.finrank F L : ℝ)) from (Real.rpow_natCast _ _).symm]
  rw [hfin, ← Real.rpow_mul hpos, hexp]

/-- The relative different is trivial exactly when `L/F` is unramified at every prime. -/
theorem isUnramifiedExtensionForallPrimes_iff_differentIdeal_eq_top :
    IsUnramifiedExtensionForallPrimes F L ↔ differentIdeal (𝓞 F) (𝓞 L) = ⊤ := by
  letI : Algebra (FractionRing (𝓞 F)) (FractionRing (𝓞 L)) :=
    FractionRing.liftAlgebra (R := 𝓞 F) (FractionRing (𝓞 L))
  haveI : Algebra.IsSeparable (FractionRing (𝓞 F)) (FractionRing (𝓞 L)) := inferInstance
  refine ⟨differentIdeal_eq_top_of_isUnramifiedExtensionForallPrimes, fun h 𝔓 h𝔓 ↦ ?_⟩
  have hnd : ¬ 𝔓 ∣ differentIdeal (𝓞 F) (𝓞 L) := by
    rw [h, Ideal.dvd_iff_le, top_le_iff]
    exact h𝔓.ne_top
  have hunr : Algebra.IsUnramifiedAt (𝓞 F) 𝔓 := not_dvd_differentIdeal_iff.mp hnd
  exact (Ideal.ramificationIdx_eq_one_iff (R := 𝓞 F) (q := 𝔓)).mpr hunr

/-- **Discriminant of a Galois unramified extension.** -/
theorem natAbs_discr_eq_pow_of_isUnramifiedExtension [IsGalois F L]
    (h : IsUnramifiedExtension F L) :
    (discr L).natAbs = (discr F).natAbs ^ Module.finrank F L :=
  natAbs_discr_eq_pow_of_isUnramifiedExtensionForallPrimes h.forallPrimes

/-- **Root discriminant of a Galois unramified extension.** -/
theorem rootDiscr_eq_of_isUnramifiedExtension [IsGalois F L]
    (h : IsUnramifiedExtension F L) : rootDiscr L = rootDiscr F :=
  rootDiscr_eq_of_isUnramifiedExtensionForallPrimes h.forallPrimes

end Tower

section RootDiscr

/-- The root discriminant of a number field is at least `1`. -/
theorem one_le_rootDiscr (K : Type*) [Field K] [NumberField K] : 1 ≤ rootDiscr K := by
  rw [rootDiscr_def]
  refine Real.one_le_rpow ?_ (by positivity)
  have := Int.one_le_abs (discr_ne_zero K)
  exact_mod_cast this

end RootDiscr
end Work
