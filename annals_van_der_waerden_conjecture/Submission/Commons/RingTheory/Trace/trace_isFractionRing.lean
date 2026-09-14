import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

set_option linter.style.haveILetI false

namespace Commons.RingTheory.Trace

open Polynomial

/-- If `b ≠ 0` is an element of a domain `S` which is integral over a domain `R`, then the
constant coefficient of the minimal polynomial of `b` over `R` is nonzero. -/
private lemma minpoly_coeff_zero_ne_zero {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Algebra R S] {b : S} (hb : b ≠ 0) (hint : IsIntegral R b) :
    (minpoly R b).coeff 0 ≠ 0 := by
  intro h
  obtain ⟨q, hq⟩ := X_dvd_iff.2 h
  have hdeg : q.degree < (minpoly R b).degree := by
    rw [hq, mul_comm]
    refine degree_lt_degree_mul_X fun hq0 => ?_
    rw [hq0, mul_zero] at hq
    exact minpoly.ne_zero hint hq
  have hqmonic : q.Monic := by
    suffices (minpoly R b).Monic by
      rwa [Monic.def, hq, mul_comm, leadingCoeff_mul_X, ← Monic.def] at this
    exact minpoly.monic hint
  have hz : aeval b q = 0 := by
    have h0 := minpoly.aeval R b
    rw [hq, aeval_mul, aeval_X] at h0
    exact (mul_eq_zero.mp h0).resolve_left hb
  exact not_le.2 hdeg (minpoly.min R b hqmonic hz)

/-- If `S` is a finite extension of a domain `R` and `b ≠ 0` in `S`, then `b` divides some
nonzero element of `R`, viewed inside `S`. -/
private lemma exists_mul_eq_algebraMap_of_ne_zero {R S : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S] {b : S} (hb : b ≠ 0) :
    ∃ u : S, ∃ c : R, c ≠ 0 ∧ b * u = algebraMap R S c := by
  have hint : IsIntegral R b := (Algebra.IsIntegral.of_finite R S).isIntegral b
  have hcoeff : (minpoly R b).coeff 0 ≠ 0 := minpoly_coeff_zero_ne_zero hb hint
  refine ⟨aeval b (divX (minpoly R b)), -(minpoly R b).coeff 0, neg_ne_zero.mpr hcoeff, ?_⟩
  have h := minpoly.aeval R b
  rw [← X_mul_divX_add (minpoly R b)] at h
  simp only [map_add, map_mul, aeval_X, aeval_C] at h
  rw [map_neg]
  exact eq_neg_of_add_eq_zero_left h

/-- The fraction field `L` of `S` is the localization of `S` at the image of the nonzero divisors
of `R`, when `S` is a finite free extension of the domain `R`. -/
private lemma isLocalization_algebraMapSubmonoid_nonZeroDivisors {R S L : Type*} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] [Algebra R S] [Module.Free R S] [Module.Finite R S]
    [Field L] [Algebra S L] [IsFractionRing S L] [Algebra R L] [IsScalarTower R S L] :
    IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) L := by
  have hinj : Function.Injective (algebraMap R S) :=
    (faithfulSMul_iff_algebraMap_injective R S).mp inferInstance
  have hMle : Algebra.algebraMapSubmonoid S (nonZeroDivisors R) ≤ nonZeroDivisors S := by
    rintro y ⟨r, hr, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr
      (fun h => (mem_nonZeroDivisors_iff_ne_zero.mp hr) (hinj (by simpa using h)))
  refine ⟨?_, ?_, ?_⟩
  · intro y
    exact IsLocalization.map_units L ⟨y.1, hMle y.2⟩
  · intro z
    obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective S z
    have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
    obtain ⟨u, c, hc0, hcu⟩ := exists_mul_eq_algebraMap_of_ne_zero (R := R) (S := S) hb0
    have hc : c ∈ nonZeroDivisors R := mem_nonZeroDivisors_iff_ne_zero.mpr hc0
    refine ⟨(a * u, ⟨algebraMap R S c, Algebra.mem_algebraMapSubmonoid_of_mem ⟨c, hc⟩⟩), ?_⟩
    have hbne : algebraMap S L b ≠ 0 :=
      fun h => hb0 (IsFractionRing.injective S L (by simpa using h))
    have h1 : z * algebraMap S L b = algebraMap S L a := by
      rw [← hab]
      exact div_mul_cancel₀ _ hbne
    calc z * algebraMap S L (algebraMap R S c)
        = z * algebraMap S L (b * u) := by rw [hcu]
      _ = z * (algebraMap S L b * algebraMap S L u) := by rw [map_mul]
      _ = (z * algebraMap S L b) * algebraMap S L u := by ring
      _ = algebraMap S L a * algebraMap S L u := by rw [h1]
      _ = algebraMap S L (a * u) := by rw [map_mul]
  · intro x y hxy
    exact ⟨1, by simp [IsFractionRing.injective S L hxy]⟩

theorem trace_isFractionRing {R S K L : Type*}
    [CommRing R] [IsDomain R] [CommRing S] [Algebra R S] [IsDomain S]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra S L] [IsFractionRing S L] [Algebra R L] [IsScalarTower R S L]
    [Algebra K L] [IsScalarTower R K L]
    [Module.Free R S] [Module.Finite R S] (x : S) :
    Algebra.trace K L (algebraMap S L x) = algebraMap R K (Algebra.trace R S x) := by
  haveI := isLocalization_algebraMapSubmonoid_nonZeroDivisors (R := R) (S := S) (L := L)
  exact Algebra.trace_localization R (nonZeroDivisors R) x

end Commons.RingTheory.Trace