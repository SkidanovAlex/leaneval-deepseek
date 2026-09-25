import Mathlib
import Submission.Work.CFTLib.splitsCompletelySet
import Submission.Work.CFTLib.splitSetOf_density
import Submission.Work.Tower.Unramified.splitsCompletelyIn_of_NF
import Submission.Work.Tower.Unramified.splitsCompletelyInNF_of_ramification_inertia

open NumberField

set_option linter.style.haveILetI false

namespace Work.CFTLib

/-- **A prime with ramification index one and inertia degree one splits completely.**  If `L/K` is
finite Galois and the (well defined) ramification index and inertia degree of `v` in `L` are both
`1`, then `v` splits completely in `L`: every prime of `𝓞 L` above `v` is unramified with trivial
residue extension, so the fundamental identity `∑ e·f = [L : K]` produces exactly `[L : K]`
completely split primes above `v`. -/
theorem splitsCompletelyIn_of_ramificationIdxIn_eq_one_of_inertiaDegIn_eq_one {K A : Type*}
    [Field K] [NumberField K] [Field A] [NumberField A] [Algebra K A]
    (L : IntermediateField K A) [FiniteDimensional K L] [IsGalois K ↥L]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (he : v.asIdeal.ramificationIdxIn (NumberField.RingOfIntegers ↥L) = 1)
    (hf : Ideal.inertiaDegIn v.asIdeal (NumberField.RingOfIntegers ↥L) = 1) :
    Work.Tower.SplitsCompletelyIn K ↥L v.asIdeal := by
  refine Work.Tower.Unramified.splitsCompletelyIn_of_NF v.isPrime v.ne_bot ?_
  refine Work.Tower.Unramified.splitsCompletelyInNF_of_ramification_inertia v.isPrime ?_
  intro P
  haveI := P.2.1
  haveI := P.2.2
  refine ⟨?_, ?_⟩
  · rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (A := NumberField.RingOfIntegers K)
      (B := NumberField.RingOfIntegers ↥L) v.asIdeal P.1 Gal(↥L/K), he]
  · rw [← Ideal.inertiaDegIn_eq_inertiaDeg (A := NumberField.RingOfIntegers K)
      (B := NumberField.RingOfIntegers ↥L) v.asIdeal P.1 Gal(↥L/K), hf]

theorem finite_sdiff_inertiaDegIn_splitsCompletelySet {K A : Type*} [Field K] [NumberField K]
    [Field A] [NumberField A] [Algebra K A] (L : IntermediateField K A) [FiniteDimensional K L]
    [IsGalois K ↥L] :
    ({v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) |
        Ideal.inertiaDegIn v.asIdeal (NumberField.RingOfIntegers ↥L) = 1} \
          splitsCompletelySet L).Finite := by
  classical
  refine (finite_setOf_ramificationIdxIn_ne_one (K := K) (L := ↥L)).subset ?_
  intro v hv
  rw [Set.mem_sdiff] at hv
  obtain ⟨hf, hspl⟩ := hv
  intro he
  exact hspl ((mem_splitsCompletelySet L v).mpr
    (splitsCompletelyIn_of_ramificationIdxIn_eq_one_of_inertiaDegIn_eq_one L v he hf))

end Work.CFTLib
