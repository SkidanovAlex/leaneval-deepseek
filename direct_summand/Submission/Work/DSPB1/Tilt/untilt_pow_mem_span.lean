import Mathlib
import Submission.Work.DSMap.Map
import Submission.Work.DSPB1.Basic

set_option linter.style.haveILetI false

namespace Work.DSPB1.Tilt

/-- `untilt` is a monoid homomorphism, so it commutes with the `p`-th power; by PB1
(`varpiTilt_untilt`) `untilt (varpiTilt P) = ϖ_0`, and `ϖ_0 ^ p = p · v` for a unit `v`. -/
theorem untilt_pow_mem_span {p : ℕ} [Fact p.Prime] {C : Type*} [CommRing C]
    [Fact ¬IsUnit (p : C)] (P : DSMap.PerfectoidData p C) :
    (letI := P.complete; PreTilt.untilt (Work.DSPB1.varpiTilt P ^ p)) ∈ Ideal.span {(p : C)} := by
  letI := P.complete
  rw [map_pow, Work.DSPB1.varpiTilt_untilt]
  obtain ⟨v, hv⟩ := P.unit
  rw [hv]
  exact Ideal.mul_mem_right (v : C) (Ideal.span {(p : C)}) (Ideal.mem_span_singleton_self (p : C))

end Work.DSPB1.Tilt
