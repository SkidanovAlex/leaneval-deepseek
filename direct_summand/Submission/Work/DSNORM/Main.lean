import Submission.Work.DSNORM.Integral
import Submission.Work.DSMap.Gaps

/-!
# DSNORM — main theorem: a regular local ring is integrally closed

The deliverable of the area DSNORM is `DSMap.Gaps.area_NORM_proved`, a proof of the frozen node
`DSMap.Gaps.area_NORM`:

`theorem area_NORM (A : Type a) [CommRing A] [IsRegularLocalRing A] : IsIntegrallyClosed A`

The proof goes through the initial-form (associated graded) theory of a regular local ring:

* `Work.DSNORM.params A` is a regular system of parameters of `𝔪`, of size `nParams A = dim A`;
* `Work.DSNORM.inForm A a ∈ k[X₁,…,X_d]` is the initial form of `a`, and
  `Work.DSNORM.inForm_mul`/`Work.DSNORM.ord_mul` say that it is multiplicative
  (this uses `Work.DSNORM.regularSequence_quasiRegular`, i.e. quasi-regularity of a regular
  sequence, Stacks 00LN, and `Work.DSNORM.params_regularSequence`);
* for an integral element `a / b` the integrality relation forces `inForm b ∣ inForm a`
  (`Work.DSNORM.inForm_dvd_of_isIntegral`), whence `b ∣ a` by successive approximation and Krull's
  intersection theorem (`Work.DSNORM.dvd_of_isIntegral`);
* summing up, `Work.DSNORM.isIntegrallyClosed_of_isRegularLocalRing : IsIntegrallyClosed A`.

See `Submission/Work/DSNORM/NOTES.md` for the full description of the area.
-/

namespace DSMap.Gaps

universe a

/-- **NORM**: a regular local ring is integrally closed (same statement as the frozen
`DSMap.Gaps.area_NORM`). -/
theorem area_NORM_proved (A : Type a) [CommRing A] [IsRegularLocalRing A] : IsIntegrallyClosed A :=
  Work.DSNORM.isIntegrallyClosed_of_isRegularLocalRing A

end DSMap.Gaps
