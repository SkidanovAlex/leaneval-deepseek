import Mathlib
import Submission.Work.DSM4p.Plan
import Submission.Work.DSPB2.Main

/-!
# DSM4p — every element of `B` is `♯`-lifted modulo `p` from the tilt

For `Q : DSMap.PerfectoidData p B` and any `x : B` there is `xb : PreTilt B p` with
`♯ xb ≡ x mod p` (`♯ = PreTilt.untilt`).  This is the "PB2 dictionary" input of step (3) of the
Route U plan (`Submission/Work/DSM4p/Plan.lean`).

The proof is a direct application of the surjectivity of the `0`-th coefficient
`PreTilt.coeff 0 : PreTilt B p →+* B ⧸ (p)` — which holds because the Frobenius of `B ⧸ (p)` is
surjective (`Q.frobSurj`), see `Work.DSPB2.coeff_zero_surjective` — together with Mathlib's
`PreTilt.mk_untilt_eq_coeff_zero`.
-/

universe a

namespace Work.DSM4p

theorem exists_untilt_lift {p : ℕ} [Fact p.Prime] {B : Type a} [CommRing B]
    [Fact (¬ IsUnit (p : B))] [IsAdicComplete (Ideal.span {(p : B)}) B]
    (Q : DSMap.PerfectoidData p B) (x : B) :
    ∃ xb : PreTilt B p, PreTilt.untilt xb - x ∈ Ideal.span {(p : B)} := by
  obtain ⟨xb, hxb⟩ :=
    Work.DSPB2.coeff_zero_surjective p B Q
      (Ideal.Quotient.mk (Ideal.span {(p : B)}) x)
  refine ⟨xb, ?_⟩
  have h : Ideal.Quotient.mk (Ideal.span {(p : B)}) (PreTilt.untilt xb - x) = 0 := by
    rw [map_sub, PreTilt.mk_untilt_eq_coeff_zero, hxb, sub_self]
  exact Ideal.Quotient.eq_zero_iff_mem.mp h

end Work.DSM4p
