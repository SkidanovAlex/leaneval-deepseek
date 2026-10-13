import Submission.Work.DSMap.Mix
import Submission.Work.DSPB1.Basic

/-!
# DSPB1 — the area theorem: ϖ-flatness of a perfectoid ring (`PB1`)

This file contains the deliverable of the subproject `DSPB1`:

  `DSMap.Mix.perfectoid_varpiFlat_proved`

whose statement is *identical* (up to universe names) to the frozen interface
`DSMap.Mix.perfectoid_varpiFlat` of the read-only file `Submission/Work/DSMap/Mix.lean`
(the `PB1` node of `sources/dsmap/direct_summand_mix_design.md`):

> for a `p`-torsion-free `p`-adically complete ring `C` with pseudo-uniformizer data
> `P : DSMap.PerfectoidData p C` there is an element `ϖf` of the tilt `PreTilt C p = Perfection (C ⧸ (p)) p`
> whose Teichmüller untilt is *exactly* `P.ϖ 0`.

The proof is `⟨Work.DSPB1.varpiTilt P, Work.DSPB1.varpiTilt_untilt P⟩`, where `varpiTilt P` is
the compatible system `n ↦ ϖ_n mod p` and `varpiTilt_untilt` computes its untilt through
`Perfection.teichmuller_spec` (see `Submission/Work/DSPB1/Basic.lean` for the mathematics).

`Work.DSPB1.perfectoid_varpiFlat_proved` is a plain alias, so that a consumer who only knows the
area directory `Submission.Work.DSPB1` finds the theorem under the area namespace as well.
-/

namespace DSMap.Mix

universe a

/-- **PB1 (ϖ-flatness), proved.**  The compatible system `(ϖ_n mod p)_n ∈ PreTilt C p` of
`Work.DSPB1.varpiTilt` has Teichmüller untilt exactly `ϖ_0`.  Statement identical to the frozen
`DSMap.Mix.perfectoid_varpiFlat`. -/
theorem perfectoid_varpiFlat_proved (p : ℕ) [Fact p.Prime] (C : Type a) [CommRing C]
    (P : PerfectoidData p C) [Fact ¬IsUnit (p : C)] :
    letI := P.complete
    ∃ ϖf : PreTilt C p, PreTilt.untilt ϖf = P.ϖ 0 :=
  ⟨Work.DSPB1.varpiTilt P, Work.DSPB1.varpiTilt_untilt P⟩

/-- the proved statement (type and proof) is definitionally the frozen declaration
`DSMap.Mix.perfectoid_varpiFlat`; this also checks that universes and instance binders agree
(Lean unifies the universe metavariables here) -/
example : @DSMap.Mix.perfectoid_varpiFlat_proved = @DSMap.Mix.perfectoid_varpiFlat := rfl

end DSMap.Mix

namespace Work.DSPB1

universe a

/-- Area-namespace alias of `DSMap.Mix.perfectoid_varpiFlat_proved` (`PB1`, ϖ-flatness). -/
theorem perfectoid_varpiFlat_proved (p : ℕ) [Fact p.Prime] (C : Type a) [CommRing C]
    (P : DSMap.PerfectoidData p C) [Fact ¬IsUnit (p : C)] :
    letI := P.complete
    ∃ ϖf : PreTilt C p, PreTilt.untilt ϖf = P.ϖ 0 :=
  DSMap.Mix.perfectoid_varpiFlat_proved p C P

end Work.DSPB1
