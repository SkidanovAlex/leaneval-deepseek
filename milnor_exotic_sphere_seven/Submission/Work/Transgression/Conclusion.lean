import Submission.Work.Transgression.Gysin
import Submission.Work.Transgression.PuncturedCohCardAll

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# SUBPROJECT TRANSGRESSION: the deliverable

The whole chapter assembled: `Work.Transgression.PuncturedCohCardAll` (the Mayer–Vietoris /
transgression computation of `H⁴` of the punctured total space of `clutchBundle a b`) fed into the
Gysin reduction `Work.Transgression.EulerClutch_of_puncturedCohCard` gives **the deliverable**

`Work.Agree.EulerClutch` — for every `a b : ℤ` and every Thom class `T` of `clutchBundle a b`,

  `π^*(T.eulerClass) = (a+b) • Work.Milnor.tauD`  or  `= -((a+b) • Work.Milnor.tauD)`.
-/

namespace Work.Transgression

open Work.TangentClasses

noncomputable section

/-- **THE DELIVERABLE, unconditionally.**  The Euler class of the rank-`4` real bundle
`clutchBundle a b` over `S⁴` (clutching `v ↦ qᵃ·v·qᵇ`) is `± (a + b)` times the generator, i.e.
the transgression theorem in the form the paper's core theorem consumes. -/
theorem EulerClutch : Work.Agree.EulerClutch :=
  EulerClutch_of_puncturedCohCard PuncturedCohCardAll

end

end Work.Transgression
