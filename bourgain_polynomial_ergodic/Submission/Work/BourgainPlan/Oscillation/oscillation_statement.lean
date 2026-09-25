import Mathlib
import Submission.BourgainPlan.Interfaces
import Submission.Work.BourgainPlan.Oscillation.oscillation_reduction
import Submission.Work.BourgainPlan.Oscillation.oscillation_assembly

/-!  Bourgain's ℓ² oscillation inequality along lacunary sequences.

The statement `Submission.BourgainPlan.OscillationStatement` (Bourgain, *Pointwise ergodic
theorems for arithmetic sets*, IHÉS 69 (1989), (2.14)) is proved here by the reduction
`oscillation_statement_of_sublinear` applied to the analytic core

  `Work.BourgainPlan.Oscillation.lacunary_oscillation_core : SublinearOscillationStatement`

proved in `oscillation_assembly.lean`: the non-negative integer polynomial averages
`discAvg P N g n = N⁻¹ Σ_{k<N} g (n + P(k))` satisfy, along the lacunary scales `⌊ρ^i⌋` and for
every strictly increasing block sequence `k`, the *uniform* (`O(1)` in `J`) block-oscillation bound

  `Σ_{j<J} ∫⁻_n (sup_{k_j ≤ i < k_{j+1}} |discAvg P ⌊ρ^i⌋ g n − discAvg P ⌊k_j⌋ g n|)² ≤ C ∫⁻‖g‖²`,

which is sublinear in `J` and hence implies the `o(J)` inequality; see `STATUS.md` in this
directory for the full circle-method route (major-arc model at arbitrary scales, the sharp
core/weighted-neighbourhood maximal, the profile error, the `ℕ → ℤ` transfer, and the
degree-`≤ 1` case). -/

namespace Work.BourgainPlan.Oscillation

/-- Bourgain's ℓ² oscillation inequality along lacunary sequences; see `Submission/BourgainPlan/Interfaces.lean`. -/
theorem oscillation_statement : Submission.BourgainPlan.OscillationStatement :=
  oscillation_statement_of_sublinear lacunary_oscillation_core

end Work.BourgainPlan.Oscillation
