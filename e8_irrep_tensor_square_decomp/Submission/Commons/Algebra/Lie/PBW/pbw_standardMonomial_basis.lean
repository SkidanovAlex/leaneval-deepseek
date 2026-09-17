import Mathlib.Algebra.Lie.UniversalEnveloping
import Submission.Commons.Algebra.Lie.PBW.standardMonomial_basis

noncomputable section
set_option maxHeartbeats 800000
universe u

namespace Commons.Algebra.Lie.PBW

/-- **Poincaré–Birkhoff–Witt: the standard-monomial basis of the universal enveloping
algebra.**  This is `Commons.Algebra.Lie.PBW.standardMonomial_basis`, proved by a colleague
via `Commons.Algebra.Lie.PBW.standardMonomial_spanning` and
`Commons.Algebra.Lie.PBW.standardMonomial_linearIndependent`. -/
theorem pbw_standardMonomial_basis (K L ι : Type u) [Field K] [CharZero K]
    [LieRing L] [LieAlgebra K L] [LinearOrder ι]
    (e : Module.Basis ι K L) :
    ∃ b : Module.Basis {w : List ι // w.Pairwise (fun a b : ι => a ≤ b)} K
          (UniversalEnvelopingAlgebra K L),
      ∀ w : {w : List ι // w.Pairwise (fun a b : ι => a ≤ b)},
        b w = (w.1.map (fun i => UniversalEnvelopingAlgebra.ι K (e i))).prod := by
  exact Commons.Algebra.Lie.PBW.standardMonomial_basis K L ι e

end Commons.Algebra.Lie.PBW
