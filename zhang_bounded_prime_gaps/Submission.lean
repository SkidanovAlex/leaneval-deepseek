import Mathlib
import Lake.Toml
import Lake.Util.Message
import Lean
import Submission.BoundedGaps
import Submission.FinalAssembly

open Filter Finset MeasureTheory
open scoped BigOperators Topology

namespace Submission

/--
The deep sieve ingredient of the Maynard--Polymath8 proof, exactly the claim
`DHL[50, 2]` of Polymath8a, "Variants of the Selberg sieve", Theorem 3.2(i):
every admissible 50-tuple has arbitrarily large translates with at least two
prime values.  Combined with the admissible 50-tuple `BoundedGaps.h50` of
diameter 246 (Polymath8a, Figure 1) this yields `H₁ ≤ 246`.

The proof is the Maynard multidimensional Selberg sieve: the Bombieri--Vinogradov
theorem (level of distribution `ϑ = 1/2 - 10⁻⁶`, `Submission/LevelOfDistribution.lean`
and `Submission/BVFinal.lean`), the Polymath8 variational certificate
`M_{50,1/25} > 4` (`Submission/CertMkEps.lean` and the certificate chapters), the
continuity/smoothing chapter (`Submission/CertSmoothRescale.lean`), the tensor
localisation and the `§5.3` `hkey` machinery (`Submission/SieveCertificate.lean`,
`Submission/TensorThinFull.lean`), and the final assembly
`Commons.NumberTheory.MaynardSieve.DHL_fifty` in `Submission/FinalAssembly.lean`.
Everything is proved in this workspace.  The endgame reduction
(admissibility of `h50`, the passage from a translate with two prime values to a
prime gap `≤ 246`) is contained in `Submission.BoundedGaps`.
-/
lemma maynard_DHL50 : BoundedGaps.DHL 50 :=
  Commons.NumberTheory.MaynardSieve.DHL_fifty

theorem zhang_bounded_prime_gaps :
    ∀ n : ℕ, ∃ p q : ℕ, n ≤ p ∧ p.Prime ∧ q.Prime ∧ p < q ∧ q - p ≤ 246 := by
  exact BoundedGaps.boundedPrimeGaps_of_DHL50 maynard_DHL50

end Submission
