import Mathlib
import Submission.Work.CFT.Kummer.Hypotheses

namespace Work.CFT.Kummer
/-- `H²(G, 𝔽_p)` with trivial coefficients has the same `𝔽_p`-rank as `H²(H, 𝔽_p)` when
`G ≃* H` (group cohomology is invariant under isomorphism of the group). -/
theorem finrank_H2Fp_mulEquiv {p : ℕ} {G H : Type} [Group G] [Group H] (e : G ≃* H) :
    Module.finrank (ZMod p) (Work.CFT.Kummer.H2Fp p G) =
      Module.finrank (ZMod p) (Work.CFT.Kummer.H2Fp p H) := by
  exact (groupCohomology.mapIso e (LinearEquiv.refl (ZMod p) (ZMod p))
    (fun g => by simp [Representation.trivial]) 2).toLinearEquiv.finrank_eq

end Work.CFT.Kummer
