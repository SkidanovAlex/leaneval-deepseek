import Mathlib
import Submission.Work.Tower.Shafarevich.Defs

namespace Work.Tower.Shafarevich.Cohomology

/-- The first group cohomology `H¹(G, 𝔽_p)` with trivial coefficients is the space of
group homomorphisms `G → 𝔽_p`, so their `𝔽_p`-dimensions agree.  This is the linear
equivalence underlying Mathlib's `groupCohomology.H1IsoOfIsTrivial`. -/
theorem finrank_H1Fp_eq_finrank_hom (p : ℕ) (G : Type) [Group G] :
    Module.finrank (ZMod p) (Work.Tower.Shafarevich.H1Fp p G) =
      Module.finrank (ZMod p) (Additive G →+ ZMod p) :=
  LinearEquiv.finrank_eq
    (groupCohomology.H1IsoOfIsTrivial (Rep.trivial (ZMod p) G (ZMod p))).toLinearEquiv

end Work.Tower.Shafarevich.Cohomology
