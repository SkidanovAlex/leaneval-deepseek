import Mathlib
import Submission.Work.CFT.Kummer.Hypotheses
import Submission.Work.Tower.Shafarevich.Cohomology.finrank_H1Fp_eq_finrank_hom

namespace Work.CFT.Kummer

/-- Precomposition with a multiplicative equivalence `G ≃* H` is a `ZMod p`-linear
equivalence between the homomorphism spaces `Hom(G, 𝔽_p)` and `Hom(H, 𝔽_p)`. -/
noncomputable def homPrecompLinearEquiv {p : ℕ} {G H : Type} [Group G] [Group H] (e : G ≃* H) :
    (Additive G →+ ZMod p) ≃ₗ[ZMod p] (Additive H →+ ZMod p) where
  toFun f := f.comp e.toAdditive.symm.toAddMonoidHom
  map_add' f g := rfl
  map_smul' r f := rfl
  invFun f := f.comp e.toAdditive.toAddMonoidHom
  left_inv f := by
    ext x
    simp
  right_inv f := by
    ext x
    simp

/-- `H¹(G, 𝔽_p)` with trivial coefficients has the same `𝔽_p`-rank as `H¹(H, 𝔽_p)` when
`G ≃* H`: both are the ranks of the homomorphism spaces into `𝔽_p`, which are identified by
precomposition with the isomorphism. -/
theorem finrank_H1Fp_mulEquiv {p : ℕ} {G H : Type} [Group G] [Group H] (e : G ≃* H) :
    Module.finrank (ZMod p) (Work.CFT.Kummer.H1Fp p G) =
      Module.finrank (ZMod p) (Work.CFT.Kummer.H1Fp p H) :=
  (Work.Tower.Shafarevich.Cohomology.finrank_H1Fp_eq_finrank_hom p G).trans
    ((LinearEquiv.finrank_eq (homPrecompLinearEquiv e)).trans
      (Work.Tower.Shafarevich.Cohomology.finrank_H1Fp_eq_finrank_hom p H).symm)

end Work.CFT.Kummer
