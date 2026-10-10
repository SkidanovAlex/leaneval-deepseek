import Mathlib
import Submission.Work.CY3Stab.Variety
import Submission.Work.CY3.isoOver_stronglyBirational
import Submission.Work.K3Inputs.affineN_prodOver_iso

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CY3Stab.Prod.stronglyBirational_wProd_affine`

The identification `𝔸ᵏ × 𝔸⁵ ≅ 𝔸^{k+5}` of the stabilisation step of Lin–Shinder's proof of
`thm:bir-generation` (c), in the vocabulary of strong birationality: the cylinder
`Work.CY3Stab.WProd (𝔸⁵) k = 𝔸ᵏ ×_{Spec 𝕜} 𝔸⁵` is *strongly birational* to affine `(k+5)`-space
`Work.CY3.Affine 𝕜 (k + 5) = 𝔸^{k+5}`.

This is the interface hypothesis `hBC` of `Submission/Work/CY3Stab/Main.lean` (see
`Submission/Work/CY3Stab/NOTES.md` §4): it transports a non-vanishing invariant coefficient of a
Cremona map of `𝔸ᵏ × 𝔸⁵` to one of `𝔸^{k+5}` along the transport `Work.CY3.transportCr`
(`Work.CY3.cInv_transport_eq_of_eq_zero`).

The proof is the isomorphism route: `Work.K3Inputs.affineN_prodOver_iso 𝕜 k 5` provides
`𝔸ᵏ ×_{Spec 𝕜} 𝔸⁵ ≅ 𝔸^{k+5}` *over* `Spec 𝕜` (in the `Work.K3.prodOver` presentation of the
fibre product, which is the presentation `Work.CY3Stab.WProd` uses), and an isomorphism over `𝕜`
is a strong birationality (`Work.CY3.isoOver_stronglyBirational`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.CY3Stab.Prod

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

/-- **The cylinder over `𝔸⁵` is strongly birational to `𝔸^{k+5}`.**

`𝔸ᵏ ×_{Spec 𝕜} 𝔸⁵` and `𝔸^{k+5}` are isomorphic over `Spec 𝕜`
(`Work.K3Inputs.affineN_prodOver_iso`), and an isomorphism over the base is a strong
birationality (`Work.CY3.isoOver_stronglyBirational`), i.e. a birational map over `Spec 𝕜` all of
whose invariant coefficients vanish. -/
theorem stronglyBirational_wProd_affine (𝕜 : Type) [Field 𝕜] (k : ℕ) :
    @Work.CY3.StronglyBirational 𝕜 _
      (Work.CY3Stab.WProd (𝕜 := 𝕜) (Work.CY3.Affine 𝕜 5) k)
      (Work.CY3.Affine 𝕜 (k + 5))
      (Work.CY3Stab.varietyWProd (𝕜 := 𝕜) (Work.CY3.Affine 𝕜 5) k)
      (inferInstance : MotivicInvariants.Variety 𝕜 (Work.CY3.Affine 𝕜 (k + 5))) := by
  -- The cylinder `𝔸ᵏ × 𝔸⁵` is a variety: the `Variety` structure is the pinned one
  -- `Work.CY3Stab.varietyWProd` (whose `over` field is `wProdOver …`), installed locally so
  -- that `IsoOver`/`StronglyBirational` are elaborated with exactly the instances of the goal.
  letI hV : Variety 𝕜 (Work.CY3Stab.WProd (𝕜 := 𝕜) (Work.CY3.Affine 𝕜 5) k) :=
    Work.CY3Stab.varietyWProd (𝕜 := 𝕜) (Work.CY3.Affine 𝕜 5) k
  -- `𝔸ᵏ ×_{Spec 𝕜} 𝔸⁵ ≅ 𝔸^{k+5}` over `Spec 𝕜`.
  obtain ⟨e, he⟩ := Work.K3Inputs.affineN_prodOver_iso 𝕜 k 5
  exact Work.CY3.isoOver_stronglyBirational ⟨e, he⟩

end

end Work.CY3Stab.Prod
