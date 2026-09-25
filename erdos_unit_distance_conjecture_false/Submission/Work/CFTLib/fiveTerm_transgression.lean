import Mathlib
import Submission.Work.CFTLib.fiveTerm_exact
import Submission.Work.CFTLib.fiveTerm_candFun_mem_Z2
import Submission.Work.CFTLib.fiveTerm_precomp_candFun_eq
import Submission.Work.CFTLib.fiveTerm_exists_candFun_sub_mem_B2
import Submission.Work.CFTLib.fiveTerm_candFun_mem_B2_iff

/-!
# The transgression `H¹(N,𝔽_p)^{G'} → H²(G,𝔽_p)`

Assembling the vocabulary of `fiveTerm_setup`/`fiveTerm_exact` with the cocycle computations
`fiveTerm_candFun_mem_Z2` (the transgression cocycle is a cocycle), `fiveTerm_precomp_candFun_eq`
(its inflation is a coboundary), `fiveTerm_exists_candFun_sub_mem_B2` (every cocycle whose
inflation is a coboundary differs from a transgression cocycle by a coboundary) and
`fiveTerm_candFun_mem_B2_iff` (the transgression cocycle is a coboundary iff the character is a
restriction), this file defines the transgression and proves the two exactness statements of the
five-term sequence:

* `range_transgression_eq_ker_infl`: `im(transgression) = ker(inf)`;
* `ker_transgression_eq_range_beta`: `ker(transgression) = im(beta)`.

It also records `finrank_H1_eq`: `dim H¹(G,𝔽_p) = dim Hom(G,𝔽_p)`.
-/

namespace Work.CFTLib

open CategoryTheory Representation groupCohomology
open scoped Classical

noncomputable section

variable (p : ℕ) [Fact p.Prime] {G G' : Type} [Group G] [Group G']

/-- The cocycle property of the transgression cocycle, as the argument of `Psi`. -/
abbrev candMembership (π : G' →* G) (hπ : Function.Surjective π) :
    ∀ t : invCharSubmodule p π.ker, candFun π hπ t ∈ Z2 p G :=
  fun t => fiveTerm_candFun_mem_Z2 π hπ t

/-- **The transgression** `H¹(N,𝔽_p)^{G'} → H²(G,𝔽_p)`, `t ↦ [candFun t]`. -/
abbrev transgression (π : G' →* G) (hπ : Function.Surjective π) :
    invCharSubmodule p π.ker →ₗ[ZMod p] H2 p G :=
  Psi p π hπ (candMembership p π hπ)

/-- `H¹(G,𝔽_p)` and the space of additive characters of `G` have the same dimension. -/
lemma finrank_H1_eq (G : Type) [Group G] [Fintype G] :
    Module.finrank (ZMod p) (H1 p G) = Module.finrank (ZMod p) (Additive G →+ ZMod p) :=
  LinearEquiv.finrank_eq
    (groupCohomology.H1IsoOfIsTrivial (Rep.trivial (ZMod p) G (ZMod p))).toLinearEquiv

/-- **Exactness at the transgression**: the range of the transgression is the kernel of the
inflation. -/
lemma range_transgression_eq_ker_infl (π : G' →* G) (hπ : Function.Surjective π) :
    LinearMap.range (transgression p π hπ) = LinearMap.ker (inflMap p π) :=
  le_antisymm
    (range_Psi_le_ker_infl p π hπ (candMembership p π hπ)
      (fun t => fiveTerm_precomp_candFun_eq π hπ t))
    (ker_infl_le_range_Psi p π hπ (candMembership p π hπ)
      (fun z hz b hb => fiveTerm_exists_candFun_sub_mem_B2 π hπ z hz b hb))

/-- **Exactness at `H¹(N,𝔽_p)^{G'}`**: the kernel of the transgression is the range of the
restriction map. -/
lemma ker_transgression_eq_range_beta (π : G' →* G) (hπ : Function.Surjective π) :
    LinearMap.ker (transgression p π hπ) = LinearMap.range (beta (p := p) π) :=
  ker_Psi_eq_range_beta p π hπ (candMembership p π hπ)
    (fun t => fiveTerm_candFun_mem_B2_iff π hπ t)

/-- **Rank–nullity for the restriction map on characters.** -/
lemma finrank_eq_ker_add_range_beta [Fintype G'] (π : G' →* G) :
    Module.finrank (ZMod p) (Additive G' →+ ZMod p)
      = Module.finrank (ZMod p) (LinearMap.ker (beta (p := p) π))
        + Module.finrank (ZMod p) (LinearMap.range (beta (p := p) π)) := by
  haveI : Module.Finite (ZMod p) (Additive G' →+ ZMod p) := by
    have := finiteDimensional_addHom (p := p) (G := G'); infer_instance
  have h := @LinearMap.quotKerEquivRange (ZMod p) (Additive G' →+ ZMod p)
    (invCharSubmodule p π.ker) _ _ _ _ _ (beta (p := p) π)
  have hiso := LinearEquiv.finrank_eq h
  have hrn := Submodule.finrank_quotient_add_finrank (LinearMap.ker (beta (p := p) π))
  omega

/-- **Rank–nullity for the transgression.** -/
lemma finrank_eq_ker_add_range_transgression [Fintype G'] (π : G' →* G)
    (hπ : Function.Surjective π) :
    Module.finrank (ZMod p) (invCharSubmodule p π.ker)
      = Module.finrank (ZMod p) (LinearMap.ker (transgression p π hπ))
        + Module.finrank (ZMod p) (LinearMap.range (transgression p π hπ)) := by
  haveI : Module.Finite (ZMod p) ↥(invCharSubmodule p π.ker) := by
    have := finiteDimensional_invCharSubmodule (p := p) (N := π.ker); infer_instance
  have hrn := @Submodule.finrank_quotient_add_finrank (R := ZMod p)
    (M := ↥(invCharSubmodule p π.ker)) _ _ _ _ _ _
    (LinearMap.ker (transgression p π hπ))
  have h := @LinearMap.quotKerEquivRange (ZMod p) (↥(invCharSubmodule p π.ker)) (H2 p G) _ _ _ _ _
    (transgression p π hπ)
  have hiso := LinearEquiv.finrank_eq h
  omega

end

end Work.CFTLib
