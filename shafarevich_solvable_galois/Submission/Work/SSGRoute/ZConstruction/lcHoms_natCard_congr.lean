import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Field.ZMod
import Mathlib.Topology.LocallyConstant.Basic
import Submission.Work.SSGRoute.ZConstruction.levelK_kummerCharHom_dictionary
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `lcHoms` is invariant under a topological group isomorphism

`Work.SSGRoute.lcHoms p Γ` is the group of *locally constant* monoid characters `Γ →* 𝔽_p`.
Composing with a topological group isomorphism `e : Γ ≃* Γ'` (continuous, with continuous inverse)
is a bijection `lcHoms p Γ ≃ lcHoms p Γ'`.

This is the transport step of the level-`K` local Kummer count: it moves the count
`Work.SSGRoute.PTembedding.lcHoms_localUnits` -- `|lcHoms p G_κ| = |κˣ ⧸ (κˣ)^p|` for the absolute
Galois group `G_κ` of the completion `κ = 𝔭.adicCompletion ↥K` -- to the level-`K` local group
`↥(decomp (k := ↥K) A)`, along the canonical identification
`decomp (k := ↥K) A ≃* Gal(κ̄/κ)` (`NK.Mine.localGaloisEquiv`, a homeomorphism by
`NK.Mine.isHomeomorph_...`; the composite with the base change `decompEquiv_fok` is the
`e₁.trans e₂` of the proof of `Work.SSGRoute.finite_openKernel_homs_decomp_kernel`).
-/

open scoped Pointwise

namespace Work.SSGRoute.ZConstruction

/-- **A topological group isomorphism induces a bijection of locally constant characters**: hence
an equality of cardinalities. -/
theorem natCard_lcHoms_congr (p : ℕ) [Fact p.Prime] {Γ Γ' : Type} [Group Γ] [TopologicalSpace Γ]
    [Group Γ'] [TopologicalSpace Γ'] (e : Γ ≃* Γ')
    (he : Continuous (e : Γ → Γ')) (he' : Continuous (e.symm : Γ' → Γ)) :
    Nat.card ↥(Work.SSGRoute.lcHoms p Γ) = Nat.card ↥(Work.SSGRoute.lcHoms p Γ') := by
  refine Nat.card_congr (Equiv.subtypeEquiv ?_ ?_)
  · refine { toFun := fun χ => χ.comp e.symm.toMonoidHom
             invFun := fun ξ => ξ.comp e.toMonoidHom
             left_inv := fun χ => by ext g; simp
             right_inv := fun ξ => by ext g; simp }
  · intro χ
    constructor
    · intro hχ
      have h1 : IsLocallyConstant ((χ : Γ →* Multiplicative (ZMod p)) ∘ (e.symm : Γ' → Γ)) :=
        hχ.comp_continuous he'
      exact h1
    · intro hχ
      have h1 : IsLocallyConstant
          (((χ.comp e.symm.toMonoidHom : Γ' →* Multiplicative (ZMod p))) ∘ (e : Γ → Γ')) :=
        hχ.comp_continuous he
      have h2 : ((χ.comp e.symm.toMonoidHom : Γ' →* Multiplicative (ZMod p))) ∘ (e : Γ → Γ') =
          (χ : Γ → Multiplicative (ZMod p)) := by
        funext g
        simp
      rwa [h2] at h1

end Work.SSGRoute.ZConstruction
