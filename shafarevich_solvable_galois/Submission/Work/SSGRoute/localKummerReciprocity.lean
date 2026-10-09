import Mathlib
import Submission.NK.LocalAnabelian.Kummer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Lane (a): the reciprocity/Kummer statement `(R)` over a completion

This is the arithmetic statement the `Ext`-side computation of E7a consumes.  For a finite place `q`
of `K` (so `L := q.adicCompletion K = Place.localField K (Place.ofFinite q)` is the local field whose
units are the module `localUnitsK` of the statement), the Kummer class group

  `KummerGroup p L = Lˣ ⧸ (Lˣ)^p`

is the Pontryagin dual of the maximal elementary `p`-abelian quotient of the absolute Galois group
`Γ_L = (AlgebraicClosure L) ≃ₐ[L] (AlgebraicClosure L)`, i.e. of the continuous characters
`Γ_L → 𝔽_p`.  Because both sides are elementary abelian `p`-groups of the same order (Kummer theory
plus local Tate duality in degree `1`, i.e. `(b)`/`(02)`), the *existence* of the isomorphism is the
content: this is the "local field units modulo `p`-th powers ↔ H¹ of the local group" bridge of the
design's route.

Formal choices (settled here):

* `Γ_L` carries Mathlib's Krull topology (`krullTopology L (AlgebraicClosure L)`), the same
  convention as the rest of `SSGRoute` (`SSGRoute.IsLocConstOn` is Mathlib's `IsLocallyConstant` on
  the whole group, cf. `bridge_isLocConstOn_top_of_isLocallyConstant`);
* the characters are written `Γ_L →* Multiplicative (ZMod p)` (monoid homs into the multiplicative
  copy of `𝔽_p`), because `Γ_L` is multiplicative while `KummerGroup` is a quotient *group*; the
  continuous ones form the `Subgroup` `lcHoms p Γ_L` below;
* everything is at universe `0`, like the rest of NK's local layer (`Place : (K : Type) → … → Type`).

Ingredients for the proof, already on disk: `NK.LocalAnabelian.kummerCorrespondence` /
`KummerGroup` (Kummer side) and `NK.NUV2.kernelCondition_all_of_reciprocityLaw` (reciprocity at
completions, in kernel form — sorry-free), together with the finiteness/dimension input `(02)`.
-/

namespace Work.SSGRoute

/-- The locally constant (equivalently: continuous) characters `Γ → 𝔽_p`, as a subgroup of the group
of all monoid homomorphisms `Γ →* Multiplicative (ZMod p)`. -/
def lcHoms (p : ℕ) [Fact p.Prime] (Γ : Type*) [Group Γ] [TopologicalSpace Γ] :
    Subgroup (Γ →* Multiplicative (ZMod p)) where
  carrier := {χ | IsLocallyConstant χ}
  one_mem' := IsLocallyConstant.const 1
  mul_mem' := fun hχ hψ => hχ.mul hψ
  inv_mem' := fun hχ => hχ.inv

end Work.SSGRoute
