/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The division closure of `K[G]` as a rational `Kˣ × G`-semiring

[JZLA20, §4.3]: the division closure `D = D_{K[G],U}` of `φ(K[G])` in `U` is a rational
`Kˣ × G`-semiring, with `smul (λ,g) x = φ(λ·g) · x`, `smulRight x (λ,g) = x · φ(λ·g)` and
`x⋄ = x⁻¹` if `x` is a unit of `D` (and `0` otherwise).  This is the structure from which the
universal morphism `Φ : Rat(Kˣ × G) →+* D` of [JZLA20, Lemma 4.2] is defined, and it is what makes
the `G`-complexity `Tree_G` of [JZLA20, §4.3] available in the proof of [JZLA20, Theorem 6.1].

The structure itself (and the three structural identities pinned below) is produced by
`Section6/exists_ratStruct.lean`; here it is packaged as `ratStruct` together with the universal
morphism `Phi` and its basic properties.

The key point of the construction is that `⋄` is *inversion on the units*: hence the image of `Φ`
is closed under inverses of its units, and — since it is a subring containing `φ(K[G])` — an
induction on the division-closure chain shows that `Φ` is **surjective** onto `D`
([JZLA20, Lemma 4.2], [Sthesis, Examples 5.37, 5.38]).  Surjectivity is exactly the existence
clause of `Prop51Data.treeH_spec`, so this file (with `Section6/Phi_surjective.lean`) is the bridge
from the envelope data of [JZLA20, Theorem 6.1] to the data of [JZLA20, Proposition 5.1].
-/
import Mathlib
import Submission.Work.ORHughesFree.Section6.ClosureBasic
import Submission.Work.ORHughesFree.Section6.exists_ratStruct
import Submission.Work.ORHughesFree.Rat.OfGroup

set_option autoImplicit false

namespace Work.ORHughesFree

variable {K : Type} [Field K] {G : Type} [Group G] {U : Type} [Ring U]

/-- **[JZLA20, §4.3]**: the division closure of `φ(K[G])` in `U`, with its structure of rational
`Kˣ × G`-semiring.  The rational operation is `x⋄ = x⁻¹` on the units of the division closure and
`x⋄ = 0` otherwise, and the two actions are multiplication by the images `φ(λ·g)`. -/
noncomputable def ratStruct (φ : MonoidAlgebra K G →+* U) :
    RationalUSemiring (Kˣ × G) ↥(divisionClosure (Set.range φ)) :=
  (Section6.exists_ratStruct φ).choose

/-- The left action is multiplication by the image under `φ` of the group-like unit `λ·g`. -/
theorem ratStruct_smul (φ : MonoidAlgebra K G →+* U) (u : Kˣ × G)
    (x : ↥(divisionClosure (Set.range φ))) :
    ↑((ratStruct φ).smul u x) = φ (unitOf u) * ↑x :=
  (Section6.exists_ratStruct φ).choose_spec.1 u x

/-- The right action is multiplication by the image under `φ` of the group-like unit `λ·g`. -/
theorem ratStruct_smulRight (φ : MonoidAlgebra K G →+* U)
    (x : ↥(divisionClosure (Set.range φ))) (u : Kˣ × G) :
    ↑((ratStruct φ).smulRight x u) = ↑x * φ (unitOf u) :=
  (Section6.exists_ratStruct φ).choose_spec.2.1 x u

/-- The rational operation is inversion on the units of the division closure, and `0` otherwise. -/
theorem ratStruct_ratOp (φ : MonoidAlgebra K G →+* U) (x : ↥(divisionClosure (Set.range φ))) :
    (ratStruct φ).ratOp x = ratOpClosure (divisionClosure (Set.range φ)) x :=
  (Section6.exists_ratStruct φ).choose_spec.2.2 x

/-- **The universal morphism of rational `Kˣ × G`-semirings** `Φ : Rat(Kˣ × G) →+* D_{K[G],U}`
([JZLA20, Lemma 4.2]), obtained from the rational structure of the division closure. -/
noncomputable def Phi (φ : MonoidAlgebra K G →+* U) :
    RatU (Kˣ × G) →+* ↥(divisionClosure (Set.range φ)) :=
  RatU.lift _ (ratStruct φ)

/-- `Φ` is a morphism of rational `Kˣ × G`-semirings. -/
theorem Phi_isRational (φ : MonoidAlgebra K G →+* U) :
    IsRationalUSemiringHom (RatU.rational) (ratStruct φ) (Phi φ) :=
  RatU.lift_isHom _ _

/-- The image of the group element `(λ,g)` under `Φ` is `φ(λ·g)`. -/
theorem Phi_ofGroup (φ : MonoidAlgebra K G →+* U) (u : Kˣ × G) :
    Phi φ (RatU.ofGroup u) = imElem φ u := by
  rw [show RatU.ofGroup u = (RatU.rational (U := Kˣ × G)).smul u 1 from rfl,
    (Phi_isRational φ).map_smul, map_one]
  refine Subtype.ext ?_
  rw [ratStruct_smul]
  simp [imElem]

end Work.ORHughesFree
