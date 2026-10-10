import Submission.Work.CY3.StronglyRational

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CY3.G2` — Layer 1: the `G₂`-Grassmannian infrastructure of `thm:CY3`

This file records the **first layer** of the CY3 construction of Lin–Shinder,
*Motivic invariants of birational maps* (Annals **199** (1), 2024, § *K-trivial threefolds*,
`thm:CY3` and its proof): the two `G₂`-Grassmannians `G/P`, `G/P'` and the `ℙ¹`-fibration
`G/B → G/P` (resp. `G/B → G/P'`) sitting over them.

## The paper's Layer 1 (all of it a *named input* here)

> Let `G` be the connected and simply connected split simple group scheme of type `G₂` over `ℤ`.
> Let `B ⊂ G` be the Borel subgroup, and `P, P' ⊊ G` the two maximal parabolic subgroups of `G`
> containing `B`.  The quotients `G/B`, `G/P`, `G/P'` are smooth and projective over `ℤ` by
> [Milne, Theorem 13.33] and [SGA3, Cor. XXII.5.8.5].  The natural projection `p : G/B → G/P` is
> smooth.  Since `p_ℚ` is a `ℙ¹`-fibration, so is `p`.  ... `X^*(G) = 0` and `Pic(G) = 0`
> [Raynaud, Remark VII.1.7 a)], hence `Pic(G/P) ≅ X^*(P) ≅ ℤ` [Raynaud, Prop. VII.1.5].
> Similarly `Pic(G/P') ≅ ℤ`.  Let `M`, `M'` be the ample generators ...  `L ≔ p*M ⊗ p'*M'` is then
> ample ...  `deg(L_𝕜)|_{F_𝕜} = 1` ... It follows that `E ≔ p_*L` is locally free of rank `2` and
> `G/B ≅ ℙ(E)` over `G/P`.  `L` is very ample [RamRam, Theorem 3].

Mathlib has no group scheme `G₂`, no Borel/parabolic subgroups, no quotient `G/P`, no Picard
group, no locally free sheaf `p_*L`, no smoothness and no very ampleness, so this layer is
recorded as a *structure of named inputs* — `Work.CY3.G2Grassmannian` — with one field per fact of
the paragraph above, each carrying its citation in the docstring.

**Why this is uniform in the field.**  Everything in the paragraph is *defined over `Spec ℤ`*: the
group scheme, the Borels, the parabolics and the quotients are `ℤ`-schemes, and the properties
(smooth, projective, `ℙ¹`-fibration, `Pic ≅ ℤ`, very ample) are `Spec ℤ`-properties, preserved by
base change along `Spec 𝕜 → Spec ℤ`.  That is why the *same* structure is available over **every**
field `𝕜` — this is the paper's "extension to an arbitrary field", and the only place where
`Infinite 𝕜` is used is Bertini (Layer 2, `Work.CY3.Section`).

## What is proved here (the "provable parts" of the split)

* `Work.CY3.G2Grassmannian.stronglyRational` — the paper's `lem:GP-strongly-rational` for the two
  quotients, i.e. the strong rationality of `G/P` and `G/P'` (a named input, one field per
  quotient);
* `Work.CY3.G2Grassmannian.stronglyBirational` — **(L2) of the definition of an L-link**: the two
  `G₂`-Grassmannians *are* strongly birational to each other, with the birational map constructed
  from the two strong rationalities through `ℙ⁵`.  This is *proved* from the named inputs by
  additivity of the invariant (`Work.Motivic.cInv_add`), see
  `Work.CY3.IsStronglyRational.stronglyBirational`;
* `Work.CY3.G2Grassmannian.stronglyRational` — the two quotients are *strongly rational* in the
  paper's sense (`Work.CY3.IsStronglyRational`, i.e. strongly birational to `ℙ⁵`), which is a
  *named input* here.

The transports to *affine* space `𝔸⁵` — which is what the challenge's `Cr 𝕜 5 = Bir(𝔸⁵/𝕜)` needs —
are *not* derived from strong rationality: between `𝔸ⁿ` and a projective variety no transport has
all its coefficients zero (e.g. `cInv` distinguishes `ℙ¹` from `𝔸¹`), so they are supplied, with
their vanishing at the base point of the link, as fields of `Work.CY3.CY3Data` (Layer 3), exactly
as in the K3 area.  See `Submission/Work/CY3/StronglyRational.lean` and `NOTES.md` §5.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.CY3

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

/-- **Named input: the ample generators of the two Picard groups and the very ample line bundle
`L = p*M ⊗ p'*M'`.**

`HasCyLineBundle 𝕜 B P P' p p'` is the bundle-theoretic part of Layer 1 of `thm:CY3`:

* `M` (resp. `M'`) is an *ample generator* of `Pic(G/P) ≅ ℤ` (resp. `Pic(G/P') ≅ ℤ`), which is
  `X^*(P) ≅ ℤ` because `X^*(G) = 0` and `Pic(G) = 0` (Raynaud, *Ample vector bundles*,
  Prop. VII.1.5 and Remark VII.1.7 a));
* `L ≔ p*M ⊗ p'*M'` is an ample line bundle on `G/B` whose restriction to a fibre
  `F ≃ ℙ¹` of `p` has degree one (`deg(L_𝕜)|_{F_𝕜} = 1`, Ito–Miura–Okawa–Ueda), whence
  `E ≔ p_*L` is locally free of rank two and the projection `p` identifies `G/B ≅ ℙ(E)` over
  `G/P` — again uniformly over `Spec ℤ`;
* `L` is very ample (RamRam, Theorem 3).

Mathlib has neither line bundles nor `Pic` nor `p_*`, so this is a named hypothesis.  It is the
input consumed by the Bertini/general-section layer (Layer 2, `Work.CY3.IsGeneralSectionZeroLocus`)
which cuts the zero loci `X ⊂ G/B`, `Z ⊂ G/P`, `Z' ⊂ G/P'` out of `L` and `p_*L`, `p'_*L`. -/
class HasCyLineBundle (𝕜 : Type) [Field 𝕜] (B P P' : Scheme.{0}) (p : B ⟶ P)
    (p' : B ⟶ P') : Prop

/-- **Layer 1 of `thm:CY3`: the `G₂`-Grassmannian infrastructure.**

The scheme `B` is `G/B`, the schemes `P`, `P'` are the two five-dimensional `G₂`-Grassmannians
`G/P`, `G/P'` for the two maximal parabolics containing the Borel `B` of the split simply
connected simple group scheme of type `G₂` (over `Spec ℤ`, base changed to `𝕜`), and `p`, `p'` are
the two projections.  Each field is a *named input*, cited to the paper's sources; nothing in this
structure is proved here.

This is the datum whose existence is the group-theoretic half of `thm:CY3`.  A producer of it has
to build `G₂` over `ℤ`, its Borel and its two maximal parabolics, their quotients and the stated
properties; the rest of the CY3 area only uses the named facts below. -/
structure G2Grassmannian (𝕜 : Type) [Field 𝕜] where
  /-- `G/B`, the (five-dimensional) flag variety of the split `G₂`. -/
  B : Scheme.{0}
  [varietyB : Variety 𝕜 B]
  /-- `G/P`, the first five-dimensional `G₂`-Grassmannian. -/
  P : Scheme.{0}
  [varietyP : Variety 𝕜 P]
  /-- `G/P'`, the second five-dimensional `G₂`-Grassmannian. -/
  P' : Scheme.{0}
  [varietyP' : Variety 𝕜 P']
  /-- the projection `p : G/B → G/P`. -/
  p : B ⟶ P
  [isOverP : p.IsOver (Spec (.of 𝕜))]
  /-- the projection `p' : G/B → G/P'`. -/
  p' : B ⟶ P'
  [isOverP' : p'.IsOver (Spec (.of 𝕜))]
  /-- **Named input** (`Milne` Thm 13.33, `SGA3` Cor. XXII.5.8.5; `Raynaud`;
  `lem:GP-strongly-rational`): `G/P` is the `G₂`-Grassmannian — smooth projective of Picard rank
  one, strongly rational, of motivic class `[ℙ⁵]`. -/
  isG2_P : IsG2Grassmannian 𝕜 P
  /-- **Named input**: the same for `G/P'`. -/
  isG2_P' : IsG2Grassmannian 𝕜 P'
  /-- **Named input** (`lem:GP-strongly-rational`): `G/P` is *strongly rational*, i.e. strongly
  birational to `ℙ⁵` (`Work.CY3.IsStronglyRational 𝕜 P 5`).  The paper obtains this from the
  Bruhat decomposition: `G/P` is isomorphic to `𝔸⁵` outside the unique codimension-one stratum,
  which is an irreducible rational divisor `D`, and the induced birational map `φ : G/P ⤏ ℙ⁵` has
  `c(φ) = [ℙ⁴] − [D] = 0` because `D` is rational. -/
  stronglyRational_P : IsStronglyRational 𝕜 P 5
  /-- **Named input** (`lem:GP-strongly-rational`): `G/P'` is strongly rational. -/
  stronglyRational_P' : IsStronglyRational 𝕜 P' 5
  /-- **Named input** (`Milne` Thm 13.33, `SGA3` Cor. XXII.5.8.5): `p` is smooth — the quotient of
  a smooth `ℤ`-scheme by a smooth connected group scheme. -/
  smooth_p : Smooth p
  /-- **Named input**: `p'` is smooth. -/
  smooth_p' : Smooth p'
  /-- **Named input**: `p : G/B → G/P` is a `ℙ¹`-fibration — a fibre is `P_𝕜/B_𝕜 ≃ ℙ¹_𝕜`
  (the two Borels of `G₂` are conjugate), and the statement is uniform over `Spec ℤ`. -/
  isP1Fibration_p : IsP1Fibration p
  /-- **Named input**: `p' : G/B → G/P'` is a `ℙ¹`-fibration. -/
  isP1Fibration_p' : IsP1Fibration p'
  /-- **Named input** (`Raynaud` Prop. VII.1.5 + Remark VII.1.7 a); `IMOUG2`; `RamRam`
  Thm 3): the ample generators of the two Picard groups and the very ample bundle
  `L = p*M ⊗ p'*M'` with `G/B ≅ ℙ(p_*L)`. -/
  lineBundle : HasCyLineBundle 𝕜 B P P' p p'

attribute [instance] G2Grassmannian.varietyB G2Grassmannian.varietyP G2Grassmannian.varietyP'
  G2Grassmannian.isOverP G2Grassmannian.isOverP'

namespace G2Grassmannian

variable {𝕜 : Type} [Field 𝕜] (G : G2Grassmannian 𝕜)

local instance instVarietyB : Variety 𝕜 G.B := G.varietyB
local instance instVarietyP : Variety 𝕜 G.P := G.varietyP
local instance instVarietyP' : Variety 𝕜 G.P' := G.varietyP'
local instance instIsOverP : G.p.IsOver (Spec (.of 𝕜)) := G.isOverP
local instance instIsOverP' : G.p'.IsOver (Spec (.of 𝕜)) := G.isOverP'

/-- **Layer 1, first consequence: the two `G₂`-Grassmannians are strongly rational.**  This is the
paper's `lem:GP-strongly-rational` for the two homogeneous spaces (each of Picard rank one, so its
Bruhat decomposition has exactly one codimension-one stratum, and `G/P ≃ 𝔸⁵` outside it). -/
theorem stronglyRational : IsStronglyRational 𝕜 G.P 5 ∧ IsStronglyRational 𝕜 G.P' 5 :=
  ⟨G.stronglyRational_P, G.stronglyRational_P'⟩

/-- **Layer 1, second consequence: (L2) of the L-link.**  The two `G₂`-Grassmannians are strongly
birational to each other.  The birational map is produced by transporting through `ℙ⁵` and all its
coefficients vanish, by additivity of the invariant; this is the paper's `(L2)`, i.e. its
`def:strong-birat` applied to `G/P` and `G/P'` (paper `lemma:L-link` (2), and
`Work.CY3.IsStronglyRational.stronglyBirational`). -/
theorem stronglyBirational : StronglyBirational 𝕜 G.P G.P' :=
  G.stronglyRational_P.stronglyBirational G.stronglyRational_P'

/-- The dimension of the two `G₂`-Grassmannians is five: this is the content of the `5` in the
strong rationality, and it is what makes the CY3 link a link in `ℙ⁵` / `𝔸⁵`, i.e. Theorem 1.2 (3)
of the challenge for `n = 5`. -/
theorem dimensional : IsStronglyRational 𝕜 G.P 5 ∧ IsStronglyRational 𝕜 G.P' 5 :=
  G.stronglyRational

end G2Grassmannian

end

end Work.CY3
