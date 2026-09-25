/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The level dictionary transported to cohomology

`NK.HassePrinciple.levelGroupMulEquivLevelGalois` (in
`Submission/Work/HassePrinciple/LevelDictionary.lean`) identifies the finite level group of a
subgroup `V ≤ Gal(K'/K)` with the Galois group of the finite extension
`L / (L ⊓ K'^V)`,

`LevelGroup V L ≃* Gal(L / (L ⊓ K'^V))`.

Since `H²(·, Z/p)` is a contra-functor on groups, an isomorphism of groups induces an isomorphism
of the level cohomologies.  This file records that transport: the level `H²` of a level group is
the group cohomology of the Galois group of the corresponding finite extension of number fields.

## Main results

* `NK.HassePrinciple.H2MulEquiv` — an isomorphism of groups `G ≃* H` induces an isomorphism
  `H²(G, Z/p) ≅ H²(H, Z/p)` (contravariantly, via `H2.map`);
* `NK.HassePrinciple.levelH2MulEquiv` — the level dictionary on cohomology:
  `LevelH2 p V L ≅ H²(Gal(L / (L ⊓ K'^V)), Z/p)`.
-/

import Mathlib
import Submission.NK.HassePrinciple.LevelDictionary

set_option autoImplicit false

universe u

namespace NK.HassePrinciple

open NK.BrauerHasse

/-- **Isomorphism invariance of `H²(·, Z/p)`.**  A group isomorphism `e : G ≃* H` induces an
isomorphism of the second cohomology with trivial coefficients `Z/p`, contravariantly: the forward
map is `e.symm*` and the backward map is `e*`.  The two composites are the identity by
`H2.map_comp` and `H2.map_id`. -/
noncomputable def H2MulEquiv {p : ℕ} {G H : Type u} [Group G] [Group H] (e : G ≃* H) :
    H2 p G ≅ H2 p H where
  hom := H2.map (p := p) (e.symm : H →* G)
  inv := H2.map (p := p) (e : G →* H)
  hom_inv_id := by
    rw [← H2.map_comp (f := (e.symm : H →* G)) (g := (e : G →* H))]
    have hid : (e.symm : H →* G).comp (e : G →* H) = MonoidHom.id G := by ext x; simp
    rw [hid, H2.map_id]
  inv_hom_id := by
    rw [← H2.map_comp (f := (e : G →* H)) (g := (e.symm : H →* G))]
    have hid : (e : G →* H).comp (e.symm : H →* G) = MonoidHom.id H := by ext x; simp
    rw [hid, H2.map_id]

/-- **The level dictionary on cohomology.**  The level `H²(LevelGroup V L, Z/p)` of the finite
levels of the profinite cohomology `H²(V, Z/p)` is the group cohomology of the Galois group of the
finite extension of number fields `L / (L ⊓ K'^V)` with coefficients `Z/p`.  It is the transport of
`NK.HassePrinciple.levelGroupMulEquivLevelGalois` along `H2MulEquiv`. -/
theorem levelH2MulEquiv {K K' : Type u} [Field K] [Field K'] [Algebra K K'] [IsSepClosure K K']
    (p : ℕ) (V : Subgroup (K' ≃ₐ[K] K')) (L : FiniteGaloisIntermediateField K K') :
    Nonempty (NK.BrauerHasse.LevelH2 p V L ≅
      NK.BrauerHasse.H2 p (↥L ≃ₐ[↥(IntermediateField.fixedField (V.map (NK.HassePrinciple.levelRestrict L)))] ↥L)) :=
  ⟨H2MulEquiv (p := p) (levelGroupMulEquivLevelGalois V L)⟩

end NK.HassePrinciple
