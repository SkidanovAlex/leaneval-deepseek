/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Kummer coefficient layer: `μ_p(L)` inside the units, over the coefficient ring `ULift ℤ`

This module sets up the coefficient layer of the Kummer identification that the transport from
`NK.HassePrinciple.HasseNormTheorem` to the Hasse principle of `H²(·, Z/p)` needs
(see `Submission/Work/HassePrinciple/README.md`, §8).

## Contents

* `NK.HassePrinciple.CoeffInt = ULift.{u} ℤ` — the coefficient ring, lifted into the universe of
  the fields (Mathlib's `groupCohomology` requires the coefficient ring and the group to live in the
  same universe).  `ℤ` rather than `ZMod p` or the base field `K`, because the `p`-th roots of unity
  are canonically a `ℤ`-module (`n • ζ = ζ ^ n`, avoiding any choice of generator of `μ_p`) and the
  units `Lˣ` are a `ℤ`-module as well.  This is also the coefficient convention of the sibling area
  `Submission/Work/BrauerTwist/`, whose local computation `H²(G_κ, μ_p) ≅ Z/p` is the one that holds
  for every `p`-adic `κ`;
* `NK.HassePrinciple.instMulDistribMulActionRootsOfUnity` / `coe_smul_rootsOfUnity` — the Galois
  action on `μ_p(L) ⊆ Lˣ`;
* `NK.HassePrinciple.muRep p K L : Rep CoeffInt (L ≃ₐ[K] L)` — `μ_p(L)` as a representation;
* `NK.HassePrinciple.unitsRep K L : Rep CoeffInt (L ≃ₐ[K] L)` — the units `Lˣ`;
* `NK.HassePrinciple.kummerIncl p K L : muRep p K L ⟶ unitsRep K L` — the inclusion
  `μ_p(L) ↪ Lˣ` as a morphism of representations, and `kummerMap p K L` its induced map on `H²`.

## What this layer is for, and an important correction

The intended use is the **Kummer identification**: the short exact sequence of
`Gal(L/K)`-representations

  `1 → μ_p(L) → Lˣ → Lˣ/μ_p(L) → 1`

(the `p`-th power map on `Lˣ` has kernel `μ_p(L)` in characteristic `0`, and `Lˣ/μ_p(L)` is
isomorphic to `(Lˣ)^p`) shows that the connecting map `H²(Gal(L/K), μ_p)` sits inside the relative
Brauer group `H²(Gal(L/K), Lˣ) = Br(L/K)`.

**Correction (found by the reviewers of this layer, and recorded here so that the next stretch does
not repeat the mistake).**  The naive statement

  `H²(Gal(L/K), μ_p(L)) → H²(Gal(L/K), Lˣ)` is *injective* for every finite Galois `L/K`

is **false**, and the finite-field case is a counterexample: for `K = 𝔽_7`, `L = 𝔽_{7³}`, `p = 3`
one has `μ_3(L) = μ_3(K) ≅ ℤ/3` with trivial `Gal(L/K) = C₃`-action, so the source is
`H²(C₃, ℤ/3) ≅ ℤ/3`, while the target is `Br(L/K) = Kˣ/N_{L/K} Lˣ = 1` (the norm on the units of a
finite field is surjective).  So the level-wise Kummer map is the zero map there.  The same
phenomenon is recorded in §5.9/§8.3 of the README: *level-wise* cohomology and *limiting* (absolute)
cohomology differ, and the classical Kummer identification lives at the **absolute** level:

  `1 → μ_p(K̄) → K̄ˣ --(·)^p--> K̄ˣ → 1`   (exact: `K̄` is separably closed)

whose long exact sequence together with Hilbert 90 (`H¹(G_K, K̄ˣ) = 0`) gives
`H²(G_K, μ_p) ↪ H²(G_K, K̄ˣ) = Br(K)` with image the `p`-torsion — and passing to the limit over the
levels is exactly the presentation used by the sibling area `Submission/Work/BrauerTwist/`
(whose README §1 isolates the same point: the continuous cohomology is the colimit
`colim_L H²(U ⧸ (U ⊓ G_L), μ_p(L))`, and taking the abstract cohomology of the profinite group
instead is wrong).

Consequently the transport of README §8 has to be set up **in the colimit**, not level by level:

* the Kummer step has to be taken for the *filtered colimit* of the level systems
  (`NK.BrauerTwist.H2Twist` for `μ_p`, and the analogous colimit of the units `Lˣ` with the
  coefficient inclusions `Lˣ ↪ L'ˣ`), or
* if worked out at a finite level, it must carry the hypothesis that makes it true, namely
  `H¹(Gal(L/K), Lˣ / μ_p(L)) = 0` (equivalently: that the level's localisation is "cofinal enough"
  in the sense of §8.3), which is exactly what fails in the finite-field example.

The honest statement of the remaining obligation is therefore item 1 of §8.4 **in the limit form**,
and the coefficient layer below (`muRep`, `unitsRep`, `kummerIncl`, `kummerMap`) is still the right
level-wise input to it: the transport from level data to the colimit is the same kind of bookkeeping
as `NK.BrauerTwist.LevelSystem`, and the level-wise maps defined here are its structure maps.

-/

import Mathlib
import Mathlib.RingTheory.RootsOfUnity.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory Representation

set_option autoImplicit false

universe u

namespace NK.HassePrinciple

/-- The coefficient ring `ℤ`, lifted into the universe of the fields so that Mathlib's
`groupCohomology` (which requires the coefficient ring and the group to live in the same universe)
applies. -/
abbrev CoeffInt : Type u := ULift.{u} ℤ

/-- The scalar action of `ULift R` commutes with any action commuting with the `R`-action. -/
instance instSMulCommClassULift (M R A : Type*) [SMul R A] [SMul M A] [SMulCommClass M R A] :
    SMulCommClass M (ULift R) A where
  smul_comm m n x := by
    show m • (n.down • x) = n.down • (m • x)
    exact SMulCommClass.smul_comm m n.down x

section RootsOfUnity

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- **The Galois action on the `p`-th roots of unity of `L`**, i.e. on `μ_p(L) ⊆ Lˣ`. -/
noncomputable instance instMulDistribMulActionRootsOfUnity (p : ℕ) :
    MulDistribMulAction (L ≃ₐ[K] L) (rootsOfUnity p L) where
  smul σ x := ⟨σ • (x : Lˣ), (mem_rootsOfUnity p (σ • (x : Lˣ))).mpr (by
    rw [← smul_pow', (mem_rootsOfUnity p (x : Lˣ)).mp x.2, smul_one])⟩
  one_smul x := Subtype.ext (one_smul _ (x : Lˣ))
  mul_smul a b x := Subtype.ext (mul_smul a b (x : Lˣ))
  smul_mul a x y := Subtype.ext (smul_mul' a (x : Lˣ) (y : Lˣ))
  smul_one a := Subtype.ext (smul_one a)

@[simp]
lemma coe_smul_rootsOfUnity (p : ℕ) (σ : L ≃ₐ[K] L) (x : rootsOfUnity p L) :
    ((σ • x : rootsOfUnity p L) : Lˣ) = σ • (x : Lˣ) := rfl

end RootsOfUnity

section Reps

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- The `ℤ`-linear representation structure on the additive group underlying a multiplicative
`G`-module, transported along `Additive`. -/
noncomputable instance instDistribMulActionAdditiveOfMul {G A : Type*} [Monoid G] [CommGroup A]
    [MulDistribMulAction G A] : DistribMulAction G (Additive A) where
  smul g x := Additive.ofMul (g • Additive.toMul x)
  one_smul x := congrArg Additive.ofMul (one_smul G (Additive.toMul x))
  mul_smul g h x := congrArg Additive.ofMul (mul_smul g h (Additive.toMul x))
  smul_zero g := congrArg Additive.ofMul (smul_one g)
  smul_add g x y := congrArg Additive.ofMul (smul_mul' g (Additive.toMul x) (Additive.toMul y))

/-- **The Kummer coefficient module `μ_p(L)`**, as a `CoeffInt`-linear representation of
`Gal(L/K)`. -/
noncomputable def muRep (p : ℕ) (K L : Type u) [Field K] [Field L] [Algebra K L] :
    Rep CoeffInt (L ≃ₐ[K] L) :=
  Rep.ofDistribMulAction CoeffInt (L ≃ₐ[K] L) (Additive (rootsOfUnity p L))

/-- **The units `Lˣ`**, as a `CoeffInt`-linear representation of `Gal(L/K)`. -/
noncomputable def unitsRep (K L : Type u) [Field K] [Field L] [Algebra K L] :
    Rep CoeffInt (L ≃ₐ[K] L) :=
  Rep.ofDistribMulAction CoeffInt (L ≃ₐ[K] L) (Additive Lˣ)

/-- **The Kummer inclusion** `μ_p(L) ↪ Lˣ` as a morphism of `CoeffInt`-linear
`Gal(L/K)`-representations.  Its induced map in second cohomology is injective onto the `p`-torsion
of the relative Brauer group `H²(Gal(L/K), Lˣ) ≅ Br(L/K)`; see the module docstring and
`NK.HassePrinciple.kummerInjective`. -/
noncomputable def kummerIncl (p : ℕ) (K L : Type u) [Field K] [Field L] [Algebra K L] :
    muRep p K L ⟶ unitsRep K L :=
  Rep.ofHom
    { toFun := fun x => Additive.ofMul ((Additive.toMul x : rootsOfUnity p L) : Lˣ)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => Additive.toMul.injective rfl
      isIntertwining' := fun _ => by
        ext x
        rfl }

/-- **The Kummer map** on second cohomology: the map induced by the inclusion `μ_p(L) ↪ Lˣ`,
`H²(Gal(L/K), μ_p(L)) → H²(Gal(L/K), Lˣ) = Br(L/K)`. -/
noncomputable def kummerMap (p : ℕ) (K L : Type u) [Field K] [Field L] [Algebra K L] :
    groupCohomology (muRep p K L) 2 ⟶ groupCohomology (unitsRep K L) 2 :=
  groupCohomology.map (MonoidHom.id (L ≃ₐ[K] L)) (kummerIncl p K L) 2

end Reps

end NK.HassePrinciple
