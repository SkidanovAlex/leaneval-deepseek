/-
# `HomologyIso/`: the Mayer–Vietoris identifications of the cover `M̂ = A ∪ B`

This area produces the three `Work.Final.FinalInputs` fields that identify the two first slots of
the Mayer–Vietoris long exact sequence of the cover `M̂ = A ∪ B` with the free models of
`Work.HomologyMV`:

* `eM k : ModelM k ≅ L.H (k,0)` — `H_k(A ∩ B) ≅ ℤ^{rankM k}`;
* `eN k : ModelN k ≅ L.H (k,1)` — `H_k(A) ⊞ H_k(B) ≅ ℤ^{rankN k}`;
* `hsq k : (eM k).hom ≫ L.d (k,0) = wConcrete k ≫ (eN k).hom`.

## Design

The two slots are

* `L.H (k,0) = HInter A B k = H_k(A ∩ B)` (singular homology of the subspace `A ∩ B`);
* `L.H (k,1) = HBiprod A B k = H_k(C_*(A) ⊞ C_*(B))`,

so the identifications are *not* stated directly: they are decomposed into the three homology
computations of the geometry

| piece | rank | source |
|---|---|---|
| `A ∩ B` (five cusp collars `S¹ × T²_v`) | `rankM = 5·(1,3,3,1) = (5,15,15,5)` | `DeltaHomology` + `Certificates` |
| `A` (homotopy equivalent to `M̄`) | `rankA = (1,5,10,4)` | `DeltaHomology` + `Certificates` |
| `B` (five filling tori `T²_v`) | `rankB = 5·(1,2,1) = (5,10,5)` | `DeltaHomology` + `Certificates` |

which are the *hypotheses* of this area (`Work.HomologyIso.PieceData`), together with the
commuting square (`Work.HomologyIso.Inputs.hsq`, from the torus-bridge refinement data of
`rtdata/` and the homotopies of `SPACE`).  Everything else — the assembly of `ModelN` from
`ModelA` and `ModelB`, the transport from the `ℕ`-graded terms to the `ℤ`-graded sequence, the
conversion of the Mayer–Vietoris map `mvF` into the sequence map `L.d`, and the negative degrees —
is proved here.

## Main results

* `Work.HomologyIso.mhatLES` — the Mayer–Vietoris long exact sequence of `M̂ = A ∪ B`, built
  **without** any `FinalInputs` instance;
* `Work.HomologyIso.eM`, `Work.HomologyIso.eN`, `Work.HomologyIso.hsq` — the three fields;
* `Work.HomologyIso.Fields` — the three packaged as a structure, for a single-line instantiation.
-/
import Submission.Work.Final.All
import Submission.Work.HomologyMV.All

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open LeanEval.Topology
open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.HomologyIso

noncomputable section

variable [rt : Work.Space.RTData]

/-! ## §1  The two open sets of the cover, and its Mayer–Vietoris sequence -/

/-- `A`: the thickened hyperbolic part of `M̂`. -/
abbrev Aset : Set rt.Mhat := Work.Final.mhatAset (rt := rt)

/-- `B`: the union of the five filling pieces. -/
abbrev Bset : Set rt.Mhat := Work.Final.mhatBset (rt := rt)

/-- `M̂` as a topological space. -/
abbrev Xhat : TopCat := TopCat.of rt.Mhat

/-- The `A ∩ B` slot of the Mayer–Vietoris sequence in degree `k`: `H_k(A ∩ B)`. -/
abbrev HI (k : ℕ) : ModuleCat ℤ := Work.Cohomology.HInter (X := Xhat (rt := rt)) Aset Bset k

/-- The `A ⊞ B` slot of the Mayer–Vietoris sequence in degree `k`: `H_k(C_*(A) ⊞ C_*(B))`. -/
abbrev HB (k : ℕ) : ModuleCat ℤ := Work.Cohomology.HBiprod (X := Xhat (rt := rt)) Aset Bset k

/-- The first Mayer–Vietoris map `H_k(A ∩ B) ⟶ H_k(A) ⊞ H_k(B)`. -/
abbrev mvFhat (k : ℕ) : HI (rt := rt) k ⟶ HB (rt := rt) k :=
  Work.Final.mvF (X := Xhat (rt := rt)) Aset Bset k

/-- **The degree-`0` Mayer–Vietoris input of the cover `M̂ = A ∪ B`**, proved here so that the
sequence below needs no `FinalInputs` instance.  It is `Work.Final.mvRightX_zero_surjective`
(surjectivity of the degree-`0` Mayer–Vietoris map) through
`Work.Final.mvExactDegreeZero_of_mvRightX`. -/
theorem mhatMVExactDegreeZero :
    Work.Final.MVExactDegreeZero (X := Xhat (rt := rt)) (Aset (rt := rt)) (Bset (rt := rt)) :=
  Work.Final.mvExactDegreeZero_of_mvRightX (X := Xhat (rt := rt)) _ _
    (Work.Final.mhatAset_isOpen (rt := rt)) (Work.Final.mhatBset_isOpen (rt := rt))
    (Work.Final.mhatAset_union_mhatBset (rt := rt))
    (Work.Final.mvRightX_zero_surjective (X := Xhat (rt := rt)) _ _
      (Work.Final.mhatAset_isOpen (rt := rt)) (Work.Final.mhatBset_isOpen (rt := rt))
      (Work.Final.mhatAset_union_mhatBset (rt := rt)))

/-- **The Mayer–Vietoris long exact sequence of `M̂ = A ∪ B`**, with no hypothesis: the terms are
`HInter A B`, `HBiprod A B`, `HSmall A B` in non-negative degrees and the zero module in negative
degrees, and the maps are `mvF`, `mvG` and `mvD` transported along the canonical isomorphisms. -/
abbrev mhatLES : Work.HomologyMV.MVLES :=
  Work.Final.mhatMVLES (rt := rt) (mhatMVExactDegreeZero (rt := rt))

/-- The `(k,0)`-slot of `mhatLES` is `H_k(A ∩ B)`, for `k : ℤ` and `0 ≤ k`. -/
theorem mhatLES_H_zero (k : ℤ) (hk : 0 ≤ k) :
    (mhatLES (rt := rt)).H (k, 0) = HI (rt := rt) k.toNat :=
  Work.Final.coverH_zero (X := Xhat (rt := rt)) Aset Bset hk

/-- The `(k,1)`-slot of `mhatLES` is `H_k(A) ⊞ H_k(B)`, for `k : ℤ` and `0 ≤ k`. -/
theorem mhatLES_H_one (k : ℤ) (hk : 0 ≤ k) :
    (mhatLES (rt := rt)).H (k, 1) = HB (rt := rt) k.toNat :=
  Work.Final.coverH_one (X := Xhat (rt := rt)) Aset Bset hk

/-- The `(k,0)`-slot of `mhatLES` is the zero module in negative degrees. -/
theorem mhatLES_H_zero_neg (k : ℤ) (hk : ¬ 0 ≤ k) :
    (mhatLES (rt := rt)).H (k, 0) = Work.Final.mvZero :=
  Work.Final.coverH_neg (X := Xhat (rt := rt)) Aset Bset hk (0 : Fin 3)

/-- The `(k,1)`-slot of `mhatLES` is the zero module in negative degrees. -/
theorem mhatLES_H_one_neg (k : ℤ) (hk : ¬ 0 ≤ k) :
    (mhatLES (rt := rt)).H (k, 1) = Work.Final.mvZero :=
  Work.Final.coverH_neg (X := Xhat (rt := rt)) Aset Bset hk (1 : Fin 3)

/-- The map `(k,0)` of `mhatLES` is the first Mayer–Vietoris map `mvF`, in non-negative degrees. -/
theorem mhatLES_d_zero (k : ℤ) (hk : 0 ≤ k) :
    (mhatLES (rt := rt)).d (k, 0)
      = eqToHom (mhatLES_H_zero (rt := rt) k hk) ≫ mvFhat (rt := rt) k.toNat
        ≫ eqToHom (mhatLES_H_one (rt := rt) k hk).symm :=
  Work.Final.coverD_zero (X := Xhat (rt := rt)) Aset Bset
    (Work.Final.mhatAset_isOpen (rt := rt)) (Work.Final.mhatBset_isOpen (rt := rt))
    (Work.Final.mhatAset_union_mhatBset (rt := rt)) hk

/-- The map `(k,0)` of `mhatLES` is the zero map in negative degrees. -/
theorem mhatLES_d_zero_neg (k : ℤ) (hk : ¬ 0 ≤ k) :
    (mhatLES (rt := rt)).d (k, 0)
      = eqToHom (mhatLES_H_zero_neg (rt := rt) k hk) ≫ (0 : Work.Final.mvZero ⟶ Work.Final.mvZero)
        ≫ eqToHom (mhatLES_H_one_neg (rt := rt) k hk).symm :=
  Work.Final.coverD_zero_neg (X := Xhat (rt := rt)) Aset Bset
    (Work.Final.mhatAset_isOpen (rt := rt)) (Work.Final.mhatBset_isOpen (rt := rt))
    (Work.Final.mhatAset_union_mhatBset (rt := rt)) hk

end

end Work.HomologyIso
