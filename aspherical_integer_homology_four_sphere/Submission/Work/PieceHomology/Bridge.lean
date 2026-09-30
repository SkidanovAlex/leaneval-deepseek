/-
# `PieceHomology/`: the bridge — the Mayer–Vietoris map is the concrete matrix `wConcrete`

The last input of `Work.HomologyIso.CuspInputs` / `Work.HomologyIso.Inputs` is the *bridge*: the
first Mayer–Vietoris map `H_k(A ∩ B) → H_k(A) ⊞ H_k(B)` (the map `(incl_*, incl_*)`, see
`Work.Cohomology.mvLeft`) is the concrete matrix `Work.HomologyMV.wConcrete k` in the bases of the
models.

The area `Work.HomologyIso` already *reduced* the bridge to the chain level
(`Work.HomologyIso.hsq_of_chainLevel`, proved): from finite complexes `C₁`, `C₂` with
quasi-isomorphisms

```
q₁ : C₁ ⟶ C_*(A ∩ B),     q₂ : C₂ ⟶ C_*(A) ⊞ C_*(B),
```

a chain map `φ : C₁ ⟶ C₂` whose square with `mvLeft` commutes *up to homotopy*, and an algebraic
square `eM ≫ H(φ) = wConcrete ≫ eN` on the finite complexes.  This file names exactly that data as
`Work.PieceHomology.Bridge` and derives the bridge field of `Work.HomologyIso.CuspInputs` (and of
`Work.HomologyIso.Inputs`) from it.

## The two obligations of a provider

1. **The homotopy** `hφ : Homotopy (q₁ ≫ mvLeft) (φ ≫ q₂)`: this is what the subdivision chain
   maps `sd_A`, `sd_B` and the witnesses `sd_B(z_B) − sd_A(z_A) = ∂w` of
   `rtdata/data/mv_certificate.json` certify, through
   `Work.Certificates.boundaryWitnessCheck_sound` and the cycle-class interface of
   `Work.HomologyExtra`.
2. **The square** `hsq`: the algebraic square on the finite complexes, in the bases *induced by the
   geometric identifications* of the models — i.e. `φ` is the matrix `wConcrete k` when
   `C₁.homology k` is identified with `ModelM k` through the model of `H_k(A ∩ B)`  (the cusp-major
   basis `(σ, λ₂, λ₃)` of `Work.HomologyMV.Data`) and `C₂.homology k` with `ModelN k` through the
   models of `H_k(A)` and of `H_k(B)`.  It is checked on the basis vectors
   (`Work.HomologyMV.ext_on_basis`).

## Conventions

The two chain complexes `SingInter`, `SingUnion` below are the ones *of the cover*
(`Work.Cohomology.mvShort`), so that the homology of `SingInter` is *definitionally* the first slot
`Work.HomologyIso.HI` and that of `SingUnion` the second slot `Work.HomologyIso.HB`; the two maps
`eMtf`, `eNtf` are the transport of the geometric identifications of the models along `q₁` and `q₂`.
-/
import Submission.Work.PieceHomology.Basic
import Submission.Work.HomologyIso.hsq_of_chainLevel

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
set_option maxHeartbeats 2000000

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open LeanEval.Topology
open scoped Topology

namespace Work.PieceHomology

noncomputable section

variable [rt : Work.Space.RTData]

/-! ## §1  The two subsets of the cover and their singular chain complexes -/

/-- The first open set of the Mayer–Vietoris cover of `M̂` (the thickened hyperbolic piece). -/
abbrev USet : Set rt.Mhat := Work.HomologyIso.Aset (rt := rt)

/-- The second open set of the Mayer–Vietoris cover of `M̂` (the union of the filling pieces). -/
abbrev VSet : Set rt.Mhat := Work.HomologyIso.Bset (rt := rt)

/-- The Mayer–Vietoris short complex of the cover of `M̂` (over the space `M̂` itself). -/
abbrev MVShort : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  Work.Cohomology.mvShort (X := TopCat.of rt.Mhat) (USet (rt := rt)) (VSet (rt := rt))

/-- The singular chain complex of the intersection `A ∩ B` (the first term of the short complex,
whose homology is the `(k,0)`-slot). -/
abbrev SingInter : ChainComplex (ModuleCat ℤ) ℕ := (MVShort (rt := rt)).X₁

/-- The biproduct of the singular chain complexes of `A` and of `B` (the second term of the short
complex, whose homology is the `(k,1)`-slot). -/
abbrev SingUnion : ChainComplex (ModuleCat ℤ) ℕ := (MVShort (rt := rt)).X₂

/-- The first term of the short complex is the singular chains of `A ∩ B`. -/
theorem singInter_eq (k : ℕ) :
    (SingInter (rt := rt)).homology k = Work.HomologyIso.HI (rt := rt) k := rfl

/-- The second term of the short complex is the sum of the singular chains of `A` and of `B`. -/
theorem singUnion_eq (k : ℕ) :
    (SingUnion (rt := rt)).homology k = Work.HomologyIso.HB (rt := rt) k := rfl

/-! ## §2  The transport of the geometric identifications along the quasi-isomorphisms -/

/-- **The identification of `ModelM k` with `C₁.homology k` used in the bridge**: the geometric
identification `D.eAB k : ModelM k ≅ H_k(A ∩ B)`, transported along the quasi-isomorphism `q₁`.

Its values on the basis vectors of `ModelM k` are the columns of `wConcrete k` in the bridge
square. -/
def eMtf (D : Work.HomologyIso.PieceData (rt := rt)) {C₁ : ChainComplex (ModuleCat ℤ) ℕ}
    (q₁ : C₁ ⟶ SingInter (rt := rt)) (hq₁ : QuasiIso q₁) (k : ℕ) :
    Work.HomologyMV.ModelM (k : ℤ) ≅ C₁.homology k :=
  D.eAB k ≪≫ (asIso (homologyMap q₁ k)).symm

/-- **The identification of `ModelN k` with `C₂.homology k` used in the bridge**: the geometric
identification `D.eN k : ModelN k ≅ H_k(A) ⊞ H_k(B)`, transported along the quasi-isomorphism
`q₂`. -/
def eNtf (D : Work.HomologyIso.PieceData (rt := rt)) {C₂ : ChainComplex (ModuleCat ℤ) ℕ}
    (q₂ : C₂ ⟶ SingUnion (rt := rt)) (hq₂ : QuasiIso q₂) (k : ℕ) :
    Work.HomologyMV.ModelN (k : ℤ) ≅ C₂.homology k :=
  D.eN k ≪≫ (asIso (homologyMap q₂ k)).symm

/-! ## §3  The bridge -/

/-- **The bridge data**: the chain-level content of the commuting square
`(eAB k).hom ≫ mvFhat k = wConcrete k ≫ (eN k).hom`.

* `q₁` — a quasi-isomorphism from a finite complex onto the singular chains of `A ∩ B` (the
  subdivision of the collar complex along the refinement of `rtdata/data/mv_certificate.json`);
* `q₂` — a quasi-isomorphism from a finite complex onto `C_*(A) ⊞ C_*(B)`;
* `φ` — the chain map between the two finite complexes (the subdivision map of the bridge);
* `hφ` — the chain homotopy making the square with the Mayer–Vietoris map `mvLeft = (incl_*, incl_*)`
  commute (certified by the witnesses `sd_B(z_B) − sd_A(z_A) = ∂w` of `rtdata/`);
* `hsq` — the algebraic square on the finite complexes, in the bases induced by the geometric
  identifications `eMtf`, `eNtf` (the matrix identity of `mv_certificate.json`).

The bridge is stated relative to the *piece data* `D` (which fixes the bases); the per-cusp variant
takes `D := (Dcusp).toPieceData`. -/
structure Bridge (D : Work.HomologyIso.PieceData (rt := rt)) where
  /-- The finite complex on the `A ∩ B` side. -/
  C₁ : ChainComplex (ModuleCat ℤ) ℕ
  /-- The quasi-isomorphism from it to the singular chains of `A ∩ B`. -/
  q₁ : C₁ ⟶ SingInter (rt := rt)
  /-- It is a quasi-isomorphism (a subdivision map). -/
  hq₁ : QuasiIso q₁
  /-- The finite complex on the `A ⊞ B` side. -/
  C₂ : ChainComplex (ModuleCat ℤ) ℕ
  /-- The quasi-isomorphism from it to `C_*(A) ⊞ C_*(B)`. -/
  q₂ : C₂ ⟶ SingUnion (rt := rt)
  /-- It is a quasi-isomorphism. -/
  hq₂ : QuasiIso q₂
  /-- The chain map between the two finite complexes. -/
  φ : C₁ ⟶ C₂
  /-- **The square commutes up to homotopy**: the witnesses `sd_B(z_B) − sd_A(z_A) = ∂w` of
  `rtdata/data/mv_certificate.json` certify this. -/
  hφ : Homotopy (q₁ ≫ Work.Cohomology.mvLeft (X := TopCat.of rt.Mhat)
    (USet (rt := rt)) (VSet (rt := rt))) (φ ≫ q₂)
  /-- **The algebraic square**: `φ` is the concrete matrix `wConcrete k` in the bases induced by
  the geometric identifications `eMtf`, `eNtf`. -/
  hsq : ∀ k : ℕ, (eMtf (rt := rt) D q₁ hq₁ k).hom ≫ homologyMap φ k
    = Work.HomologyMV.wConcrete (k : ℤ) ≫ (eNtf (rt := rt) D q₂ hq₂ k).hom

namespace Bridge

variable {D : Work.HomologyIso.PieceData (rt := rt)}

/-- **The bridge field of `Work.HomologyIso.Inputs` from a `Bridge`** — the reason the interface is
the one it is: `Work.HomologyIso.hsq_of_chainLevel` (proved) turns the chain-level data into the
declared square, the two transports `eMtf`, `eNtf` cancelling definitionally. -/
theorem mvSquare (B : Bridge (rt := rt) D) (k : ℕ) :
    (D.eAB k).hom ≫ Work.HomologyIso.mvFhat (rt := rt) k
      = Work.HomologyMV.wConcrete (k : ℤ) ≫ (D.eN k).hom := by
  have h := Work.HomologyIso.hsq_of_chainLevel (X := TopCat.of rt.Mhat)
    (USet (rt := rt)) (VSet (rt := rt)) B.q₁ B.hq₁ B.q₂ B.hq₂ B.φ B.hφ
    (eMtf (rt := rt) D B.q₁ B.hq₁) (eNtf (rt := rt) D B.q₂ B.hq₂) B.hsq k
  simpa only [eMtf, eNtf, Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl] using h

/-- **The bridge data, as the declared fields of `Work.HomologyIso.Inputs`.** -/
def toInputs (D : Work.HomologyIso.PieceData (rt := rt)) (B : Bridge (rt := rt) D) :
    Work.HomologyIso.Inputs (rt := rt) where
  toPieceData := D
  hsq := fun k => B.mvSquare k

/-- **The bridge data, as the declared fields of `Work.HomologyIso.CuspInputs`** (per-cusp
preferred form: the piece data comes from the per-cusp computations). -/
def toCuspInputs (D : Work.HomologyIso.CuspData (rt := rt))
    (B : Bridge (rt := rt) D.toPieceData) : Work.HomologyIso.CuspInputs (rt := rt) where
  toCuspData := D
  hsq := fun k => B.mvSquare k

end Bridge

end

end Work.PieceHomology
