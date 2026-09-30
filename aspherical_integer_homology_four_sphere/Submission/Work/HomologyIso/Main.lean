/-
# `HomologyIso/`: the three fields `eM`, `eN`, `hsq` of `Work.Final.FinalInputs`

This is the main file of the area.  It names the inputs (all of them in flight in the areas
`DeltaHomology`, `Subdivision`, `HomologyExtra` and `Certificates`) and produces the three
Mayer–Vietoris identifications of the challenge's `Work.Final.FinalInputs`.

## The inputs

* `Work.HomologyIso.PieceData` — the three homology computations of the geometry:

  | field | statement | provider |
  |---|---|---|
  | `eAB` | `∀ k : ℕ, ModelM (k : ℤ) ≅ HInter A B k`, i.e. `H_k(A ∩ B) ≅ ℤ^{rankM k}` | `DeltaHomology` + `Certificates` |
  | `eA` | `∀ k : ℕ, ModelA (k : ℤ) ≅ H_k(A)`, i.e. `H_k(M̄) ≅ ℤ^{rankA k}` | `DeltaHomology` + `Certificates` |
  | `eB` | `∀ k : ℕ, ModelB (k : ℤ) ≅ H_k(B)`, i.e. `⊕_v H_k(T²_v) ≅ ℤ^{rankB k}` | `DeltaHomology` + `Certificates` |

* `Work.HomologyIso.Inputs` — the above plus the commuting square
  `(eAB k).hom ≫ mvF A B k = wConcrete k ≫ (eN k).hom` with the *derived* `eN` (the bridge
  witnesses `sd_B(z_B) − sd_A(z_A) = ∂w` of `rtdata/`, and the homotopies of `SPACE`).

## The output

* `Work.HomologyIso.eM`, `Work.HomologyIso.eN` — the identifications of the two first slots of
  `mhatLES` with the free models, in every degree `k : ℤ`;
* `Work.HomologyIso.hsq` — the commuting square with the concrete matrix `wConcrete`;
* `Work.HomologyIso.Fields` — the three packaged, whose fields have *exactly* the types of
  `Work.Final.FinalInputs.eM/eN/hsq` with `L := Work.Final.FinalInputs.mhatLES`.
-/
import Submission.Work.HomologyIso.Algebra

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
set_option backward.isDefEq.respectTransparency false

open LeanEval.Topology
open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.HomologyIso

noncomputable section

variable [rt : Work.Space.RTData]

/-! ## §1  The named inputs -/

/-- **The three homology computations of the geometry.**  Each of them is the output of the
`Δ`-complex realisation of `DeltaHomology` (a `Δ`-cell structure on the piece, realised on the
space) composed with the `SDR` certificate of `Certificates`, in the bases of
`Work.HomologyMV.Data`.

* `eAB` — `H_k(A ∩ B) ≅ ℤ^{rankM k}`; `A ∩ B` is the union of the five collar annuli
  `S¹ × T²_v` (`A ∩ B ≃ₕ ⊔_v ∂[-1,1]² × T²_v`, `Work.Space.Split.retrAB_homotopyEquiv`);
* `eA` — `H_k(A) ≅ ℤ^{rankA k}`; `A` is homotopy equivalent to `M̄`
  (`Work.Space.Split.retrA_homotopyEquiv`), whose homology is `(1,5,10,4)`;
* `eB` — `H_k(B) ≅ ℤ^{rankB k}`; `B` is homotopy equivalent to the five filling tori `T²_v`
  (`Work.Space.Split.retrB_homotopyEquiv`), whose homology is `5·(1,2,1)`. -/
structure PieceData where
  /-- **`H_k(A ∩ B) ≅ ℤ^{rankM k}`** (`rankM = 5·(1,3,3,1) = (5,15,15,5)`). -/
  eAB : ∀ k : ℕ,
    Work.HomologyMV.ModelM (k : ℤ) ≅ HI (rt := rt) k
  /-- **`H_k(A) ≅ ℤ^{rankA k}`** (`rankA = (1,5,10,4)`, the homology of `M̄`). -/
  eA : ∀ k : ℕ,
    ModelA (k : ℤ) ≅ intHomology k (TopCat.of ↥(Aset (rt := rt)))
  /-- **`H_k(B) ≅ ℤ^{rankB k}`** (`rankB = 5·(1,2,1) = (5,10,5)`, the homology of the five
  filling tori `T²_v`). -/
  eB : ∀ k : ℕ,
    ModelB (k : ℤ) ≅ intHomology k (TopCat.of ↥(Bset (rt := rt)))

/-- **`eN` from the two pieces**: the second slot `H_k(A) ⊞ H_k(B)` of the Mayer–Vietoris
sequence is the direct sum of the two computations, by
`Work.Homology.HomologyBiprod` (homology commutes with the biproduct of chain complexes) and the
algebraic splitting `ℤ^{rankA + rankB} = ℤ^{rankA} ⊞ ℤ^{rankB}` (`modelNSplit`).

This is the only content of the field `eN` of `Work.Final.FinalInputs` that is not a computation
of the geometry. -/
def PieceData.eN (I : PieceData (rt := rt)) (k : ℕ) :
    Work.HomologyMV.ModelN (k : ℤ) ≅ HB (rt := rt) k :=
  (modelNSplit (k : ℤ)).trans
    ((biprod.mapIso (I.eA k).symm (I.eB k).symm).symm.trans
      ((Work.Homology.HomologyBiprod
        (Work.Homology.singChain Work.Homology.ZMod (TopCat.of ↥(Aset (rt := rt))))
        (Work.Homology.singChain Work.Homology.ZMod (TopCat.of ↥(Bset (rt := rt)))) k).some.symm))

/-- **The named inputs of the area, with the bridge.**  The commuting square says that in the
bases of the models, the first Mayer–Vietoris map `H_k(A ∩ B) ⟶ H_k(A) ⊞ H_k(B)` (which is
`(incl_*, incl_*)`, see `Work.Cohomology.mvLeft`) is the matrix `wConcrete k = φ_k` of
`rtdata/data/mv_certificate.json` (`φ₁`, `φ₂`, `φ₃` with `det φ₁ = det φ₂ = −1`, the bridge
witnesses `sd_B(z_B) − sd_A(z_A) = ∂w`). -/
structure Inputs extends PieceData (rt := rt) where
  /-- **The bridge**: the Mayer–Vietoris map is the concrete matrix `wConcrete k`. -/
  hsq : ∀ k : ℕ,
    (toPieceData.eAB k).hom ≫ mvFhat (rt := rt) k
      = Work.HomologyMV.wConcrete (k : ℤ) ≫ (toPieceData.eN k).hom

/-! ## §2  Transport along an equality of the degree -/

/-- The transport of the model `ModelM` along an equality of degrees. -/
def castM {k₁ k₂ : ℤ} (h : k₁ = k₂) : Work.HomologyMV.ModelM k₁ ≅ Work.HomologyMV.ModelM k₂ :=
  eqToIso (congrArg Work.HomologyMV.ModelM h)

/-- The transport of the model `ModelN` along an equality of degrees. -/
def castN {k₁ k₂ : ℤ} (h : k₁ = k₂) : Work.HomologyMV.ModelN k₁ ≅ Work.HomologyMV.ModelN k₂ :=
  eqToIso (congrArg Work.HomologyMV.ModelN h)

/-- **The concrete matrices are compatible with the transport of the degree**: `wConcrete` is a
family of matrices indexed by the degree, so transporting the source and the target of
`wConcrete k₁` along an equality `k₁ = k₂` gives `wConcrete k₂`. -/
theorem wConcrete_cast {k₁ k₂ : ℤ} (h : k₁ = k₂) :
    (castM h).hom ≫ Work.HomologyMV.wConcrete k₂
      = Work.HomologyMV.wConcrete k₁ ≫ (castN h).hom := by
  cases h
  simp [castM, castN]

/-- **A general cancellation of the `eqToHom`s of an equality of modules.** -/
theorem eqToHom_symm_comp {P Q : ModuleCat ℤ} (h : P = Q) :
    eqToHom h.symm ≫ eqToHom h = 𝟙 Q := by
  subst h
  simp

/-! ## §3  The two identifications, in every degree -/

/-- **`eM`: the first slot of the Mayer–Vietoris sequence of `M̂ = A ∪ B` is the free model
`ℤ^{rankM k}`.**

In non-negative degrees this is the computation `PieceData.eAB` of the geometry, transported along
`(k.toNat : ℤ) = k`; in negative degrees both sides are the zero module. -/
def eM (I : PieceData (rt := rt)) (k : ℤ) :
    Work.HomologyMV.ModelM k ≅ (mhatLES (rt := rt)).H (k, 0) :=
  if hk : 0 ≤ k then
    castM (Int.toNat_of_nonneg hk).symm ≪≫ I.eAB k.toNat
      ≪≫ (eqToIso (mhatLES_H_zero (rt := rt) k hk)).symm
  else
    eqToIso (congrArg Work.HomologyMV.freeMod
        (Work.HomologyMV.rankM_eq_zero k (by omega) (by omega) (by omega) (by omega)))
      ≪≫ freeModZeroIso ≪≫ (eqToIso (mhatLES_H_zero_neg (rt := rt) k hk)).symm

/-- **`eN`: the second slot of the Mayer–Vietoris sequence of `M̂ = A ∪ B` is the free model
`ℤ^{rankN k}`.** -/
def eN (I : PieceData (rt := rt)) (k : ℤ) :
    Work.HomologyMV.ModelN k ≅ (mhatLES (rt := rt)).H (k, 1) :=
  if hk : 0 ≤ k then
    castN (Int.toNat_of_nonneg hk).symm ≪≫ I.eN k.toNat
      ≪≫ (eqToIso (mhatLES_H_one (rt := rt) k hk)).symm
  else
    eqToIso (congrArg Work.HomologyMV.freeMod
        (Work.HomologyMV.rankN_eq_zero k (by omega) (by omega) (by omega) (by omega)))
      ≪≫ freeModZeroIso ≪≫ (eqToIso (mhatLES_H_one_neg (rt := rt) k hk)).symm

/-! ## §4  The commuting square -/

/-- **A general cancellation of the `eqToHom`s of an equality of modules** — the form used in
proofs written with the right-associated composition `≫`. -/
theorem eqToHom_symm_comp_assoc {P Q Z : ModuleCat ℤ} (h : P = Q) (f : Q ⟶ Z) :
    eqToHom h.symm ≫ (eqToHom h ≫ f) = f := by
  subst h
  simp

/-- **The bridge input in the right-associated form** in which it is consumed below. -/
theorem Inputs.hsq_assoc (I : Inputs (rt := rt)) (k : ℕ) {Z : ModuleCat ℤ}
    (g : HB (rt := rt) k ⟶ Z) :
    (I.toPieceData.eAB k).hom ≫ (mvFhat (rt := rt) k ≫ g)
      = Work.HomologyMV.wConcrete (k : ℤ) ≫ ((I.toPieceData.eN k).hom ≫ g) := by
  rw [← Category.assoc, ← Category.assoc, I.hsq k]

/-- **`wConcrete_cast` in the right-associated form.** -/
theorem wConcrete_cast_assoc {k₁ k₂ : ℤ} (h : k₁ = k₂) {Z : ModuleCat ℤ}
    (g : Work.HomologyMV.ModelN k₂ ⟶ Z) :
    (castM h).hom ≫ (Work.HomologyMV.wConcrete k₂ ≫ g)
      = Work.HomologyMV.wConcrete k₁ ≫ ((castN h).hom ≫ g) := by
  rw [← Category.assoc, ← Category.assoc, wConcrete_cast h]

/-! ## §4  The commuting square -/

/-- **`hsq`: the first Mayer–Vietoris map is the concrete matrix `wConcrete k`.**

For `k ≥ 0` this is the bridge input `Work.HomologyIso.Inputs.hsq` transported to the
`ℤ`-graded sequence (`mhatLES_d_zero`, `wConcrete_cast`); for `k < 0` both slots are the zero
module, so both sides are zero. -/
theorem hsq (I : Inputs (rt := rt)) (k : ℤ) :
    (eM I.toPieceData k).hom ≫ (mhatLES (rt := rt)).d (k, 0)
      = Work.HomologyMV.wConcrete k ≫ (eN I.toPieceData k).hom := by
  by_cases hk : 0 ≤ k
  · have hn : ((k.toNat : ℤ)) = k := Int.toNat_of_nonneg hk
    have hMeq : (eM I.toPieceData k).hom
        = (castM hn.symm).hom ≫ ((I.toPieceData.eAB k.toNat).hom
          ≫ eqToHom (mhatLES_H_zero (rt := rt) k hk).symm) := by
      rw [eM]
      simp only [dif_pos hk, Iso.trans_hom, Iso.symm_hom, eqToIso.inv]
    have hNeq : (eN I.toPieceData k).hom
        = (castN hn.symm).hom ≫ ((I.toPieceData.eN k.toNat).hom
          ≫ eqToHom (mhatLES_H_one (rt := rt) k hk).symm) := by
      rw [eN]
      simp only [dif_pos hk, Iso.trans_hom, Iso.symm_hom, eqToIso.inv]
    rw [hMeq, hNeq, mhatLES_d_zero (rt := rt) k hk]
    simp only [Category.assoc]
    rw [eqToHom_symm_comp_assoc (mhatLES_H_zero (rt := rt) k hk)]
    rw [Inputs.hsq_assoc (rt := rt) I k.toNat]
    rw [wConcrete_cast_assoc hn.symm]
  · haveI : Subsingleton (↥((mhatLES (rt := rt)).H (Work.HomologyMV.mvSucc (k, 0)))) := by
      rw [Work.HomologyMV.mvSucc_zero, mhatLES_H_one_neg (rt := rt) k hk]
      infer_instance
    exact Subsingleton.elim _ _

/-! ## §5  The three fields, packaged -/

/-- **The output of the area**: the two identifications `eM`, `eN` of the first two slots of the
Mayer–Vietoris sequence `mhatLES` with the free models of `Work.HomologyMV`, and the commuting
square `hsq` with the concrete matrix `wConcrete`.

With `L = Work.HomologyIso.mhatLES` (which is *definitionally* the field `L` of
`Work.Final.FinalInputs`, see `Submission/Work/HomologyIso/Check.lean`), the three fields of this
structure have exactly the types of `Work.Final.FinalInputs.eM`, `.eN`, `.hsq`. -/
structure Fields (I : Inputs (rt := rt)) where
  /-- `H_k(A ∩ B) ≅ ℤ^{rankM k}`. -/
  eM : ∀ k : ℤ, Work.HomologyMV.ModelM k ≅ (mhatLES (rt := rt)).H (k, 0)
  /-- `H_k(A) ⊞ H_k(B) ≅ ℤ^{rankN k}`. -/
  eN : ∀ k : ℤ, Work.HomologyMV.ModelN k ≅ (mhatLES (rt := rt)).H (k, 1)
  /-- The first Mayer–Vietoris map is the concrete matrix `wConcrete k`. -/
  hsq : ∀ k : ℤ,
    (eM k).hom ≫ (mhatLES (rt := rt)).d (k, 0) = Work.HomologyMV.wConcrete k ≫ (eN k).hom

/-- **The three fields from the two named inputs** — the single call the lead's instantiation
needs. -/
def fields (I : Inputs (rt := rt)) : Fields (rt := rt) I :=
  ⟨eM I.toPieceData, eN I.toPieceData, hsq I⟩

@[simp] theorem fields_eM (I : Inputs (rt := rt)) (k : ℤ) :
    (fields I).eM k = eM I.toPieceData k := rfl

@[simp] theorem fields_eN (I : Inputs (rt := rt)) (k : ℤ) :
    (fields I).eN k = eN I.toPieceData k := rfl

@[simp] theorem fields_hsq (I : Inputs (rt := rt)) (k : ℤ) :
    (fields I).hsq k = hsq I k := rfl

end

end Work.HomologyIso
