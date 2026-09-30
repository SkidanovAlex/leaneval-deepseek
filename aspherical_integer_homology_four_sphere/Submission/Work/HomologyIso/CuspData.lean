/-
# `HomologyIso/`: the per-cusp refinement of the two homology computations

The interface `Work.HomologyIso.PieceData` asks for the homology of the three *pieces* of the cover
`M̂ = A ∪ B`.  This file refines it to the five cusps: the pieces are

* `A ∩ B ≃ₕ ⊔_{v=1..5} (∂[-1,1]² × T²_v)` — five copies of the cusp cross-section `T³`,
* `A ≃ₕ M̄`,
* `B ≃ₕ ⊔_{v=1..5} T²_v` — five filling tori,

(`Work.Space.Split.retrAB_homotopyEquiv`, `retrA_homotopyEquiv`, `retrB_homotopyEquiv`), so it is
enough to supply the computation *once*, cusp by cusp:

```lean
structure CuspData where
  eTorus : ∀ v, ∀ k, ℤ^{rankT k} ≅ H_k(∂[-1,1]² × T²_v)     -- rankT = (1,3,3,1)
  eA     : ∀ k, ℤ^{rankA k} ≅ H_k(M̄)                        -- rankA = (1,5,10,4)
  eT2    : ∀ v, ∀ k, ℤ^{rankT2 k} ≅ H_k(T²_v)               -- rankT2 = (1,2,1)
```

and `Work.HomologyIso.CuspData.toPieceData` assembles them into `PieceData` using

* `Work.HomologyIso.intHomology_iso_of_homotopyEquiv` (the three homotopy equivalences above),
* `Work.HomologyIso.intHomology_sigma` (`H_k(⊔_v X_v) ≅ ⨁_v H_k(X_v)` for the finite cusp index),
* `Work.HomologyIso.biproduct_freeMod` (`⨁_v ℤ^{r_v} ≅ ℤ^{∑ r_v}`, the algebra of the models),
* `rankM = 5 · rankT`, `rankB = 5 · rankT2`.

This is the form in which the `rtdata` computations are organised (one SDR certificate per cusp,
proved degree by degree): see `Work.HomologyIso.Gen.Cusps` (the cusp cube complexes `A_v`) and
`Work.HomologyIso.Gen.T2` (the filling tori).
-/
import Submission.Work.HomologyIso.Spaces
import Submission.Work.HomologyIso.intHomology_sigma
import Submission.Work.HomologyIso.biproduct_freeMod

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open LeanEval.Topology
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Topology

namespace Work.HomologyIso

noncomputable section

variable [rt : Work.Space.RTData]

/-! ## §1  The two finite disjoint unions -/

/-- The boundary of the square `∂[-1,1]²`, as a subspace of the filling pieces. -/
abbrev BdryPt : Type := Work.Space.Split.BdryPt

/-- The five cusp cross-sections `∂[-1,1]² × T²_v`, i.e. the space `A ∩ B` up to homotopy. -/
abbrev CuspBdry : Type :=
  Σ v : Work.Space.Cusp, BdryPt × rt.core.Torus v

/-- The five filling tori `T²_v`, i.e. the space `B` up to homotopy. -/
abbrev CuspTorus : Type := Σ v : Work.Space.Cusp, rt.core.Torus v

/-- **`H_k(A ∩ B) ≅ ⨁_v H_k(∂[-1,1]² × T²_v)`** — the first slot, cusp by cusp. -/
theorem homology_inter_iso_sigma (k : ℕ) :
    Nonempty (HI (rt := rt) k ≅
      biproduct (fun v : Work.Space.Cusp =>
        intHomology k (TopCat.of (BdryPt × rt.core.Torus v)))) := by
  obtain ⟨e⟩ := Work.Space.Split.retrAB_homotopyEquiv rt.core
  obtain ⟨h⟩ := intHomology_iso_of_homotopyEquiv
    (X := TopCat.of ↥(Aset (rt := rt) ∩ Bset (rt := rt)))
    (Y := TopCat.of (CuspBdry (rt := rt))) e k
  obtain ⟨s⟩ := intHomology_sigma k (fun v : Work.Space.Cusp => BdryPt × rt.core.Torus v)
  exact ⟨h ≪≫ s⟩

/-- **`H_k(B) ≅ ⨁_v H_k(T²_v)`** — the second slot, cusp by cusp. -/
theorem homology_B_iso_sigma (k : ℕ) :
    Nonempty (intHomology k (TopCat.of ↥(Bset (rt := rt))) ≅
      biproduct (fun v : Work.Space.Cusp => intHomology k (TopCat.of (rt.core.Torus v)))) := by
  obtain ⟨e⟩ := Work.Space.Split.retrB_homotopyEquiv rt.core
  obtain ⟨h⟩ := intHomology_iso_of_homotopyEquiv
    (X := TopCat.of ↥(Bset (rt := rt))) (Y := TopCat.of (CuspTorus (rt := rt))) e k
  obtain ⟨s⟩ := intHomology_sigma k (fun v : Work.Space.Cusp => rt.core.Torus v)
  exact ⟨h ≪≫ s⟩

/-! ## §2  The models as biproducts over the five cusps -/

/-- The five cusps contribute the same rank, so the sum of the per-cusp ranks is `5 · rankT`. -/
theorem sum_rankT (k : ℤ) :
    (Finset.univ.sum fun _ : Work.Space.Cusp => rankT k) = 5 * rankT k := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- The analogous statement for the filling tori. -/
theorem sum_rankT2 (k : ℤ) :
    (Finset.univ.sum fun _ : Work.Space.Cusp => rankT2 k) = 5 * rankT2 k := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- **`ModelM k ≅ ⨁_v ModelT k`**: the free model `ℤ^{rankM k}` is the direct sum of the five
per-cusp models, in the cusp-major order. -/
theorem modelM_iso_biproduct (k : ℤ) :
    Nonempty (Work.HomologyMV.ModelM k ≅
      biproduct (fun _ : Work.Space.Cusp => ModelT k)) := by
  obtain ⟨e⟩ := biproduct_freeMod (fun _ : Work.Space.Cusp => rankT k)
  exact ⟨freeModCast ((rankM_eq_five_mul_rankT k).trans (sum_rankT k).symm) ≪≫ e.symm⟩

/-- **`ModelB k ≅ ⨁_v ModelT2 k`**: the same for the filling tori. -/
theorem modelB_iso_biproduct (k : ℤ) :
    Nonempty (ModelB k ≅ biproduct (fun _ : Work.Space.Cusp => ModelT2 k)) := by
  obtain ⟨e⟩ := biproduct_freeMod (fun _ : Work.Space.Cusp => rankT2 k)
  exact ⟨freeModCast ((rankB_eq_five_mul_rankT2 k).trans (sum_rankT2 k).symm) ≪≫ e.symm⟩

/-! ## §3  The per-cusp interface -/

/-- **The per-cusp inputs**: the homology of the cusp cross-section `∂[-1,1]² × T²_v` (the first
slot), of `M̄` (the hyperbolic piece), and of the filling torus `T²_v` (the second slot).

Each of the three is supplied by a `Δ`-complex (cell) structure together with an SDR certificate;
the `rtdata` data certifies the five cusp cube complexes `A_v` (`Gen.Cusps`) and the filling tori
(`Gen.T2`), and `Gen.Mbar` the polytopal complex of `M̄`. -/
structure CuspData where
  /-- `H_k(∂[-1,1]² × T²_v) ≅ ℤ^{rankT k}` for each of the five cusps. -/
  eTorus : ∀ v : Work.Space.Cusp, ∀ k : ℕ, ModelT (k : ℤ) ≅
    intHomology k (TopCat.of (BdryPt × rt.core.Torus v))
  /-- `H_k(M̄) ≅ ℤ^{rankA k}` (the hyperbolic piece `M̄ ⊂ A`). -/
  eA : ∀ k : ℕ, ModelA (k : ℤ) ≅ intHomology k (TopCat.of rt.core.Mbar)
  /-- `H_k(T²_v) ≅ ℤ^{rankT2 k}` for each of the five filling tori. -/
  eT2 : ∀ v : Work.Space.Cusp, ∀ k : ℕ, ModelT2 (k : ℤ) ≅
    intHomology k (TopCat.of (rt.core.Torus v))

namespace CuspData

/-- **The first slot of the Mayer–Vietoris sequence, from the per-cusp data**:
`H_k(A ∩ B) ≅ ℤ^{rankM k}`. -/
def eAB (D : CuspData (rt := rt)) (k : ℕ) :
    Work.HomologyMV.ModelM (k : ℤ) ≅ HI (rt := rt) k :=
  (modelM_iso_biproduct (rt := rt) (k : ℤ)).some
    ≪≫ (biproduct.mapIso fun v : Work.Space.Cusp => (D.eTorus v k).symm).symm
    ≪≫ (homology_inter_iso_sigma (rt := rt) k).some.symm

/-- **`H_k(A) ≅ H_k(M̄) ≅ ℤ^{rankA k}`** — the hyperbolic piece, from the `M̄` computation. -/
def eA' (D : CuspData (rt := rt)) (k : ℕ) :
    ModelA (k : ℤ) ≅ intHomology k (TopCat.of ↥(Aset (rt := rt))) :=
  D.eA k ≪≫ (homology_A_iso (rt := rt) k).some.symm

/-- **The second slot, from the per-cusp data**: `H_k(B) ≅ ℤ^{rankB k}`. -/
def eB' (D : CuspData (rt := rt)) (k : ℕ) :
    ModelB (k : ℤ) ≅ intHomology k (TopCat.of ↥(Bset (rt := rt))) :=
  (modelB_iso_biproduct (rt := rt) (k : ℤ)).some
    ≪≫ (biproduct.mapIso fun v : Work.Space.Cusp => (D.eT2 v k).symm).symm
    ≪≫ (homology_B_iso_sigma (rt := rt) k).some.symm

/-- **The per-cusp data gives the three homology computations of the geometry** — all the algebra
of the direct sums is done here. -/
def toPieceData (D : CuspData (rt := rt)) : PieceData (rt := rt) where
  eAB := D.eAB
  eA := D.eA'
  eB := D.eB'

end CuspData

/-- **The per-cusp inputs together with the bridge**: this is the form in which the whole area can
be instantiated cusp by cusp. -/
structure CuspInputs extends CuspData (rt := rt) where
  /-- The bridge (see `Work.HomologyIso.Inputs.hsq`). -/
  hsq : ∀ k : ℕ,
    (toCuspData.eAB (rt := rt) k).hom ≫ mvFhat (rt := rt) k
      = Work.HomologyMV.wConcrete (k : ℤ) ≫ (toCuspData.toPieceData.eN k).hom

namespace CuspInputs

/-- **The per-cusp inputs, as the inputs of the area.** -/
def toInputs (I : CuspInputs (rt := rt)) : Inputs (rt := rt) where
  toPieceData := I.toCuspData.toPieceData
  hsq := I.hsq

end CuspInputs

end

end Work.HomologyIso
