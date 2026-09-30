import Mathlib
import Submission.Work.Serre.CWModel.Tower
import Submission.Work.Serre.C1Cyl
import Submission.Work.Serre.Defs
import Submission.Work.Serre.Engine
import Submission.Work.StemsB.Fibrations
import Submission.Work.Thom.Cohomology
import Submission.Work.Serre.ratFibreTransport
import Submission.Work.Serre.ThomCylDefs
import Submission.Work.Serre.thomCylAt_of_homeo
import Submission.Work.Serre.thomCylBaseCase
import Submission.Work.Serre.isSerreFibration_restrictFibre
import Submission.Work.Serre.CWModelThomAux
import Submission.Work.RatHurewicz.cellStepShell

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The CW-model Thom case: `Work.Serre.cwModelThomCase`

The target of this file is the *relative* Thom isomorphism of a rational spherical fibration over
the CW models `Work.Serre.CWModel.towerA B b₀ 2 (le_refl 2) hB2 k` of `Submission/Work/Serre/
CWModel/Tower.lean`, in the range given by the *fibre* (no rational acyclicity of the total space
is assumed, unlike `Work.Serre.ThomIsoCylFibreRange`; the total space *cannot* be acyclic here,
since the fibre is a rational sphere).

## The proof architecture

The statement is proved by the cell-by-cell induction over the stages of the model tower
(`towerA`, whose steps `genStep`/`killStep` are cell attachments along maps into the previous
stage; every cell has dimension `≥ 2`, which is what makes the extension of the Thom class
unobstructed — the `1`-cells would carry the monodromy of the local system `H^r(F;ℚ)`).

* `Work.Serre.ThomCylAt r N q` is the *conclusion* as a predicate of the fibration `q`.  The
  target `cwModelThomCase` is this predicate at `Γ = (towerA … k).Y`.
* `Work.Serre.fibreConditions_of_path` (**proved here**) turns the target's hypotheses — stated at
  the base point only — into the hypotheses at *every* point of the CW model, which is the form
  the cell step needs (`Work.Serre.ratH_fibre_iso_of_path`).
* `Work.Serre.thomCylCellStep` (**the crux**, now proved via `Work.RatHurewicz.thomCylCellStepAlt_free`) is the inductive step: attaching cells of
  dimension `D ≥ 2` to `Γ` along `f`, and a Serre fibration over the attachment whose fibres
  satisfy the hypotheses at every point, the conclusion over the old part
  `↥(q ⁻¹' range (attachIncl (D-2) Γ ι f))` implies the conclusion over the attachment.
* `Work.Serre.restrictFibre` is the restriction of a fibration to the preimage of a subset.
* `Work.Serre.thomCylBaseCase` (**proved**, `Submission/Work/Serre/thomCylBaseCase.lean`) is the base case `Γ = PUnit` (the cone pair).
* `Work.Serre.thomCylAt_of_homeo` (**proved**, `Submission/Work/Serre/thomCylAt_of_homeo.lean`)
  is the invariance of the conclusion under a homeomorphism of the base, which identifies the old
  part of an attachment with the previous stage.

## Mathematical route for the cell step

Let `D' = cyl q`, `A' = range (cylIncl q)` (the sphere part) and `N = (cylRetract q)⁻¹ Γ ∪ A'`
(the old disc bundle together with the new spheres).  The triple `A' ⊆ N ⊆ D'` gives the long
exact sequence
`H^{n}(D',N) → H^{n}(D',A') → H^{n}(N,A') → H^{n+1}(D',N) → …`,
whose first term is the *new cells* and whose third term is the *old part*.  Comparing it (with the
degree shift `r+1`) with the long exact sequence of the pair `(Γ', Γ)` and applying the five lemma
reduces the cell step to

* the **cell comparison** `H^{j}(Γ',Γ) → H^{j+r+1}(D',N)` — the cross product with the fibre
  fundamental class, computed cell by cell from the fibre-homotopy triviality of `q` over a disc
  (`Work.StemsB.fibreTrivial_of_contraction`, `Work.Serre.Csr.csrSourceDiscIso`) and the local Thom
  class of the trivial pair bundle (`Work.Serre.modelThomRatPairQ`, the relative form over a cube
  being `Work.StemsB.cubePair_main`/`Work.Serre.cubePairRelHomology`-shaped), together with its
  compatibility with the connecting maps and with the cup product with the target class;
* the **vanishing of the obstruction** `∂U = 0`: with `U` the class over the old part, the
  obstruction lives in `H^{r+2}(D',N) ≅ ⊕ᵢ H̃^{r+1-D}(F_{cᵢ})`, which vanishes for `D ≥ 2` because
  the fibre is a rational `r`-sphere through degree `N` and `r+1-D < r`.

The two comparison squares are the naturality of the mixed cup product
(`Work.StemsB.mixedCupC_pairNaturalR`, `Work.StemsB.mixedCup_relToAbs_R`) and the Leibniz rule for
the connecting map (`Work.StemsB.pairDelta_mixedCup_general_R`); the five lemma itself is
`Work.Serre.RatTower.fiveLemmaTau2` (ℚ-valued short complexes) or `Work.Serre.fiveLemmaInt`.

## State

| piece | status |
|---|---|
| `ThomCylAt`, `restrictFibre` | `Submission/Work/Serre/ThomCylDefs.lean` |
| `fibreConditions_of_path` | proved here |
| `Work.Serre.thomCylAt_of_homeo` (base change) | **proved** (`Submission/Work/Serre/thomCylAt_of_homeo.lean`) |
| `Work.Serre.thomCylBaseCase` (base case `Γ = PUnit`) | **proved** (`Submission/Work/Serre/thomCylBaseCase.lean`) |
| `Work.Serre.modelThomRatPairQ` (local model, trivial pair bundle) | proved (`Submission/Work/Serre/modelThomRatPairQ.lean`) |
| `Work.Serre.thomCylCellStep` (cellular step) | **proved** — by `Work.RatHurewicz.thomCylCellStepAlt_free` (`Submission/Work/RatHurewicz/cellStepShell.lean`) |
| `Work.Serre.cwModelThomCase_of_pieces` (tower induction) | proved here |
| `Work.Serre.cwModelThomCase` (the target) | proved here |

## The cellular step, and where its proof now lives

`Work.Serre.thomCylCellStep` (the cellular step, i.e. `Work.Serre.ThomCylCellStepAlt` up to the
order of the quantifiers) is proved *elsewhere*, so that this file stays independent of the long
`E3(b)` tower that consumes it: the theorem

  `Work.RatHurewicz.thomCylCellStepAlt_free : Work.Serre.ThomCylCellStepAlt`

in `Submission/Work/RatHurewicz/cellStepShell.lean` proves the cellular step at every cell dimension
`D ≥ 2` (with the vacuous case `N < r` handled inside), with axiom footprint
`propext, Classical.choice, Quot.sound`.  Its route is the one prepared in this file: the shell
family of `Work.Serre.thomCylCellStep_of_shellsBall` is fed by
`Work.Serre.bijective_cup_shell_of_thomCylAt` and, over the interior sphere of a cell, by
`Work.RatHurewicz.quarterSphereThom_of_nonzeroClass` applied to the non-zero extension class
`Work.Serre.cellStepU`; the sphere case itself is
`Work.RatHurewicz.sphereThom_of_nonzeroClass` over the orthant cover `Work.RatHurewicz.cvPiece`,
glued by `Work.RatHurewicz.cvGoodIUnion`.

The earlier analyses of the alternatives (the cellular ladder with the five lemma, the
Mayer–Vietoris/CellImageEq routes, the traps of the cell comparison) are recorded in
`Submission/Work/Serre/THOMGAP_PLAN.md`, `CWMODELTHOM_CRUX.md`, `CWMODEL_CVN_NOTES.md` and
`THOMCYL_GLUING_NOTES.md`; they are superseded by the route above.

-/


namespace Work.Serre

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option maxHeartbeats 1600000

/-- **The fibre conditions propagate from one point of a path connected base to every point.**
This is what turns the target's hypotheses (stated at the base point `γ₀` only) into the
hypotheses at every point of the CW model, which is the form the cell-by-cell induction needs:
the fibre homology of a Serre fibration is base-point independent along paths
(`Work.Serre.ratH_fibre_iso_of_path`, `Work.Serre.isZero_ratH_fibre_of_path`). -/
theorem fibreConditions_of_path {Γ : Type} [TopologicalSpace Γ] [PathConnectedSpace Γ]
    {X : Type} [TopologicalSpace X] (q : C(X, Γ)) (hq : Work.StemsB.IsSerreFibration q)
    (γ₀ : Γ) (r N : ℕ)
    (hvan : ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N → CategoryTheory.Limits.IsZero
      (ratH (TopCat.of (Work.StemsB.fibre q γ₀)) t))
    (hgen : Nonempty (ratH (TopCat.of (Work.StemsB.fibre q γ₀)) r ≅ ModuleCat.of ℚ ℚ))
    (γ : Γ) :
    (∀ t : ℕ, 0 < t → t ≠ r → t ≤ N → CategoryTheory.Limits.IsZero
      (ratH (TopCat.of (Work.StemsB.fibre q γ)) t)) ∧
    Nonempty (ratH (TopCat.of (Work.StemsB.fibre q γ)) r ≅ ModuleCat.of ℚ ℚ) := by
  obtain ⟨p⟩ := PathConnectedSpace.joined γ₀ γ
  have h0 : p.toContinuousMap 0 = γ₀ := p.source
  have h1 : p.toContinuousMap 1 = γ := p.target
  constructor
  · intro t ht htr htN
    obtain ⟨e⟩ := ratH_fibre_iso_of_path q hq p.toContinuousMap t
    rw [h0, h1] at e
    exact IsZero.of_iso (hvan t ht htr htN) e.symm
  · obtain ⟨e⟩ := ratH_fibre_iso_of_path q hq p.toContinuousMap r
    rw [h0, h1] at e
    exact ⟨e.symm.trans hgen.some⟩

/-! ## The attachment step of the induction

The two structural lemmas below reduce the tower induction (`cwModelThomCase_of_pieces`) to its two
inputs: the base case `Γ = PUnit` and the cellular step (`thomCylCellStep`, the crux).  Everything
here is pure bookkeeping: the cell step is applied to a fibration over the *new* stage, whose old
part is identified with the previous stage through the homeomorphism
`Work.RatHurewicz.rangeHomeo`. -/

/-- **One attachment step of the tower induction.**  `hcell` is the cellular step (in the form of
the hypothesis `hstep` of `cwModelThomCase_of_pieces`).  Given a Serre fibration `q` over an
attachment `attachCells n Y ι f` whose fibres carry the fibre data `CWThom.FibreData r N`, and the
conclusion for every such fibration over the *old* base `Y` (with the same fibre data and a path
connected fibre over the base point `y₀`), the conclusion holds for `q`.

The proof is the reduction of the old part of the attachment to `Y`: `q` restricts to
`restrictFibre q (range attachIncl)`, which is `rangeHomeo`-conjugate to the fibration `q'` over
`Y`; the fibre data transports along both operations (`CWThom.fibreData_restrictFibre`,
`CWThom.fibreData_comp_homeo`) and the conclusion transports back by
`Work.Serre.thomCylAt_of_homeo`. -/
theorem thomCylAt_of_attachCells (r N : ℕ)
    (hcell : ∀ (D : ℕ) (hD : 2 ≤ D) {Γ : Type} [TopologicalSpace Γ]
      (hΓ : PathConnectedSpace Γ) (ι : Type)
      (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ))
      {X : Type} [TopologicalSpace X] (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)),
      Work.StemsB.IsSerreFibration q →
      (∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
        CategoryTheory.Limits.IsZero (ratH (TopCat.of (Work.StemsB.fibre q γ)) t)) →
      (∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
        Nonempty (ratH (TopCat.of (Work.StemsB.fibre q γ)) r ≅ ModuleCat.of ℚ ℚ)) →
      (∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
        PathConnectedSpace (Work.StemsB.fibre q γ)) →
      ThomCylAt r N (restrictFibre q (Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f))) →
      ThomCylAt r N q)
    {Y : Type} [TopologicalSpace Y] (hY : PathConnectedSpace Y) (y₀ : Y) (n : ℕ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells n Y ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (hd : CWThom.FibreData r N q)
    (hpc : ∀ γ : Work.RatHurewicz.attachCells n Y ι f,
      PathConnectedSpace (Work.StemsB.fibre q γ))
    (hpc0 : PathConnectedSpace {x : X // q x = Work.RatHurewicz.attachIncl n Y ι f y₀})
    (IH : ∀ (X' : Type) [TopologicalSpace X'] (q' : C(X', Y)), Work.StemsB.IsSerreFibration q' →
      CWThom.FibreData r N q' → PathConnectedSpace {x : X' // q' x = y₀} → ThomCylAt r N q') :
    ThomCylAt r N q := by
  refine hcell (n + 2) (by omega) hY ι f q hq (fun γ => (hd γ).1) (fun γ => (hd γ).2) hpc ?_
  set S : Set (Work.RatHurewicz.attachCells n Y ι f) :=
    Set.range (Work.RatHurewicz.attachIncl n Y ι f) with hS
  let φ : Y ≃ₜ ↥S := Work.RatHurewicz.rangeHomeo n Y ι f
  let q' : C(↥(q ⁻¹' S), Y) :=
    (⟨φ.symm, φ.symm.continuous_toFun⟩ : C(↥S, Y)).comp (restrictFibre q S)
  have hq' : Work.StemsB.IsSerreFibration q' :=
    CWThom.isSerreFibration_comp_homeo φ.symm (isSerreFibration_restrictFibre q hq S)
  have hd' : CWThom.FibreData r N q' :=
    CWThom.fibreData_comp_homeo φ.symm (CWThom.fibreData_restrictFibre hd S)
  -- the path connectedness of the fibre at the old base point
  have hpc' : PathConnectedSpace {x : ↥(q ⁻¹' S) // q' x = y₀} := by
    have h1 : {x : ↥(q ⁻¹' S) // q' x = y₀} ≃ₜ
        {x : ↥(q ⁻¹' S) // restrictFibre q S x = φ y₀} :=
      CWThom.fibreHomeo_comp_homeo φ.symm (restrictFibre q S) y₀
    have h2 : {x : ↥(q ⁻¹' S) // restrictFibre q S x = φ y₀} ≃ₜ
        {x : X // q x = Work.RatHurewicz.attachIncl n Y ι f y₀} :=
      CWThom.fibreHomeo_restrictFibre q S (φ y₀)
    exact CWThom.pathConnectedSpace_of_homeo (h1.trans h2).symm hpc0
  -- the fibre homeomorphism of the restricted fibration is `φ`-equivariant
  have hfibHomeo : ∀ γ : Y, Work.StemsB.fibre q' γ ≃ₜ Work.StemsB.fibre q (φ γ).1 := fun γ => by
    exact (CWThom.fibreHomeo_comp_homeo φ.symm (restrictFibre q S) γ).trans
      (CWThom.fibreHomeo_restrictFibre q S (φ γ))
  -- the conclusion for the restriction, then the invariance under the range homeomorphism
  have hres : ThomCylAt r N (restrictFibre q S) :=
    thomCylAt_of_homeo r N φ.symm q' (restrictFibre q S)
      (fun x => by
        show restrictFibre q S x = (φ.symm).symm (q' x)
        rw [show q' x = φ.symm (restrictFibre q S x) from rfl, Homeomorph.symm_symm,
          Homeomorph.apply_symm_apply])
      (IH _ q' hq' hd' hpc')
  exact hres

/-- **The cellular step of the CW-model Thom case** (the crux of the cell-by-cell induction).

Let `Γ' = Work.RatHurewicz.attachCells (D-2) Γ ι f` be obtained from `Γ` by attaching cells of
dimension `D ≥ 2` along the maps `f`, let `q : C(X,Γ')` be a Serre fibration whose fibres satisfy
the hypotheses of the target at *every* point of `Γ'`, and suppose the conclusion
(`Work.Serre.ThomCylAt r N`) holds for the restriction of `q` to the old part
`↥(q ⁻¹' range (attachIncl (D-2) Γ ι f))`.  Then it holds for `q` itself.

This is the inductive step of the cell-by-cell induction: it combines

* the triviality of the disc-pair bundle of `q` over each new cell (the fibre-homotopy
  triviality of a Serre fibration over a disc),
* the *local* Thom class of the trivial pair bundle over a cell
  (`Work.Serre.modelThomRatPairQ`, or its relative form over a cube),
* the long exact sequences of the triple `A' ⊆ N ⊆ D'` (with `D' = cyl q`,
  `A' = range (cylIncl q)` and `N = (cylRetract q)⁻¹ Γ ∪ A'`) and of the pair `(Γ', Γ)`,
  compared by the cup product with the Thom class and the cross product with the fibre
  fundamental class, via the Leibniz rules `Work.StemsB.pairDelta_mixedCup_general_R`,
  `Work.StemsB.mixedCup_relToAbs_R` and the naturality `Work.Cohomology.cupNaturalH`. -/
theorem thomCylCellStep (r N : ℕ) (hr : 1 ≤ r) (D : ℕ) (hD : 2 ≤ D)
    {Γ : Type} [TopologicalSpace Γ] (hΓ : PathConnectedSpace Γ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ))
    {X : Type} [TopologicalSpace X] (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (hq : Work.StemsB.IsSerreFibration q)
    (hvan : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hgen : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      Nonempty (ratH (TopCat.of (Work.StemsB.fibre q γ)) r ≅ ModuleCat.of ℚ ℚ))
    (hpc : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      PathConnectedSpace (Work.StemsB.fibre q γ))
    (IH : ThomCylAt r N (restrictFibre q (Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f)))) :
    ThomCylAt r N q := by
  -- This is the cellular step of the project, proved independently (and axiom-clean) in
  -- `Submission/Work/RatHurewicz/cellStepShell.lean` as `Work.Serre.ThomCylCellStepAlt_free`
  -- (the cell step at every level `D ≥ 2`, with the vacuous case `N < r` handled internally).
  exact Work.RatHurewicz.thomCylCellStepAlt_free r N hr D hD hΓ ι f q hq hvan hgen hpc IH

/-- **The reduction of the CW-model Thom case to its base case and its cellular step.**

This is the *assembly*: pure bookkeeping over the model tower once

* `hbase` — the base case `Γ = PUnit` (`Work.Serre.thomCylBaseCase`), and
* `hstep` — the cellular step (`Work.Serre.thomCylCellStep`, the crux)

are available.  The induction runs over the stages of `Work.Serre.CWModel.towerA`, whose step is
`killStep (genStep ·)`, each sub-step being a cell attachment (`Work.RatHurewicz.attachCells`); so
`hstep` is applied twice per stage.  The fibre hypotheses must hold at *every* point of the current
stage: they come from the ones at the base point by `Work.Serre.fibreConditions_of_path` (the
stages are path connected, `StA.conn`), and the identification of the old part of an attachment
with the previous stage is `Work.Serre.thomCylAt_of_homeo` applied to the homeomorphism
`↥(range (attachIncl …)) ≃ₜ Γ` (`Topology.IsEmbedding.toHomeomorph` of
`Work.RatHurewicz.isInducing_attachIncl` and `Work.RatHurewicz.AttachRange.attachIncl_injective`). -/
theorem cwModelThomCase_of_pieces (B : Type) [TopologicalSpace B] (b₀ : B)
    (hB2 : ∀ i : ℕ, i < 2 → Subsingleton (HomotopyGroup (Fin i) B b₀)) (N r : ℕ) (hr : 1 ≤ r)
    (hbase : ∀ (X : Type) [TopologicalSpace X] (q : C(X, PUnit)),
      Work.StemsB.IsSerreFibration q →
      PathConnectedSpace (Work.StemsB.fibre q ()) →
      (∀ t : ℕ, 0 < t → t ≠ r → t ≤ N → CategoryTheory.Limits.IsZero
        (ratH (TopCat.of (Work.StemsB.fibre q ())) t)) →
      Nonempty (ratH (TopCat.of (Work.StemsB.fibre q ())) r ≅ ModuleCat.of ℚ ℚ) →
      ThomCylAt r N q)
    (hstep : ∀ (D : ℕ) (hD : 2 ≤ D) {Γ : Type} [TopologicalSpace Γ]
      (hΓ : PathConnectedSpace Γ) (ι : Type)
      (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ))
      {X : Type} [TopologicalSpace X] (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)),
      Work.StemsB.IsSerreFibration q →
      (∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
        CategoryTheory.Limits.IsZero (ratH (TopCat.of (Work.StemsB.fibre q γ)) t)) →
      (∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
        Nonempty (ratH (TopCat.of (Work.StemsB.fibre q γ)) r ≅ ModuleCat.of ℚ ℚ)) →
      (∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
        PathConnectedSpace (Work.StemsB.fibre q γ)) →
      ThomCylAt r N (restrictFibre q (Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f))) →
      ThomCylAt r N q) :
    ∀ k : ℕ, ∀ (X : Type) [TopologicalSpace X]
      (q : C(X, (Work.Serre.CWModel.towerA B b₀ 2 (le_refl 2) hB2 k).Y)),
      Work.StemsB.IsSerreFibration q →
      SimplyConnectedSpace (Work.Serre.CWModel.towerA B b₀ 2 (le_refl 2) hB2 k).Y →
      PathConnectedSpace (Work.StemsB.fibre q (Work.Serre.CWModel.towerA B b₀ 2 (le_refl 2) hB2 k).y₀) →
      (∀ t : ℕ, 0 < t → t ≠ r → t ≤ N → CategoryTheory.Limits.IsZero
        (ratH (TopCat.of (Work.StemsB.fibre q
          (Work.Serre.CWModel.towerA B b₀ 2 (le_refl 2) hB2 k).y₀)) t)) →
      Nonempty (ratH (TopCat.of (Work.StemsB.fibre q
        (Work.Serre.CWModel.towerA B b₀ 2 (le_refl 2) hB2 k).y₀)) r ≅ ModuleCat.of ℚ ℚ) →
      ∃ U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q)
          (Set.range (Work.Serre.cylIncl q)),
        ∀ m : ℕ, m + r + 1 ≤ N + 1 →
          CategoryTheory.IsIso (ModuleCat.ofHom
            (((Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl q)) m (r + 1))).flip U ∘ₗ
              (Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ m).hom)) := by

  classical
  intro k X _ q hq hsc hfib0 hvan hgen
  haveI hconn : PathConnectedSpace
      (Work.Serre.CWModel.towerA B b₀ 2 (le_refl 2) hB2 k).Y :=
    (Work.Serre.CWModel.towerA B b₀ 2 (le_refl 2) hB2 k).conn
  have hd : CWThom.FibreData r N q :=
    CWThom.fibreData_of_point hq (Work.Serre.CWModel.towerA B b₀ 2 (le_refl 2) hB2 k).y₀
      hvan hgen
  have key : ∀ k : ℕ, ∀ (X : Type) [TopologicalSpace X]
      (q : C(X, (Work.Serre.CWModel.towerA B b₀ 2 (le_refl 2) hB2 k).Y)),
      Work.StemsB.IsSerreFibration q → CWThom.FibreData r N q →
      PathConnectedSpace {x : X // q x = (Work.Serre.CWModel.towerA B b₀ 2 (le_refl 2) hB2 k).y₀} →
      ThomCylAt r N q := by
    intro k
    induction k with
    | zero =>
      intro X _ q hq hd hpc
      exact thomCylBaseCase r N hr X q hq hpc
        (fun t ht htr htN => (hd ()).1 t ht htr htN) (hd ()).2
    | succ k ih =>
      intro X _ q hq hd hpc
      -- the fibration over the intermediate stage `genStep (towerA k)`
      have hmid : ∀ (X' : Type) [TopologicalSpace X']
          (q' : C(X', (Work.Serre.CWModel.genStep
            (Work.Serre.CWModel.towerA B b₀ 2 (le_refl 2) hB2 k)).Y)),
          Work.StemsB.IsSerreFibration q' → CWThom.FibreData r N q' →
          PathConnectedSpace {x : X' // q' x = (Work.Serre.CWModel.genStep
            (Work.Serre.CWModel.towerA B b₀ 2 (le_refl 2) hB2 k)).y₀} →
          ThomCylAt r N q' := by
        intro X' _ q' hq' hd' hpc'
        haveI hconn' : PathConnectedSpace
            (Work.Serre.CWModel.genStep
              (Work.Serre.CWModel.towerA B b₀ 2 (le_refl 2) hB2 k)).Y :=
          (Work.Serre.CWModel.genStep
            (Work.Serre.CWModel.towerA B b₀ 2 (le_refl 2) hB2 k)).conn
        exact thomCylAt_of_attachCells r N hstep
          (Work.Serre.CWModel.towerA B b₀ 2 (le_refl 2) hB2 k).conn
          (Work.Serre.CWModel.towerA B b₀ 2 (le_refl 2) hB2 k).y₀ ((2 : ℕ) - 2 + k) _ _
          q' hq' hd'
          (fun γ => CWThom.pathConnectedSpace_fibre_of_point q' hq'
            (Work.Serre.CWModel.genStep
              (Work.Serre.CWModel.towerA B b₀ 2 (le_refl 2) hB2 k)).y₀ hpc' γ)
          hpc'
          (fun X'' _ q'' hq'' hd'' hpc'' => ih X'' q'' hq'' hd'' hpc'')
      haveI hconn'' : PathConnectedSpace
          (Work.Serre.CWModel.towerA B b₀ 2 (le_refl 2) hB2 (k + 1)).Y :=
        (Work.Serre.CWModel.towerA B b₀ 2 (le_refl 2) hB2 (k + 1)).conn
      exact thomCylAt_of_attachCells r N hstep
        (Work.Serre.CWModel.genStep
          (Work.Serre.CWModel.towerA B b₀ 2 (le_refl 2) hB2 k)).conn
        (Work.Serre.CWModel.genStep
          (Work.Serre.CWModel.towerA B b₀ 2 (le_refl 2) hB2 k)).y₀ ((2 : ℕ) - 2 + k + 1) _ _
        q hq hd
        (fun γ => CWThom.pathConnectedSpace_fibre_of_point q hq
          (Work.Serre.CWModel.towerA B b₀ 2 (le_refl 2) hB2 (k + 1)).y₀ hpc γ)
        hpc hmid
  exact key k X q hq hd hfib0

end

theorem cwModelThomCase (B : Type) [TopologicalSpace B] (b₀ : B)
    (hB2 : ∀ i : ℕ, i < 2 → Subsingleton (HomotopyGroup (Fin i) B b₀))
    (N r : ℕ) (hr : 1 ≤ r) :
    ∀ k : ℕ, ∀ (X : Type) [TopologicalSpace X]
      (q : C(X, (Work.Serre.CWModel.towerA B b₀ 2 (le_refl 2) hB2 k).Y)),
      Work.StemsB.IsSerreFibration q →
      SimplyConnectedSpace (Work.Serre.CWModel.towerA B b₀ 2 (le_refl 2) hB2 k).Y →
      PathConnectedSpace (Work.StemsB.fibre q (Work.Serre.CWModel.towerA B b₀ 2 (le_refl 2) hB2 k).y₀) →
      (∀ t : ℕ, 0 < t → t ≠ r → t ≤ N → CategoryTheory.Limits.IsZero
        (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q
          (Work.Serre.CWModel.towerA B b₀ 2 (le_refl 2) hB2 k).y₀)) t)) →
      Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q
        (Work.Serre.CWModel.towerA B b₀ 2 (le_refl 2) hB2 k).y₀)) r ≅ ModuleCat.of ℚ ℚ) →
      ∃ U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q)
          (Set.range (Work.Serre.cylIncl q)),
        ∀ m : ℕ, m + r + 1 ≤ N + 1 →
          CategoryTheory.IsIso (ModuleCat.ofHom
            (((Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl q)) m (r + 1))).flip U ∘ₗ
              (Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ m).hom)) := by
  intro k X _ q hq hsc hpc hvan hgen
  exact cwModelThomCase_of_pieces B b₀ hB2 N r hr
    (fun X' _ q' hq' hfib0' hvan' hgen' => thomCylBaseCase r N hr X' q' hq' hfib0' hvan' hgen')
    (fun D hD Γ _ hΓ ι f X' _ q' hq' hvan' hgen' hpc' IH =>
      thomCylCellStep r N hr D hD hΓ ι f q' hq' hvan' hgen' hpc' IH)
    k X q hq hsc hpc hvan hgen

end Work.Serre
