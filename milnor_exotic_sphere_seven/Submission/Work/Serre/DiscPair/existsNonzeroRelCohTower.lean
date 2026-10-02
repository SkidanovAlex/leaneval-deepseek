import Mathlib
import Submission.Work.Serre.CWModel.Tower
import Submission.Work.Serre.CWModelThomAux
import Submission.Work.Serre.thomCylAt_of_homeo
import Submission.Work.Serre.isSerreFibration_restrictFibre
import Submission.Work.Serre.DiscPair.thomCylAt_of_contractible
import Submission.Work.Serre.DiscPair.isZero_relCoh_discPairNewCells_lt
import Submission.Work.Serre.DiscPair.isIso_relCohMap_incl_of_isZero
import Submission.Work.Serre.DiscPair.isZero_conePairRelCoh
import Submission.Work.Serre.DiscPair.oldPartRelCohIso
import Submission.Work.Serre.DiscPair.cylPair_concentrated
import Submission.Work.RatHurewicz.CompressRelToRelPi

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# A nonzero relative class over every stage of the model tower

The pair `(cyl q, range (cylIncl q))` of the mapping cylinder of a Serre fibration `q : X → Γ` is
the "disc pair bundle" of `q`: `cyl q` retracts onto `Γ` and the bottom copy of `X` plays the role
of the sphere bundle.  Its relative rational cohomology in degree `r+1` is the group in which the
relative Thom class lives.  Over a *weakly contractible* base `Γ` this group is a line
(`Work.Serre.DiscPair.cylPair_concentrated`), so a nonzero class exists.

Here we prove the corresponding *existence* statement over an arbitrary stage of the model tower
`Work.Serre.CWModel.towerA B b₀ b hb hB k`: for every Serre fibration over such a stage whose
fibres are rationally concentrated in degree `r` through degree `N` (`r ≥ 1`), the group
`H^{r+1}(cyl q, range (cylIncl q); ℚ)` is nonzero.

The proof is the cell-by-cell induction over the tower, with the two inputs

* the base case `Γ = PUnit`, where the pair is concentrated in degree `r+1` with `ℚ` there
  (`Work.Serre.DiscPair.cylPair_concentrated`, via `ratH_of_contractible_base`);
* the cellular step: for an attachment of cells of dimension `D ≥ 2`, the pullback of relative
  classes along the inclusion of the new cells is an isomorphism in degree `r+1` — the new-cell
  groups vanish in the two degrees `r+1` and `r+2` (`Work.Serre.DiscPair.isZero_relCoh_discPairNewCells`,
  `…_lt`, both `≠ D + r + 1` because `D ≥ 2`, `r ≥ 1`) — and the old part is the disc pair of the
  restriction of `q` to the previous stage (`Work.Serre.DiscPair.oldPartRelCohIso`).  So a nonzero
  class over the old part transports to a nonzero class over the attachment.

Only cells of dimension `≥ b ≥ 2` occur in the tower, so the cellular step is always applicable.
-/

namespace Work.Serre.DiscPair

open CategoryTheory CategoryTheory.Limits
open scoped Topology

noncomputable section

set_option maxHeartbeats 1600000

/-- **The existence of a nonzero relative class** `H^{r+1}(cyl q, range (cylIncl q); ℚ) ≠ 0` for
every Serre fibration over `Γ` whose fibres are rationally concentrated in degree `r` through
degree `N`.  This is the *existence half* of the relative Thom class. -/
def HasNonzeroRelCoh (Γ : Type) [TopologicalSpace Γ] : Prop :=
  ∀ {X : Type} [TopologicalSpace X] (q : C(X, Γ)) (r N : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N)
    (hq : Work.StemsB.IsSerreFibration q)
    (hpc : ∀ γ : Γ, PathConnectedSpace (Work.StemsB.fibre q γ))
    (hvan : ∀ γ : Γ, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hgen : ∀ γ : Γ,
      Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) r ≅ ModuleCat.of ℚ ℚ)),
    ∃ V : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q)
      (Set.range (Work.Serre.cylIncl q)), V ≠ 0

/-! ## The base case: a point -/

/-- The fibre of a map into a one point space is the total space. -/
def homeoFibrePUnit {X : Type} [TopologicalSpace X] (q : C(X, PUnit)) :
    Work.StemsB.fibre q () ≃ₜ X where
  toFun x := x.1
  invFun x := ⟨x, Subsingleton.elim (q x) ()⟩
  left_inv x := Subtype.ext rfl
  right_inv x := rfl
  continuous_toFun := continuous_subtype_val
  continuous_invFun := Continuous.subtype_mk continuous_id _

/-- **The base case of the induction**: over a one point base the pair is concentrated in degree
`r+1` (`Work.Serre.DiscPair.cylPair_concentrated`), so there is a nonzero class. -/
theorem hasNonzeroRelCoh_punit : HasNonzeroRelCoh PUnit := by
  intro X _ q r N hr hrN hq hpc hvan hgen
  have hBc : ∀ i : ℕ, Subsingleton (HomotopyGroup (Fin i) PUnit ()) :=
    fun i => Work.Stems.subsingleton_of_contractible (⟨⟩ : PUnit)
  haveI hX : PathConnectedSpace X :=
    Work.Serre.CWThom.pathConnectedSpace_of_homeo (homeoFibrePUnit q) (hpc ())
  obtain ⟨hXvan, hXgen⟩ := ratH_of_contractible_base q () r N hr hrN hq inferInstance hBc hX
    (hpc ()) (hvan ()) (hgen ())
  have hBacyc : Work.Serre.RatAcyclic PUnit :=
    ratAcyclic_of_weaklyContractible_base () inferInstance hBc
  obtain ⟨-, hMgen⟩ := cylPair_concentrated q r N hr hBacyc hX hXvan hXgen
  obtain ⟨eU⟩ := hMgen
  refine ⟨eU.inv.hom (1 : ℚ), ?_⟩
  intro h0
  have h1 : eU.hom.hom (eU.inv.hom (1 : ℚ)) = 1 := by
    have h := congrArg
      (fun (g : ModuleCat.of ℚ ℚ ⟶ ModuleCat.of ℚ ℚ) => ModuleCat.Hom.hom g (1 : ℚ))
      (Iso.inv_hom_id eU)
    simpa [ModuleCat.hom_comp] using h
  rw [h0, map_zero] at h1
  exact one_ne_zero h1.symm

/-! ## Invariance under a homeomorphism of the base -/

/-- **A nonzero relative class transports along a homeomorphism of the base.**  The two fibrations
`q` and `φ.symm ∘ q` have homeomorphic mapping cylinders, carrying one bottom copy onto the other,
whence an isomorphism of the relative cohomology groups. -/
theorem hasNonzeroRelCoh_of_homeo {Γ Γ' : Type} [TopologicalSpace Γ] [TopologicalSpace Γ']
    (φ : Γ ≃ₜ Γ') (h : HasNonzeroRelCoh Γ) : HasNonzeroRelCoh Γ' := by
  intro X _ q r N hr hrN hq hpc hvan hgen
  let q' : C(X, Γ) := (⟨φ.symm, φ.symm.continuous_toFun⟩ : C(Γ', Γ)).comp q
  have hq' : Work.StemsB.IsSerreFibration q' :=
    Work.Serre.CWThom.isSerreFibration_comp_homeo φ.symm hq
  have hfib : ∀ γ : Γ, Work.StemsB.fibre q' γ ≃ₜ Work.StemsB.fibre q (φ γ) := fun γ =>
    Work.Serre.CWThom.fibreHomeo_comp_homeo φ.symm q γ
  have hpc' : ∀ γ : Γ, PathConnectedSpace (Work.StemsB.fibre q' γ) := fun γ =>
    Work.Serre.CWThom.pathConnectedSpace_of_homeo (hfib γ).symm (hpc (φ γ))
  have hvan' : ∀ γ : Γ, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q' γ)) t) :=
    fun γ t ht htr htN => IsZero.of_iso (hvan (φ γ) t ht htr htN)
      (Classical.choice (Work.StemsB.c2odd_ratH_iso_of_homeo (hfib γ) t))
  have hgen' : ∀ γ : Γ, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q' γ)) r
      ≅ ModuleCat.of ℚ ℚ) := fun γ =>
    ⟨(Classical.choice (Work.StemsB.c2odd_ratH_iso_of_homeo (hfib γ) r)).trans
      (hgen (φ γ)).some⟩
  obtain ⟨V, hV⟩ := h q' r N hr hrN hq' hpc' hvan' hgen'
  -- the induced homeomorphism of mapping cylinders
  have he_q : ∀ x : X, φ (q' x) = q x := fun x => φ.apply_symm_apply (q x)
  have hd : ∀ x : X, φ.symm (q x) = q' x := fun x => rfl
  let H : Work.Serre.cyl q' ≃ₜ Work.Serre.cyl q :=
    Work.Serre.cylHomeoOfHomeo q' q φ he_q hd
  have hHI : ∀ p : X, H (Work.Serre.cylIncl q' p) = Work.Serre.cylIncl q p := fun p =>
    Work.Serre.cylHomeoOfHomeo_apply_cylIncl q' q φ he_q hd p
  have hHs : ∀ p : X, H.symm (Work.Serre.cylIncl q p) = Work.Serre.cylIncl q' p := fun p =>
    Work.Serre.cylHomeoOfHomeo_symm_apply_cylIncl q' q φ he_q hd p
  have he : ∀ y : Work.Serre.cyl q', y ∈ Set.range (Work.Serre.cylIncl q') ↔
      H y ∈ Set.range (Work.Serre.cylIncl q) := by
    intro y
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p, hHI p⟩
    · rintro ⟨p, hp⟩
      refine ⟨p, ?_⟩
      rw [← hHs p, hp, H.symm_apply_apply]
  have hf : ∀ y ∈ Set.range (Work.Serre.cylIncl q'), H y ∈ Set.range (Work.Serre.cylIncl q) :=
    fun y hy => (he y).mp hy
  haveI hiso : CategoryTheory.IsIso (Work.Thom.relCohMap
      (H : C(Work.Serre.cyl q', Work.Serre.cyl q))
      (Set.range (Work.Serre.cylIncl q')) (Set.range (Work.Serre.cylIncl q)) hf ℚ (r + 1)) :=
    Work.Thom.CapGlue.isIso_relComplexMap_homeomorph (Set.range (Work.Serre.cylIncl q'))
      (Set.range (Work.Serre.cylIncl q)) H he ℚ (r + 1)
  refine ⟨(asIso (Work.Thom.relCohMap (H : C(Work.Serre.cyl q', Work.Serre.cyl q))
      (Set.range (Work.Serre.cylIncl q')) (Set.range (Work.Serre.cylIncl q)) hf ℚ (r + 1))).inv V, ?_⟩
  intro h0
  refine hV ?_
  have h1 := Iso.inv_hom_id_apply
    (asIso (Work.Thom.relCohMap (H : C(Work.Serre.cyl q', Work.Serre.cyl q))
      (Set.range (Work.Serre.cylIncl q')) (Set.range (Work.Serre.cylIncl q)) hf ℚ (r + 1))) V
  rw [h0, map_zero] at h1
  exact h1.symm

/-! ## The cellular step -/

/-- **The cellular step.**  For an attachment of cells of dimension `D ≥ 2` to `Γ` along the maps
`f`, the relative cohomology of the disc-pair bundle in degree `r+1` is identified with that of the
old part: the new-cell groups vanish in degrees `r+1` and `r+2` (`D ≥ 2`, `r ≥ 1` imply that these
are not `D + r + 1`), and the old part is the disc pair of the restriction of `q`
(`Work.Serre.DiscPair.oldPartRelCohIso`).  So a nonzero class over the old part gives one over the
new space. -/
theorem hasNonzeroRelCoh_cellStep (D : ℕ) (hD : 2 ≤ D) {Γ : Type} [TopologicalSpace Γ]
    (ι : Type) (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f)) (r N : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N)
    (hq : Work.StemsB.IsSerreFibration q)
    (hpc : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      PathConnectedSpace (Work.StemsB.fibre q γ))
    (hvan : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hgen : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) r ≅ ModuleCat.of ℚ ℚ))
    (IH : ∃ V : Work.Thom.RelCoh ℚ (r + 1)
      (Work.Serre.cyl (Work.Serre.restrictFibre q
        (Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f))))
      (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q
        (Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f))))), V ≠ 0) :
    ∃ V : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q)
      (Set.range (Work.Serre.cylIncl q)), V ≠ 0 := by
  classical
  set A : Set (Work.Serre.cyl q) := Set.range (Work.Serre.cylIncl q) with hA
  set Nw : Set (Work.Serre.cyl q) :=
    (Work.Serre.cylRetract q) ⁻¹' Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f) ∪ A with hNw
  -- the fibre pairs at the cell centres are concentrated in degree `r+1`
  have hcone : ∀ i : ι, ∀ j : ℕ, j ≤ N + 1 → j ≠ r + 1 →
      CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ j
        ↥((Work.Serre.cylRetract q) ⁻¹' {Work.Serre.csrCentre (D - 2) Γ ι f i})
        {x | (x : Work.Serre.cyl q) ∈ A}) := by
    intro i j hj hjne
    exact isZero_conePairRelCoh D hD Γ ι f q hq r N hr i
      (hpc (Work.Serre.csrCentre (D - 2) Γ ι f i))
      (hvan (Work.Serre.csrCentre (D - 2) Γ ι f i))
      (hgen (Work.Serre.csrCentre (D - 2) Γ ι f i)) j hj hjne
  -- the new-cell groups vanish in degrees `r+1` and `r+2`
  have hnew : ∀ m : ℕ, (m = r + 1 ∨ m = r + 2) →
      CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ m (Work.Serre.cyl q) Nw) := by
    intro m hm
    by_cases hDm : D ≤ m
    · refine isZero_relCoh_discPairNewCells D hD Γ ι f q hq
        (fun i => (hpc (Work.Serre.csrCentre (D - 2) Γ ι f i)).nonempty) r N hcone m hDm ?_ ?_
      · omega
      · rcases hm with h | h <;> omega
    · exact isZero_relCoh_discPairNewCells_lt D hD Γ ι f q hq m (by omega)
  have hAB : A ⊆ Nw := Set.subset_union_right
  -- the extension over the new cells is an isomorphism
  haveI hiso1 : CategoryTheory.IsIso (Work.Thom.relCohMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥Nw, Work.Serre.cyl q))
      {x : ↥Nw | (x : Work.Serre.cyl q) ∈ A} A (fun x hx => hx) ℚ (r + 1)) :=
    isIso_relCohMap_incl_of_isZero (TopCat.of (Work.Serre.cyl q)) A Nw hAB (r + 1)
      (hnew (r + 1) (Or.inl rfl)) (hnew (r + 2) (Or.inr rfl))
  let e1 := asIso (Work.Thom.relCohMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C(↥Nw, Work.Serre.cyl q))
      {x : ↥Nw | (x : Work.Serre.cyl q) ∈ A} A (fun x hx => hx) ℚ (r + 1))
  -- the old part is the disc pair of the restricted fibration
  obtain ⟨e2⟩ := oldPartRelCohIso D hD ι f q (r + 1)
  obtain ⟨V, hV⟩ := IH
  refine ⟨(Iso.trans e1 e2).inv V, ?_⟩
  intro h0
  refine hV ?_
  have h1 := Iso.inv_hom_id_apply (Iso.trans e1 e2) V
  rw [h0, map_zero] at h1
  exact h1.symm

/-- **The cellular step, in the form used by the induction**: a nonzero class over `Γ` gives one
over an attachment of `D`-cells.  The old part of the attachment is the range of the attaching
inclusion, which is homeomorphic to `Γ` (`Work.RatHurewicz.rangeHomeo`). -/
theorem hasNonzeroRelCoh_attachCells (D : ℕ) (hD : 2 ≤ D) {Γ : Type} [TopologicalSpace Γ]
    (ι : Type) (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ)) (h : HasNonzeroRelCoh Γ) :
    HasNonzeroRelCoh (Work.RatHurewicz.attachCells (D - 2) Γ ι f) := by
  intro X _ q r N hr hrN hq hpc hvan hgen
  set S : Set (Work.RatHurewicz.attachCells (D - 2) Γ ι f) :=
    Set.range (Work.RatHurewicz.attachIncl (D - 2) Γ ι f) with hS
  let qo : C(↥(q ⁻¹' S), ↥S) := Work.Serre.restrictFibre q S
  have hS' : HasNonzeroRelCoh ↥S :=
    hasNonzeroRelCoh_of_homeo (Work.RatHurewicz.rangeHomeo (D - 2) Γ ι f) h
  have hpc' : ∀ γ : ↥S, PathConnectedSpace (Work.StemsB.fibre qo γ) := fun γ =>
    Work.Serre.CWThom.pathConnectedSpace_of_homeo
      (Work.Serre.CWThom.fibreHomeo_restrictFibre q S γ).symm (hpc γ.1)
  have hvan' : ∀ γ : ↥S, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre qo γ)) t) :=
    fun γ t ht htr htN => IsZero.of_iso (hvan γ.1 t ht htr htN)
      (Classical.choice (Work.StemsB.c2odd_ratH_iso_of_homeo
        (Work.Serre.CWThom.fibreHomeo_restrictFibre q S γ) t))
  have hgen' : ∀ γ : ↥S, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre qo γ)) r
      ≅ ModuleCat.of ℚ ℚ) := fun γ =>
    ⟨(Classical.choice (Work.StemsB.c2odd_ratH_iso_of_homeo
        (Work.Serre.CWThom.fibreHomeo_restrictFibre q S γ) r)).trans (hgen γ.1).some⟩
  obtain ⟨V, hV⟩ := hS' qo r N hr hrN
    (Work.Serre.isSerreFibration_restrictFibre q hq S) hpc' hvan' hgen'
  exact hasNonzeroRelCoh_cellStep D hD ι f q r N hr hrN hq hpc hvan hgen ⟨V, hV⟩

/-! ## The induction over the model tower -/

/-- **Every stage of the model tower carries a nonzero relative class.**  The tower is built from
the base `PUnit` by the two cell attachments `genStep`/`killStep` (of dimensions `≥ b ≥ 2`), so the
statement follows by induction from `hasNonzeroRelCoh_punit` and `hasNonzeroRelCoh_attachCells`. -/
theorem hasNonzeroRelCoh_tower (B : Type) [TopologicalSpace B] (b₀ : B) (b : ℕ) (hb : 2 ≤ b)
    (hB : ∀ i : ℕ, i < b → Subsingleton (HomotopyGroup (Fin i) B b₀)) (k : ℕ) :
    HasNonzeroRelCoh (Work.Serre.CWModel.towerA B b₀ b hb hB k).Y := by
  induction k with
  | zero => exact hasNonzeroRelCoh_punit
  | succ k ih =>
    have h1 : HasNonzeroRelCoh
        (Work.Serre.CWModel.genStep (Work.Serre.CWModel.towerA B b₀ b hb hB k)).Y :=
      hasNonzeroRelCoh_attachCells (Γ := (Work.Serre.CWModel.towerA B b₀ b hb hB k).Y)
        ((b - 2 + k) + 2) (by omega)
        (HomotopyGroup (Fin ((b - 2 + k) + 2)) B
          ((Work.Serre.CWModel.towerA B b₀ b hb hB k).g
            (Work.Serre.CWModel.towerA B b₀ b hb hB k).y₀))
        (fun _ => ContinuousMap.const (Work.RatHurewicz.cellSphere (b - 2 + k))
          (Work.Serre.CWModel.towerA B b₀ b hb hB k).y₀) ih
    show HasNonzeroRelCoh (Work.RatHurewicz.attachCells ((b - 2 + k) + 1)
        (Work.Serre.CWModel.genStep (Work.Serre.CWModel.towerA B b₀ b hb hB k)).Y
        {α : HomotopyGroup (Fin ((b - 2 + k) + 2))
            (Work.Serre.CWModel.genStep (Work.Serre.CWModel.towerA B b₀ b hb hB k)).Y
            (Work.Serre.CWModel.genStep (Work.Serre.CWModel.towerA B b₀ b hb hB k)).y₀ //
          Work.Serre.piMapN
            (Work.Serre.CWModel.genStep (Work.Serre.CWModel.towerA B b₀ b hb hB k)).g
            ((b - 2 + k) + 2)
            (Work.Serre.CWModel.genStep (Work.Serre.CWModel.towerA B b₀ b hb hB k)).y₀ α = 1}
        (fun j => Work.RatHurewicz.killFamily ((b - 2 + k) + 1)
          (Work.Serre.CWModel.genStep (Work.Serre.CWModel.towerA B b₀ b hb hB k)).Y
          (Work.Serre.CWModel.genStep (Work.Serre.CWModel.towerA B b₀ b hb hB k)).y₀ j.1))
    exact hasNonzeroRelCoh_attachCells
      (Γ := (Work.Serre.CWModel.genStep (Work.Serre.CWModel.towerA B b₀ b hb hB k)).Y)
      (((b - 2 + k) + 1) + 2) (by omega) _ _ h1



/-- **The requested lemma.**  For every stage of the model tower
`Work.Serre.CWModel.towerA B b₀ b hb hB k` and every Serre fibration over it whose fibres are
rationally concentrated in degree `r` (`r ≥ 1`) through degree `N`, the relative cohomology
`H^{r+1}(cyl q, range (cylIncl q); ℚ)` is nonzero.  This is `hasNonzeroRelCoh_tower`. -/
theorem existsNonzeroRelCohTower {B : Type} [TopologicalSpace B] (b₀ : B) (b : ℕ) (hb : 2 ≤ b)
    (hB : ∀ i : ℕ, i < b → Subsingleton (HomotopyGroup (Fin i) B b₀)) :
    ∀ k : ℕ, ∀ {X : Type} [TopologicalSpace X]
      (q : C(X, (Work.Serre.CWModel.towerA B b₀ b hb hB k).Y)) (r N : ℕ) (hr : 1 ≤ r)
      (hrN : r ≤ N)
      (hq : Work.StemsB.IsSerreFibration q)
      (hpc : ∀ γ : (Work.Serre.CWModel.towerA B b₀ b hb hB k).Y,
        PathConnectedSpace (Work.StemsB.fibre q γ))
      (hvan : ∀ γ : (Work.Serre.CWModel.towerA B b₀ b hb hB k).Y, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
        CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
      (hgen : ∀ γ : (Work.Serre.CWModel.towerA B b₀ b hb hB k).Y,
        Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) r ≅ ModuleCat.of ℚ ℚ)),
      ∃ V : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (Set.range (Work.Serre.cylIncl q)),
        V ≠ 0 := by
  intro k
  exact hasNonzeroRelCoh_tower B b₀ b hb hB k

end

end Work.Serre.DiscPair
