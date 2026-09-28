import Mathlib
import Submission.Work.RatHurewicz.cutCoverModel
import Submission.Work.RatHurewicz.AttachPush.CellInterior

/-!
# Transporting the `coneDown` contractibility to the attachment

**Diagnosis (recorded so that it is not redone).**  `Work.Serre.CellStep.cellPieceIso` is a statement
about *chain complexes / cohomology* (`cellPieceMap`), **not** about spaces: it cannot transport a
`ContractibleSpace` instance.  The transport `ContractibleSpace ↥(coneDownModel n sr ε) →
ContractibleSpace ↥(coneDown ε sr i)` factors through two homeomorphisms:

1. `coneDownModelPieceHomeo` (**proved below**): pure subtype bookkeeping between the model set read
   inside the closed model cell and the model set inside `CellVec n` — possible because
   `‖y‖ < sr < 1` puts every point of the model set in the closed unit ball `cellDisk n`.
2. `cellMap_image_homeomorph` (**stated below, open**): the characteristic map restricted to an open
   `U ⊆ cellInner n` is a homeomorphism onto its image.
-/

namespace Work.RatHurewicz

open scoped Topology

noncomputable section

variable (n : ℕ) (Γ : Type) [TopologicalSpace Γ] (ι : Type)

/-- **Subtype bookkeeping**: the model set of `coneDown`, read inside the closed model cell
`cellDisk n`, is homeomorphic to the model set inside `CellVec n`.  (`sr < 1` is what makes the
inverse well defined.) -/
def coneDownModelPieceHomeo (sr ε : ℝ) (hsr : sr < 1) :
    ↥{y : cellDisk n | (y : CellVec n) ∈ coneDownModel n sr ε} ≃ₜ
      ↥(coneDownModel n sr ε) where
  toFun y := ⟨(y : CellVec n), y.2⟩
  invFun v := ⟨⟨(v : CellVec n), by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      linarith [v.2.1, hsr]⟩, v.2⟩
  left_inv y := Subtype.ext (Subtype.ext rfl)
  right_inv v := Subtype.ext rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- **The inverse of the characteristic map on a piece inside the open cell**, as a bundled
continuous map: it sends a point of the image to the (unique, by `cellMap_injective_cellInner`)
preimage in `U`.  It is a top-level `def` because inside a `Homeomorph ... where` block the earlier
fields are not in scope in the later ones. -/
noncomputable def cellMapPieceInv (f : ι → C(cellSphere n, Γ)) (i : ι) {U : Set (cellDisk n)}
    (hUo : IsOpen U) (hU : U ⊆ cellInner n) :
    C(↥(cellMap n Γ ι f i '' U), ↥U) where
  toFun z := ⟨Classical.choose z.2, (Classical.choose_spec z.2).1⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ (fun z => (Classical.choose_spec z.2).1)
    rw [continuous_def]
    intro V' hV'o
    have himg : (fun z : ↥(cellMap n Γ ι f i '' U) =>
        (Classical.choose z.2 : cellDisk n)) ⁻¹' V'
        = Subtype.val ⁻¹' {y : attachCells n Γ ι f |
            ∃ x ∈ U ∩ V', cellMap n Γ ι f i x = y} := by
      ext z
      constructor
      · intro hz
        exact ⟨Classical.choose z.2, ⟨(Classical.choose_spec z.2).1, hz⟩,
          (Classical.choose_spec z.2).2⟩
      · rintro ⟨x, ⟨hxU, hxV⟩, hxz⟩
        have hspec := Classical.choose_spec z.2
        have heq : Classical.choose z.2 = x :=
          congrArg (fun y : ↥(cellInner n) => (y : cellDisk n))
            (Work.RatHurewicz.cellMap_injective_cellInner (f := f) i
              (show cellMap n Γ ι f i
                  (⟨Classical.choose z.2, hU hspec.1⟩ : ↥(cellInner n))
                = cellMap n Γ ι f i (⟨x, hU hxU⟩ : ↥(cellInner n)) from
                hspec.2.trans hxz.symm))
        show (Classical.choose z.2 : cellDisk n) ∈ V'
        rw [heq]
        exact hxV
    rw [himg]
    exact continuous_subtype_val.isOpen_preimage _
      (Work.RatHurewicz.isOpen_cellMap_image (hUo.inter hV'o) (fun x hx => hU hx.1))

/-- **The characteristic map is a homeomorphism onto its image on an open piece inside the open
cell.** -/
noncomputable def cellMapImageHomeo (f : ι → C(cellSphere n, Γ)) (i : ι) {U : Set (cellDisk n)}
    (hUo : IsOpen U) (hU : U ⊆ cellInner n) :
    ↥U ≃ₜ ↥(cellMap n Γ ι f i '' U) where
  toFun x := ⟨cellMap n Γ ι f i x, x.1, x.2, rfl⟩
  invFun := fun z => cellMapPieceInv n Γ ι f i hUo hU z
  left_inv x := by
    have hmem : ∃ x' ∈ U, cellMap n Γ ι f i x' = cellMap n Γ ι f i (x : cellDisk n) :=
      ⟨x.1, x.2, rfl⟩
    obtain ⟨-, h2⟩ := Classical.choose_spec hmem
    refine Subtype.ext ?_
    show (Classical.choose hmem : cellDisk n) = (x : cellDisk n)
    exact congrArg (fun y : ↥(cellInner n) => (y : cellDisk n))
      (Work.RatHurewicz.cellMap_injective_cellInner (f := f) i
        (show cellMap n Γ ι f i
            (⟨Classical.choose hmem, hU (Classical.choose_spec hmem).1⟩ : ↥(cellInner n))
          = cellMap n Γ ι f i (⟨x.1, hU x.2⟩ : ↥(cellInner n)) from h2))
  right_inv z := by
    refine Subtype.ext ?_
    exact (Classical.choose_spec z.2).2
  continuous_toFun := by fun_prop
  continuous_invFun := (cellMapPieceInv n Γ ι f i hUo hU).continuous

/-- **The characteristic map is a homeomorphism onto its image on a piece inside the open cell.** -/
theorem cellMap_image_homeomorph (f : ι → C(cellSphere n, Γ)) (i : ι) {U : Set (cellDisk n)}
    (hUo : IsOpen U) (hU : U ⊆ cellInner n) :
    Nonempty (↥U ≃ₜ ↥(cellMap n Γ ι f i '' U)) :=
  ⟨cellMapImageHomeo n Γ ι f i hUo hU⟩

/-- **The `coneDown` piece of the attachment is contractible**, for `0 < sr < 1`, `0 ≤ ε < 1`:
transport the model-set contractibility (`contractibleSpace_coneDownModel`) across
`coneDownModelPieceHomeo` and then across the characteristic-map homeomorphism
`cellMapImageHomeo`. -/
theorem contractibleSpace_coneDown (f : ι → C(cellSphere n, Γ)) (i : ι) {sr ε : ℝ}
    (hsr : 0 < sr) (hsr1 : sr < 1) (hε : 0 ≤ ε) (hε1 : ε < 1) :
    ContractibleSpace ↥(coneDown n Γ ι f ε sr i) := by
  set U : Set (cellDisk n) := {y | (y : CellVec n) ∈ coneDownModel n sr ε} with hUdef
  have hUo : IsOpen U := by
    rw [hUdef, coneDownModel]
    refine IsOpen.inter ?_ ?_
    · exact isOpen_lt (by fun_prop : Continuous fun y : cellDisk n => ‖(y : CellVec n)‖)
        continuous_const
    · refine isOpen_lt (show Continuous fun y : cellDisk n =>
        ((y : CellVec n)) (Fin.last (n+1)) + ε * ‖(y : CellVec n)‖ from by fun_prop)
        continuous_const
  have hUsub : U ⊆ cellInner n := by
    intro y hy
    rw [cellInner]
    exact lt_of_lt_of_le hy.1 (le_of_lt hsr1)
  haveI h0 : ContractibleSpace ↥(coneDownModel n sr ε) :=
    contractibleSpace_coneDownModel n hsr hε hε1
  haveI h1 : ContractibleSpace ↥U :=
    (coneDownModelPieceHomeo (n := n) (sr := sr) (ε := ε) hsr1).contractibleSpace
  haveI h2 : ContractibleSpace ↥(cellMap n Γ ι f i '' U) :=
    ((cellMapImageHomeo n Γ ι f i hUo hUsub).symm).contractibleSpace
  exact h2

/-- **The cone piece is open.**  Both defining conditions of its model set are strict inequalities of
continuous functions, and the model set lies in the open cell (`sr < 1`), so
`isOpen_cellMap_image` applies. -/
theorem isOpen_coneDown (f : ι → C(cellSphere n, Γ)) (i : ι) {sr ε : ℝ} (hsr1 : sr < 1) :
    IsOpen (coneDown n Γ ι f ε sr i) := by
  refine Work.RatHurewicz.isOpen_cellMap_image ?_ ?_
  · refine IsOpen.inter ?_ ?_
    · exact isOpen_lt (by fun_prop : Continuous fun y : cellDisk n => ‖(y : CellVec n)‖)
        continuous_const
    · refine isOpen_lt (show Continuous fun y : cellDisk n =>
        ((y : CellVec n)) (Fin.last (n+1)) + ε * ‖(y : CellVec n)‖ from by fun_prop)
        continuous_const
  · intro y hy
    rw [cellInner]
    exact lt_of_lt_of_le hy.1 (le_of_lt hsr1)

/-- **The slitted ball is open.**  The slit `{ρ ≤ ‖y‖ ∧ cellLast y + η‖y‖ ≤ 0}` that `ballSlit`
removes from the `sr`-ball is **closed** (an intersection of two closed sublevel sets), so its
complement is open — this is exactly the point of slitting by the closed cone. -/
theorem isOpen_ballSlit (f : ι → C(cellSphere n, Γ)) (i : ι) {ρ sr η : ℝ} (hsr1 : sr < 1) :
    IsOpen (ballSlit n Γ ι f ρ sr η i) := by
  refine Work.RatHurewicz.isOpen_cellMap_image ?_ ?_
  · -- the `sr`-ball minus a closed truncated cone
    have hcl : IsClosed {y : cellDisk n | ρ ≤ ‖(y : CellVec n)‖ ∧
        cellLast (y : CellVec n) + η * ‖(y : CellVec n)‖ ≤ 0} :=
      IsClosed.inter
        (isClosed_le continuous_const (by fun_prop : Continuous fun y : cellDisk n =>
          ‖(y : CellVec n)‖))
        (isClosed_le (show Continuous fun y : cellDisk n =>
          ((y : CellVec n)) (Fin.last (n+1)) + η * ‖(y : CellVec n)‖ from by fun_prop)
          continuous_const)
    exact (isOpen_lt (by fun_prop : Continuous fun y : cellDisk n => ‖(y : CellVec n)‖)
      continuous_const).inter hcl.isOpen_compl
  · intro y hy
    rw [cellInner]
    exact lt_of_lt_of_le hy.1 (le_of_lt hsr1)

/-- **The characteristic-map transport applied to `ballSlit`**: the piece is homeomorphic to the
subtype of the closed model cell cut out by `ballSlitModel`, so contractibility of the model set
transports to the piece.  (The openness of the model set is proved inline: the slit is an
intersection of two closed sublevel sets, hence closed.  Note `Work.RatHurewicz.isOpen_ballSlitModel`
is declared in `contractible_ballSlit.lean` — do **not** redeclare it here.) -/
theorem cellMapImageHomeo_ballSlit (f : ι → C(cellSphere n, Γ)) (i : ι) {ρ sr η : ℝ}
    (hsr1 : sr < 1) :
    Nonempty (↥{y : cellDisk n | (y : CellVec n) ∈ ballSlitModel n ρ sr η} ≃ₜ
      ↥(ballSlit n Γ ι f ρ sr η i)) := by
  have hcl : IsClosed {y : cellDisk n | ρ ≤ ‖(y : CellVec n)‖ ∧
      cellLast (y : CellVec n) + η * ‖(y : CellVec n)‖ ≤ 0} :=
    IsClosed.inter
      (isClosed_le continuous_const (by fun_prop : Continuous fun y : cellDisk n =>
        ‖(y : CellVec n)‖))
      (isClosed_le (show Continuous fun y : cellDisk n =>
        ((y : CellVec n)) (Fin.last (n+1)) + η * ‖(y : CellVec n)‖ from by fun_prop)
        continuous_const)
  have hUo : IsOpen {y : cellDisk n | (y : CellVec n) ∈ ballSlitModel n ρ sr η} :=
    (isOpen_lt (by fun_prop : Continuous fun y : cellDisk n => ‖(y : CellVec n)‖)
      continuous_const).inter hcl.isOpen_compl
  exact ⟨cellMapImageHomeo n Γ ι f i hUo (by
    intro y hy
    rw [cellInner]
    exact lt_of_lt_of_le hy.1 (le_of_lt hsr1))⟩

/-- **`coneDown ∩ thick ρ` is open.**  `thick ρ = Work.Serre.cellU f ρ` is the complement of the
union of the closed ρ-balls and is open (`Work.Serre.isOpen_cellU`); intersecting with the open
`coneDown` (both cut out by strict inequalities in the open cell) gives an open set. -/
theorem isOpen_coneDown_inter_thick (f : ι → C(cellSphere n, Γ)) (i : ι) {ρ sr ε : ℝ}
    (hρ1 : ρ < 1) (hsr1 : sr < 1) :
    IsOpen (coneDown n Γ ι f ε sr i ∩ thick n Γ ι f ρ) :=
  (isOpen_coneDown n Γ ι f i hsr1).inter (Work.Serre.isOpen_cellU f hρ1)

/-- **`ballSlit ∩ thick ρ` is open** — the same argument, with the slitted ball in place of the cone
piece (its openness is `isOpen_ballSlit`, which is where the *closed* slit pays off). -/
theorem isOpen_ballSlit_inter_thick (f : ι → C(cellSphere n, Γ)) (i : ι) {ρ sr η : ℝ}
    (hρ1 : ρ < 1) (hsr1 : sr < 1) :
    IsOpen (ballSlit n Γ ι f ρ sr η i ∩ thick n Γ ι f ρ) :=
  (isOpen_ballSlit n Γ ι f i hsr1).inter (Work.Serre.isOpen_cellU f hρ1)

/-- **The cone pieces of distinct cells are disjoint.**  Both are contained in the image of the
*open* model cell (`sr < 1`), and distinct cells have disjoint interiors — the same
`Work.Serre.disjoint_cellImg` that the `csrGeom` disjointness proofs use. -/
theorem disjoint_coneDown (f : ι → C(cellSphere n, Γ)) {sr ε : ℝ} (hsr1 : sr < 1)
    {i j : ι} (hij : i ≠ j) :
    Disjoint (coneDown n Γ ι f ε sr i) (coneDown n Γ ι f ε sr j) := by
  refine Work.Serre.disjoint_cellImg f hij (fun y hy => ?_)
  rw [cellInner]
  exact lt_of_lt_of_le hy.1 (le_of_lt hsr1)

end

end Work.RatHurewicz
