import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import ChallengeDeps
import Submission.ComplEnum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The occupied-fiber measure identification

For an assignment `a` and a cell `j`, with `n := cellCount a j` occupied
particles and `N − n` complement (frozen-background) particles, the maps of
`Submission.ComplEnum` assemble into a *measure-preserving bijection*

    fullEquiv a j : X n × X (N − n) ≃ X N

sending the pair `(y, z)` (positions of the occupied particles in `occEquiv`
order and of the complement particles in `complEquiv` order) to the full
configuration `fullInsert a j y z`.  Its inverse reads off the two restrictions.
The map is a coordinate reordering, hence preserves the (product) volume:

  * `fullInsert_restrict` — inserting the two restrictions of `x` recovers `x`
    (the right-inverse identity);
  * `fullEquiv` — the bijection, with `occRestrict_fullInsert`,
    `complRestrict_fullInsert`, `fullInsert_restrict` as its side conditions;
  * `measurePreserving_fullEquiv` — `volume.map (fullEquiv a j) = volume`;
  * `integral_fullInsert` — the change-of-variables identity
    `∫_x G x = ∫_y ∫_z G (fullInsert a j y z)` (Fubini-ready substrate for
    INT1/INT2 of the slice bracket).

The domain volume is the product of the volumes of the two fibers (the pair
volume is `volume.prod volume` by `rfl`).
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

noncomputable section

/-- Type of the indices of the particles assigned to the cell `j`. -/
abbrev fmOccIdx {m N : ℕ} (a : Assign m N) (j : CellIdx m) :=
  {i : Fin N // i ∈ occSet a j}

/-- Type of the indices of the complement (background) particles. -/
abbrev fmComplIdx {m N : ℕ} (a : Assign m N) (j : CellIdx m) :=
  {i : Fin N // i ∈ occCompl a j}

/-- The union of the two index sets (everything). -/
abbrev fmUnionIdx {m N : ℕ} (a : Assign m N) (j : CellIdx m) :=
  {i : Fin N // i ∈ occSet a j ∪ occCompl a j}

/-- Reindexing the occupied fiber `X (cellCount a j)` onto functions over the
occupied indices, in `occEquiv` (increasing) order. -/
noncomputable def fmMEocc {m N : ℕ} (a : Assign m N) (j : CellIdx m) :
    X (cellCount a j) ≃ᵐ (fmOccIdx a j → ℝ³) :=
  MeasurableEquiv.piCongrLeft (fun _ : fmOccIdx a j => ℝ³) (occEquiv a j).toEquiv

/-- Reindexing the complement fiber onto functions over the complement indices. -/
noncomputable def fmMEcompl {m N : ℕ} (a : Assign m N) (j : CellIdx m) :
    X (N - cellCount a j) ≃ᵐ (fmComplIdx a j → ℝ³) :=
  MeasurableEquiv.piCongrLeft (fun _ : fmComplIdx a j => ℝ³) (complEquiv a j).toEquiv

/-- Evaluation of the occupied reindexing: `occEquiv` reads back `y`. -/
lemma fmMEocc_apply {m N : ℕ} (a : Assign m N) (j : CellIdx m) (y : X (cellCount a j))
    (s : fmOccIdx a j) : (fmMEocc a j) y s = y ((occEquiv a j).symm s) := by
  dsimp [fmMEocc]
  let e := (occEquiv a j).toEquiv
  change (MeasurableEquiv.piCongrLeft (fun _ : fmOccIdx a j => ℝ³) e) y s = y (e.symm s)
  have h := Equiv.piCongrLeft_apply_apply (P := fun _ : fmOccIdx a j => ℝ³) (e := e) y (e.symm s)
  change (Equiv.piCongrLeft (fun _ : fmOccIdx a j => ℝ³) e) y s = y (e.symm s)
  conv_lhs => rw [← Equiv.apply_symm_apply e s]
  exact h

/-- Evaluation of the complement reindexing: `complEquiv` reads back `z`. -/
lemma fmMEcompl_apply {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    (z : X (N - cellCount a j)) (s : fmComplIdx a j) :
    (fmMEcompl a j) z s = z ((complEquiv a j).symm s) := by
  dsimp [fmMEcompl]
  let e := (complEquiv a j).toEquiv
  change (MeasurableEquiv.piCongrLeft (fun _ : fmComplIdx a j => ℝ³) e) z s = z (e.symm s)
  have h := Equiv.piCongrLeft_apply_apply (P := fun _ : fmComplIdx a j => ℝ³) (e := e) z (e.symm s)
  change (Equiv.piCongrLeft (fun _ : fmComplIdx a j => ℝ³) e) z s = z (e.symm s)
  conv_lhs => rw [← Equiv.apply_symm_apply e s]
  exact h

/-- The occupied set and its complement cover every particle (as an equivalence
of index types). -/
noncomputable def fmUnionEquiv {m N : ℕ} (a : Assign m N) (j : CellIdx m) :
    fmUnionIdx a j ≃ Fin N :=
  Equiv.subtypeUnivEquiv (fun i : Fin N => by
    rw [occSet_union_compl a j]
    exact Finset.mem_univ i)

/-- Gluing the two reindexed blocks back into `X N` (measure-preserving). -/
noncomputable def fmMEGlue {m N : ℕ} (a : Assign m N) (j : CellIdx m) :
    ((fmOccIdx a j → ℝ³) × (fmComplIdx a j → ℝ³)) ≃ᵐ X N :=
  (MeasurableEquiv.piFinsetUnion (fun _ : Fin N => ℝ³) (occSet_disjoint_compl a j)).trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin N => ℝ³) (fmUnionEquiv a j))

/-- The insertion `fullInsert` as a measurable equivalence (a coordinate
reordering, hence volume-preserving). -/
noncomputable def fmEins {m N : ℕ} (a : Assign m N) (j : CellIdx m) :
    (X (cellCount a j) × X (N - cellCount a j)) ≃ᵐ X N :=
  (MeasurableEquiv.prodCongr (fmMEocc a j) (fmMEcompl a j)).trans (fmMEGlue a j)

/-- Value of the gluing map at an occupied index. -/
lemma fmMEGlue_apply_occ {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    (w : fmOccIdx a j → ℝ³) (v : fmComplIdx a j → ℝ³) (i : Fin N) (hi : i ∈ occSet a j) :
    (fmMEGlue a j (w, v)) i = w ⟨i, hi⟩ := by
  dsimp [fmMEGlue]
  let e := fmUnionEquiv a j
  have hh := Equiv.piCongrLeft_apply_apply (P := fun _ : Fin N => ℝ³) (e := e)
    ((MeasurableEquiv.piFinsetUnion (fun _ : Fin N => ℝ³) (occSet_disjoint_compl a j)) (w, v))
    (e.symm i)
  change (Equiv.piCongrLeft (fun _ : Fin N => ℝ³) e)
      ((MeasurableEquiv.piFinsetUnion (fun _ : Fin N => ℝ³) (occSet_disjoint_compl a j)) (w, v)) i = w ⟨i, hi⟩
  conv_lhs => rw [← Equiv.apply_symm_apply e i]
  rw [hh]
  change (Equiv.piFinsetUnion (fun _ : Fin N => ℝ³) (occSet_disjoint_compl a j)) (w, v) (e.symm i) = w ⟨i, hi⟩
  have hmem : i ∈ occSet a j ∪ occCompl a j := by
    rw [occSet_union_compl a j]
    exact Finset.mem_univ i
  have hsymm : e.symm i = ⟨i, hmem⟩ := by
    dsimp [e, fmUnionEquiv]
    rfl
  rw [hsymm]
  exact Equiv.piFinsetUnion_left (fun _ : Fin N => ℝ³) (occSet_disjoint_compl a j)
    (hi := hi) (hi' := hmem) (f := w) (g := v)

/-- Value of the gluing map at a complement index. -/
lemma fmMEGlue_apply_compl {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    (w : fmOccIdx a j → ℝ³) (v : fmComplIdx a j → ℝ³) (i : Fin N) (hi : i ∈ occCompl a j) :
    (fmMEGlue a j (w, v)) i = v ⟨i, hi⟩ := by
  dsimp [fmMEGlue]
  let e := fmUnionEquiv a j
  have hh := Equiv.piCongrLeft_apply_apply (P := fun _ : Fin N => ℝ³) (e := e)
    ((MeasurableEquiv.piFinsetUnion (fun _ : Fin N => ℝ³) (occSet_disjoint_compl a j)) (w, v))
    (e.symm i)
  change (Equiv.piCongrLeft (fun _ : Fin N => ℝ³) e)
      ((MeasurableEquiv.piFinsetUnion (fun _ : Fin N => ℝ³) (occSet_disjoint_compl a j)) (w, v)) i = v ⟨i, hi⟩
  conv_lhs => rw [← Equiv.apply_symm_apply e i]
  rw [hh]
  change (Equiv.piFinsetUnion (fun _ : Fin N => ℝ³) (occSet_disjoint_compl a j)) (w, v) (e.symm i) = v ⟨i, hi⟩
  have hmem : i ∈ occSet a j ∪ occCompl a j := by
    rw [occSet_union_compl a j]
    exact Finset.mem_univ i
  have hsymm : e.symm i = ⟨i, hmem⟩ := by
    dsimp [e, fmUnionEquiv]
    rfl
  rw [hsymm]
  exact Equiv.piFinsetUnion_right (fun _ : Fin N => ℝ³) (occSet_disjoint_compl a j)
    (hi := hi) (hi' := hmem) (f := w) (g := v)

/-- The occupied reindexing preserves volume. -/
lemma fmMEocc_mp {m N : ℕ} (a : Assign m N) (j : CellIdx m) :
    MeasurePreserving (⇑(fmMEocc a j)) := by
  dsimp [fmMEocc]
  exact volume_measurePreserving_piCongrLeft (fun _ : fmOccIdx a j => ℝ³) (occEquiv a j).toEquiv

/-- The complement reindexing preserves volume. -/
lemma fmMEcompl_mp {m N : ℕ} (a : Assign m N) (j : CellIdx m) :
    MeasurePreserving (⇑(fmMEcompl a j)) := by
  dsimp [fmMEcompl]
  exact volume_measurePreserving_piCongrLeft (fun _ : fmComplIdx a j => ℝ³) (complEquiv a j).toEquiv

/-- The gluing map preserves volume. -/
lemma fmMEGlue_mp {m N : ℕ} (a : Assign m N) (j : CellIdx m) :
    MeasurePreserving (⇑(fmMEGlue a j)) := by
  dsimp [fmMEGlue]
  have h1 : MeasurePreserving
      (⇑(MeasurableEquiv.piFinsetUnion (fun _ : Fin N => ℝ³) (occSet_disjoint_compl a j))) := by
    exact volume_preserving_piFinsetUnion (fun _ : Fin N => ℝ³) (occSet_disjoint_compl a j)
  have h2 : MeasurePreserving
      (⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin N => ℝ³) (fmUnionEquiv a j))) := by
    exact volume_measurePreserving_piCongrLeft (fun _ : Fin N => ℝ³) (fmUnionEquiv a j)
  change MeasurePreserving
    (⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin N => ℝ³) (fmUnionEquiv a j)) ∘
     ⇑(MeasurableEquiv.piFinsetUnion (fun _ : Fin N => ℝ³) (occSet_disjoint_compl a j)))
  exact MeasurePreserving.comp h2 h1

/-- `fmEins` (the measurable coordinate-reordering) preserves volume. -/
lemma fmEins_mp {m N : ℕ} (a : Assign m N) (j : CellIdx m) :
    MeasurePreserving (⇑(fmEins a j)) := by
  dsimp [fmEins]
  have h1 : MeasurePreserving (⇑(MeasurableEquiv.prodCongr (fmMEocc a j) (fmMEcompl a j))) := by
    exact MeasurePreserving.prod (fmMEocc_mp a j) (fmMEcompl_mp a j)
  change MeasurePreserving (⇑(fmMEGlue a j) ∘ ⇑(MeasurableEquiv.prodCongr (fmMEocc a j) (fmMEcompl a j)))
  exact MeasurePreserving.comp (fmMEGlue_mp a j) h1

/-- The measurable reordering computes exactly `fullInsert`. -/
lemma fmEins_eq_fullInsert {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    (y : X (cellCount a j)) (z : X (N - cellCount a j)) :
    (fmEins a j (y, z)) = fullInsert a j y z := by
  funext i
  by_cases hi : i ∈ occSet a j
  · calc
      (fmEins a j (y, z)) i = (fmMEGlue a j ((fmMEocc a j) y, (fmMEcompl a j) z)) i := by
        dsimp [fmEins]; rfl
      _ = (fmMEocc a j) y ⟨i, hi⟩ := by
        exact fmMEGlue_apply_occ a j ((fmMEocc a j) y) ((fmMEcompl a j) z) i hi
      _ = y ((occEquiv a j).symm ⟨i, hi⟩) := by
        exact fmMEocc_apply a j y ⟨i, hi⟩
      _ = fullInsert a j y z i := by
        dsimp [fullInsert, occInsert, complInsert]
        rw [dif_pos hi]
  · have hiC : i ∈ occCompl a j := by
      simpa [occCompl, Finset.mem_compl] using hi
    calc
      (fmEins a j (y, z)) i = (fmMEGlue a j ((fmMEocc a j) y, (fmMEcompl a j) z)) i := by
        dsimp [fmEins]; rfl
      _ = (fmMEcompl a j) z ⟨i, hiC⟩ := by
        exact fmMEGlue_apply_compl a j ((fmMEocc a j) y) ((fmMEcompl a j) z) i hiC
      _ = z ((complEquiv a j).symm ⟨i, hiC⟩) := by
        exact fmMEcompl_apply a j z ⟨i, hiC⟩
      _ = fullInsert a j y z i := by
        dsimp [fullInsert, occInsert, complInsert]
        rw [dif_neg hi, dif_pos hiC]

/-- Inserting the two restrictions of a configuration recovers it. -/
lemma fullInsert_restrict {m N : ℕ} (a : Assign m N) (j : CellIdx m) (x : X N) :
    fullInsert a j (occRestrict a j x) (complRestrict a j x) = x := by
  funext i
  by_cases hi : i ∈ occSet a j
  · dsimp [fullInsert, occInsert, complInsert, occRestrict, complRestrict]
    rw [dif_pos hi]
    congr 1
    simp
  · have hiC : i ∈ occCompl a j := by
      simpa [occCompl, Finset.mem_compl] using hi
    dsimp [fullInsert, occInsert, complInsert, occRestrict, complRestrict]
    rw [dif_neg hi, dif_pos hiC]
    congr 1
    simp

/-- The bijection between the product of the occupied and complement fibers and
the full configuration space. -/
noncomputable def fullEquiv {m N : ℕ} (a : Assign m N) (j : CellIdx m) :
    (X (cellCount a j) × X (N - cellCount a j)) ≃ X N where
  toFun := fun p => fullInsert a j p.1 p.2
  invFun := fun x => (occRestrict a j x, complRestrict a j x)
  left_inv := by
    intro p
    cases p with
    | mk y z =>
      exact Prod.ext (occRestrict_fullInsert a j y z) (complRestrict_fullInsert a j y z)
  right_inv := by
    intro x
    exact fullInsert_restrict a j x

/-- `fullEquiv` is (as a function) the volume-preserving measurable reordering. -/
lemma fullEquiv_eq_fmEins {m N : ℕ} (a : Assign m N) (j : CellIdx m) :
    (fullEquiv a j : X (cellCount a j) × X (N - cellCount a j) → X N) = ⇑(fmEins a j) := by
  funext p
  cases p with
  | mk y z =>
    exact (fmEins_eq_fullInsert a j y z).symm

/-- **The occupied-fiber reordering preserves the volume** (a coordinate
permutation of the product measure). -/
lemma measurePreserving_fullEquiv {m N : ℕ} (a : Assign m N) (j : CellIdx m) :
    MeasurePreserving (fullEquiv a j : X (cellCount a j) × X (N - cellCount a j) → X N)
      volume volume := by
  rw [fullEquiv_eq_fmEins a j]
  exact fmEins_mp a j

/-- The change-of-variables identity: integrating over the full configuration
space equals integrating over the occupied fiber and the frozen background
(the Fubini-ready substrate of INT1/INT2).  `G` must be integrable (Lean's
integral convention kills non-integrable integrands, breaking the Fubini
identity for merely measurable functions). -/
lemma integral_fullInsert {m N : ℕ} (a : Assign m N) (j : CellIdx m)
    {G : X N → ℝ} (hG : AEMeasurable G) (hI : Integrable G) :
    (∫ x : X N, G x) =
      ∫ y : X (cellCount a j), ∫ z : X (N - cellCount a j), G (fullInsert a j y z) := by
  have hInt : Integrable
      (fun p : X (cellCount a j) × X (N - cellCount a j) => G (fullInsert a j p.1 p.2))
      ((volume : Measure (X (cellCount a j))).prod (volume : Measure (X (N - cellCount a j)))) := by
    exact (measurePreserving_fullEquiv a j).integrable_comp_of_integrable hI
  calc
    (∫ x : X N, G x)
        = ∫ p : X (cellCount a j) × X (N - cellCount a j), G ((fullEquiv a j) p) := by
      have hemb : MeasurableEmbedding (⇑(fullEquiv a j)) := by
        rw [fullEquiv_eq_fmEins a j]
        exact (fmEins a j).measurableEmbedding
      exact (MeasurePreserving.integral_comp (measurePreserving_fullEquiv a j) hemb G).symm
    _ = ∫ p : X (cellCount a j) × X (N - cellCount a j), G (fullInsert a j p.1 p.2) := by
      rfl
    _ = ∫ y : X (cellCount a j), ∫ z : X (N - cellCount a j), G (fullInsert a j y z) := by
      exact (integral_prod
        (μ := (volume : Measure (X (cellCount a j))))
        (ν := (volume : Measure (X (N - cellCount a j))))
        (f := fun p : X (cellCount a j) × X (N - cellCount a j) => G (fullInsert a j p.1 p.2)) hInt)

end

end BoseGases

end Submission
