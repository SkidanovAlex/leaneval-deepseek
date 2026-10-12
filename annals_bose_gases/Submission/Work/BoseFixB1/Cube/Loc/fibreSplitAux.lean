import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.SliceVocab
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.Cube.Loc.fibreSplitAux` — the vocabulary of the **Step Loc** fibre split

`Submission/Work/BoseFixB1/Cube/Loc/DESIGN_stepLoc.md` §1(iii) asks for the functional-level fibre
formula

    sbWordCube v h μ u Φ = ∫ y in (acube ℓ \ bA v μ u)^m, sbWordCube v h μ u (fibre y Φ) ,

splitting the `k + m` slots into the first `k` (the **in-box** slots) and the last `m` (the
**out-of-box** slots).  This module carries the *split vocabulary* which that formula, and the three
slot lemmas it decomposes into (`cnPlusBoxInd_fibreSplit`, `tBdiagFormInd_fibreSplit`,
`qLHSword_fibreSplit_of_integrable`), are stated in:

* `mkSlot k m z y = Sum.elim z y ∘ finSumFinEquiv.symm` — the merge of the two slot blocks; it is
  **definitionally the corpus's `mergeBlock`** (`mkSlot_eq_mergeBlock`), because
  `finSumFinEquiv (Sum.inl a) = Fin.castAdd m a` and `finSumFinEquiv (Sum.inr b) = Fin.natAdd k b`
  (`rfl`).  Hence every block-split lemma of `Submission.Work.AboxBlockSplit` /
  `Submission.Work.SmallBoxSuperadd` applies verbatim;
* `fibre`/`coslice` — the two slices, definitionally the corpus's `sbs_slice`/`sbs_slice2`, which is
  the interface of `qLHSden1_expect_eq_slice` and of the corpus's kinetic block splits;
* `Dloc m a A = (acube a \ A)^m` — the bounded out-of-box domain of the right-hand side, with its
  elementary facts (`Dloc_subset_abox`, `measurableSet_Dloc`, and
  `exists_mem_A_of_mem_abox_not_mem_Dloc`: a point of the box outside `Dloc` has a slot in `A`);
* `SubsectorSupp` — the (frozen) a.e. support hypothesis rewritten in the block coordinates, and
  `subsectorSupp_merge` — the same hypothesis transported along the measure-preserving block merge
  (`Submission.BoseGases.aboxSplit_measurePreserving_restrict`, inverted), with no measurability of
  `Φ` needed (`MeasurePreserving.preimage_null`), exactly as in
  `Work.BoseFixB1B.ae_slice_support`.

⚠ This module belongs to the **repair** of the frozen
`Submission/Work/BoseFixB1/Cube/Loc/sbWordCube_fibreSplit.lean`, whose statement is mis-stated: its
**potential** slot needs the integrability hypothesis (★)
(`FINDING_sbWordCube_fibreSplit.md` §1–§5).  Nothing here depends on that frozen statement.

Two conversions are left to the callers, since each states them in its own interface:

* the frozen `∀ᵐ x, Φ x ≠ 0 → ∀ i, ((finSumFinEquiv.symm i).isLeft → x i ∈ A) ∧ (…)` form of the
  support hypothesis gives `SubsectorSupp k m a A Φ` by `filter_upwards` and the two `rfl`-lemmas
  (`Fin.castAdd`/`Fin.natAdd`) — this is the only direction the slot lemmas need;
* the *sliced* form of `subsectorSupp_merge` (for a.e. out-of-box `y` with a slot in `A`, the fibre
  vanishes a.e. in `z`) is the composition of `subsectorSupp_merge` with
  `MeasureTheory.Measure.ae_prod_iff_ae_ae` (which needs `Measurable Φ`).
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1.Cube.Loc

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The slot merge and its two evaluation laws -/

/-- The merge of the first `k` slots (the **in-box** slots, a `Fin k`-tuple `z`) with the last `m`
slots (the **out-of-box** slots, a `Fin m`-tuple `y`).  Definitionally the corpus's `mergeBlock`
(`mkSlot_eq_mergeBlock`). -/
def mkSlot (k m : ℕ) (z : X k) (y : X m) : X (k + m) :=
  fun i => Sum.elim z y ((finSumFinEquiv (m := k) (n := m)).symm i)

lemma mkSlot_inl (k m : ℕ) (z : X k) (y : X m) (a : Fin k) :
    mkSlot k m z y (finSumFinEquiv (m := k) (n := m) (Sum.inl a)) = z a := by
  simp [mkSlot]

lemma mkSlot_inr (k m : ℕ) (z : X k) (y : X m) (b : Fin m) :
    mkSlot k m z y (finSumFinEquiv (m := k) (n := m) (Sum.inr b)) = y b := by
  simp [mkSlot]

/-- `finSumFinEquiv` sends the first block to `Fin.castAdd`. -/
lemma finSumFinEquiv_inl_eq_castAdd (k m : ℕ) (a : Fin k) :
    finSumFinEquiv (m := k) (n := m) (Sum.inl a) = Fin.castAdd m a := rfl

/-- `finSumFinEquiv` sends the second block to `Fin.natAdd`. -/
lemma finSumFinEquiv_inr_eq_natAdd (k m : ℕ) (b : Fin m) :
    finSumFinEquiv (m := k) (n := m) (Sum.inr b) = Fin.natAdd k b := rfl

/-- The slot merge **is** the corpus's `mergeBlock`. -/
lemma mkSlot_eq_mergeBlock (k m : ℕ) (z : X k) (y : X m) :
    mkSlot k m z y = mergeBlock k m (z, y) := by
  funext i
  rcases h : (finSumFinEquiv (m := k) (n := m)).symm i with a | b
  · have hi : i = Fin.castAdd m a := by
      rw [← finSumFinEquiv_inl_eq_castAdd, ← h, Equiv.apply_symm_apply (finSumFinEquiv (m := k) (n := m))]
    subst hi
    simp [mkSlot, mergeBlock, finSplit_castAdd]
  · have hi : i = Fin.natAdd k b := by
      rw [← finSumFinEquiv_inr_eq_natAdd, ← h, Equiv.apply_symm_apply (finSumFinEquiv (m := k) (n := m))]
    subst hi
    simp [mkSlot, mergeBlock, finSplit_natAdd]

/-- Updating an in-box slot commutes with the merge. -/
lemma update_mkSlot_castAdd (k m : ℕ) (z : X k) (y : X m) (a : Fin k) (t : E3) :
    Function.update (mkSlot k m z y) (Fin.castAdd m a) t
      = mkSlot k m (Function.update z a t) y := by
  funext i
  rcases hi : (finSumFinEquiv (m := k) (n := m)).symm i with c | b
  · have hsub : i = Fin.castAdd m c := by
      rw [← finSumFinEquiv_inl_eq_castAdd, ← hi, Equiv.apply_symm_apply (finSumFinEquiv (m := k) (n := m))]
    subst hsub
    by_cases h : c = a
    · subst h
      simp [mkSlot]
    · have h2 : Fin.castAdd m c ≠ Fin.castAdd m a :=
        fun hh => h (Fin.ext (by simpa using congrArg Fin.val hh))
      simp [mkSlot, Function.update_of_ne h2, h]
  · have hsub : i = Fin.natAdd k b := by
      rw [← finSumFinEquiv_inr_eq_natAdd, ← hi, Equiv.apply_symm_apply (finSumFinEquiv (m := k) (n := m))]
    subst hsub
    have hne : Fin.natAdd k b ≠ Fin.castAdd m a :=
      fun hh => castAdd_ne_natAdd a b hh.symm
    simp [mkSlot, Function.update_of_ne hne]

/-- Updating an out-of-box slot commutes with the merge. -/
lemma update_mkSlot_natAdd (k m : ℕ) (z : X k) (y : X m) (b : Fin m) (t : E3) :
    Function.update (mkSlot k m z y) (Fin.natAdd k b) t
      = mkSlot k m z (Function.update y b t) := by
  funext i
  rcases hi : (finSumFinEquiv (m := k) (n := m)).symm i with a | c
  · have hsub : i = Fin.castAdd m a := by
      rw [← finSumFinEquiv_inl_eq_castAdd, ← hi, Equiv.apply_symm_apply (finSumFinEquiv (m := k) (n := m))]
    subst hsub
    have hne : Fin.castAdd m a ≠ Fin.natAdd k b := fun hh => castAdd_ne_natAdd a b hh
    simp [mkSlot, Function.update_of_ne hne]
  · have hsub : i = Fin.natAdd k c := by
      rw [← finSumFinEquiv_inr_eq_natAdd, ← hi, Equiv.apply_symm_apply (finSumFinEquiv (m := k) (n := m))]
    subst hsub
    by_cases h : c = b
    · subst h
      simp [mkSlot]
    · have h2 : Fin.natAdd k c ≠ Fin.natAdd k b :=
        fun hh => h (Fin.ext (by simpa using congrArg Fin.val hh))
      simp [mkSlot, Function.update_of_ne h2, h]

/-- The fibre of `Φ` at the out-of-box configuration `y`: the in-box `k`-particle state. -/
def fibre (k m : ℕ) (Φ : X (k + m) → ℝ) (y : X m) : X k → ℝ :=
  fun z => Φ (mkSlot k m z y)

lemma fibre_eq_sbs_slice (k m : ℕ) (Φ : X (k + m) → ℝ) (y : X m) :
    fibre k m Φ y = sbs_slice Φ y := by
  funext z
  rw [fibre, sbs_slice, mkSlot_eq_mergeBlock]

/-- The `m`-particle slice at a frozen in-box configuration. -/
def coslice (k m : ℕ) (Φ : X (k + m) → ℝ) (z : X k) : X m → ℝ :=
  fun y => Φ (mkSlot k m z y)

lemma coslice_eq_sbs_slice2 (k m : ℕ) (Φ : X (k + m) → ℝ) (z : X k) :
    coslice k m Φ z = sbs_slice2 Φ z := by
  funext y
  rw [coslice, sbs_slice2, mkSlot_eq_mergeBlock]

/-! ## 2. The out-of-box domain -/

/-- The out-of-box configurations of the right-hand side of the fibre formula:
`(acube a \ A)^m`, i.e. every slot lies in the big cube and outside the sliding box. -/
def Dloc (m : ℕ) (a : ℝ) (A : Set E3) : Set (X m) :=
  {y | ∀ j : Fin m, y j ∈ acube a ∧ y j ∉ A}

lemma mem_Dloc_iff (m : ℕ) (a : ℝ) (A : Set E3) (y : X m) :
    y ∈ Dloc m a A ↔ ∀ j : Fin m, y j ∈ acube a ∧ y j ∉ A := Iff.rfl

lemma Dloc_subset_abox (m : ℕ) (a : ℝ) (A : Set E3) :
    Dloc m a A ⊆ abox m a := fun _ hy j => (hy j).1

lemma measurableSet_Dloc (m : ℕ) {a : ℝ} {A : Set E3} (hA : MeasurableSet A) :
    MeasurableSet (Dloc m a A) := by
  have h : Dloc m a A = Set.univ.pi (fun _ : Fin m => acube a \ A) := by
    ext y
    simp [Dloc]
  rw [h]
  exact MeasurableSet.pi (s := (Set.univ : Set (Fin m)))
    (t := fun _ : Fin m => acube a \ A) Set.countable_univ
    (fun j _ => (acube_measurable a).diff hA)

/-- Membership in `abox m a` but not in `Dloc m a A` means that some slot lies in `A`. -/
lemma exists_mem_A_of_mem_abox_not_mem_Dloc {m : ℕ} {a : ℝ} {A : Set E3} {y : X m}
    (hy : y ∈ abox m a) (hyD : y ∉ Dloc m a A) : ∃ j : Fin m, y j ∈ A := by
  by_contra h
  apply hyD
  intro j
  exact ⟨hy j, fun hj => h ⟨j, hj⟩⟩

/-! ## 3. The a.e. support condition and its transport along the merge -/

/-- The frozen support hypothesis, written in the block coordinates of `mkSlot`: a.e. `Φ` vanishes
unless the in-box slots `Fin.castAdd m ·` lie in `A` and the out-of-box slots `Fin.natAdd k ·`
avoid it. -/
def SubsectorSupp (k m : ℕ) (a : ℝ) (A : Set E3) (Φ : X (k + m) → ℝ) : Prop :=
  ∀ᵐ x ∂(MeasureTheory.volume.restrict (abox (k + m) a)), Φ x ≠ 0 →
    (∀ i : Fin k, x (Fin.castAdd m i) ∈ A) ∧ (∀ j : Fin m, x (Fin.natAdd k j) ∉ A)

/-- **The a.e. support survives the merge.**  If `Φ` is supported a.e. on the subsector of the
`(k+m)`-box, then for a.e. pair `(z,y)` the value `Φ (mergeBlock (z,y))` can be non-zero only when
every in-box coordinate `z i` lies in `A` and every out-of-box coordinate `y j` avoids `A`.

No measurability of `Φ` is used (`MeasurePreserving.preimage_null`). -/
lemma subsectorSupp_merge {k m : ℕ} {a : ℝ} {A : Set E3} {Φ : X (k + m) → ℝ}
    (h : SubsectorSupp k m a A Φ) :
    ∀ᵐ p ∂((MeasureTheory.volume.restrict (abox k a)).prod
        (MeasureTheory.volume.restrict (abox m a))),
      Φ (mergeBlock k m p) ≠ 0 → (∀ i : Fin k, p.1 i ∈ A) ∧ (∀ j : Fin m, p.2 j ∉ A) := by
  classical
  set μk : Measure (X k) := MeasureTheory.volume.restrict (abox k a) with hμk
  set μm : Measure (X m) := MeasureTheory.volume.restrict (abox m a) with hμm
  set μB : Measure (X (k + m)) := MeasureTheory.volume.restrict (abox (k + m) a) with hμB
  have hbad : μB {x : X (k + m) |
      ¬ (Φ x ≠ 0 → (∀ i : Fin k, x (Fin.castAdd m i) ∈ A) ∧
          (∀ j : Fin m, x (Fin.natAdd k j) ∉ A))} = 0 :=
    (MeasureTheory.ae_iff (μ := μB)).mp h
  have hmp : MeasurePreserving (⇑(Submission.BoseGases.blockSplitEquiv k m)) μB (μk.prod μm) := by
    simpa [hμk, hμm, hμB] using
      Submission.BoseGases.aboxSplit_measurePreserving_restrict k m a
  have hsymm := hmp.symm (e := Submission.BoseGases.blockSplitEquiv k m)
  have hcoord : ∀ p : X k × X m,
      (Submission.BoseGases.blockSplitEquiv k m).symm p = mergeBlock k m p := by
    intro p
    apply (Submission.BoseGases.blockSplitEquiv k m).injective
    rw [show (Submission.BoseGases.blockSplitEquiv k m)
          ((Submission.BoseGases.blockSplitEquiv k m).symm p) = p from Equiv.apply_symm_apply _ _,
      Submission.BoseGases.blockSplitEquiv_apply]
    exact Prod.ext (funext fun i => (merge_castAdd_coord p.1 p.2 i).symm)
      (funext fun j => (merge_natAdd_coord p.1 p.2 j).symm)
  refine (MeasureTheory.ae_iff (μ := μk.prod μm)).mpr ?_
  refine le_antisymm ?_ (by simp)
  refine le_trans (measure_mono ?_) (le_of_eq (hsymm.preimage_null hbad))
  intro p hp
  simp only [Set.mem_preimage, hcoord p]
  intro hx
  apply hp
  intro hne
  exact ⟨fun i => by
      have h1 := (hx hne).1 i
      simpa only [merge_castAdd_coord p.1 p.2 i] using h1,
    fun j => by
      have h2 := (hx hne).2 j
      simpa only [merge_natAdd_coord p.1 p.2 j] using h2⟩

end Work.BoseFixB1.Cube.Loc
