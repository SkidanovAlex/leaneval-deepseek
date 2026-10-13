/-
Area DSCOH (curric-46) — the normalization comparison: the "degenerate simplices" homotopy.

This file collects the tuple-level vocabulary for the homotopy `Work.DSCOH.Norm.semiHom` between
the identity of the semi-ordered Čech complex and the composite `ordProj ≫ ordIncl`:

* `dup a z` : the tuple obtained from `z` by inserting a copy of the `a`-th entry just after
  position `a`;
* `firstRepeat z` : the position of the first repeat of a nondecreasing non-injective tuple `z`
  (the smallest `a` with `z a = z a + 1`);
* `opDup`/`isoDup` : the canonical identification `∏ᶜ (U ∘ dup a z) ≅ ∏ᶜ (U ∘ z)` of the opens of a
  tuple and of its duplication (the two families of opens agree up to repetition);
* `semiHom` : the homotopy `semiTerm (n+1) ⟶ semiTerm n`, whose `z`-component is `0` on strictly
  increasing tuples and `(-1)^a • (π_{dup a z} ≫ isoDup)` on tuples whose first repeat is at `a`.
-/
import Mathlib
import Submission.Work.DSCOH.Norm.SemiOrd
import Submission.Work.DSCOH.Norm.Maps

namespace Work.DSCOH.Norm

open CategoryTheory Limits Opposite TopologicalSpace
open scoped Simplicial BigOperators

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

universe u v w

variable {X : Type u} [TopologicalSpace X] {A : Type v} [CommRing A]
variable {ι : Type w} [LinearOrder ι]

/-! ## Duplicating an entry of a tuple -/

/-- `dup a z` inserts a copy of the entry `z a` immediately after position `a`.  Equivalently it is
the composite `z ∘ predAbove a`; its positions `a` and `a + 1` both carry `z a`. -/
def dup {L : ℕ} (z : Fin L → ι) (a : Fin L) : Fin (L + 1) → ι := fun i => z (a.predAbove i)

@[simp]
lemma dup_apply {L : ℕ} (z : Fin L → ι) (a : Fin L) (i : Fin (L + 1)) :
    dup z a i = z (a.predAbove i) := rfl

lemma dup_castSucc {L : ℕ} (z : Fin L → ι) (a : Fin L) : dup z a (Fin.castSucc a) = z a :=
  congrArg z (Fin.predAbove_castSucc_self a)

lemma dup_succ {L : ℕ} (z : Fin L → ι) (a : Fin L) : dup z a (Fin.succ a) = z a :=
  congrArg z (Fin.predAbove_succ_self a)

lemma monotone_predAbove {L : ℕ} (a : Fin L) : Monotone (a.predAbove) := by
  intro i j hij
  simp only [Fin.predAbove]
  split_ifs <;>
    simp only [Fin.le_def, Fin.coe_castPred, Fin.val_pred] <;> omega

lemma monotone_dup {L : ℕ} {z : Fin L → ι} (hz : Monotone z) (a : Fin L) : Monotone (dup z a) :=
  hz.comp (monotone_predAbove a)

/-- The composite "delete position `a`, then duplicate position `a`" is the identity on indices. -/
lemma predAbove_succAbove_castSucc {L : ℕ} (a j : Fin (L + 1)) :
    a.predAbove ((Fin.castSucc a).succAbove j) = j := by
  by_cases h : j < a
  · rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_castSucc_iff.mpr h),
      Fin.predAbove_castSucc_of_le _ _ h.le]
  · rw [Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr (le_of_not_gt h)),
      Fin.predAbove_succ_of_le _ _ (le_of_not_gt h)]

/-- The composite "delete the entry after position `a`, then duplicate position `a`" is the
identity on indices. -/
lemma predAbove_succAbove_succ {L : ℕ} (a j : Fin (L + 1)) :
    a.predAbove ((Fin.succ a).succAbove j) = j := by
  by_cases h : j < a
  · rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_succ_iff.mpr h.le),
      Fin.predAbove_castSucc_of_le _ _ h.le]
  · rcases lt_or_eq_of_le (le_of_not_gt h) with hlt | heq
    · rw [Fin.succAbove_of_le_castSucc _ _ (Fin.succ_le_castSucc_iff.mpr hlt),
        Fin.predAbove_succ_of_le _ _ (le_of_not_gt h)]
    · subst heq
      rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_succ_iff.mpr le_rfl),
        Fin.predAbove_castSucc_of_le _ _ le_rfl]

/-- Deleting the first of the two copies of the duplicated entry recovers the original tuple. -/
lemma del_dup_castSucc {L : ℕ} (z : Fin (L + 1) → ι) (a : Fin (L + 1)) :
    del (dup z a) (Fin.castSucc a) = z := by
  funext j
  simp only [del, dup_apply]
  rw [predAbove_succAbove_castSucc]

/-- Deleting the second of the two copies of the duplicated entry recovers the original tuple. -/
lemma del_dup_succ {L : ℕ} (z : Fin (L + 1) → ι) (a : Fin (L + 1)) :
    del (dup z a) (Fin.succ a) = z := by
  funext j
  simp only [del, dup_apply]
  rw [predAbove_succAbove_succ]

/-! ## Two arithmetic identities for the deletion/duplication operations -/

/-- The index identity comparing "delete the `b`-th entry, then duplicate at the first repeat" with
"duplicate at the first repeat, then delete the `b`-th entry", in the case `b < a`. -/
lemma succAbove_predAbove_lt {k : ℕ} (a : Fin (k + 1)) (ha : a ≠ 0) (b : Fin (k + 2))
    (hb : (b : ℕ) < (a : ℕ)) (i : Fin (k + 2)) :
    b.succAbove ((a.pred ha).castSucc.predAbove i)
      = (a.castSucc : Fin (k + 2)).predAbove (b.castSucc.succAbove i) := by
  ext
  simp only [Fin.predAbove, Fin.succAbove, Fin.lt_def, Fin.val_castSucc, apply_dite Fin.val,
    Fin.val_pred, Fin.coe_castPred, dite_eq_ite, apply_ite Fin.val, Fin.val_succ]
  split_ifs <;> omega

/-- The index identity comparing "delete the `b`-th entry, then duplicate at the first repeat" with
"duplicate at the first repeat, then delete the `(b+1)`-st entry", in the case `a < b`. -/
lemma succAbove_predAbove_gt {k : ℕ} (a : Fin (k + 1)) (b : Fin (k + 2))
    (hb : (a : ℕ) < (b : ℕ)) (i : Fin (k + 2)) :
    b.succAbove (a.predAbove i)
      = (a.castSucc : Fin (k + 2)).predAbove (b.succ.succAbove i) := by
  ext
  simp only [Fin.predAbove, Fin.succAbove, Fin.lt_def, Fin.val_castSucc, apply_dite Fin.val,
    Fin.val_pred, Fin.coe_castPred, dite_eq_ite, apply_ite Fin.val, Fin.val_succ]
  split_ifs <;> omega

/-- Deleting position `a` and deleting position `a + 1` of a tuple whose entries there are equal
give the same tuple. -/
lemma del_castSucc_eq_del_succ {k : ℕ} (y : Fin (k + 2) → ι) (a : Fin (k + 1))
    (hy : y a.castSucc = y a.succ) : del y a.castSucc = del y a.succ := by
  funext i
  simp only [del]
  rcases lt_trichotomy i a with h | h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_castSucc_iff.mpr h),
        Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_succ_iff.mpr h.le)]
  · subst h
    rw [Fin.succAbove_of_le_castSucc _ _ le_rfl,
      Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_succ_iff.mpr le_rfl), hy]
  · rw [Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr h.le),
        Fin.succAbove_of_le_castSucc _ _ (Fin.succ_le_castSucc_iff.mpr h)]

/-! ## The first repeat position of a nondecreasing tuple -/

/-- A nondecreasing tuple which is not strictly increasing has an adjacent repeat. -/
lemma exists_repeat_of_monotone_not_strictMono {n : ℕ} {z : Fin (n + 1) → ι} (hz : Monotone z)
    (h : ¬ StrictMono z) : ∃ i : Fin n, z i.castSucc = z i.succ := by
  obtain ⟨i, j, hij, hlt⟩ : ∃ i j : Fin (n + 1), i < j ∧ ¬ z i < z j := by
    simpa [StrictMono] using not_forall.mp h
  have heq : z i = z j := le_antisymm (hz hij.le) (not_lt.mp hlt)
  have hi2 : i.1 < n := by have := j.isLt; omega
  refine ⟨⟨i.1, hi2⟩, ?_⟩
  have hcast : (⟨i.1, hi2⟩ : Fin n).castSucc = i := Fin.ext rfl
  have hj : (⟨i.1, hi2⟩ : Fin n).succ ≤ j :=
    Fin.le_iff_val_le_val.mpr (by simp only [Fin.val_succ]; have := j.isLt; omega)
  have hle1 : z (⟨i.1, hi2⟩ : Fin n).castSucc ≤ z (⟨i.1, hi2⟩ : Fin n).succ :=
    hz (Fin.castSucc_le_succ _)
  have hle2 : z (⟨i.1, hi2⟩ : Fin n).succ ≤ z (⟨i.1, hi2⟩ : Fin n).castSucc := by
    rw [hcast]
    exact (hz hj).trans_eq heq.symm
  exact le_antisymm hle1 hle2

/-- The position of the first repeat of a nondecreasing tuple which is not strictly increasing. -/
noncomputable def firstRepeat {n : ℕ} (z : Fin (n + 1) → ι) (hz : Monotone z)
    (h : ¬ StrictMono z) : Fin n :=
  (Finset.univ.filter (fun i : Fin n => z i.castSucc = z i.succ)).min' (by
    obtain ⟨i, hi⟩ := exists_repeat_of_monotone_not_strictMono hz h
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩)

lemma firstRepeat_mem {n : ℕ} (z : Fin (n + 1) → ι) (hz : Monotone z) (h : ¬ StrictMono z) :
    firstRepeat z hz h ∈ Finset.univ.filter (fun i : Fin n => z i.castSucc = z i.succ) :=
  Finset.min'_mem _ _

lemma firstRepeat_spec {n : ℕ} (z : Fin (n + 1) → ι) (hz : Monotone z) (h : ¬ StrictMono z) :
    z (firstRepeat z hz h).castSucc = z (firstRepeat z hz h).succ :=
  (Finset.mem_filter.mp (firstRepeat_mem z hz h)).2

lemma firstRepeat_le {n : ℕ} (z : Fin (n + 1) → ι) (hz : Monotone z) (h : ¬ StrictMono z)
    (i : Fin n) (hi : z i.castSucc = z i.succ) : firstRepeat z hz h ≤ i :=
  Finset.min'_le _ i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)

lemma firstRepeat_min {n : ℕ} (z : Fin (n + 1) → ι) (hz : Monotone z) (h : ¬ StrictMono z)
    (i : Fin n) (hi : i < firstRepeat z hz h) : z i.castSucc ≠ z i.succ := by
  intro hcontra
  exact absurd (firstRepeat_le z hz h i hcontra) (not_le.mpr hi)

/-! ## The canonical identification of the opens of a duplicated tuple -/

/-- The canonical morphism `∏ᶜ (U ∘ z) ⟶ ∏ᶜ (U ∘ dup a z)` of `Opens X`: the product over the
entries of `dup a z` is a product over the same family of opens with one entry repeated. -/
noncomputable def opDup (U : ι → Opens X) {L : ℕ} (z : Fin (L + 1) → ι) (a : Fin (L + 1)) :
    tupleOp U z ⟶ tupleOp U (dup z a) :=
  Pi.lift fun i => Pi.π (fun j : Fin (L + 1) => U (z j)) (a.predAbove i)

/-- The canonical identification `tupleMod P U (dup z a) ⟶ tupleMod P U z` of the sections over the
open of a tuple and over the open of its duplication. -/
noncomputable def isoDup (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) {L : ℕ}
    (z : Fin (L + 1) → ι) (a : Fin (L + 1)) : tupleMod P U (dup z a) ⟶ tupleMod P U z :=
  P.map (opDup U z a).op

/-- The `z`-component of the homotopy: zero on strictly increasing tuples, and
`(-1)^a • (π_{dup a z} ≫ isoDup)` when the first repeat of `z` is at `a`. -/
noncomputable def semiHomComp [HasProducts (ModuleCat A)] (P : (Opens X)ᵒᵖ ⥤ ModuleCat A)
    (U : ι → Opens X) (k : ℕ) (z : SemiIdx ι k) :
    semiTerm P U (k + 1) ⟶ tupleMod P U z.val :=
  if hz : StrictMono z.val then 0
  else (-1 : ℤ) ^ ((firstRepeat z.val z.property hz : Fin k) : ℕ) •
    (Pi.π (fun w : SemiIdx ι (k + 1) => tupleMod P U w.val)
        ⟨dup z.val (firstRepeat z.val z.property hz).castSucc,
          monotone_dup z.property _⟩ ≫
      isoDup P U z.val _)

/-- The "degenerate simplices" homotopy `semiTerm (n+1) ⟶ semiTerm n`. -/
noncomputable def semiHom [HasProducts (ModuleCat A)] (P : (Opens X)ᵒᵖ ⥤ ModuleCat A)
    (U : ι → Opens X) (k : ℕ) : semiTerm P U (k + 1) ⟶ semiTerm P U k :=
  Pi.lift fun z : SemiIdx ι k => semiHomComp P U k z

variable [HasProducts (ModuleCat A)] (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X)

lemma semiHom_comp (k : ℕ) (z : SemiIdx ι k) :
    semiHom P U k ≫ Pi.π (fun w : SemiIdx ι k => tupleMod P U w.val) z =
      semiHomComp P U k z :=
  Pi.lift_comp_π _ _

lemma semiHomComp_of_strictMono {k : ℕ} {z : SemiIdx ι k} (hz : StrictMono z.val) :
    semiHomComp P U k z = 0 := dif_pos hz

lemma semiHomComp_of_not_strictMono {k : ℕ} {z : SemiIdx ι k} (hz : ¬ StrictMono z.val) :
    semiHomComp P U k z =
      (-1 : ℤ) ^ ((firstRepeat z.val z.property hz : Fin k) : ℕ) •
        (Pi.π (fun w : SemiIdx ι (k + 1) => tupleMod P U w.val)
            ⟨dup z.val (firstRepeat z.val z.property hz).castSucc,
              monotone_dup z.property _⟩ ≫
          isoDup P U z.val _) := dif_neg hz

end Work.DSCOH.Norm
