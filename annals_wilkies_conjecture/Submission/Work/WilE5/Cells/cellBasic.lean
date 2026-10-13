import Mathlib
import Submission.Work.WilE5.Cells
import Submission.Work.WilE5.SysL
import Submission.Work.WilE5.Basic

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilE5

open WilkiesDesign WilkiesDesign.E

/-! ## Helper API for the sign cells

This file proves `Work.WilE5.Cells.cellBasic`.  The proof is assembled from the elementary
facts collected here: the sign predicate and its interaction with `signOf`, the description of
the cell conditions as a pointwise condition on the atoms, the degree bookkeeping, and the
good-cell statement. -/

/-- `Sign.holds s a` says that the real number `a` has sign `s`. -/
def Sign.holds (s : Sign) (a : ℝ) : Prop :=
  match s with
  | Sign.zero => a = 0
  | Sign.pos => 0 < a
  | Sign.neg => a < 0

@[simp] theorem Sign.holds_zero (a : ℝ) : Sign.holds Sign.zero a ↔ a = 0 := Iff.rfl
@[simp] theorem Sign.holds_pos (a : ℝ) : Sign.holds Sign.pos a ↔ 0 < a := Iff.rfl
@[simp] theorem Sign.holds_neg (a : ℝ) : Sign.holds Sign.neg a ↔ a < 0 := Iff.rfl

/-- Every sign is one of the three constructors. -/
theorem Sign.eq_zero_or_pos_or_neg (s : Sign) :
    s = Sign.zero ∨ s = Sign.pos ∨ s = Sign.neg := by
  cases s <;> simp

theorem signOf_eq_zero_iff {a : ℝ} : signOf a = Sign.zero ↔ a = 0 := by
  by_cases h : a = 0
  · simp [signOf, h]
  · by_cases h2 : 0 < a
    · simp [signOf, h, h2]
    · simp [signOf, h, h2]

theorem signOf_eq_pos_iff {a : ℝ} : signOf a = Sign.pos ↔ 0 < a := by
  by_cases h : a = 0
  · simp [signOf, h]
  · by_cases h2 : 0 < a
    · simp [signOf, h, h2]
    · simp [signOf, h, h2]

theorem signOf_eq_neg_iff {a : ℝ} : signOf a = Sign.neg ↔ a < 0 := by
  by_cases h : a = 0
  · simp [signOf, h]
  · by_cases h2 : 0 < a
    · have h3 : ¬ a < 0 := not_lt.mpr (le_of_lt h2)
      simp [signOf, h, h2, h3]
    · have h3 : a < 0 := lt_of_le_of_ne (not_lt.mp h2) h
      simp [signOf, h, h2, h3]

/-- A number has the sign given by `signOf`. -/
theorem signOf_holds (a : ℝ) : (signOf a).holds a := by
  by_cases h : a = 0
  · rw [signOf_eq_zero_iff.mpr h]; exact h
  · by_cases h2 : 0 < a
    · rw [signOf_eq_pos_iff.mpr h2]; exact h2
    · have h3 : a < 0 := lt_of_le_of_ne (not_lt.mp h2) h
      rw [signOf_eq_neg_iff.mpr h3]; exact h3

/-- Two different signs cannot both be the sign of the same number. -/
theorem holds_not_both {a : ℝ} {s t : Sign} (h : s ≠ t) : ¬ (s.holds a ∧ t.holds a) := by
  rcases s with _ | _ | _ <;> rcases t with _ | _ | _
  all_goals simp only [Sign.holds_zero, Sign.holds_pos, Sign.holds_neg]
  all_goals try (exact fun hc => absurd rfl h)
  all_goals (intro hc; linarith [hc.1, hc.2])

theorem atomDeg_neg {k r : ℕ} (Q : EAPoly k r) : atomDeg (-Q) = atomDeg Q := by
  simp [atomDeg, MvPolynomial.totalDegree_neg]

/-! ### Membership in the cell conditions -/

theorem mem_cellEqs {k : ℕ} (X : SemiPf k) (σ : Fin (atomsOf X).length → Sign)
    (f : EAPoly k X.r) :
    f ∈ cellEqs X σ ↔ ∃ i : Fin (atomsOf X).length, σ i = Sign.zero ∧
      (atomsOf X).get i = f := by
  simp only [cellEqs, List.mem_map]
  constructor
  · rintro ⟨i, hi, hf⟩
    rw [Finset.mem_toList, Finset.mem_filter] at hi
    exact ⟨i, hi.2, hf⟩
  · rintro ⟨i, hσ, rfl⟩
    exact ⟨i, by rw [Finset.mem_toList, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hσ⟩, rfl⟩

theorem mem_cellPos {k : ℕ} (X : SemiPf k) (σ : Fin (atomsOf X).length → Sign)
    (g : EAPoly k X.r) :
    g ∈ cellPos X σ ↔ ∃ i : Fin (atomsOf X).length,
      (σ i = Sign.pos ∨ σ i = Sign.neg) ∧
      (if σ i = Sign.pos then (atomsOf X).get i else -(atomsOf X).get i) = g := by
  simp only [cellPos, List.mem_map]
  constructor
  · rintro ⟨i, hi, hg⟩
    rw [Finset.mem_toList, Finset.mem_filter] at hi
    exact ⟨i, hi.2, hg⟩
  · rintro ⟨i, hσ, hg⟩
    exact ⟨i, by rw [Finset.mem_toList, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hσ⟩, hg⟩

theorem cellEqs_get_mem {k : ℕ} (X : SemiPf k) (σ : Fin (atomsOf X).length → Sign)
    {i : Fin (atomsOf X).length} (hi : σ i = Sign.zero) :
    (atomsOf X).get i ∈ cellEqs X σ :=
  (mem_cellEqs X σ _).mpr ⟨i, hi, rfl⟩

theorem cellPos_get_mem {k : ℕ} (X : SemiPf k) (σ : Fin (atomsOf X).length → Sign)
    {i : Fin (atomsOf X).length} (hi : σ i = Sign.pos) :
    (atomsOf X).get i ∈ cellPos X σ :=
  (mem_cellPos X σ _).mpr ⟨i, Or.inl hi, by simp [hi]⟩

theorem cellPos_get_mem_neg {k : ℕ} (X : SemiPf k) (σ : Fin (atomsOf X).length → Sign)
    {i : Fin (atomsOf X).length} (hi : σ i = Sign.neg) :
    -(atomsOf X).get i ∈ cellPos X σ :=
  (mem_cellPos X σ _).mpr ⟨i, Or.inr hi, by simp [hi]⟩

/-- The atoms of a basic disjunct of `X` are atoms of `X`. -/
theorem mem_atomsOf_of_mem_basics {k : ℕ} {X : SemiPf k} {B : Basic k X.r} (hB : B ∈ X.basics)
    {f : EAPoly k X.r} (hf : f ∈ B.eqs ∨ f ∈ B.pos) : f ∈ atomsOf X := by
  simp only [atomsOf, List.mem_flatMap]
  exact ⟨B, hB, List.mem_append.mpr hf⟩

/-! ### The pointwise description of a cell -/

theorem cell_holds_iff {k : ℕ} (X : SemiPf k) (σ : Fin (atomsOf X).length → Sign)
    (x : Fin k → ℝ) :
    (cell X σ).holds X.c x ↔ ∀ i, (σ i).holds (eaEval X.c ((atomsOf X).get i) x) := by
  constructor
  · intro h i
    rcases Sign.eq_zero_or_pos_or_neg (σ i) with hs | hs | hs
    · rw [hs]; exact h.1 _ (cellEqs_get_mem X σ hs)
    · rw [hs]; exact h.2 _ (cellPos_get_mem X σ hs)
    · rw [hs]
      have hh := h.2 _ (cellPos_get_mem_neg X σ hs)
      rw [eaEval_neg] at hh
      exact neg_pos.mp hh
  · intro h
    refine ⟨fun f hf => ?_, fun g hg => ?_⟩
    · obtain ⟨i, hσ, hif⟩ := (mem_cellEqs X σ f).mp hf
      have hi := h i
      rw [hσ] at hi
      rw [← hif]
      simpa using hi
    · obtain ⟨i, hσ, hif⟩ := (mem_cellPos X σ g).mp hg
      have hi := h i
      rcases hσ with hσ | hσ
      · rw [hσ] at hi
        rw [← hif]
        simpa [hσ] using hi
      · rw [hσ] at hi
        have hi' : eaEval X.c ((atomsOf X).get i) x < 0 := by simpa using hi
        rw [← hif]
        rw [if_neg (by rw [hσ]; decide), eaEval_neg]
        exact neg_pos.mpr hi'

theorem holds_of_mem_cellSemiPf {k : ℕ} {X : SemiPf k}
    {σ : Fin (atomsOf X).length → Sign} {x : Fin k → ℝ}
    (hx : x ∈ (cellSemiPf X σ).set) : (cell X σ).holds X.c x := by
  have hx' : x ∈ cubeC k ∧ ∃ B ∈ [cell X σ], B.holds X.c x := hx
  obtain ⟨-, B, hB, hh⟩ := hx'
  rw [List.mem_singleton] at hB
  subst hB
  exact hh

/-! ### The six clauses of `cellBasic` -/

theorem cell_holds_signAssign {k : ℕ} (X : SemiPf k) (z : Fin k → ℝ) :
    (cell X (signAssign X z)).holds X.c z := by
  rw [cell_holds_iff]
  intro i
  rw [show signAssign X z i = signOf (eaEval X.c ((atomsOf X).get i) z) from rfl]
  exact signOf_holds _

theorem cellSemiPf_subset {k : ℕ} (X : SemiPf k) {z : Fin k → ℝ} (hz : z ∈ X.set) :
    (cellSemiPf X (signAssign X z)).set ⊆ X.set := by
  intro x hx
  have hcell := (cell_holds_iff X (signAssign X z) x).mp (holds_of_mem_cellSemiPf hx)
  obtain ⟨hx1, B, hB, hh⟩ := hx
  obtain ⟨-, B0, hB0, hB0h⟩ := hz
  refine ⟨hx1, B0, hB0, ?_⟩
  refine ⟨fun f hf => ?_, fun g hg => ?_⟩
  · obtain ⟨i, hif⟩ :=
      List.mem_iff_get.mp (mem_atomsOf_of_mem_basics hB0 (Or.inl hf))
    have hz0 : eaEval X.c ((atomsOf X).get i) z = 0 := by rw [hif]; exact hB0h.1 f hf
    have hs : signAssign X z i = Sign.zero := by
      simpa [signAssign] using signOf_eq_zero_iff.mpr hz0
    have hi := hcell i
    rw [hs] at hi
    rw [← hif]
    simpa using hi
  · obtain ⟨i, hif⟩ :=
      List.mem_iff_get.mp (mem_atomsOf_of_mem_basics hB0 (Or.inr hg))
    have hzp : 0 < eaEval X.c ((atomsOf X).get i) z := by rw [hif]; exact hB0h.2 g hg
    have hs : signAssign X z i = Sign.pos := by
      simpa [signAssign] using signOf_eq_pos_iff.mpr hzp
    have hi := hcell i
    rw [hs] at hi
    rw [← hif]
    simpa using hi

theorem cells_disjoint {k : ℕ} (X : SemiPf k)
    {σ τ : Fin (atomsOf X).length → Sign} (h : σ ≠ τ) :
    Disjoint (cellSemiPf X σ).set (cellSemiPf X τ).set := by
  rw [Set.disjoint_left]
  intro x hxσ hxτ
  have hσ := (cell_holds_iff X σ x).mp (holds_of_mem_cellSemiPf hxσ)
  have hτ := (cell_holds_iff X τ x).mp (holds_of_mem_cellSemiPf hxτ)
  have hex : ∃ i, σ i ≠ τ i := by
    by_contra hc
    exact h (funext fun i => by
      by_contra hne
      exact hc ⟨i, hne⟩)
  obtain ⟨i, hi⟩ := hex
  exact holds_not_both hi ⟨hσ i, hτ i⟩

theorem sum_flatMap_atomDeg {k r : ℕ} (L : List (Basic k r)) :
    (L.flatMap fun A => (A.eqs ++ A.pos).map atomDeg).sum
      = (L.map fun A => ((A.eqs ++ A.pos).map atomDeg).sum).sum := by
  induction L with
  | nil => rfl
  | cons A L ih =>
    simp only [List.flatMap_cons, List.map_cons, List.sum_cons, List.sum_append, ih]

theorem atomsOf_deg {k : ℕ} (X : SemiPf k) : ((atomsOf X).map atomDeg).sum = X.deg := by
  rw [atomsOf, List.map_flatMap]
  exact sum_flatMap_atomDeg X.basics

theorem cell_deg_le {k : ℕ} (X : SemiPf k) (σ : Fin (atomsOf X).length → Sign) :
    (cell X σ).deg ≤ X.deg := by
  have hcellEqs : (cellEqs X σ).map atomDeg
      = (Finset.univ.filter fun i => σ i = Sign.zero).toList.map
          (fun i => atomDeg ((atomsOf X).get i)) := by
    unfold cellEqs
    exact List.map_map
  have hcellPos : (cellPos X σ).map atomDeg
      = (Finset.univ.filter fun i => σ i = Sign.pos ∨ σ i = Sign.neg).toList.map
          (fun i => atomDeg ((atomsOf X).get i)) := by
    unfold cellPos
    rw [List.map_map]
    congr 1
    funext i
    show atomDeg (if σ i = Sign.pos then (atomsOf X).get i else -(atomsOf X).get i)
        = atomDeg ((atomsOf X).get i)
    by_cases h : σ i = Sign.pos
    · simp [h]
    · simp [h, atomDeg_neg]
  have hX : ((atomsOf X).map atomDeg).sum
      = ∑ i : Fin (atomsOf X).length, atomDeg ((atomsOf X).get i) := by
    rw [← List.ofFn_getElem_eq_map (atomsOf X) atomDeg]
    exact List.sum_ofFn
  have hEqs : ((cellEqs X σ).map atomDeg).sum
      = (Finset.univ.filter fun i => σ i = Sign.zero).sum
          (fun i => atomDeg ((atomsOf X).get i)) := by
    rw [hcellEqs, Finset.sum_map_toList]
  have hPos : ((cellPos X σ).map atomDeg).sum
      = (Finset.univ.filter fun i => σ i = Sign.pos ∨ σ i = Sign.neg).sum
          (fun i => atomDeg ((atomsOf X).get i)) := by
    rw [hcellPos, Finset.sum_map_toList]
  rw [← atomsOf_deg X, hX]
  change ((cellEqs X σ ++ cellPos X σ).map atomDeg).sum
      ≤ ∑ i : Fin (atomsOf X).length, atomDeg ((atomsOf X).get i)
  rw [List.map_append, List.sum_append, hEqs, hPos]
  have hpart : (Finset.univ.filter fun i => σ i = Sign.zero) ∪
      (Finset.univ.filter fun i => σ i = Sign.pos ∨ σ i = Sign.neg) = Finset.univ := by
    ext i
    rcases Sign.eq_zero_or_pos_or_neg (σ i) with h | h | h <;> simp [h]
  have hdisj : Disjoint (Finset.univ.filter fun i => σ i = Sign.zero)
      (Finset.univ.filter fun i => σ i = Sign.pos ∨ σ i = Sign.neg) := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi1 hi2
    rcases hi2 with h2 | h2
    · rw [hi1] at h2
      exact absurd h2 (by decide)
    · rw [hi1] at h2
      exact absurd h2 (by decide)
  rw [← Finset.sum_union hdisj, hpart]

theorem mem_cellSemiPf_self {k : ℕ} (X : SemiPf k) {z : Fin k → ℝ} (hz : z ∈ cubeC k) :
    z ∈ (cellSemiPf X (signAssign X z)).set :=
  ⟨hz, cell X (signAssign X z), List.mem_singleton.mpr rfl, cell_holds_signAssign X z⟩

theorem signAssign_mem_goodCells {k : ℕ} (X : SemiPf k) {z : Fin k → ℝ}
    (hz : z ∈ X.set) : signAssign X z ∈ goodCells X := by
  have hmem : signAssign X z ∈ allSigns X := by
    rw [allSigns, Finset.mem_toList]
    exact Finset.mem_univ _
  have hne : (cellSemiPf X (signAssign X z)).set.Nonempty :=
    Set.nonempty_of_mem (mem_cellSemiPf_self X hz.1)
  have hsub : (cellSemiPf X (signAssign X z)).set ⊆ X.set := cellSemiPf_subset X hz
  have hgood : signAssign X z ∈ (allSigns X).filter
      (fun σ => (cellSemiPf X σ).set.Nonempty ∧ (cellSemiPf X σ).set ⊆ X.set) := by
    rw [List.mem_filter]
    exact ⟨hmem, decide_eq_true ⟨hne, hsub⟩⟩
  simpa [goodCells] using hgood

end Work.WilE5

namespace Work.WilE5.Cells

theorem cellBasic {k : ℕ} (X : WilkiesDesign.E.SemiPf k) :
    (∀ z : Fin k → ℝ, (Work.WilE5.cell X (Work.WilE5.signAssign X z)).holds X.c z) ∧
    (∀ z : Fin k → ℝ, z ∈ X.set →
      (Work.WilE5.cellSemiPf X (Work.WilE5.signAssign X z)).set ⊆ X.set) ∧
    (∀ σ τ : Fin (Work.WilE5.atomsOf X).length → Work.WilE5.Sign, σ ≠ τ →
      Disjoint (Work.WilE5.cellSemiPf X σ).set (Work.WilE5.cellSemiPf X τ).set) ∧
    (∀ σ : Fin (Work.WilE5.atomsOf X).length → Work.WilE5.Sign,
      (WilkiesDesign.E.Basic.deg (Work.WilE5.cell X σ)) ≤ X.deg) ∧
    ((Work.WilE5.atomsOf X).map WilkiesDesign.E.atomDeg).sum = X.deg ∧
    (∀ z : Fin k → ℝ, z ∈ X.set → Work.WilE5.signAssign X z ∈ Work.WilE5.goodCells X) := by
  refine ⟨Work.WilE5.cell_holds_signAssign X, fun z hz => Work.WilE5.cellSemiPf_subset X hz,
    fun σ τ h => Work.WilE5.cells_disjoint X h, Work.WilE5.cell_deg_le X,
    Work.WilE5.atomsOf_deg X, fun z hz => Work.WilE5.signAssign_mem_goodCells X hz⟩

end Work.WilE5.Cells
