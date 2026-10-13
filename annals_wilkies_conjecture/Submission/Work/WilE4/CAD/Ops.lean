/-
  WilE4 / CAD — the two set operations the fibrewise closure needs, on the vocabulary of
  `Decomp.lean`:

  * `projSAd`  — the existential projection along the last coordinate;
  * `complSAd` — the complement.

  Both are built out of the cell list `CadCells`: the complement of a set that is a union of cells is
  the union of the *other* cells, and the projection of such a set is the union of the base cells
  that carry a cell contained in it.

  The projection theorem needs one extra input, `hconst`: on every base cell, a sign vector of the
  level-`(k+1)` family that is realised somewhere on the cell is realised at *every* point of the
  cell (the "type-constancy" of the CAD).  It is the only place where the analytic content of the
  CAD enters: the complement and both degree bounds are purely combinatorial.
-/
import Submission.Work.WilE4.CAD.Decomp

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilE4.CAD

open MvPolynomial Polynomial
open Work.WilE4 (rot spec tower)

variable {k m n : ℕ}

/-! ## Union of a list of cells -/

/-- The union of a list of `SAd`s, as an `SAd` (concatenation of the basic sets). -/
def unionCells {m : ℕ} (L : List (SAd m)) : SAd m := ⟨L.flatMap SAd.basics⟩

theorem unionCells_cons {m : ℕ} (a : SAd m) (t : List (SAd m)) :
    unionCells (a :: t) = ⟨a.basics ++ (unionCells t).basics⟩ := rfl

theorem set_append {m : ℕ} (l₁ l₂ : List (BasicD m)) :
    (⟨l₁ ++ l₂⟩ : SAd m).set = (⟨l₁⟩ : SAd m).set ∪ (⟨l₂⟩ : SAd m).set := by
  ext z
  simp only [SAd.set, Set.mem_union, Set.mem_setOf_eq, List.mem_append]
  constructor
  · rintro ⟨B, hB | hB, hz⟩
    · exact Or.inl ⟨B, hB, hz⟩
    · exact Or.inr ⟨B, hB, hz⟩
  · rintro (⟨B, hB, hz⟩ | ⟨B, hB, hz⟩)
    · exact ⟨B, Or.inl hB, hz⟩
    · exact ⟨B, Or.inr hB, hz⟩

theorem deg_append {m : ℕ} (l₁ l₂ : List (BasicD m)) :
    (⟨l₁ ++ l₂⟩ : SAd m).deg = (⟨l₁⟩ : SAd m).deg + (⟨l₂⟩ : SAd m).deg := by
  simp [SAd.deg, List.map_append, List.sum_append]

theorem unionCells_set {m : ℕ} (L : List (SAd m)) :
    (unionCells L).set = {z : Fin m → ℝ | ∃ C ∈ L, z ∈ C.set} := by
  induction L with
  | nil => ext z; simp [unionCells, SAd.set]
  | cons a t ih =>
    ext z
    have hmem : z ∈ (unionCells (a :: t)).set ↔ z ∈ a.set ∨ z ∈ (unionCells t).set := by
      rw [unionCells_cons]
      show z ∈ (⟨a.basics ++ (unionCells t).basics⟩ : SAd m).set ↔
        z ∈ a.set ∨ z ∈ (unionCells t).set
      rw [set_append, Set.mem_union]
    rw [hmem, ih]
    constructor
    · rintro (hz | ⟨C, hC, hzC⟩)
      · exact ⟨a, List.mem_cons_self, hz⟩
      · exact ⟨C, List.mem_cons_of_mem a hC, hzC⟩
    · rintro ⟨C, hC, hzC⟩
      rcases List.mem_cons.mp hC with rfl | hC
      · exact Or.inl hzC
      · exact Or.inr ⟨C, hC, hzC⟩

theorem unionCells_deg {m : ℕ} (L : List (SAd m)) :
    (unionCells L).deg = (L.map SAd.deg).sum := by
  induction L with
  | nil => simp [unionCells, SAd.deg]
  | cons a t ih =>
    rw [unionCells_cons, deg_append, ih, SAd.deg, List.map_cons, List.sum_cons]
    rfl

theorem unionCells_deg_le_mul {m : ℕ} {L : List (SAd m)} {B : ℕ} (hB : ∀ C ∈ L, C.deg ≤ B) :
    (unionCells L).deg ≤ L.length * B := by
  rw [unionCells_deg]
  calc (L.map SAd.deg).sum ≤ (L.map SAd.deg).length • B :=
        List.sum_le_card_nsmul _ _ fun x hx => by
          obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hx
          exact hB C hC
    _ = L.length • B := by rw [List.length_map]
    _ = L.length * B := nsmul_eq_mul _ _

/-- A `filterMap` that keeps exactly the elements satisfying a predicate is shorter than the list. -/
theorem length_filterMap_le {α β : Type*} (l : List α) (f : α → Option β) :
    (l.filterMap f).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.filterMap_cons]
    rcases hfa : f a with _ | b
    · simp only [Option.elim_none]
      exact ih.trans (Nat.le_succ _)
    · simp only [Option.elim_some, List.length_cons]
      exact Nat.succ_le_succ ih

/-! ## The complement -/

/-- A cell is kept unless it is contained in `Z`. -/
def keepNot {m : ℕ} (Z : SAd m) (C : SAd m) : Prop := ¬ (C.set ⊆ Z.set)

/-- The cells not contained in `Z`. -/
def complCells {m : ℕ} (H : List (MvPolynomial (Fin m) ℝ)) (Z : SAd m) : List (SAd m) :=
  (CadCells m H).filterMap fun C => if keepNot Z C then some C else none

theorem complCells_mem {m : ℕ} (H : List (MvPolynomial (Fin m) ℝ)) (Z : SAd m) :
    ∀ C ∈ complCells H Z, C ∈ CadCells m H ∧ keepNot Z C := by
  intro C hC
  rw [complCells, List.mem_filterMap] at hC
  obtain ⟨C₀, hC₀, hC₀l⟩ := hC
  by_cases hsub : keepNot Z C₀
  · rw [if_pos hsub] at hC₀l
    have hCC : C₀ = C := Option.some.inj hC₀l
    rw [hCC] at hC₀ hsub
    exact ⟨hC₀, hsub⟩
  · rw [if_neg hsub] at hC₀l
    exact absurd hC₀l (by simp)

/-- The complement of `Z`, as a union of cells. -/
def complSAd {m : ℕ} (H : List (MvPolynomial (Fin m) ℝ)) (Z : SAd m) : SAd m :=
  unionCells (complCells H Z)

theorem complSAd_set {m : ℕ} (H : List (MvPolynomial (Fin m) ℝ)) (Z : SAd m)
    (hCov : ∀ z : Fin m → ℝ, ∃ C ∈ CadCells m H, z ∈ C.set)
    (hUn : ∀ C ∈ CadCells m H, C.set ⊆ Z.set ∨ Disjoint C.set Z.set) :
    (complSAd H Z).set = Z.setᶜ := by
  rw [complSAd, unionCells_set]
  ext z
  constructor
  · rintro ⟨C, hC, hzC⟩
    obtain ⟨hCab, hCsub⟩ := complCells_mem H Z C hC
    intro hzZ
    exact Set.disjoint_left.mp ((hUn C hCab).resolve_left hCsub) hzC hzZ
  · intro hz
    obtain ⟨C, hC, hzC⟩ := hCov z
    refine ⟨C, ?_, hzC⟩
    rw [complCells, List.mem_filterMap]
    refine ⟨C, hC, ?_⟩
    rw [if_pos]
    exact fun hsub => hz (hsub hzC)

theorem complSAd_deg_le {m : ℕ} (H : List (MvPolynomial (Fin m) ℝ)) (Z : SAd m) {B : ℕ}
    (hB : ∀ C ∈ CadCells m H, C.deg ≤ B) :
    (complSAd H Z).deg ≤ (CadCells m H).length * B :=
  (unionCells_deg_le_mul fun C hC => hB C (complCells_mem H Z C hC).1).trans
    (Nat.mul_le_mul_right B (length_filterMap_le (CadCells m H) _))

/-! ## The projection along the last coordinate -/

/-- A base cell is kept if it carries a cell contained in `Z`. -/
def keepProj {k : ℕ} (H : List (MvPolynomial (Fin (k + 1)) ℝ)) (Z : SAd (k + 1)) (C : SAd k) :
    Prop :=
  ∃ w : Fin H.length → SignType, RealizedOn H C w ∧ (cell C H w).set ⊆ Z.set

/-- The base cells that carry a cell contained in `Z`. -/
def projCells {k : ℕ} (H : List (MvPolynomial (Fin (k + 1)) ℝ)) (Z : SAd (k + 1)) : List (SAd k) :=
  (CadCells k (projDataT k H)).filterMap fun C => if keepProj H Z C then some C else none

theorem projCells_mem {k : ℕ} (H : List (MvPolynomial (Fin (k + 1)) ℝ)) (Z : SAd (k + 1)) :
    ∀ C ∈ projCells H Z, C ∈ CadCells k (projDataT k H) ∧ keepProj H Z C := by
  intro C hC
  rw [projCells, List.mem_filterMap] at hC
  obtain ⟨C₀, hC₀, hC₀l⟩ := hC
  by_cases h : keepProj H Z C₀
  · rw [if_pos h] at hC₀l
    have hCC : C₀ = C := Option.some.inj hC₀l
    rw [hCC] at hC₀ h
    exact ⟨hC₀, h⟩
  · rw [if_neg h] at hC₀l
    exact absurd hC₀l (by simp)

/-- A cell of the decomposition, viewed at the next level. -/
theorem cell_mem_CadCells {k : ℕ} {H : List (MvPolynomial (Fin (k + 1)) ℝ)} {C : SAd k}
    {w : Fin H.length → SignType} (hC : C ∈ CadCells k (projDataT k H)) (hw : RealizedOn H C w) :
    cell C H w ∈ CadCells (k + 1) H :=
  (mem_CadCells_succ).mpr ⟨C, hC, w, hw, rfl⟩

/-- The projection of `Z` along the last coordinate, as an `SAd`. -/
def projSAd {k : ℕ} (H : List (MvPolynomial (Fin (k + 1)) ℝ)) (Z : SAd (k + 1)) : SAd k :=
  unionCells (projCells H Z)

theorem projSAd_set {k : ℕ} (H : List (MvPolynomial (Fin (k + 1)) ℝ)) (Z : SAd (k + 1))
    (hCov : ∀ z : Fin k → ℝ, ∃ C ∈ CadCells k (projDataT k H), z ∈ C.set)
    (hUn : ∀ D ∈ CadCells (k + 1) H, D.set ⊆ Z.set ∨ Disjoint D.set Z.set)
    (hconst : ∀ C ∈ CadCells k (projDataT k H), ∀ w : Fin H.length → SignType,
      RealizedOn H C w → ∀ x ∈ C.set,
        ∃ t : ℝ, ∀ i, SignType.sign (MvPolynomial.eval (Fin.snoc x t) (H.get i)) = w i) :
    (projSAd H Z).set = WilkiesDesign.projLast Z.set := by
  rw [projSAd, unionCells_set]
  ext z
  constructor
  · rintro ⟨C, hC, hzC⟩
    obtain ⟨hCab, w, hw, hwZ⟩ := projCells_mem H Z C hC
    obtain ⟨t, ht⟩ := hconst C hCab w hw z hzC
    refine ⟨t, hwZ ?_⟩
    rw [mem_cell_iff, Fin.init_snoc]
    exact ⟨hzC, ht⟩
  · rintro ⟨t, ht⟩
    obtain ⟨C, hC, hzC⟩ := hCov z
    have hw : RealizedOn H C (signVec H (Fin.snoc z t)) := ⟨z, hzC, t, fun i => rfl⟩
    have hcell : cell C H (signVec H (Fin.snoc z t)) ∈ CadCells (k + 1) H :=
      cell_mem_CadCells hC hw
    have hmem : Fin.snoc z t ∈ (cell C H (signVec H (Fin.snoc z t))).set := by
      rw [mem_cell_iff]
      simp only [Fin.init_snoc]
      exact ⟨hzC, fun i => rfl⟩
    have hsub : (cell C H (signVec H (Fin.snoc z t))).set ⊆ Z.set :=
      (hUn _ hcell).resolve_right fun hd => Set.disjoint_left.mp hd hmem ht
    refine ⟨C, ?_, hzC⟩
    rw [projCells, List.mem_filterMap]
    exact ⟨C, hC, by rw [if_pos ⟨signVec H (Fin.snoc z t), hw, hsub⟩]⟩

theorem projSAd_deg_le {k : ℕ} (H : List (MvPolynomial (Fin (k + 1)) ℝ)) (Z : SAd (k + 1)) {B : ℕ}
    (hB : ∀ C ∈ CadCells k (projDataT k H), C.deg ≤ B) :
    (projSAd H Z).deg ≤ (CadCells k (projDataT k H)).length * B :=
  (unionCells_deg_le_mul fun C hC => hB C (projCells_mem H Z C hC).1).trans
    (Nat.mul_le_mul_right B (length_filterMap_le (CadCells k (projDataT k H)) _))

end Work.WilE4.CAD
