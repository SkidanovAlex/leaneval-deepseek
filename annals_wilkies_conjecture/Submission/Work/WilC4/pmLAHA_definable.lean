/-
  WilC4/pmLAHA_definable : the definability of the two *relations* attached to a `∅`-definable
  family of partial functions.

  `PMonoLA Y` and `PMonoHA Y` (`Submission/Work/WilC4/CritDefs.lean`) are the families of
  `(x, w, c)` such that the fibre `Cfib Y c` carries values `y` at `x` and `y'` at `w` with
  `y < y'`, resp. `y' < y`.  Concretely

  `v ∈ PMonoLA Y ↔ ∃ y y', (v 0, y, c) ∈ Y ∧ (v 1, y', c) ∈ Y ∧ y < y'`,  `c i = v (i + 2)`.

  This is *purely first-order*: two existential real quantifiers, two occurrences of the
  membership relation of `Y` (along reindexings), and one comparison.  The proof follows the
  pattern of `Work.WilC4.pw_definable` in `Submission/Work/WilC4/critAux.lean`:

  * on the index type `LASig k = Fin (k+2) ⊕ Fin 2`, whose `Fin 2` block carries the two values
    `y`, `y'`, define the body `LAS k Y R` of the formula: `t ∘ LAτ₁ ∈ Y`, `t ∘ LAτ₂ ∈ Y` and
    the pair of values lies in the relation `R` on `Fin 2 → ℝ`;
  * `LAS k Y R` is `∅`-definable by two `Definable.preimage_comp` (the membership of `Y` along
    the reindexings `LAτ₁`, `LAτ₂`) and one more `preimage_comp` (the relation `R` on the values,
    pulled back along `Fin 2 → LASig k`);
  * projecting the two value coordinates out is the finite existential quantifier
    `Set.Definable.exists_of_finite`, and the identification of the projection with
    `PMonoLA Y` / `PMonoHA Y` is the reindexing computation `comp_LAτ₁` / `comp_LAτ₂`
    together with the unfolding of `MonoLA` / `MonoHA`.
-/
import Mathlib
import Submission.Work.WilC4.critAux

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. The doubled index type and the reindexings -/

/-- The index type of the two-relation construction: the `k+2` coordinates of the ambient point
`v = (x, w, c)`, together with the two value coordinates `y, y'`. -/
abbrev LASig (k : ℕ) : Type := Fin (k + 2) ⊕ Fin 2

/-- The reindexing `(x, y, c) ↦ v = (x, w, c)`: `0 ↦ inl 0` (the coordinate `v 0`), `1 ↦ inr 0`
(the first value), `j+2 ↦ inl (j+2)` (the parameters). -/
def LAτ₁ (k : ℕ) : Fin (k + 2) → LASig k :=
  Fin.cons (Sum.inl 0) (Fin.cons (Sum.inr 0) (fun j : Fin k => Sum.inl j.succ.succ))

/-- The reindexing `(w, y', c)`: `0 ↦ inl 1` (the coordinate `v 1`), `1 ↦ inr 1` (the second
value), `j+2 ↦ inl (j+2)` (the parameters). -/
def LAτ₂ (k : ℕ) : Fin (k + 2) → LASig k :=
  Fin.cons (Sum.inl 1) (Fin.cons (Sum.inr 1) (fun j : Fin k => Sum.inl j.succ.succ))

/-- `LAτ₁` reads the coordinates `(v 0, u 0, v 2, …)` off the split tuple `Sum.elim v u`. -/
lemma comp_LAτ₁ (k : ℕ) (v : Fin (k + 2) → ℝ) (u : Fin 2 → ℝ) :
    (fun i => (Sum.elim v u) (LAτ₁ k i)) =
      Fin.cons (v 0) (Fin.cons (u 0) (fun j : Fin k => v j.succ.succ)) := by
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ j =>
    induction j using Fin.cases with
    | zero => rfl
    | succ l => rfl

/-- `LAτ₂` reads the coordinates `(v 1, u 1, v 2, …)` off the split tuple `Sum.elim v u`. -/
lemma comp_LAτ₂ (k : ℕ) (v : Fin (k + 2) → ℝ) (u : Fin 2 → ℝ) :
    (fun i => (Sum.elim v u) (LAτ₂ k i)) =
      Fin.cons (v 1) (Fin.cons (u 1) (fun j : Fin k => v j.succ.succ)) := by
  funext i
  induction i using Fin.cases with
  | zero => rfl
  | succ j =>
    induction j using Fin.cases with
    | zero => rfl
    | succ l => rfl

/-! ## 2. The body of the formula on the doubled index type -/

/-- The body of the parametric `MonoLA`/`MonoHA` formula: both `(v 0, y, c)` and `(v 1, y', c)`
lie in `Y`, and the pair `(y, y')` of values lies in the relation `R`. -/
def LAS (k : ℕ) (Y : Set (Fin (k + 2) → ℝ)) (R : Set (Fin 2 → ℝ)) : Set (LASig k → ℝ) :=
  {t | (fun i => t (LAτ₁ k i)) ∈ Y ∧ (fun i => t (LAτ₂ k i)) ∈ Y ∧
    (fun j : Fin 2 => t (Sum.inr j)) ∈ R}

/-- `LAS k Y R` is `∅`-definable whenever `Y` and `R` are. -/
lemma LAS_definable {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)} {R : Set (Fin 2 → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) (hR : (∅ : Set ℝ).Definable LRc R) :
    (∅ : Set ℝ).Definable LRc (LAS k Y R) := by
  have h1 : (∅ : Set ℝ).Definable LRc {t : LASig k → ℝ | (fun i => t (LAτ₁ k i)) ∈ Y} := by
    have h := hY.preimage_comp (LAτ₁ k)
    convert h using 1
    ext t; simp [Function.comp_def]
  have h2 : (∅ : Set ℝ).Definable LRc {t : LASig k → ℝ | (fun i => t (LAτ₂ k i)) ∈ Y} := by
    have h := hY.preimage_comp (LAτ₂ k)
    convert h using 1
    ext t; simp [Function.comp_def]
  have h3 : (∅ : Set ℝ).Definable LRc
      {t : LASig k → ℝ | (fun j : Fin 2 => t (Sum.inr j)) ∈ R} := by
    have h := hR.preimage_comp (fun j : Fin 2 => (Sum.inr j : LASig k))
    convert h using 1
    ext t; simp [Function.comp_def]
  have h := (h1.inter h2).inter h3
  convert h using 1
  ext t
  simp only [LAS, Set.mem_inter_iff, Set.mem_ofPred_eq]
  tauto

/-! ## 3. Unfolding the two relations -/

/-- Membership in the parametric `MonoLA` family, in decoded form. -/
lemma mem_PMonoLA {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)} {v : Fin (k + 2) → ℝ} :
    v ∈ PMonoLA Y ↔ ∃ y y' : ℝ, CGr Y (fun i => v i.succ.succ) (v 0) y ∧
      CGr Y (fun i => v i.succ.succ) (v 1) y' ∧ y < y' := by
  simp only [PMonoLA, Set.mem_ofPred_eq, MonoLA, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, y', h1, h2, h3⟩
    exact ⟨y, y', by simpa [Cfib] using h1, by simpa [Cfib] using h2, h3⟩
  · rintro ⟨y, y', h1, h2, h3⟩
    exact ⟨y, y', by simpa [Cfib] using h1, by simpa [Cfib] using h2, h3⟩

/-- Membership in the parametric `MonoHA` family, in decoded form. -/
lemma mem_PMonoHA {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)} {v : Fin (k + 2) → ℝ} :
    v ∈ PMonoHA Y ↔ ∃ y y' : ℝ, CGr Y (fun i => v i.succ.succ) (v 0) y ∧
      CGr Y (fun i => v i.succ.succ) (v 1) y' ∧ y' < y := by
  simp only [PMonoHA, Set.mem_ofPred_eq, MonoHA, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨y, y', h1, h2, h3⟩
    exact ⟨y, y', by simpa [Cfib] using h1, by simpa [Cfib] using h2, h3⟩
  · rintro ⟨y, y', h1, h2, h3⟩
    exact ⟨y, y', by simpa [Cfib] using h1, by simpa [Cfib] using h2, h3⟩

/-- `PMonoLA Y` is the projection, along the two value coordinates, of the body `LAS` with the
relation `y < y'` on the values. -/
lemma PMonoLA_eq (k : ℕ) (Y : Set (Fin (k + 2) → ℝ)) :
    PMonoLA Y = {v : Fin (k + 2) → ℝ | ∃ u : Fin 2 → ℝ,
      Sum.elim v u ∈ LAS k Y {r : Fin 2 → ℝ | r 0 < r 1}} := by
  ext v
  rw [mem_PMonoLA]
  constructor
  · rintro ⟨y, y', h1, h2, h3⟩
    refine ⟨![y, y'], ?_⟩
    simp only [LAS, Set.mem_ofPred_eq]
    refine ⟨?_, ?_, ?_⟩
    · rw [comp_LAτ₁]; simpa [CGr] using h1
    · rw [comp_LAτ₂]; simpa [CGr] using h2
    · simpa using h3
  · rintro ⟨u, hu⟩
    simp only [LAS, Set.mem_ofPred_eq] at hu
    obtain ⟨h1, h2, h3⟩ := hu
    refine ⟨u 0, u 1, ?_, ?_, ?_⟩
    · rw [comp_LAτ₁] at h1; simpa [CGr] using h1
    · rw [comp_LAτ₂] at h2; simpa [CGr] using h2
    · simpa using h3

/-- `PMonoHA Y` is the projection, along the two value coordinates, of the body `LAS` with the
relation `y' < y` on the values. -/
lemma PMonoHA_eq (k : ℕ) (Y : Set (Fin (k + 2) → ℝ)) :
    PMonoHA Y = {v : Fin (k + 2) → ℝ | ∃ u : Fin 2 → ℝ,
      Sum.elim v u ∈ LAS k Y {r : Fin 2 → ℝ | r 1 < r 0}} := by
  ext v
  rw [mem_PMonoHA]
  constructor
  · rintro ⟨y, y', h1, h2, h3⟩
    refine ⟨![y, y'], ?_⟩
    simp only [LAS, Set.mem_ofPred_eq]
    refine ⟨?_, ?_, ?_⟩
    · rw [comp_LAτ₁]; simpa [CGr] using h1
    · rw [comp_LAτ₂]; simpa [CGr] using h2
    · simpa using h3
  · rintro ⟨u, hu⟩
    simp only [LAS, Set.mem_ofPred_eq] at hu
    obtain ⟨h1, h2, h3⟩ := hu
    refine ⟨u 0, u 1, ?_, ?_, ?_⟩
    · rw [comp_LAτ₁] at h1; simpa [CGr] using h1
    · rw [comp_LAτ₂] at h2; simpa [CGr] using h2
    · simpa using h3

/-! ## 4. Coordinates of `ℝ^{Fin 2}` compare definably -/

/-- `{v | v i < v j}` is `∅`-definable: `<` is the comparison of the two ring terms `var i`,
`var j`. -/
lemma definable_lt_coord {α : Type} (i j : α) :
    (∅ : Set ℝ).Definable LRc {v : α → ℝ | v i < v j} := by
  have h := definable_lt_terms (α := α) (Term.var i) (Term.var j)
  simpa using h

/-! ## 5. The two families are `∅`-definable -/

theorem pmLAHA_definable {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PMonoLA Y) ∧
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (PMonoHA Y) := by
  have hR1 : (∅ : Set ℝ).Definable LRc {r : Fin 2 → ℝ | r 0 < r 1} := definable_lt_coord 0 1
  have hR2 : (∅ : Set ℝ).Definable LRc {r : Fin 2 → ℝ | r 1 < r 0} := definable_lt_coord 1 0
  constructor
  · rw [PMonoLA_eq k Y]
    exact (LAS_definable hY hR1).exists_of_finite
  · rw [PMonoHA_eq k Y]
    exact (LAS_definable hY hR2).exists_of_finite

end Work.WilC4
