/-
  WilC4/ulpmTot_definable : the total, zero-free replacement `UlpmTot Y` of a `∅`-definable
  family `Y ⊆ ℝ^{k+2}` is again `∅`-definable.

  Recall (`Submission/Work/WilC4/ULPMDev.lean`)

      UlpmTot Y = {v | (v ∈ Y ∧ v 1 ≠ 0) ∨
                      (v 1 = 1 ∧ ∀ y' : ℝ, ¬ (Gr Y (fun i => v i.succ.succ) (v 0) y' ∧ y' ≠ 0))}

  i.e. the fibre of `UlpmTot Y` is the fibre of `Y` where that is defined and nonzero, and the
  constant `1` everywhere else on the level `v 1 = 1`.

  The content is pure quantifier bookkeeping.  Reading a tuple `w` of
  `Fin (k+2) ⊕ Fin 1 → ℝ` as `(x, y, c, y')`, the "failure" predicate

      ¬ (w' is a nonzero value of the fibre of Y at (c, x)),   w' = (x, y', c),

  is `∅`-definable: it is the complement of the pullback of `Y` along the index embedding
  `UlpmEmb` (which reads `(x, y', c)` off `(x, y, c, y')`) intersected with `y' ≠ 0`.  The
  universal quantifier over `y' : ℝ` is a finite quantifier (`∀ u : Fin 1 → ℝ`), so it preserves
  definability (`Set.Definable.forall_of_finite`).  The two remaining conjuncts `v 1 ≠ 0` and
  `v 1 = 1` are coordinate conditions, `∅`-definable because `LRc` names every real as a
  constant (`Work.WilC4.empty_definable_coord_eq`).
-/
import Mathlib
import Submission.Work.WilC4.ULPMDev

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. The index embedding -/

/-- The index embedding along which the tuple `(x, y', c)` is read off the tuple
`(x, y, c, y')`: it sends `0 ↦ Sum.inl 0` (the argument `x`), `1 ↦ Sum.inr 0` (the quantified
value `y'`) and `i + 2 ↦ Sum.inl (i + 2)` (the parameters `c i`). -/
def UlpmEmb (k : ℕ) : Fin (k + 2) → (Fin (k + 2) ⊕ Fin 1) :=
  Fin.cases (Sum.inl (0 : Fin (k + 2)))
    (fun i : Fin (k + 1) => Fin.cases (Sum.inr (0 : Fin 1))
      (fun i' : Fin k => Sum.inl (i'.succ.succ)) i)

theorem ulpmEmb_zero (k : ℕ) : UlpmEmb k (0 : Fin (k + 2)) = Sum.inl (0 : Fin (k + 2)) := rfl

theorem ulpmEmb_one (k : ℕ) : UlpmEmb k (Fin.succ (0 : Fin (k + 1))) = Sum.inr (0 : Fin 1) := by
  simp only [UlpmEmb, Fin.cases_succ, Fin.cases_zero]

theorem ulpmEmb_succ_succ (k : ℕ) (i : Fin k) :
    UlpmEmb k (i.succ.succ) = Sum.inl (i.succ.succ) := by
  simp only [UlpmEmb, Fin.cases_succ]

/-- The composition of `Sum.elim v u` with the index embedding is exactly the tuple
`(v 0, u 0, v 2, …, v (k+1))`, i.e. the fibre tuple `(x, y', c)` of `Y`. -/
theorem ulpmEmb_comp (k : ℕ) (v : Fin (k + 2) → ℝ) (u : Fin 1 → ℝ) :
    (Sum.elim v u) ∘ (UlpmEmb k) =
      Fin.cons (v 0) (Fin.cons (u 0) (fun i : Fin k => v i.succ.succ)) := by
  funext j
  refine Fin.cases ?_ ?_ j
  · simp only [Function.comp_apply, ulpmEmb_zero, Sum.elim_inl, Fin.cons_zero]
  · intro j'
    refine Fin.cases ?_ ?_ j'
    · simp only [Function.comp_apply, ulpmEmb_one, Sum.elim_inr, Fin.cons_zero, Fin.cons_succ]
    · intro i
      simp only [Function.comp_apply, ulpmEmb_succ_succ, Sum.elim_inl, Fin.cons_succ]

/-! ## 2. The failure predicate is definable -/

/-- `UlpmT Y` is the set of tuples `(x, y, c, y')` for which `y'` is **not** a nonzero value of
the fibre of `Y` at `(c, x)`. -/
def UlpmT {k : ℕ} (Y : Set (Fin (k + 2) → ℝ)) : Set (Fin (k + 2) ⊕ Fin 1 → ℝ) :=
  ({w | (w ∘ UlpmEmb k) ∈ Y} ∩ {w | w (Sum.inr (0 : Fin 1)) ≠ 0})ᶜ

/-- Reading the failure predicate on the free coordinates: for the tuple
`Sum.elim v u` (`v` the free coordinates, `u 0` the quantified `y'`), membership in `UlpmT Y`
is exactly the negation of the fibre condition of `UlpmTot`. -/
theorem ulpmT_iff (k : ℕ) (Y : Set (Fin (k + 2) → ℝ)) (v : Fin (k + 2) → ℝ) (u : Fin 1 → ℝ) :
    Sum.elim v u ∈ UlpmT Y ↔
      ¬ (Route.Gr Y (fun i : Fin k => v i.succ.succ) (v 0) (u 0) ∧ u 0 ≠ 0) := by
  simp only [UlpmT, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_ofPred_eq, Route.Gr,
    ulpmEmb_comp, Sum.elim_inr]

theorem ulpmT_definable {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable LRc Y) :
    (∅ : Set ℝ).Definable LRc (UlpmT Y) := by
  have h1 : (∅ : Set ℝ).Definable LRc
      {w : Fin (k + 2) ⊕ Fin 1 → ℝ | (w ∘ UlpmEmb k) ∈ Y} := by
    convert hY.preimage_comp (UlpmEmb k) using 1
    ext w
    rfl
  have h2 : (∅ : Set ℝ).Definable LRc
      {w : Fin (k + 2) ⊕ Fin 1 → ℝ | w (Sum.inr (0 : Fin 1)) ≠ 0} := by
    convert (empty_definable_coord_eq (α := Fin (k + 2) ⊕ Fin 1)
      (Sum.inr (0 : Fin 1)) (0 : ℝ)).compl using 1
    ext w
    rfl
  simpa only [UlpmT] using (h1.inter h2).compl

/-! ## 3. The theorem -/

theorem ulpmTot_definable {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)}
    (hY : (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc Y) :
    (∅ : Set ℝ).Definable WilkiesDesign.CG.LRc (Work.WilC4.UlpmTot Y) := by
  have hT : (∅ : Set ℝ).Definable LRc (UlpmT Y) := ulpmT_definable hY
  -- the universal quantifier over the value `y' : ℝ`, as a finite quantifier
  have hU : (∅ : Set ℝ).Definable LRc
      {v : Fin (k + 2) → ℝ | ∀ u : Fin 1 → ℝ, Sum.elim v u ∈ UlpmT Y} :=
    hT.forall_of_finite
  have h1 : (∅ : Set ℝ).Definable LRc (Y ∩ {v : Fin (k + 2) → ℝ | v 1 ≠ 0}) :=
    hY.inter (by
      convert (empty_definable_coord_eq (α := Fin (k + 2)) (1 : Fin (k + 2)) (0 : ℝ)).compl using 1
      ext v
      rfl)
  have h2 : (∅ : Set ℝ).Definable LRc
      ({v : Fin (k + 2) → ℝ | v 1 = 1} ∩
        {v : Fin (k + 2) → ℝ | ∀ u : Fin 1 → ℝ, Sum.elim v u ∈ UlpmT Y}) :=
    (empty_definable_coord_eq (α := Fin (k + 2)) (1 : Fin (k + 2)) (1 : ℝ)).inter hU
  have hset : UlpmTot Y = (Y ∩ {v : Fin (k + 2) → ℝ | v 1 ≠ 0}) ∪
      ({v : Fin (k + 2) → ℝ | v 1 = 1} ∩
        {v : Fin (k + 2) → ℝ | ∀ u : Fin 1 → ℝ, Sum.elim v u ∈ UlpmT Y}) := by
    ext v
    simp only [UlpmTot, Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff]
    constructor
    · rintro (⟨hvY, hv⟩ | ⟨hv1, hv⟩)
      · exact Or.inl ⟨hvY, hv⟩
      · refine Or.inr ⟨hv1, fun u => (ulpmT_iff k Y v u).mpr (hv (u 0))⟩
    · rintro (⟨hvY, hv⟩ | ⟨hv1, hv⟩)
      · exact Or.inl ⟨hvY, hv⟩
      · exact Or.inr ⟨hv1, fun y' => (ulpmT_iff k Y v (fun _ : Fin 1 => y')).mp
          (hv (fun _ : Fin 1 => y'))⟩
  rw [hset]
  exact h1.union h2

end Work.WilC4
