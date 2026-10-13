/-
  WilC1 — the realization set of every `LRc`-formula is `REx`.

  `Sof φ ⊆ ℝ^{α ⊕ Fin k}` is the realization set of `φ : LRc.BoundedFormula α k`.  The induction
  over formulas has five cases (`falsum`, `equal`, `rel`, `imp`, `all`); `imp` needs closure under
  complement and union, `all` needs complement, pullback along the reindexing
  `(α ⊕ Fin k) ⊕ Fin 1 ≃ α ⊕ Fin (k+1)` and projection, and the atomic case `equal` is the graph
  lemma for terms.  Each case is proved as a separate lemma with the arity `k` explicit.
-/
import Submission.Work.WilC1.Defs
import Submission.Work.WilC1.REx_preimage
import Submission.Work.WilC1.REx_union
import Submission.Work.WilC1.REx_proj

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC1

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture

universe u

variable {α : Type u}

/-- `Sum.elim` of the two components of a function is the function. -/
theorem sumElim_comp_self {τ : Type*} (w : (α ⊕ τ) → ℝ) :
    Sum.elim (w ∘ Sum.inl) (w ∘ Sum.inr) = w := by
  funext q
  rcases q with x | j <;> rfl

/-! ## The reindexing `(α ⊕ Fin k) ⊕ Fin 1 ≃ α ⊕ Fin (k+1)` -/

/-- Peeling off the last bound variable. -/
def sumFinSnocEquiv (α : Type u) (k : ℕ) : (α ⊕ Fin k) ⊕ Fin 1 ≃ α ⊕ Fin (k + 1) :=
  (Equiv.sumAssoc α (Fin k) (Fin 1)).trans
    (Equiv.sumCongr (Equiv.refl α) (finSumFinEquiv (m := k) (n := 1)))

@[simp] theorem sumFinSnocEquiv_apply_inl_inl {k : ℕ} {x : α} :
    sumFinSnocEquiv α k (Sum.inl (Sum.inl x)) = Sum.inl x := by
  simp [sumFinSnocEquiv]

@[simp] theorem sumFinSnocEquiv_apply_inl_inr {k : ℕ} (j : Fin k) :
    sumFinSnocEquiv α k (Sum.inl (Sum.inr j)) = Sum.inr (Fin.castAdd 1 j) := by
  simp [sumFinSnocEquiv]

@[simp] theorem sumFinSnocEquiv_apply_inr {k : ℕ} (j : Fin 1) :
    sumFinSnocEquiv α k (Sum.inr j) = Sum.inr (Fin.natAdd k j) := by
  simp [sumFinSnocEquiv]

@[simp] theorem sumFinSnocEquiv_symm_apply_inl {k : ℕ} (x : α) :
    (sumFinSnocEquiv α k).symm (Sum.inl x) = Sum.inl (Sum.inl x) := by
  rw [Equiv.symm_apply_eq]
  simp

@[simp] theorem sumFinSnocEquiv_symm_apply_inr_castAdd {k : ℕ} (j : Fin k) :
    (sumFinSnocEquiv α k).symm (Sum.inr (Fin.castAdd 1 j)) = Sum.inl (Sum.inr j) := by
  rw [Equiv.symm_apply_eq]
  simp

@[simp] theorem sumFinSnocEquiv_symm_apply_inr_natAdd {k : ℕ} (j : Fin 1) :
    (sumFinSnocEquiv α k).symm (Sum.inr (Fin.natAdd k j)) = Sum.inr j := by
  rw [Equiv.symm_apply_eq]
  simp

/-- The first `k` coordinates after pulling back along `sumFinSnocEquiv`. -/
theorem comp_symm_inl {k : ℕ} (w : (α ⊕ Fin k) → ℝ) (a : Fin 1 → ℝ) :
    (Sum.elim w a ∘ (sumFinSnocEquiv α k).symm) ∘ Sum.inl = w ∘ Sum.inl := by
  funext x
  simp only [Function.comp_apply, Sum.elim_inl, sumFinSnocEquiv_symm_apply_inl]

/-- The last coordinate after pulling back along `sumFinSnocEquiv`. -/
theorem comp_symm_inr {k : ℕ} (w : (α ⊕ Fin k) → ℝ) (a : Fin 1 → ℝ) :
    (Sum.elim w a ∘ (sumFinSnocEquiv α k).symm) ∘ Sum.inr
      = Fin.snoc (w ∘ Sum.inr) (a 0) := by
  funext j
  refine Fin.lastCases ?_ ?_ j
  · simp only [Function.comp_apply]
    rw [show Fin.last k = Fin.natAdd k (0 : Fin 1) from (Fin.ext rfl).symm,
      sumFinSnocEquiv_symm_apply_inr_natAdd, Sum.elim_inr,
      show Fin.natAdd k (0 : Fin 1) = Fin.last k from Fin.ext rfl, Fin.snoc_last]
  · intro i
    simp only [Function.comp_apply]
    rw [show Fin.castSucc i = Fin.castAdd 1 i from (Fin.ext rfl).symm,
      sumFinSnocEquiv_symm_apply_inr_castAdd, Sum.elim_inl,
      show Fin.castAdd 1 i = Fin.castSucc i from Fin.ext rfl, Fin.snoc_castSucc]
    rfl

/-! ## The `all` case -/

/-- Membership in `Sof φ` after reindexing the coordinates along `sumFinSnocEquiv`. -/
theorem mem_Sof_comp {k : ℕ} (φ : LRc.BoundedFormula α (k + 1)) (w : (α ⊕ Fin k) → ℝ)
    (a : Fin 1 → ℝ) :
    Sum.elim w a ∘ (sumFinSnocEquiv α k).symm ∈ Sof φ ↔
      φ.Realize (w ∘ Sum.inl) (Fin.snoc (w ∘ Sum.inr) (a 0)) := by
  rw [Sof]
  simp only [Set.mem_ofPred_eq, comp_symm_inl, comp_symm_inr]

/-- The realization of `φ.all` in terms of the realization of `φ` on `α ⊕ Fin (k+1)`. -/
theorem mem_Sof_all_iff {k : ℕ} (φ : LRc.BoundedFormula α (k + 1)) (w : (α ⊕ Fin k) → ℝ) :
    w ∈ Sof (φ.all) ↔ ∀ a : Fin 1 → ℝ,
      Sum.elim w a ∘ (sumFinSnocEquiv α k).symm ∈ Sof φ := by
  rw [Sof]
  simp only [Set.mem_ofPred_eq, BoundedFormula.realize_all]
  constructor
  · intro h a
    rw [mem_Sof_comp]
    exact h (a 0)
  · intro h a
    have := h (fun _ : Fin 1 => a)
    rw [mem_Sof_comp (a := fun _ : Fin 1 => a)] at this
    simpa using this

/-! ## The five cases, with the arity explicit -/

theorem REx_Sof_falsum (α : Type u) (k : ℕ) :
    REx (α ⊕ Fin k) (Sof (⊥ : LRc.BoundedFormula α k)) := by
  have h : Sof (⊥ : LRc.BoundedFormula α k) = ∅ := by
    ext w
    simp [Sof]
  exact REx.congr h.symm (REx.empty (ι := α ⊕ Fin k))

theorem REx_Sof_equal {k : ℕ} (t₁ t₂ : LRc.Term (α ⊕ Fin k))
    (h : REx (α ⊕ Fin k) {w : (α ⊕ Fin k) → ℝ |
      Term.realize w t₁ = Term.realize w t₂}) :
    REx (α ⊕ Fin k) (Sof (BoundedFormula.equal t₁ t₂)) := by
  refine h.congr ?_
  ext w
  simp only [Sof, Set.mem_ofPred_eq]
  change Term.realize w t₁ = Term.realize w t₂ ↔
    Term.realize (Sum.elim (w ∘ Sum.inl) (w ∘ Sum.inr)) t₁ =
      Term.realize (Sum.elim (w ∘ Sum.inl) (w ∘ Sum.inr)) t₂
  rw [sumElim_comp_self]

theorem REx_Sof_rel {k l : ℕ} (R : LRc.Relations l)
    (ts : Fin l → LRc.Term (α ⊕ Fin k)) :
    REx (α ⊕ Fin k) (Sof (@BoundedFormula.rel LRc α k l R ts)) :=
  (isEmpty_rel l).elim R

theorem REx_Sof_imp {k : ℕ} [Fintype α] {φ ψ : LRc.BoundedFormula α k}
    (hφ : REx (α ⊕ Fin k) (Sof φ)) (hψ : REx (α ⊕ Fin k) (Sof ψ))
    (hcompl : ∀ {ι : Type u} [Fintype ι] (X : Set (ι → ℝ)), REx ι X → REx ι Xᶜ) :
    REx (α ⊕ Fin k) (Sof (φ.imp ψ)) := by
  refine (REx_union (hcompl (Sof φ) hφ) hψ).congr ?_
  ext w
  simp only [Sof, Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq,
    BoundedFormula.realize_imp, imp_iff_not_or]

theorem REx_Sof_all {k : ℕ} [Fintype α] (φ : LRc.BoundedFormula α (k + 1))
    (hφ : REx (α ⊕ Fin (k + 1)) (Sof φ))
    (hcompl : ∀ {ι : Type u} [Fintype ι] (X : Set (ι → ℝ)), REx ι X → REx ι Xᶜ) :
    REx (α ⊕ Fin k) (Sof (BoundedFormula.all φ)) := by
  have h2 : REx ((α ⊕ Fin k) ⊕ Fin 1)
      {u : ((α ⊕ Fin k) ⊕ Fin 1) → ℝ |
        u ∘ (sumFinSnocEquiv α k).symm ∈ Sof φ} :=
    REx_preimage (sumFinSnocEquiv α k).symm hφ
  have h3 : REx ((α ⊕ Fin k) ⊕ Fin 1)
      ({u : ((α ⊕ Fin k) ⊕ Fin 1) → ℝ |
        u ∘ (sumFinSnocEquiv α k).symm ∈ Sof φ})ᶜ := hcompl _ h2
  have h4 : REx (α ⊕ Fin k)
      {w : (α ⊕ Fin k) → ℝ | ∃ a : Fin 1 → ℝ, Sum.elim w a ∈
        ({u : ((α ⊕ Fin k) ⊕ Fin 1) → ℝ |
          u ∘ (sumFinSnocEquiv α k).symm ∈ Sof φ})ᶜ} := REx_proj 1 h3
  have h5 : REx (α ⊕ Fin k)
      ({w : (α ⊕ Fin k) → ℝ | ∃ a : Fin 1 → ℝ, Sum.elim w a ∈
        ({u : ((α ⊕ Fin k) ⊕ Fin 1) → ℝ |
          u ∘ (sumFinSnocEquiv α k).symm ∈ Sof φ})ᶜ})ᶜ := hcompl _ h4
  refine h5.congr ?_
  ext w
  rw [Set.mem_compl_iff, Set.mem_ofPred_eq, not_exists, mem_Sof_all_iff]
  constructor
  · intro h a
    by_contra hc
    exact h a hc
  · intro h a
    by_contra hc
    exact hc (h a)

/-! ## The formula induction -/

/-- Every `LRc`-formula has an `REx` realization set.  The atomic case (`∀ ι`), the complement
closure, and the arity live as hypotheses so that the induction over `φ` never has to name the
arity of a case. -/
theorem REx_Sof_of {k : ℕ} [Fintype α]
    (hatom : ∀ {ι : Type u} (t₁ t₂ : LRc.Term ι),
      REx ι {x : ι → ℝ | Term.realize x t₁ = Term.realize x t₂})
    (hcompl : ∀ {ι : Type u} [Fintype ι] (X : Set (ι → ℝ)), REx ι X → REx ι Xᶜ)
    (φ : LRc.BoundedFormula α k) : REx (α ⊕ Fin k) (Sof φ) := by
  induction φ with
  | falsum => exact REx_Sof_falsum α _
  | equal t₁ t₂ => exact REx_Sof_equal t₁ t₂ (hatom t₁ t₂)
  | rel R ts => exact REx_Sof_rel R ts
  | imp φ ψ ihφ ihψ => exact REx_Sof_imp ihφ ihψ hcompl
  | all φ ih => exact REx_Sof_all φ ih hcompl

end Work.WilC1
