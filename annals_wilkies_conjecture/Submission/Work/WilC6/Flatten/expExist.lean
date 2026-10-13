/-
  WilC6 — flattening `IsEF` formulas into `ExpExist` sets.

  The main theorem `expExist` states that over `ℝ` every `IsEF` formula defines an `ExpExist` set.
  The proof is an induction on the derivation of `IsEF`, using:

  * the graph lemma `Gr_expExist` (every term graph is `ExpExistI`),
  * the atom lemmas `expExistI_eq_term` / `expExistI_ne_term`,
  * closure of `ExpExistI` under finite intersections, unions, projections and reindexings.
-/
import Mathlib
import Submission.Work.WilC6.Base
import Submission.Work.WilkiesB.Defs
import Submission.Work.WilkiesB.Closure
import Submission.Work.WilkiesB.Term
import Submission.Work.WilC6.Flatten.graph

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open Classical FirstOrder FirstOrder.Language
open WilkiesDesign.CG
open Work.WilkiesB

namespace Work.WilC6.Flatten

/-! ## The set defined by a bounded formula -/

/-- The subset of `(Fin k ⊕ Fin m) → ℝ` defined by a bounded formula: the free variables come
first (`Fin k`) and the bound variables last (`Fin m`). -/
def bset {k m : ℕ} (φ : LEc.BoundedFormula (Fin k) m) : Set ((Fin k ⊕ Fin m) → ℝ) :=
  {σ | φ.Realize (σ ∘ Sum.inl) (σ ∘ Sum.inr)}

/-! ## The reindexing used for the existential-quantifier step -/

theorem snocEquiv_comp_inl {k m : ℕ} (σ : Fin k ⊕ Fin m → ℝ) (b : ℝ) :
    ((Sum.elim σ (fun _ : Fin 1 => b)) ∘ ⇑(sumFinSnocEquiv (Fin k) m)) ∘
        (Sum.inl : Fin k → Fin k ⊕ Fin (m + 1)) = σ ∘ Sum.inl := by
  funext i
  simp only [Function.comp_apply, sumFinSnocEquiv_inl, Sum.elim_inl]

theorem snocEquiv_comp_inr {k m : ℕ} (σ : Fin k ⊕ Fin m → ℝ) (b : ℝ) :
    ((Sum.elim σ (fun _ : Fin 1 => b)) ∘ ⇑(sumFinSnocEquiv (Fin k) m)) ∘
        (Sum.inr : Fin (m + 1) → Fin k ⊕ Fin (m + 1)) = snocReal (σ ∘ Sum.inr) b := by
  funext j
  induction j using Fin.lastCases with
  | last =>
      show (Sum.elim σ (fun _ : Fin 1 => b)) (sumFinSnocEquiv (Fin k) m (Sum.inr (Fin.last m))) =
        snocReal (σ ∘ Sum.inr) b (Fin.last m)
      rw [sumFinSnocEquiv_inr_last, Sum.elim_inr]
      exact (snocReal_last (σ ∘ Sum.inr) b).symm
  | cast j =>
      show (Sum.elim σ (fun _ : Fin 1 => b)) (sumFinSnocEquiv (Fin k) m (Sum.inr j.castSucc)) =
        snocReal (σ ∘ Sum.inr) b j.castSucc
      rw [sumFinSnocEquiv_inr_castSucc, Sum.elim_inl]
      exact (snocReal_castSucc (σ ∘ Sum.inr) b j).symm

/-! ## The existential-quantifier step -/

theorem ex_step {k m : ℕ} {ψ : LEc.BoundedFormula (Fin k) (m + 1)}
    (hX : ExpExistI (bset ψ)) :
    ExpExistI (bset (BoundedFormula.ex ψ)) := by
  refine (ExpExistI.projLast
    (ExpExistI.pullback (⇑(sumFinSnocEquiv (Fin k) m)) hX)).of_eq ?_
  ext σ
  constructor
  · rintro ⟨a, ha⟩
    simp only [Set.mem_ofPred_eq, bset] at ha
    simp only [Set.mem_ofPred_eq, bset, BoundedFormula.realize_ex]
    refine ⟨a, ?_⟩
    rw [snocEquiv_comp_inl, snocEquiv_comp_inr] at ha
    exact ha
  · intro hσ
    simp only [Set.mem_ofPred_eq, bset, BoundedFormula.realize_ex] at hσ
    obtain ⟨a, ha⟩ := hσ
    simp only [Set.mem_ofPred_eq, bset]
    refine ⟨a, ?_⟩
    rw [snocEquiv_comp_inl, snocEquiv_comp_inr]
    exact ha

/-! ## The induction on `IsEF` -/

/-- Every `IsEF` bounded formula defines an `ExpExistI` set. -/
theorem expExistI_of_isEF {k m : ℕ} (φ : LEc.BoundedFormula (Fin k) m) (h : IsEF φ) :
    ExpExistI (bset φ) := by
  induction h with
  | top =>
      exact ExpExistI.of_eq (by ext σ; simp [bset]) ExpExistI_univ
  | bot =>
      exact ExpExistI.of_eq (by ext σ; simp [bset]) ExpExistI_empty
  | bdEq t₁ t₂ =>
      refine (expExistI_eq_term t₁ t₂).of_eq ?_
      ext σ
      change t₁.realize σ = t₂.realize σ ↔ σ ∈ bset (Term.bdEqual t₁ t₂)
      simp only [Set.mem_ofPred_eq, bset, BoundedFormula.realize_bdEqual, sumElim_comp_self]
  | bdNe t₁ t₂ =>
      refine (expExistI_ne_term t₁ t₂).of_eq ?_
      ext σ
      change t₁.realize σ ≠ t₂.realize σ ↔ σ ∈ bset (BoundedFormula.not (Term.bdEqual t₁ t₂))
      simp only [Set.mem_ofPred_eq, bset, BoundedFormula.realize_not,
        BoundedFormula.realize_bdEqual, sumElim_comp_self]
  | inf _ _ ih₁ ih₂ =>
      refine (ExpExistI.inter ih₁ ih₂).of_eq ?_
      ext σ
      simp only [Set.mem_ofPred_eq, bset, Set.mem_inter_iff, BoundedFormula.realize_inf]
  | sup _ _ ih₁ ih₂ =>
      refine (ExpExistI.union ih₁ ih₂).of_eq ?_
      ext σ
      simp only [Set.mem_ofPred_eq, bset, Set.mem_union, BoundedFormula.realize_sup]
  | ex _ ih =>
      exact ex_step ih

/-! ## The target theorem -/

theorem expExist {n : ℕ} (φ : WilkiesDesign.CG.LEc.Formula (Fin n))
    (h : Work.WilC6.IsEF φ) :
    WilkiesDesign.ExpExist (Work.WilC6.realizeSet φ) := by
  have hS := expExistI_of_isEF (k := n) (m := 0) φ h
  refine (Work.WilkiesB.expExist_iff_expExistI _).mpr ?_
  refine ExpExistI.of_eq ?_
    (ExpExistI.pullback (Sum.elim id (fun j : Fin 0 => Fin.elim0 j)) hS)
  ext x
  have h1 : (x ∘ Sum.elim id (fun j : Fin 0 => Fin.elim0 j)) ∘ (Sum.inl : Fin n → Fin n ⊕ Fin 0)
      = x := by
    funext i; rfl
  constructor
  · intro hx
    simp only [Set.mem_ofPred_eq, bset] at hx
    rw [h1] at hx
    exact (Formula.boundedFormula_realize_eq_realize φ x _).mp hx
  · intro hx
    simp only [Set.mem_ofPred_eq, bset]
    rw [h1]
    exact (Formula.boundedFormula_realize_eq_realize φ x _).mpr hx

end Work.WilC6.Flatten
