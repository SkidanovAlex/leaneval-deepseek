/-
  Area C0 (Wilkie's conjecture for Pfaffian structures): the deliverable.

  `WilkiesDesign.CG.C0_rexp_syntax_proved` has exactly the conclusion of the frozen hole
  `WilkiesDesign.CG.C0_rexp_syntax` of `Submission/Work/Wilkies/CG/Spec.lean`:

    every `LRc`-definable subset of `ℝⁿ` is `RExpExist`, given Gabrielov's theorem of the
    complement for `ℝ_rexp` (`hR`).

  The proof is the syntax induction carried out in `Work.WilC0`:
  * `Work.WilC0.RExpExistI` is `RExpExist` with an arbitrary index type of the ambient variables
    and an arbitrary finite witness type (`Submission/Work/WilC0/Basic.lean`);
  * `Work.WilC0.rexExistI_iff_rexExist` bridges it back to the frozen `RExpExist`
    (`Submission/Work/WilC0/Bridge.lean`);
  * `Work.WilC0.bfSet_rex` handles all connectives and quantifiers, using
    `Work.WilC0.termGraph_rex` for the atomic case and `Work.WilC0.RExpExistI.compl` for
    negation (`Submission/Work/WilC0/termGraph_rex.lean`, `bfSet_rex.lean`, `Compl.lean`).
-/
import Submission.Work.WilC0.Basic
import Submission.Work.WilC0.Bridge
import Submission.Work.WilC0.Compl
import Submission.Work.WilC0.termGraph_rex
import Submission.Work.WilC0.bfSet_rex

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
open FirstOrder FirstOrder.Language
open scoped FirstOrder

namespace WilkiesDesign.CG

open WilkiesDesign WilkiesConjecture
open Work.WilC0

/-- **C0, proved.** Every `LRc`-definable set of `ℝⁿ` is the projection of the zero set of a
single exp-polynomial, given Gabrielov's theorem of the complement for `ℝ_rexp`. -/
theorem C0_rexp_syntax_proved
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), RExpExist X → RExpExist Xᶜ)
    {n : ℕ} (X : Set (Fin n → ℝ)) (h : (∅ : Set ℝ).Definable LRc X) : RExpExist X := by
  obtain ⟨φ, hφ⟩ := (Set.empty_definable_iff (L := LRc) (α := Fin n)).mp h
  -- the syntax induction, applied to `φ`
  have hbf : RExpExistI {z : (Fin n ⊕ Fin 0) → ℝ |
      BoundedFormula.Realize φ (z ∘ Sum.inl) (z ∘ Sum.inr)} :=
    bfSet_rex hR (fun t => termGraph_rex t) φ
  -- `Fin 0 → ℝ` is a subsingleton: the bound-variable valuation is immaterial
  have hsub : ∀ (v : Fin n → ℝ) (xs ys : Fin 0 → ℝ),
      BoundedFormula.Realize φ v xs ↔ BoundedFormula.Realize φ v ys :=
    fun _ xs ys => by rw [Subsingleton.elim xs ys]
  have hmem : ∀ z : (Fin n ⊕ Fin 0) → ℝ,
      z ∈ {z : (Fin n ⊕ Fin 0) → ℝ | BoundedFormula.Realize φ (z ∘ Sum.inl) (z ∘ Sum.inr)}
        ↔ z ∈ {z : (Fin n ⊕ Fin 0) → ℝ |
            z ∘ (Sum.inl : Fin n → Fin n ⊕ Fin 0) ∈ Set.ofPred φ.Realize} := by
    intro z
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, Set.mem_ofPred_eq, Formula.Realize]
    exact hsub (z ∘ Sum.inl) (z ∘ Sum.inr) _
  have hA : RExpExistI {z : (Fin n ⊕ Fin 0) → ℝ |
      z ∘ (Sum.inl : Fin n → Fin n ⊕ Fin 0) ∈ Set.ofPred φ.Realize} :=
    hbf.of_eq (by ext z; exact hmem z)
  -- the canonical projection `Fin n ⊕ Fin 0 → Fin n` retracts `Sum.inl`
  let g : Fin n ⊕ Fin 0 → Fin n := Sum.elim id (fun i : Fin 0 => i.elim0)
  have hg : ∀ v : Fin n → ℝ, (v ∘ g) ∘ (Sum.inl : Fin n → Fin n ⊕ Fin 0) = v :=
    fun _ => rfl
  have hS : RExpExistI (Set.ofPred φ.Realize) :=
    (hA.pullback g).of_eq (by
      ext v
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hg v])
  rw [hφ]
  exact (rexExistI_iff_rexExist _).mp hS

/-- The same statement through the more flexible `Work.WilC0.RExpExistI` interface: usable when a
caller wants to keep manipulating the set (projections, intersections, reindexing) before applying
`Work.WilC0.rexExistI_iff_rexExist`. -/
theorem definable_rexExistI
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), RExpExist X → RExpExist Xᶜ)
    {n : ℕ} (X : Set (Fin n → ℝ)) (h : (∅ : Set ℝ).Definable LRc X) : RExpExistI X :=
  (rexExistI_iff_rexExist X).mpr (C0_rexp_syntax_proved hR X h)

end WilkiesDesign.CG
