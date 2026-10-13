/-
  Area C2 (WilC2): `definable_fin_params`.

  Any set `X ⊆ M¹` definable in `LRc` with parameters from all of `M` is the fibre of a
  *parametric* `LRc`-formula in finitely many parameters, evaluated at a point of `M`.

  The mathematical content is that a first order formula is a finite syntactic object and
  therefore uses only finitely many of its free variables: after transporting the constants
  to free variables (`Set.definable_iff_exists_formula_sum`) we may restrict to the finite
  set `freeVarFinset` of variables actually occurring, and re-index its `Fin k`-block
  faithfully (`exists_equiv_fin_sum`).
-/
import Mathlib
import Submission.Work.WilC2.Basic
import Submission.Work.WilC2.Convert
import Submission.Work.WilC2.exists_equiv_fin_sum

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC2

open WilkiesDesign.CG (LR LRc TR rexpL)

/-- **Finitely many parameters suffice.** Let `φ` be an `L`-formula whose free variables are
split as `γ ⊕ Fin k`. Then, without changing its truth value on any assignment, `φ` can be
replaced by a formula whose `γ`-block has been compressed to finitely many variables `Fin n`,
the `Fin k`-block being left untouched. -/
theorem exists_fin_relabel_elim {L : FirstOrder.Language} {M : Type} [L.Structure M]
    {γ : Type*} {k : ℕ} (φ : L.Formula (γ ⊕ Fin k)) :
    ∃ (n : ℕ) (σ : Fin n → γ) (ψ : L.Formula (Fin n ⊕ Fin k)),
      ∀ (v : γ → M) (w : Fin k → M),
        ψ.Realize (Sum.elim (v ∘ σ) w) ↔ φ.Realize (Sum.elim v w) := by
  classical
  set s' := φ.freeVarFinset ∪ Finset.univ.image (Sum.inr : Fin k → γ ⊕ Fin k) with hs'def
  obtain ⟨n, σ, E, hE1, hE2⟩ := exists_equiv_fin_sum s' (by intro j; simp [hs'def])
  refine ⟨n, σ,
    Formula.relabel E (φ.restrictFreeVar (Set.inclusion (by simp [hs'def] : ↑φ.freeVarFinset ⊆ ↑s'))),
    ?_⟩
  intro v w
  rw [Formula.realize_relabel]
  refine BoundedFormula.realize_restrictFreeVar (φ := φ)
    (f := Set.inclusion (by simp [hs'def] : ↑φ.freeVarFinset ⊆ ↑s'))
    (v := (Sum.elim (v ∘ σ) w) ∘ (E : ↥s' → (Fin n ⊕ Fin k)))
    (xs := default) (Sum.elim v w) ?_
  intro a
  change (Sum.elim (v ∘ σ) w) (E ⟨↑a, Finset.mem_union_left _ a.property⟩) = (Sum.elim v w) ↑a
  rcases hb : E ⟨↑a, Finset.mem_union_left _ a.property⟩ with i | j
  · have h3 : (E.symm (Sum.inl i)) = (⟨↑a, Finset.mem_union_left _ a.property⟩ : ↥s') :=
      (Equiv.symm_apply_eq E).mpr hb.symm
    have h4 : (↑a : γ ⊕ Fin k) = Sum.inl (σ i) :=
      (congrArg Subtype.val h3).symm.trans (hE2 i)
    simp only [h4, Sum.elim_inl, Function.comp_apply]
  · have h3 : (E.symm (Sum.inr j)) = (⟨↑a, Finset.mem_union_left _ a.property⟩ : ↥s') :=
      (Equiv.symm_apply_eq E).mpr hb.symm
    have h5 : E.symm (Sum.inr j) = ⟨Sum.inr j, by simp [hs'def]⟩ :=
      (Equiv.symm_apply_eq E).mpr (hE1 j).symm
    have h4 : (↑a : γ ⊕ Fin k) = Sum.inr j :=
      (congrArg Subtype.val h3).symm.trans (congrArg Subtype.val h5)
    simp only [h4, Sum.elim_inr]

theorem definable_fin_params {M : Type} [WilkiesDesign.CG.LRc.Structure M] {X : Set (Fin 1 → M)}
    (h : (Set.univ : Set M).Definable WilkiesDesign.CG.LRc X) :
    ∃ (n : ℕ) (φ : ParamFormula n) (v : Fin n → M),
      X = {x : Fin 1 → M | φ.Realize (Sum.elim v x)} := by
  classical
  have h' : ∃ φ : LRc.Formula ((↥(Set.univ : Set M)) ⊕ Fin 1),
      X = {v | φ.Realize (Sum.elim (fun a : ↥(Set.univ : Set M) => (a : M)) v)} :=
    (Set.definable_iff_exists_formula_sum (A := (Set.univ : Set M)) (L := LRc) (α := Fin 1)).mp h
  obtain ⟨ψ, hX⟩ := h'
  obtain ⟨n, σ, χ, hχ⟩ :=
    exists_fin_relabel_elim (L := LRc) (M := M) (k := 1) ψ
  refine ⟨n, χ, fun i => (σ i : M), ?_⟩
  rw [hX]
  apply Set.ext
  intro x
  simp only [Set.mem_ofPred_eq]
  exact (hχ (fun a : ↥(Set.univ : Set M) => (a : M)) x).symm

end Work.WilC2
