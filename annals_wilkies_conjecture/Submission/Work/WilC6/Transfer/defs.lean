import Mathlib
import Submission.Work.WilC6.Base

set_option autoImplicit false
noncomputable section

open Classical FirstOrder FirstOrder.Language
open WilkiesDesign WilkiesDesign.CG
open Work.WilC6

namespace Work.WilC6.Transfer

/-- The `IsEF` part of the diagram of `M`, in the language `LEc[[M]]` (whose constants are
interpreted by the identity in `M`). -/
def diagM (M : Type) [LEc.Structure M] : LEc[[M]].Theory :=
  {ψ | IsEF ψ ∧ M ⊨ ψ}

/-- The `Finset`s of `IsEF` sentences of `LEc[[M]]` which hold in `M`. -/
abbrev diagIdx (M : Type) [LEc.Structure M] : Type :=
  {F : Finset (LEc[[M]].Sentence) // ∀ ψ ∈ F, ψ ∈ diagM M}

/-- Converting membership in `diagM M` to the `constantsVarsEquiv` form. -/
theorem diagM_mem_iff {M : Type} [LEc.Structure M] (ψ : LEc[[M]].Sentence) :
    ψ ∈ diagM M ↔ IsEF ψ ∧
      Formula.Realize (BoundedFormula.constantsVarsEquiv ψ) (Sum.elim id (fun e : Empty => e.elim)) := by
  rw [diagM, Set.mem_ofPred_eq]
  have key : Formula.Realize (BoundedFormula.constantsVarsEquiv ψ) (Sum.elim id (fun e : Empty => e.elim))
      ↔ (M ⊨ ψ) := by
    have h := @BoundedFormula.realize_constantsVarsEquiv LEc M _ M Empty _ _ 0 ψ
      (default : Empty → M) (default : Fin 0 → M)
    have hass : (Sum.elim (fun a : M => ↑(LEc.con a)) (default : Empty → M) : M ⊕ Empty → M)
        = Sum.elim id (fun e : Empty => e.elim) := by
      funext x; rcases x with m | e
      · simp only [Sum.elim_inl]
        show @Structure.funMap (LEc.sum (constantsOn M)) M _ 0
            (Sum.inr m : (LEc.sum (constantsOn M)).Functions 0) (default : Fin 0 → M) = m
        rfl
      · exact e.elim
    rw [hass] at h
    exact h
  exact ⟨fun h => ⟨h.1, key.mpr h.2⟩, fun h => ⟨h.1, key.mp h.2⟩⟩

/-- The interpretation of the `M`-constants in `M` itself is the identity. -/
theorem constantMap_con_self {M : Type} [LEc.Structure M] (m : M) :
    (FirstOrder.Language.constantMap (L := LEc[[M]]) (LEc.con m) : M) = m := by
  show @Structure.funMap (LEc.sum (constantsOn M)) M _ 0
      (Sum.inr m : (LEc.sum (constantsOn M)).Functions 0) (default : Fin 0 → M) = m
  rfl

/-- The term associated with a constant symbol. -/
abbrev cTerm {L : Language} {α : Type*} (c : L.Constants) : L.Term α :=
  Term.func c fun j : Fin 0 => j.elim0

@[simp]
theorem realize_cTerm {L : Language} {α : Type*} {M : Type} [L.Structure M] (c : L.Constants)
    (v : α → M) : Term.realize v (Term.func c fun j : Fin 0 => (j.elim0 : L.Term α)) = (c : M) := by
  simp only [Term.realize, funMap_eq_coe_constants]

/-- The sentence of `LEc[[M ⊕ N]]` linking the `M`-constant `a i` with the `N`-constant `b i`. -/
def linkSentence {n : ℕ} {M : Type} [LEc.Structure M] {N : Type} [LEc.Structure N]
    (a : Fin n → M) (b : Fin n → N) (i : Fin n) : (LEc[[M ⊕ N]]).Sentence :=
  Term.bdEqual (cTerm (Sum.inr (Sum.inl (a i)) : (LEc[[M ⊕ N]]).Functions 0))
    (cTerm (Sum.inr (Sum.inr (b i)) : (LEc[[M ⊕ N]]).Functions 0))

/-- The realization of the linking sentence. -/
theorem realize_linkSentence {n : ℕ} {M : Type} [LEc.Structure M] {N : Type} [LEc.Structure N]
    (a : Fin n → M) (b : Fin n → N) (i : Fin n) {K : Type} [(LEc[[M ⊕ N]]).Structure K] :
    (K ⊨ linkSentence a b i) ↔
      (FirstOrder.Language.constantMap (L := LEc[[M ⊕ N]])
          (Sum.inr (Sum.inl (a i)) : (LEc[[M ⊕ N]]).Functions 0) : K)
        = (FirstOrder.Language.constantMap (L := LEc[[M ⊕ N]])
          (Sum.inr (Sum.inr (b i)) : (LEc[[M ⊕ N]]).Functions 0) : K) := by
  simp only [linkSentence, Sentence.Realize, Formula.Realize]
  rw [BoundedFormula.realize_bdEqual]
  simp only [Term.realize]
  have hx : (fun i : Fin 0 => Term.realize (Sum.elim (default : Empty → K) (default : Fin 0 → K))
      (i.elim0 : (LEc[[M ⊕ N]]).Term (Empty ⊕ Fin 0))) = (default : Fin 0 → K) :=
    funext fun i => i.elim0
  rw [hx]
  exact Iff.rfl

/-- One slice of the amalgamation theory, indexed by a finite set of `IsEF` sentences of
`LEc[[M]]` which hold in `M`. -/
def Tp {n : ℕ} (M : Type) [LEc.Structure M] (N : Type) [LEc.Structure N]
    (a : Fin n → M) (b : Fin n → N) (F : diagIdx M) : (LEc[[M ⊕ N]]).Theory :=
  (LEc.lhomWithConstants (M ⊕ N)).onTheory TE
   ∪ (LEc.lhomWithConstantsMap (Sum.inr : N → M ⊕ N)).onTheory (LEc[[N]].completeTheory N)
   ∪ Set.range (linkSentence a b)
   ∪ (LEc.lhomWithConstantsMap (Sum.inl : M → M ⊕ N)).onTheory (F.val : Set _)

/-- The amalgamation theory: a model of it is an `LEc`-structure in which `M` embeds (with `a`
mapped to the `N`-copy of `b`) and which is elementarily equivalent to `N` on the tuple `b`. -/
def amalgTheory {n : ℕ} (M : Type) [LEc.Structure M] (N : Type) [LEc.Structure N]
    (a : Fin n → M) (b : Fin n → N) : (LEc[[M ⊕ N]]).Theory :=
  ⋃ F, Tp M N a b F

end Work.WilC6.Transfer
