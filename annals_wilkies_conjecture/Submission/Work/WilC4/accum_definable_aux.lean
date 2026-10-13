import Mathlib
import Submission.Work.WilC4.PBSyntax
import Submission.Work.WilC4.PBRealize
import Submission.Work.WilC4.Defs

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.WilC4

open FirstOrder FirstOrder.Language
open WilkiesDesign WilkiesDesign.CG
open Work.WilC2 (liftR leF model_exists_sq)

/-!
  `accum_definable_aux`: the three sets attached to a `T`-definable `D ⊆ M` -- its positive
  part, its negative part, and the set of lower bounds of its positive part -- are again
  `LRc`-definable over `T`.

  The language `LRc` has no order symbol, so `0 < x`, `x < 0` and `l ≤ a` have to be written as
  ring formulas: `x` is a nonzero square, `-x` is a nonzero square, and `a - l` is a square
  (`posStrictAtom`, `leF` of `Work.WilC4.PBSyntax` / `Work.WilC2.Basic`).  The hypothesis
  `hM : M ⊨ TR` is what makes the square-defined order agree with the order of the field
  (`Work.WilC2.model_exists_sq`: in a model of `TR` every nonnegative element is a square).

  Siblings proved independently in this area (the same decomposition, to be preferred by
  consumers who need a single piece): `Work.WilC4.accum_posNeg_definable` (the parameter-free
  definability of `{x | 0 < x}` and `{x | x < 0}`) and
  `Work.WilC4.accum_lowerBounds_definable` (if `P` is `T`-definable then so is the set of its
  lower bounds).
-/

section Aux

variable {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] [Ring.CompatibleRing M]
  [rexpL.Structure M] [(constantsOn ℝ).Structure M]

/-- `{x | 0 < x}` is `LRc`-definable without parameters: it is the ring formula
`x ≠ 0 ∧ ∃ y, y * y = x`. -/
theorem posStrictSet_definable (hM : M ⊨ TR) :
    (∅ : Set M).Definable LRc {z : Fin 1 → M | 0 < z 0} := by
  rw [Set.empty_definable_iff]
  refine ⟨liftR (fun _ : Fin 1 => (0 : Fin 1)) posStrictAtom, ?_⟩
  ext z
  simp only [Set.mem_ofPred_eq]
  exact (posStrictAtom_lift (fun _ : Fin 1 => (0 : Fin 1)) z (model_exists_sq hM)).symm

/-- `{x | x < 0}` is `LRc`-definable without parameters: it is the complement of the ring formula
`∃ y, y * y = x` (`0 ≤ x`), negated using `M ⊨ TR`. -/
theorem negStrictSet_definable (hM : M ⊨ TR) :
    (∅ : Set M).Definable LRc {z : Fin 1 → M | z 0 < 0} := by
  have hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z := model_exists_sq hM
  have hpos : (∅ : Set M).Definable LRc {z : Fin 1 → M | 0 ≤ z 0} := by
    rw [Set.empty_definable_iff]
    refine ⟨liftR (fun _ : Fin 1 => (0 : Fin 1)) posAtom, ?_⟩
    ext z
    simp only [Set.mem_ofPred_eq]
    rw [posAtom_lift (fun _ : Fin 1 => (0 : Fin 1)) z, exists_sq_iff_nonneg hsq]
  have h := hpos.compl
  convert h using 1
  ext z
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]

/-- `{(x, y) | x ≤ y}` is `LRc`-definable without parameters, in any variable context: it is the
ring formula `∃ z, x + z * z = y`. -/
theorem leCtx_definable (hM : M ⊨ TR) {Ctx : Type} (u v : Ctx) :
    (∅ : Set M).Definable LRc {z : Ctx → M | z u ≤ z v} := by
  rw [Set.empty_definable_iff]
  refine ⟨liftR ![u, v] leF, ?_⟩
  ext z
  simp only [Set.mem_ofPred_eq]
  exact (leF_lift2 u v z (model_exists_sq hM)).symm

/-- `Definable₁` is closed under intersections. -/
theorem definable₁_inter {A : Set M} {s t : Set M}
    (hs : A.Definable₁ LRc s) (ht : A.Definable₁ LRc t) : A.Definable₁ LRc (s ∩ t) := by
  have hset : ({v : Fin 1 → M | v 0 ∈ s} ∩ {v : Fin 1 → M | v 0 ∈ t})
      = {v : Fin 1 → M | v 0 ∈ s ∩ t} := by
    ext v
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  rw [Set.Definable₁, ← hset]
  exact hs.inter ht

/-- If `P` is `A`-definable then so is the set of its lower bounds: the universal quantification
is removed by `Definable.forall_of_finite`, and `l ≤ a` is the parameter-free `LRc`-definable
relation `leCtx_definable`. -/
theorem lowerBounds_definable (hM : M ⊨ TR) {A P : Set M}
    (hP : A.Definable LRc {x : Fin 1 → M | x 0 ∈ P}) :
    A.Definable LRc {v : Fin 1 → M | ∀ a : M, a ∈ P → v 0 ≤ a} := by
  classical
  set W : Set ((Fin 1 ⊕ Fin 1) → M) :=
    {w | (w (Sum.inr 0) ∈ P) → w (Sum.inl 0) ≤ w (Sum.inr 0)} with hWdef
  have hW1 : A.Definable LRc {w : (Fin 1 ⊕ Fin 1) → M | w (Sum.inr 0) ∈ P} := by
    have h := hP.preimage_comp (Sum.inr : Fin 1 → Fin 1 ⊕ Fin 1)
    convert h using 1
    ext w
    rfl
  have hW2 : A.Definable LRc {w : (Fin 1 ⊕ Fin 1) → M | w (Sum.inl 0) ≤ w (Sum.inr 0)} :=
    (leCtx_definable hM (Sum.inl (0 : Fin 1)) (Sum.inr (0 : Fin 1))).mono
      (Set.empty_subset A)
  have hW : A.Definable LRc W := by
    rw [hWdef]
    have h := hW1.compl.union hW2
    convert h using 1
    ext w
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq]
    tauto
  have hforall := hW.forall_of_finite (α := Fin 1) (β := Fin 1)
  convert hforall using 1
  ext v
  rw [hWdef]
  simp only [Set.mem_ofPred_eq, Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro hv u hu
    exact hv (u 0) hu
  · intro hv a ha
    exact hv (fun _ => a) ha

end Aux

theorem accum_definable_aux {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M] (hM : M ⊨ WilkiesDesign.CG.TR) {T D : Set M} (hDd : T.Definable₁ WilkiesDesign.CG.LRc D) : T.Definable₁ WilkiesDesign.CG.LRc {x : M | x ∈ D ∧ 0 < x} ∧ T.Definable₁ WilkiesDesign.CG.LRc {x : M | x ∈ D ∧ x < 0} ∧ T.Definable₁ WilkiesDesign.CG.LRc {l : M | ∀ a : M, a ∈ D → 0 < a → l ≤ a} := by
  have hpos : T.Definable₁ LRc {x : M | 0 < x} :=
    (posStrictSet_definable hM).mono (Set.empty_subset T)
  have hneg : T.Definable₁ LRc {x : M | x < 0} :=
    (negStrictSet_definable hM).mono (Set.empty_subset T)
  have hP : T.Definable₁ LRc {a : M | a ∈ D ∧ 0 < a} := definable₁_inter hDd hpos
  have hPn : T.Definable₁ LRc {a : M | a ∈ D ∧ a < 0} := definable₁_inter hDd hneg
  refine ⟨?_, ?_, ?_⟩
  · rw [Set.Definable₁]
    exact hP
  · rw [Set.Definable₁]
    exact hPn
  · rw [Set.Definable₁]
    have hle : T.Definable LRc
        {v : Fin 1 → M | ∀ a : M, a ∈ {a : M | a ∈ D ∧ 0 < a} → v 0 ≤ a} :=
      lowerBounds_definable hM hP
    convert hle using 1
    ext v
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro hv a haD
      exact hv a haD.1 haD.2
    · intro hv a haD hpos
      exact hv a ⟨haD, hpos⟩

end Work.WilC4
