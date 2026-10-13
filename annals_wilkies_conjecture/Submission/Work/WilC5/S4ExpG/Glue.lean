import Mathlib
import Submission.Work.WilC5.S4OnePointCases
import Submission.Work.WilC5.S4OnePoint
import Submission.Work.WilC5.extends_elemOn_sat
import Submission.Work.WilC5.elemOn_insert_of_type
import Submission.Work.WilC5.Translate
import Submission.Work.WilC5.realizes_cut
import Submission.Work.WilC5.RealConst

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

attribute [local instance] Work.WilC5.reductStruct

/-! ## 0. Saturation transfers from `LEc` to `LRc`

Every `LRc`-formula is equivalent, over any `LEc`-structure, to the `LEc`-formula `formulaTrans φ`
(`Translate.lean`).  Hence a `κ`-saturated `LEc`-structure is `κ`-saturated for the reduct `LRc`:
an `LRc`-type pulls back to an `LEc`-type with the same finite satisfiability. -/
theorem lrcSaturated_of_lecSaturated {M : Type} [LEc.Structure M] (κ : Cardinal.{0})
    (h : @Work.WilC5.IsSaturated LEc M _ κ) :
    @Work.WilC5.IsSaturated LRc M (reductStruct M) κ := by
  classical
  letI : LRc.Structure M := reductStruct M
  intro A hA p hp
  set q : Set (LEc.Formula (A ⊕ Fin 1)) := {ψ | ∃ φ ∈ p, ψ = formulaTrans φ} with hq
  have hqmem : ∀ ψ, ψ ∈ q ↔ ∃ φ ∈ p, ψ = formulaTrans φ := fun ψ => Iff.rfl
  have hqfin : ∀ F : Finset (LEc.Formula (A ⊕ Fin 1)), (∀ ψ ∈ F, ψ ∈ q) →
      ∃ x : Fin 1 → M, ∀ ψ ∈ F,
        @BoundedFormula.Realize LEc M _ (A ⊕ Fin 1) 0 ψ
          (Sum.elim Subtype.val x) (fun i : Fin 0 => i.elim0) := by
    intro F hF
    have hg : ∀ b : {ψ // ψ ∈ F},
        ∃ φ ∈ p, (b.1 : LEc.Formula (A ⊕ Fin 1)) = formulaTrans φ :=
      fun b => (hqmem b.1).mp (hF b.1 b.2)
    set g : {ψ // ψ ∈ F} → LRc.Formula (A ⊕ Fin 1) :=
      fun b => Classical.choose (hg b) with hgdef
    have hg_mem : ∀ b : {ψ // ψ ∈ F}, g b ∈ p := fun b => (Classical.choose_spec (hg b)).1
    have hg_eq : ∀ b : {ψ // ψ ∈ F}, (b.1 : LEc.Formula (A ⊕ Fin 1)) =
        formulaTrans (g b) := fun b => (Classical.choose_spec (hg b)).2
    set G : Finset (LRc.Formula (A ⊕ Fin 1)) := F.attach.image g with hGdef
    have hGsub : ∀ φ ∈ G, φ ∈ p := by
      intro φ hφ
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.mp hφ
      exact hg_mem b
    obtain ⟨x, hx⟩ := hp G hGsub
    refine ⟨x, fun ψ hψ => ?_⟩
    have hb : g ⟨ψ, hψ⟩ ∈ G :=
      Finset.mem_image.mpr ⟨⟨ψ, hψ⟩, Finset.mem_attach F ⟨ψ, hψ⟩, rfl⟩
    have h1 : @BoundedFormula.Realize LRc M (reductStruct M)
        (A ⊕ Fin 1) 0 (g ⟨ψ, hψ⟩) (Sum.elim Subtype.val x) (fun i : Fin 0 => i.elim0) :=
      hx (g ⟨ψ, hψ⟩) hb
    have hψeq : ψ = formulaTrans (g ⟨ψ, hψ⟩) := hg_eq ⟨ψ, hψ⟩
    rw [hψeq]
    exact (cutBounded_iff (formulaTrans (g ⟨ψ, hψ⟩))
      (Sum.elim Subtype.val x)).mpr ((formulaTrans_realize (g ⟨ψ, hψ⟩)
        (Sum.elim Subtype.val x) (fun i : Fin 0 => i.elim0)).mpr h1)
  obtain ⟨x, hx⟩ := h A hA q hqfin
  refine ⟨x, fun φ hφ => ?_⟩
  have hmem : formulaTrans φ ∈ q := ⟨φ, hφ, rfl⟩
  have h1 := hx (formulaTrans φ) hmem
  exact (cutBounded_iff φ (Sum.elim Subtype.val x)).mpr
    ((formulaTrans_realize φ (Sum.elim Subtype.val x) (fun i : Fin 0 => i.elim0)).mp
      ((cutBounded_iff (formulaTrans φ) (Sum.elim Subtype.val x)).mp h1))

/-! ## 0b. Transporting saturation along an equality of structures -/

/-- `IsSaturated` only depends on the `LRc`-structure through the realization of formulas, so it
transports along an equality of structures. -/
theorem isSaturated_congr {M : Type} {i i' : LRc.Structure M} (h : i = i') (κ : Cardinal.{0}) :
    @Work.WilC5.IsSaturated LRc M i κ ↔ @Work.WilC5.IsSaturated LRc M i' κ := by
  cases h
  exact Iff.rfl

/-! ## 1. Glue: moving substructures across two equal `LRc`-structures -/

/-- A substructure of `M` at an explicitly given `LRc`-structure, from a carrier and its
closure under the function symbols. -/
noncomputable def mkSubAt (M : Type) (i : LRc.Structure M) (S : Set M)
    (hmem : ∀ {n : ℕ} (f : LRc.Functions n) (x : Fin n → M),
      (∀ k, x k ∈ S) → @Structure.funMap LRc M i n f x ∈ S) :
    @FirstOrder.Language.Substructure LRc M i := by
  letI : LRc.Structure M := i
  exact ⟨S, fun {n} f x hx => hmem f x hx⟩

@[simp] theorem mkSubAt_coe {M : Type} (i : LRc.Structure M) (S : Set M) (hmem) :
    (mkSubAt M i S hmem : Set M) = S := rfl

/-- **The `rexp`-reduct of an `LEc`-structure agrees with the syntactic `LRc`-structure**
synthesised from the ordered-field data. -/
theorem reductStruct_eq_withConstants {M : Type} [LEc.Structure M] [Field M] [LinearOrder M]
    [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M] :
    (reductStruct M : LRc.Structure M) = (LR.withConstantsStructure ℝ) := by
  ext n f x
  · rcases f with (g | c)
    · rcases g with (g | r)
      · rfl
      · cases r
        show rexpFromExp (x 0) = _
        rfl
    · rfl
  · nomatch f

/-- The `funMap`s of the two equal `LRc`-structures agree. -/
theorem funMap_reduct_synth {M : Type} [LEc.Structure M] [Field M] [LinearOrder M]
    [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M] {n : ℕ} (f : LRc.Functions n)
    (x : Fin n → M) :
    @Structure.funMap LRc M (LR.withConstantsStructure ℝ) n f x
      = @Structure.funMap LRc M (reductStruct M) n f x :=
  (congrArg (fun i => @Structure.funMap LRc M i n f x)
    (reductStruct_eq_withConstants (M := M))).symm

/-- The `realConst`s of the two equal `LRc`-structures agree. -/
theorem realConst_reduct_synth {M : Type} [LEc.Structure M] [Field M] [LinearOrder M]
    [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M] (r : ℝ) :
    realConst M r = @Work.WilC5.realConst M (LR.withConstantsStructure ℝ) r := by
  show @Structure.funMap LRc M (reductStruct M) 0 (Sum.inr r) ![] =
    @Structure.funMap LRc M (LR.withConstantsStructure ℝ) 0 (Sum.inr r) ![]
  exact congrArg (fun i => @Structure.funMap LRc M i 0 (Sum.inr r) ![])
    (reductStruct_eq_withConstants (M := M))


/-- Realization of a bounded formula is unaffected by replacing the `LRc`-structure by an equal
one. -/
theorem boundedRealize_struct_congr {M : Type} (i i' : LRc.Structure M) (h : i = i')
    {α : Type} {n : ℕ} (φ : LRc.BoundedFormula α n) (v : α → M) (xs : Fin n → M) :
    @BoundedFormula.Realize LRc M i α n φ v xs ↔
      @BoundedFormula.Realize LRc M i' α n φ v xs := by
  cases h
  exact Iff.rfl

/-- Rewriting a membership along an equation of carrier sets. -/
theorem mem_congr {M : Type} {S T : Set M} (h : S = T) {x : M} (hx : x ∈ S) : x ∈ T :=
  h ▸ hx

/-- Realization of a formula is unaffected by replacing the `LRc`-structure by an equal one. -/
theorem formulaRealize_congr {M : Type} (i i' : LRc.Structure M) (h : i = i')
    {α : Type} (φ : LRc.Formula α) (v : α → M) :
    @FirstOrder.Language.Formula.Realize LRc M i α φ v ↔
      @FirstOrder.Language.Formula.Realize LRc M i' α φ v := by
  cases h
  exact Iff.rfl


end Work.WilC5
