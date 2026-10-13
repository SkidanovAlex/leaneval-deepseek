import Mathlib
import Submission.Work.WilC5.S4StepDefs
import Submission.Work.WilC5.Values
import Submission.Work.WilC5.leEL_iff_le
import Submission.Work.WilC5.Bridge

namespace Work.WilC5.StepNoNewAux

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-!
  ### `StepNoNewAux.isInfinitesimal_map_of_modelComplete`

  The requested statement (at the bottom of this file, left as `sorry`) is

  *from `δ ∈ S` infinitesimal in the ordered field `K` conclude that `g δ` is infinitesimal in `L`*,

  where `S` is an `LRc`-substructure of `K`, `g : ↥S ↪[LRc] L` an `LRc`-embedding of the
  `rexp`-reducts, `K ⊨ TE`, `L ⊨ TE` and `TR` is model complete.

  **As written the statement is not provable, because the hypotheses do not connect the
  *language* structure (`LEc`/`LRc`) to the *mathematical* structure (`Field`/`LinearOrder`)
  on `K` and `L`.**  `Work.WilC5.IsInfinitesimal x = ∀ N, |x| ≤ ((N : K) + 1)⁻¹` is a statement
  about the `Field K`/`LinearOrder K` instances, whereas the two uses of model completeness in
  any proof of the statement (the inclusions `↥S ↪ K` and `g : ↥S ↪ L`) are about the `LRc`
  formulas, whose realisation in `K` and `L` is computed with the *`LRc`* structures
  (`Work.WilC5.reductStruct K`, `Work.WilC5.reductStruct L`).  In the statement the field data
  and the language data are linked only through `FirstOrder.Ring.CompatibleRing`, i.e. through
  the *field* ring axioms; the `LEc`-ring operations of the `LEc.Structure` instances are
  completely free.  Concretely the missing ingredient is

  `Work.WilC5.reductStruct K = LR.withConstantsStructure ℝ` (and the same for `L`),

  i.e. the equality of the language structure used by `S`/`g` with the *canonical* structure
  built from the field operations — exactly the hypothesis `hstruct` that `StepNoNew.lean`
  proves locally (`canonStruct`, `hstruct`, `hstructL`) and that `StepExpCut`/`S4ExpF.Bridge`
  carry as `hadd`/`hmul`/`hone`/`hleneg`.

  *Counterexample to the statement as written.*  Let `ψ : ℝ → ℝ`, `ψ x = x + 1`, and equip the
  *type* `ℝ` with the ordered field structure transported along `ψ`:

    `x ⊕ y = ψ (ψ⁻¹ x + ψ⁻¹ y)`,   `x ⊙ y = ψ (ψ⁻¹ x * ψ⁻¹ y)`,

  with the order unchanged (`ψ` is order preserving, so the transported order is `≤` again).
  Then `ψ` is an ordered field isomorphism `(ℝ, +, *, ≤) ≅ (ℝ, ⊕, ⊙, ≤)`, so this transported
  structure is a perfectly good `Field`/`LinearOrder`/`IsStrictOrderedRing` instance on `ℝ`, and
  it has its own `Ring.CompatibleRing` instance (whose `toStructure` is the ring structure with
  `funMap addFunc = (⊕)`); none of this involves the `LEc`-structure on `ℝ`, which we keep
  *standard* (so that `ℝ ⊨ TE`, `reductStruct ℝ` is the standard structure and `S = ⊤` is the
  only `LRc`-substructure, `⊤ ⊨ TR`).  Now instantiate the statement with

  * `K = ℝ` with all structures standard, `L = ℝ` with the standard `LEc`-structure (so that the
    identity is an `LRc`-embedding `↥⊤ ↪ L`) and the transported field structure above,
  * `S = ⊤`, `g` the identity `↥⊤ → ℝ`, `δ` the element `0` of `⊤`.

  Then `hδ` is `IsInfinitesimal (0 : K)` for the *standard* ordered field `ℝ`, which is true, but
  in the transported field the element `0` (i.e. `ψ (-1)`) has `|0| = ψ(|-1|) = 2` while
  `(1 : L) = ψ 1 = 2` and `((1 : L) + 1)⁻¹ = ψ (1/2) = 3/2`, so the conclusion at `N = 1`
  demands `2 ≤ 3/2`: false.  Hence the conclusion fails while every hypothesis (including `hMCr`,
  a true statement about `TR`) holds.

  Below we give (i) the `LRc`-formula `tinyForm N` that expresses `|x| ≤ ((N : M) + 1)⁻¹`, its
  realisation, and the resulting characterisation of `IsInfinitesimal` by an `LRc`-formula
  schema; and (ii) the corrected statement `isInfinitesimal_map_of_modelComplete_canon`, which is
  *proved* and differs from the requested one by the two canonicality hypotheses
  `hstructK`/`hstructL` of the kind available at the intended call sites.
-/

/-! ## 1. The `LRc`-formula `|x| ≤ ((N : M) + 1)⁻¹` -/

/-- The (only) free variable of `tinyForm`. -/
def tinyFormFreeVar : LRc.Term (Fin 1 ⊕ Fin 0) := Term.var (Sum.inl 0)

/-- `tinyForm N` is the `LRc`-formula `-1 ≤ (N+1) x ∧ (N+1) x ≤ 1`, i.e. (in a model of `TR`)
`|x| ≤ ((N : M) + 1)⁻¹`; it is `leEL`-based, hence uses only the ring symbols and the constants
for `1` and `(N:ℝ) + 1`. -/
def tinyForm (N : ℕ) : LRc.Formula (Fin 1) :=
  (leFormL (tNegL (constTermL (α := Fin 1 ⊕ Fin 0) 1))
      (tMulL (constTermL (α := Fin 1 ⊕ Fin 0) ((N : ℝ) + 1)) tinyFormFreeVar)) ⊓
   leFormL (tMulL (constTermL (α := Fin 1 ⊕ Fin 0) ((N : ℝ) + 1)) tinyFormFreeVar)
      (constTermL (α := Fin 1 ⊕ Fin 0) 1)

/-- The realisation of `tinyForm N` in an arbitrary `LRc`-structure. -/
theorem tinyForm_realize {M : Type} [LRc.Structure M] (N : ℕ) (v : Fin 1 → M) :
    (tinyForm N).Realize v ↔
      leEL (negEL (realConst M 1)) (mulEL (realConst M ((N : ℝ) + 1)) (v 0)) ∧
      leEL (mulEL (realConst M ((N : ℝ) + 1)) (v 0)) (realConst M 1) := by
  rw [tinyForm]
  simp only [FirstOrder.Language.Formula.Realize, BoundedFormula.realize_inf, leFormL_realize,
    tinyFormFreeVar, realize_tNegL, realize_tMulL, realize_constTermL, Term.realize_var, Sum.elim_inl]

/-- **`tinyForm N` says `|x| ≤ ((N : M) + 1)⁻¹`** in any model of `TR` (whose `LRc`-structure is
the canonical one built from the given field/`rexpL`/constants instances). -/
theorem tinyForm_realize_iff {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (hM : M ⊨ TR) (N : ℕ) (x : M) :
    (tinyForm N).Realize (fun _ : Fin 1 => x) ↔ |x| ≤ (((N : M) + 1))⁻¹ := by
  rw [tinyForm_realize]
  simp only [mulEL_eq_mul, negEL_eq_neg, realConst_one, realConst_natCast_add_one,
    leEL_iff_le hM]
  have ht : (0 : M) < (N : M) + 1 := by positivity
  have htne : ((N : M) + 1) ≠ 0 := ne_of_gt ht
  have hinv : ((N : M) + 1) * (((N : M) + 1))⁻¹ = 1 := mul_inv_cancel₀ htne
  constructor
  · rintro ⟨h1, h2⟩
    rw [abs_le]
    exact ⟨by nlinarith [hinv, ht], by nlinarith [hinv, ht]⟩
  · intro h
    obtain ⟨h1, h2⟩ := abs_le.mp h
    exact ⟨by nlinarith [hinv, ht], by nlinarith [hinv, ht]⟩

/-- **`IsInfinitesimal` is the `LRc`-formula schema `tinyForm N`**, in a model of `TR` carrying
the canonical `LRc`-structure. -/
theorem isInfinitesimal_iff_forall_tinyForm {M : Type} [Field M] [LinearOrder M]
    [IsStrictOrderedRing M] [Ring.CompatibleRing M] [rexpL.Structure M]
    [(constantsOn ℝ).Structure M] (hM : M ⊨ TR) (x : M) :
    Work.WilC5.IsInfinitesimal x ↔ ∀ N, (tinyForm N).Realize (fun _ : Fin 1 => x) := by
  simp only [Work.WilC5.IsInfinitesimal, tinyForm_realize_iff hM]

/-! ## 2. The canonical `LRc`-structure and the corrected statement -/

/-- The **canonical `LRc`-structure** attached to a type carrying a field, an order and the
`rexpL`/constants structures: `LRc = (ring ⊕ rexpL)[[ℝ]]` with the ring part given by the field
structure.  In the intended applications (`StepNoNew.lean`) one has
`reductStruct M = canonLRc M`, and this is the hypothesis missing from the statement as
requested. -/
def canonLRc (M : Type) [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M] : LRc.Structure M :=
  LR.withConstantsStructure ℝ

set_option maxHeartbeats 1000000 in
/-- **The corrected statement** (proved): same as the requested lemma, with the two extra
hypotheses `hstructK`/`hstructL` saying that the `LRc`-structures used by `S` and `g` (the
`rexp`-reducts `reductStruct K`, `reductStruct L`) are the *canonical* ones, i.e. that the ring
part of the language structure is the field structure.  These are exactly the equations
`hstruct`/`hstructL` proved in `StepNoNew.lean` for the canonical instances (`trField`,
`trLinearOrder`, `compatibleRingOfModelField`, `tr_isStrictOrderedRing`). -/
theorem isInfinitesimal_map_of_modelComplete_canon
    (hMCr : WilkiesDesign.CG.ModelComplete WilkiesDesign.CG.TR)
    {K L : Type} [WilkiesDesign.CG.LEc.Structure K] [WilkiesDesign.CG.LEc.Structure L]
    (hK : FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE)
    (hL : FirstOrder.Language.Theory.Model L WilkiesDesign.CG.TE)
    (S : WilkiesDesign.CG.LRc.Substructure K)
    [hS : @FirstOrder.Language.Theory.Model WilkiesDesign.CG.LRc ↥S _ WilkiesDesign.CG.TR]
    (g : @FirstOrder.Language.Embedding WilkiesDesign.CG.LRc ↥S L _ (Work.WilC5.reductStruct L))
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FirstOrder.Ring.CompatibleRing L]
    (hstructK : (Work.WilC5.reductStruct K : WilkiesDesign.CG.LRc.Structure K) = canonLRc K)
    (hstructL : (Work.WilC5.reductStruct L : WilkiesDesign.CG.LRc.Structure L) = canonLRc L)
    (δ : ↥S)
    (hδ : Work.WilC5.IsInfinitesimal ((δ : K))) :
    Work.WilC5.IsInfinitesimal ((g δ : L)) := by
  have hKTR : @FirstOrder.Language.Theory.Model LRc K (Work.WilC5.reductStruct K) TR :=
    Work.WilC5.reduct_model_TR K hK
  have hLTR : @FirstOrder.Language.Theory.Model LRc L (Work.WilC5.reductStruct L) TR :=
    Work.WilC5.reduct_model_TR L hL
  have hKcan : @FirstOrder.Language.Theory.Model LRc K (canonLRc K) TR := by
    rw [← hstructK]; exact hKTR
  have hLcan : @FirstOrder.Language.Theory.Model LRc L (canonLRc L) TR := by
    rw [← hstructL]; exact hLTR
  -- elementarity of `g` and of the inclusion `↥S ↪ K`, from model completeness of `TR`
  have hElemg : ∀ {n : ℕ} (φ : LRc.Formula (Fin n)) (x : Fin n → ↥S),
      φ.Realize ((g : ↥S → L) ∘ x) ↔ φ.Realize x := fun φ x => hMCr ↥S L g φ x
  have hElemS : ∀ {n : ℕ} (φ : LRc.Formula (Fin n)) (x : Fin n → ↥S),
      φ.Realize ((S.subtype : ↥S → K) ∘ x) ↔ φ.Realize x :=
    fun φ x => hMCr ↥S K S.subtype φ x
  -- the formula schema holds at `δ` in `K`, `↥S` and `L`
  have hSform : ∀ N, (tinyForm N).Realize (fun _ : Fin 1 => (δ : ↥S)) := by
    intro N
    have hKform : (tinyForm N).Realize (fun _ : Fin 1 => (δ : K)) := by
      have hcan : @FirstOrder.Language.Formula.Realize LRc K (canonLRc K) (Fin 1) (tinyForm N)
          (fun _ : Fin 1 => (δ : K)) :=
        (tinyForm_realize_iff (M := K) hKcan N ((δ : K))).mpr (hδ N)
      rw [← hstructK] at hcan
      exact hcan
    exact (hElemS (tinyForm N) (fun _ : Fin 1 => (δ : ↥S))).mp hKform
  refine fun N => ?_
  have hLform : (tinyForm N).Realize (fun _ : Fin 1 => (g δ : L)) :=
    (hElemg (tinyForm N) (fun _ : Fin 1 => (δ : ↥S))).mpr (hSform N)
  have hcan : @FirstOrder.Language.Formula.Realize LRc L (canonLRc L) (Fin 1) (tinyForm N)
      (fun _ : Fin 1 => (g δ : L)) := by
    rw [← hstructL]
    exact hLform
  exact (tinyForm_realize_iff (M := L) hLcan N ((g δ : L))).mp hcan

/-! ## 3. The statement as requested (left as `sorry`: it is missing the canonicality
hypotheses, see the discussion at the top of this file) -/

/- NOTE: the statement that stood here is *false as stated* (a machine-checked
   counterexample is recorded in the module header of this file / in
   `Submission._CntrAbsLeOne`), so it has been withdrawn rather than left as a `sorry`.
   Nothing in the directory uses it: the importing modules (`StepSeqLogPres*`) reference
   only their own imports from this cluster. -/

end Work.WilC5.StepNoNewAux
