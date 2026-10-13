-- NOTE (WilC5 / S4OnePoint_general): a clash-free *copy* of `Submission/Work/WilC5/StepNoNewPrep.lean`:
-- the import of the `StepNoNewPrep`/`StepNoNew` chain is redirected to the corresponding
-- `…Cut` copies, in which the auxiliary definition `mkSubAt` is renamed to `mkSubAtSN`, because
-- the original `Work.WilC5.mkSubAt` clashes with the identically named definition of
-- `Submission/Work/WilC5/S4ExpG/Glue.lean` (which the §4 Lemma-4.4 assembly needs through
-- `ExistsStepSeq`/`StepSeqDecomp`/`DclExtensionCast`).

/-
  WilC5 — `Work.WilC5.StepNoNew`: vdDMM Lemma 4.2 (the "no new value" step of §4), as a single
  extension step of the §4 iteration.

  The situation is that of `Work.WilC5.S4Pair` (`S4Setup.lean`): `p = (B, τ)` is a partial extension
  of the §4 iteration — `B ≤ K` is a `Dcl`-closed `LRc`-substructure of the `rexp`-reduct of a model
  `K ⊨ TE`, closed under the definable logarithm, and `τ : B → L` is an `LRc`-embedding into
  `L ⊨ TE` commuting with the definable logarithm — and `x ∉ B` is an element of `K` such that
  *every* element of the definable closure `F = Dcl (B ∪ {x})` has the value of an element of `B`
  (`v(F^×) = v(B^×)`, the hypothesis of vdDMM Lemma 4.2).  The claim is that `p` extends strictly
  to a partial extension whose domain contains `x`.

  The proof has three parts.

  * **The domain.**  `F = Dcl (B ∪ {x})` is `Dcl`-closed, so it is the carrier of an
    `LRc`-substructure `S ≤ K` which is a model of `TR` (Tarski–Vaught:
    `Work.WilC5.model_TR_of_dcl_closed`).  The `Dcl`-API of `WilC2`/`WilC4` is stated at the
    `LRc`-structure synthesized from the canonical instance bundle, whereas the §4 layer fixes the
    `rexp`-reduct `Work.WilC5.reductStruct`; `model_TR_of_dclClosed_reduct` below transports the
    conclusion across the (explicitly proved) equality of the two.

  * **The embedding.**  `B ⊨ TR` and `L` is `κ`-saturated with `κ > |K| ≥ |B|`, so model
    completeness of `TR` (`Work.WilC5.hasExtProp_of_modelComplete`) extends `τ` to an `LRc`-embedding
    `g : K → L`; its restriction to `S` is the required extension (elementary on `S`, since
    `S ⊨ TR`).

  * **Log-closure and log-preservation.**  The value-theoretic content of vdDMM Lemma 4.2.  For
    `0 < w ∈ F` the hypothesis gives `b ∈ B` with `v(w) = v(b)`, so `w = (c_r · b)(1 + ε)` with
    `c_r · b ∈ B` and `ε ∈ F` infinitesimal (`Work.WilC5.decomposition_of_same_value`: the residue
    field of a model of `TR` is `ℝ`).  Then

      `log w = log (c_r b) + log (1 + ε)`,

    where `log (c_r b) ∈ B` (log-closure of `B`) and, for `|2ε| ≤ 1`, `log (1+ε)` is *the unique* `u`
    with `rexp u = 1 + ε` (`Work.WilC5.logFun_one_add_rexp`, `Work.WilC5.logFun_eq_of_rexp_eq`), so
    it is definable from the parameters `w`, `c_r b` — in particular it lies in `F`.  Hence `F` is
    log-closed.  The same identity on the `L`-side, with `g` commuting with the `rexp` symbol,
    gives `σ'(log w) = log (σ' w)`.
-/
import Mathlib
import Submission.Work.WilC5.S4StepDefs
import Submission.Work.WilC5.LRcSatOfLEcSat
import Submission.Work.WilC5.decomposition_of_same_value
import Submission.Work.WilC5.logFun_one_add_rexp
import Submission.Work.WilC5.logFun_eq_of_rexp_eq
import Submission.Work.WilC5.logFun_mul
import Submission.Work.WilC5.model_TR_of_dcl_closed
import Submission.Work.WilC5.hasExtProp_of_modelComplete
import Submission.Work.WilC5.dclClosed_substructure
import Submission.Work.WilC2.meetsDefinable_dcl
import Submission.Work.WilC2.dcl_exchange
import Submission.Work.WilC2.Square

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-! ## 1. The canonical `LRc`-structure of a model of `TR`

The `Dcl`-API of `WilC2`/`WilC4` (idempotence, `definable_of_param_formula`, …) is stated at the
`LRc`-structure synthesized by Mathlib from the canonical ring/`rexp`/constants data, whereas the
§4 layer of this area fixes the `rexp`-reduct `Work.WilC5.reductStruct` as the `LRc`-structure of a
model of `TE`.  `canonStruct` names the former, so that the two can be related by an explicit
equality. -/

/-- The `LRc`-structure synthesized from the canonical instance bundle. -/
@[instance_reducible]
def canonStruct (M : Type) [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M] : LRc.Structure M :=
  LR.withConstantsStructure ℝ

/-- A substructure at an explicitly given `LRc`-structure, from its carrier. -/
def mkSubAtSN (M : Type) (i : LRc.Structure M) (S : Set M)
    (hmem : ∀ {n : ℕ} (f : LRc.Functions n) (x : Fin n → M),
      (∀ k, x k ∈ S) → @Structure.funMap LRc M i n f x ∈ S) :
    @FirstOrder.Language.Substructure LRc M i := by
  letI : LRc.Structure M := i
  exact ⟨S, fun {n} f x hx => hmem f x hx⟩

@[simp] theorem mkSubAtSN_coe {M : Type} {i : LRc.Structure M} {S : Set M} {hmem} :
    (mkSubAtSN M i S hmem : Set M) = S := rfl

/-- **A `Dcl`-closed substructure of a model of `TR` is a model of `TR`, at the `rexp`-reduct
`Work.WilC5.reductStruct`.**  The transport between the two `LRc`-structures is the hypothesis
`hstruct`. -/
theorem model_TR_of_dclClosed_reduct {K : Type} [LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [Ring.CompatibleRing K]
    (hstruct : (Work.WilC5.reductStruct K : LRc.Structure K) = canonStruct K)
    (hOM : OMinModels)
    (hKTR : @Theory.Model LRc K (Work.WilC5.reductStruct K) TR)
    (S : @LRc.Substructure K (Work.WilC5.reductStruct K))
    (hS : @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) (S : Set K) ⊆ (S : Set K)) :
    @Theory.Model LRc ↥S (@FirstOrder.Language.Substructure.inducedStructure LRc K
      (Work.WilC5.reductStruct K) S) TR := by
  have hmem : ∀ {n : ℕ} (f : LRc.Functions n) (x : Fin n → K),
      (∀ k, x k ∈ (S : Set K)) → @Structure.funMap LRc K (canonStruct K) n f x ∈ (S : Set K) := by
    intro n f x hx
    have h1 : @Structure.funMap LRc K (canonStruct K) n f x =
        @Structure.funMap LRc K (Work.WilC5.reductStruct K) n f x :=
      (congrArg (fun i => @Structure.funMap LRc K i n f x) hstruct).symm
    rw [h1]
    exact S.fun_mem f x hx
  let Scan : @LRc.Substructure K (canonStruct K) := mkSubAtSN K (canonStruct K) (S : Set K) hmem
  have hScoe : (Scan : Set K) = (S : Set K) := rfl
  have hScan_dcl : @Work.WilC2.Dcl K (canonStruct K) (Scan : Set K) ⊆ (Scan : Set K) := by
    intro z hz
    rw [hScoe] at hz ⊢
    have h1 : @Work.WilC2.Dcl K (canonStruct K) (S : Set K) =
        @Work.WilC2.Dcl K (Work.WilC5.reductStruct K) (S : Set K) :=
      (congrArg (fun i => @Work.WilC2.Dcl K i (S : Set K)) hstruct).symm
    rw [h1] at hz
    exact hS hz
  have hKTcan : @Theory.Model LRc K (canonStruct K) TR := by rw [← hstruct]; exact hKTR
  have hScanTR : @Theory.Model LRc ↥Scan
      (@FirstOrder.Language.Substructure.inducedStructure LRc K (canonStruct K) Scan) TR :=
    @model_TR_of_dcl_closed hOM K _ _ _ _ _ _ hKTcan Scan hScan_dcl
  have hinst : (@FirstOrder.Language.Substructure.inducedStructure LRc K (canonStruct K) Scan)
      = (@FirstOrder.Language.Substructure.inducedStructure LRc K
          (Work.WilC5.reductStruct K) S) := by
    ext n f x
    · exact (congrArg (fun i => @Structure.funMap LRc K i n f
        (fun i => ((x i : ↥Scan) : K))) hstruct).symm
    · nomatch f
  exact hinst ▸ hScanTR

/-! ## 2. Auxiliary lemmas about the definable logarithm and the definable closure -/

/-- `logFun y = 0` for `y` in the non-positive part of the definable order. -/
theorem logFun_eq_zero_of_not_pos {M : Type} [LEc.Structure M] (hM : M ⊨ TE) {y : M}
    (hy : ¬ (leE zeroE y ∧ ¬ leE y zeroE)) : logFun y = zeroE := by
  have hspec : logDefSet y (logFun y) := logFun_spec_of_model hM y
  rw [logDefSet] at hspec
  rcases hspec with ⟨hp, _⟩ | ⟨_, he⟩
  · exact absurd hp hy
  · exact expE_injective_of_model hM _ _ (by rw [he, expE_zero_of_model hM])

/-- `SameArch x 0` forces `x = 0`. -/
theorem sameArch_eq_zero_right {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    {x : M} (h : SameArch x 0) : x = 0 := by
  rcases h with ⟨N, h1, _⟩
  have : |x| ≤ 0 := by
    calc |x| ≤ ((N : M) + 1) * |(0 : M)| := h1
      _ = 0 := by rw [abs_zero, mul_zero]
  exact abs_eq_zero.mp (le_antisymm this (abs_nonneg x))

/-- The `LRc`-term naming `1`, in an arbitrary context. -/
def oneTerm {α : Type} : LRc.Term α :=
  Term.func (ringSymL Ring.oneFunc) Fin.elim0

@[simp] theorem realize_oneTerm {M : Type} [LRc.Structure M] {α : Type} (w : α → M) :
    Term.realize w (oneTerm (α := α)) = oneEL := by
  rw [oneTerm, Term.realize_func, oneEL]
  congr 1
  exact fin0_funext _ _


/-- The `LRc`-formula `v = ρ * (1 + δ)`, with the parameters `(v, ρ)` and the one free variable
`δ`. -/
def eqMulForm : LRc.Formula (Fin 2 ⊕ Fin 1) :=
  Term.bdEqual (Term.var (Sum.inl (Sum.inl (0 : Fin 2))))
    (tMulL (Term.var (Sum.inl (Sum.inl (1 : Fin 2))))
      (tAddL (oneTerm (α := (Fin 2 ⊕ Fin 1) ⊕ Fin 0))
        (Term.var (Sum.inl (Sum.inr (0 : Fin 1))))))

theorem eqMulForm_realize {M : Type} [LRc.Structure M] (c : Fin 2 → M) (v : Fin 1 → M) :
    @BoundedFormula.Realize LRc M _ (Fin 2 ⊕ Fin 1) 0 eqMulForm (Sum.elim c v)
      (fun i : Fin 0 => i.elim0) ↔
      c 0 = mulEL (c 1) (addEL oneEL (v 0)) := by
  rw [eqMulForm, BoundedFormula.realize_bdEqual]
  simp only [Term.realize_var, Sum.elim_inl, Sum.elim_inr, realize_tMulL, realize_tAddL,
    realize_oneTerm]

/-- The `rexp` symbol of `LRc`. -/
def rexpSymL : LRc.Functions 1 := Sum.inl (Sum.inr rexpFunc.rexp)

/-- The `LRc`-formula `rexp u = 1 + ε`, with the parameter `ε` and the one free variable `u`. -/
def rexpOneAddForm : LRc.Formula (Fin 1 ⊕ Fin 1) :=
  Term.bdEqual (Term.func rexpSymL ![Term.var (Sum.inl (Sum.inr (0 : Fin 1)))])
    (tAddL (oneTerm (α := (Fin 1 ⊕ Fin 1) ⊕ Fin 0))
      (Term.var (Sum.inl (Sum.inl (0 : Fin 1)))))

theorem rexpOneAddForm_realize {M : Type} [LRc.Structure M] (c : Fin 1 → M) (v : Fin 1 → M) :
    @BoundedFormula.Realize LRc M _ (Fin 1 ⊕ Fin 1) 0 rexpOneAddForm (Sum.elim c v)
      (fun i : Fin 0 => i.elim0) ↔
      @Structure.funMap LRc M _ 1 rexpSymL ![v 0] = addEL oneEL (c 0) := by
  rw [rexpOneAddForm, BoundedFormula.realize_bdEqual]
  have hkey : (Term.realize (Sum.elim (Sum.elim c v) (fun i : Fin 0 => i.elim0))
      (Term.func rexpSymL ![Term.var (Sum.inl (Sum.inr (0 : Fin 1)))])) =
      @Structure.funMap LRc M _ 1 rexpSymL ![v 0] := by
    rw [Term.realize_func]
    congr 1
    funext i
    fin_cases i
    simp [Term.realize_var]
  rw [hkey]
  simp only [Term.realize_var, Sum.elim_inl, Sum.elim_inr, realize_tAddL, realize_oneTerm]

/-- The `LRc`-formula `absLeOne v`, i.e. `∃z, z*z = 1 - v` and `∃z, z*z = 1 + v`
(in an ordered field this says `|v| ≤ 1`). -/
def absLeFormL {α : Type} (t : LRc.Term (α ⊕ Fin 0)) : LRc.Formula α :=
  sqFormL (tSubL (oneTerm (α := α ⊕ Fin 0)) t) ⊓
    sqFormL (tAddL (oneTerm (α := α ⊕ Fin 0)) t)

theorem absLeFormL_realize {M : Type} [LRc.Structure M] {α : Type} (t : LRc.Term (α ⊕ Fin 0))
    (v : α → M) :
    (absLeFormL t).Realize v ↔
      (∃ z : M, mulEL z z
        = subEL oneEL (Term.realize (Sum.elim v (fun i : Fin 0 => i.elim0)) t)) ∧
        (∃ z : M, mulEL z z
          = addEL oneEL (Term.realize (Sum.elim v (fun i : Fin 0 => i.elim0)) t)) := by
  rw [formulaRealize_iff_bounded, absLeFormL, BoundedFormula.realize_inf, sqFormL_realize,
    sqFormL_realize]
  simp only [realize_tSubL, realize_tAddL, realize_oneTerm]

/-- The `LRc`-term naming `0`. -/
def zeroTerm {α : Type} : LRc.Term α :=
  Term.func (ringSymL Ring.zeroFunc) Fin.elim0

@[simp] theorem realize_zeroTerm {M : Type} [LRc.Structure M] {α : Type} (w : α → M) :
    Term.realize w (zeroTerm (α := α)) = zeroEL := by
  rw [zeroTerm, Term.realize_func, zeroEL]
  congr 1
  exact fin0_funext _ _

/-- The `LRc`-formula `0 < v`, i.e. `∃z, z*z = v` and `¬ ∃z, z*z = -v`. -/
def posFormL : LRc.Formula (Fin 1) :=
  sqFormL (tSubL (Term.var (Sum.inl (0 : Fin 1))) (zeroTerm (α := Fin 1 ⊕ Fin 0))) ⊓
    (sqFormL (tSubL (zeroTerm (α := Fin 1 ⊕ Fin 0)) (Term.var (Sum.inl (0 : Fin 1))))).not

theorem posFormL_realize {M : Type} [LRc.Structure M] (v : Fin 1 → M) :
    posFormL.Realize v ↔ leEL zeroEL (v 0) ∧ ¬ leEL (v 0) zeroEL := by
  rw [formulaRealize_iff_bounded, posFormL, BoundedFormula.realize_inf,
    BoundedFormula.realize_not, sqFormL_realize, sqFormL_realize]
  simp only [realize_tSubL, realize_zeroTerm, Term.realize_var, Sum.elim_inl, Sum.elim_inr,
    leEL, isSquareL]

/-- The two-variable `LRc`-term `1 + 1`. -/
def twoTerm {α : Type} : LRc.Term α := tAddL (oneTerm (α := α)) (oneTerm (α := α))

/-! ## 3. The `LRc`-symbols of the ring operations and their interpretation in a reduct -/

/-- The addition symbol of `LRc`. -/
def addSymL : LRc.Functions 2 := Sum.inl (Sum.inl Ring.addFunc)

/-- The multiplication symbol of `LRc`. -/
def mulSymL : LRc.Functions 2 := Sum.inl (Sum.inl Ring.mulFunc)

/-- The negation symbol of `LRc`. -/
def negSymL : LRc.Functions 1 := Sum.inl (Sum.inl Ring.negFunc)

/-- The constant `1` of `LRc`. -/
def oneSymL : LRc.Functions 0 := Sum.inl (Sum.inl Ring.oneFunc)

/-- The constant `0` of `LRc`. -/
def zeroSymL : LRc.Functions 0 := Sum.inl (Sum.inl Ring.zeroFunc)

theorem reductStruct_funMap_rexpSymL {M : Type} [LEc.Structure M] (xs : Fin 1 → M) :
    @Structure.funMap LRc M (reductStruct M) 1 rexpSymL xs = rexpFromExp (xs 0) := by
  rw [show rexpSymL = (Sum.inl (Sum.inr rexpFunc.rexp) : LRc.Functions 1) from rfl,
    reductStruct_funMap_rexp]

theorem reductStruct_addSymL {M : Type} [LEc.Structure M] (u v : M) :
    @Structure.funMap LRc M (reductStruct M) 2 addSymL ![u, v] = addE u v := by
  rw [show addSymL = (Sum.inl (Sum.inl Ring.addFunc) : LRc.Functions 2) from rfl,
    reductStruct_funMap_ring, addE]

theorem reductStruct_mulSymL {M : Type} [LEc.Structure M] (u v : M) :
    @Structure.funMap LRc M (reductStruct M) 2 mulSymL ![u, v] = mulE u v := by
  rw [show mulSymL = (Sum.inl (Sum.inl Ring.mulFunc) : LRc.Functions 2) from rfl,
    reductStruct_funMap_ring, mulE]

theorem reductStruct_negSymL {M : Type} [LEc.Structure M] (u : M) :
    @Structure.funMap LRc M (reductStruct M) 1 negSymL ![u] = negE u := by
  rw [show negSymL = (Sum.inl (Sum.inl Ring.negFunc) : LRc.Functions 1) from rfl,
    reductStruct_funMap_ring, negE]

theorem reductStruct_oneSymL (M : Type) [LEc.Structure M] :
    @Structure.funMap LRc M (reductStruct M) 0 oneSymL default = oneE := by
  rw [show oneSymL = (Sum.inl (Sum.inl Ring.oneFunc) : LRc.Functions 0) from rfl,
    reductStruct_funMap_ring, oneE]

theorem reductStruct_zeroSymL (M : Type) [LEc.Structure M] :
    @Structure.funMap LRc M (reductStruct M) 0 zeroSymL default = zeroE := by
  rw [show zeroSymL = (Sum.inl (Sum.inl Ring.zeroFunc) : LRc.Functions 0) from rfl,
    reductStruct_funMap_ring, zeroE]

/-! ## 4. An `LRc`-embedding of `rexp`-reducts commutes with the `LEc` operations -/

/-- An `LRc`-embedding of `rexp`-reducts maps the unit to the unit. -/
theorem map_oneE_reduct {K L : Type} [LEc.Structure K] [LEc.Structure L]
    (f : @Embedding LRc K L (reductStruct K) (reductStruct L)) :
    f (oneE : K) = (oneE : L) := by
  letI : LRc.Structure K := reductStruct K
  letI : LRc.Structure L := reductStruct L
  have h : f (oneEL : K) = (oneEL : L) := by
    rw [oneEL, oneEL, f.map_fun]
    congr 1
    funext i
    exact Fin.elim0 i
  exact h

/-- **`|·| ≤ 1` is preserved by an `LRc`-embedding of the `rexp`-reducts** — `absLeOne` is a
boolean combination of ring equations. -/
theorem map_absLeOne_reduct {K L : Type} [LEc.Structure K] [LEc.Structure L]
    (f : @Embedding LRc K L (reductStruct K) (reductStruct L)) {x : K}
    (h : absLeOne x) : absLeOne (f x) := by
  obtain ⟨z1, hz1⟩ := h.1
  obtain ⟨z2, hz2⟩ := h.2
  refine ⟨⟨f z1, ?_⟩, ⟨f z2, ?_⟩⟩
  · have h1 : f (mulE z1 z1) = f (subE oneE x) := congrArg f hz1
    rwa [map_mulE_reduct, map_subE_reduct, map_oneE_reduct] at h1
  · have h1 : f (mulE z2 z2) = f (addE oneE x) := congrArg f hz2
    rwa [map_mulE_reduct, map_addE_reduct, map_oneE_reduct] at h1

/-- **`absLeOne` in terms of `|·|`**, from the bridges between the language operations and the
ordered-field structure. -/
theorem absLeOne_iff_le {M : Type} [LEc.Structure M] [Field M] [LinearOrder M]
    [IsStrictOrderedRing M]
    (hadd : ∀ u v : M, addE u v = u + v) (hmul : ∀ u v : M, mulE u v = u * v)
    (hone : (oneE : M) = 1) (hzero : (zeroE : M) = 0) (hneg : ∀ u : M, negE u = -u)
    (hleE : ∀ u v : M, leE u v ↔ u ≤ v) :
    ∀ x : M, absLeOne x ↔ |x| ≤ 1 := by
  intro x
  have hsub0 : ∀ y : M, subE y zeroE = y := by
    intro y
    rw [subE, hadd y (negE zeroE), hneg zeroE, hzero, neg_zero, add_zero]
  have hSq : ∀ y : M, isSquare y ↔ 0 ≤ y := by
    intro y
    have h1 : isSquare y ↔ leE zeroE y := by
      rw [leE]
      exact (iff_of_eq (congrArg isSquare (hsub0 y))).symm
    exact h1.trans ((hleE zeroE y).trans (iff_of_eq (congrArg (fun z : M => z ≤ y) hzero)))
  have hsub1 : ∀ y : M, subE oneE y = 1 - y := by
    intro y
    rw [subE, hadd oneE (negE y), hneg y, hone, sub_eq_add_neg]
  have hadd1 : ∀ y : M, addE oneE y = 1 + y := fun y => by rw [hadd oneE y, hone]
  rw [absLeOne, hSq (subE oneE x), hSq (addE oneE x), hsub1, hadd1, abs_le]
  constructor <;> intro h <;> exact ⟨by linarith, by linarith⟩

/-- **An element defined as the unique solution of a formula with parameters in `Dcl A` lies in
`Dcl A`** (for the `LRc`-structure `i` at which `Dcl` is idempotent). -/
theorem mem_dcl_of_unique_solution {M : Type} (i : LRc.Structure M) [Field M] [LinearOrder M]
    [IsStrictOrderedRing M] [Ring.CompatibleRing M] {A : Set M} {γ : Type}
    (c : γ → M) (hc : ∀ j, c j ∈ @Work.WilC2.Dcl M i A)
    (φ : LRc.Formula (γ ⊕ Fin 1)) {u : M}
    (hu : @Formula.Realize LRc M i (γ ⊕ Fin 1) φ (Sum.elim c (fun _ => u)))
    (huniq : ∀ v : Fin 1 → M, @Formula.Realize LRc M i (γ ⊕ Fin 1) φ (Sum.elim c v) →
      v = fun _ : Fin 1 => u)
    (hidem : @Work.WilC2.Dcl M i (@Work.WilC2.Dcl M i A) = @Work.WilC2.Dcl M i A) :
    u ∈ @Work.WilC2.Dcl M i A := by
  have hdef : @Set.Definable M (@Work.WilC2.Dcl M i A) LRc i (Fin 1)
      {v : Fin 1 → M | @Formula.Realize LRc M i (γ ⊕ Fin 1) φ (Sum.elim c v)} :=
    @Work.WilC2.definable_of_param_formula LRc M i (@Work.WilC2.Dcl M i A) γ (Fin 1) c hc φ
  have hset : {v : Fin 1 → M | @Formula.Realize LRc M i (γ ⊕ Fin 1) φ (Sum.elim c v)}
      = {v : Fin 1 → M | v 0 = u} := by
    ext v
    constructor
    · intro hv
      rw [huniq v hv]
      rfl
    · intro hv
      have hv' : v = fun _ : Fin 1 => u := by
        funext j
        rw [Subsingleton.elim j 0]
        exact hv
      rw [hv']
      exact hu
  have hdef' : @Set.Definable M (@Work.WilC2.Dcl M i A) LRc i (Fin 1)
      {v : Fin 1 → M | v 0 = u} := hset ▸ hdef
  have h1 : u ∈ @Work.WilC2.Dcl M i (@Work.WilC2.Dcl M i A) := by
    rw [Work.WilC2.mem_dcl]
    exact hdef'
  rwa [hidem] at h1

end Work.WilC5
