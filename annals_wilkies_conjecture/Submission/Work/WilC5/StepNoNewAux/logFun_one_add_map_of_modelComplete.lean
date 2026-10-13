/-
  WilC5 / StepNoNewAux — `logFun_one_add_map_of_modelComplete`.

  **The one-point step of vdDMM Lemma 4.2: an `LRc`-embedding commutes with the definable
  logarithm of `1 + ε` near `1`.**

  Situation: `K, L ⊨ TE` (models of `Th(ℝ, exp)`), `S ≤ K` is an `LRc`-substructure of the
  `rexp`-reduct which is a model of `TR` (`hS`, used only to make the setting well-formed here),
  `g : S ↪[LRc] L` is an `LRc`-embedding into the `rexp`-reduct of `L`, and `δ ∈ S` satisfies
  `|2δ| ≤ 1`.  If `logFun (1+δ) ∈ S`, then

      `g (logFun (1+δ)) = logFun (1 + g δ)`.

  The mathematical content is that `log(1+ε)` for `|2ε| ≤ 1` is *definable in the `rexp`
  language*: it is the unique `u` with `rexpFromExp u = 1+ε` (`Work.WilC5.logFun_one_add_rexp`
  shows that `u = logFun (1+ε)` is such a `u`, and `Work.WilC5.logFun_eq_of_rexp_eq` that it is
  the only one, in any model of `TE`).  Consequently the *equation* `rexp u = 1 + ε`, which is an
  atomic `LRc`-statement, holds of `(ε, logFun (1+ε))`, and every `LRc`-embedding preserves
  equations.  Since `L ⊨ TE`, the image `g (logFun (1+ε))` is therefore the (unique) `u` with
  `rexpFromExp u = 1 + g ε`, i.e. `logFun (1 + g ε)`.

  Formally the argument is carried out with the `LRc`-symbols

  * `rexpSymL` — the `rexp` symbol of `LRc`,
  * `addSymL`, `oneSymL` — the ring symbols `+` and `1` of `LRc`,

  together with the three bridges

  * `realize_*SymL_reduct` — in the `rexp`-reduct `reductStruct M` of an `LEc`-structure, the
    `LRc`-interpretation of these symbols is `rexpFromExp`, `addE`, `oneE` (`Bridge.lean`);
  * `coe_funMap_substructure` — the interpretation of a symbol in a substructure `S ≤ K`
    coerce to the interpretation in `K` (`Substructure.inducedStructure` is `rfl`-transparent for
    the coercion);
  * `map_*SymL` — an `LRc`-embedding `g` commutes with the interpretation of a symbol
    (`HomClass.map_fun`).

  The hypothesis `hMCr` (`TR` model complete) is not needed by this argument — the preservation
  used is that of *atomic* `LRc`-statements by an embedding, not elementarity; it is kept in the
  statement for the caller's convenience.
-/
import Mathlib
import Submission.Work.WilC5.S4StepDefs
import Submission.Work.WilC5.logFun_one_add_rexp
import Submission.Work.WilC5.logFun_eq_of_rexp_eq
import Submission.Work.WilC5.model_TR_of_dcl_closed
import Submission.Work.WilC5.hasExtProp_of_modelComplete

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section
open Classical

namespace Work.WilC5.StepNoNewAux

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-! ## 1. The `LRc`-symbols

`LRc = (ring ⊕ rexpL)[[ℝ]]`, so a ring symbol `f` is `Sum.inl (Sum.inl f)`, the `rexp` symbol is
`Sum.inl (Sum.inr rexp)`, and a real constant is `Sum.inr c`.  These `def`s are kept *unfolded*
only through the lemmas below: unfolding them inside a goal leaves an ill-typed term (the
projection `LRc.Functions` of the `def rexpL` is not visible at instance transparency), so every
statement about them is phrased with the symbol and rewritten with a `rfl`-step first. -/

/-- The `rexp`-symbol of `LRc`. -/
def rexpSymL : WilkiesDesign.CG.LRc.Functions 1 := Sum.inl (Sum.inr rexpFunc.rexp)

/-- The addition symbol of `LRc`. -/
def addSymL : WilkiesDesign.CG.LRc.Functions 2 := Sum.inl (Sum.inl Ring.addFunc)

/-- The constant `1` of `LRc`. -/
def oneSymL : WilkiesDesign.CG.LRc.Functions 0 := Sum.inl (Sum.inl Ring.oneFunc)

/-! ## 2. The interpretation of the symbols in the `rexp`-reduct of an `LEc`-structure -/

/-- In the `rexp`-reduct `reductStruct M`, the `rexp`-symbol is interpreted by `rexpFromExp`. -/
theorem realize_rexpSymL_reduct {M : Type} [WilkiesDesign.CG.LEc.Structure M] (xs : Fin 1 → M) :
    @Structure.funMap WilkiesDesign.CG.LRc M (Work.WilC5.reductStruct M) 1 rexpSymL xs =
      Work.WilC5.rexpFromExp (xs 0) := by
  rw [show rexpSymL =
      (Sum.inl (Sum.inr WilkiesDesign.CG.rexpFunc.rexp) :
        WilkiesDesign.CG.LRc.Functions 1) from rfl,
    Work.WilC5.reductStruct_funMap_rexp]

/-- In the `rexp`-reduct `reductStruct M`, the addition symbol is interpreted by `addE`. -/
theorem realize_addSymL_reduct {M : Type} [WilkiesDesign.CG.LEc.Structure M] (xs : Fin 2 → M) :
    @Structure.funMap WilkiesDesign.CG.LRc M (Work.WilC5.reductStruct M) 2 addSymL xs =
      Work.WilC5.addE (xs 0) (xs 1) := by
  rw [show addSymL = (Sum.inl (Sum.inl Ring.addFunc) : WilkiesDesign.CG.LRc.Functions 2) from rfl,
    Work.WilC5.reductStruct_funMap_ring]
  rw [show xs = ![xs 0, xs 1] from funext (fun i => by fin_cases i <;> rfl)]
  rfl

/-- In the `rexp`-reduct `reductStruct M`, the constant `1` is interpreted by `oneE`. -/
theorem realize_oneSymL_reduct {M : Type} [WilkiesDesign.CG.LEc.Structure M] (xs : Fin 0 → M) :
    @Structure.funMap WilkiesDesign.CG.LRc M (Work.WilC5.reductStruct M) 0 oneSymL xs =
      Work.WilC5.oneE := by
  rw [show oneSymL = (Sum.inl (Sum.inl Ring.oneFunc) : WilkiesDesign.CG.LRc.Functions 0) from rfl,
    Work.WilC5.reductStruct_funMap_ring]
  rw [Subsingleton.elim xs default]
  rfl

/-! ## 3. Substructures: the interpretation coerces to the ambient one -/

/-- **A substructure's interpretation of a symbol is the ambient one.**  For `S ≤ K`, the value
in `K` of the interpretation of `f` in `↥S` is the interpretation of `f` in `K` applied to the
coerced arguments (`Substructure.inducedStructure`). -/
theorem coe_funMap_substructure {K : Type} [WilkiesDesign.CG.LEc.Structure K]
    (S : WilkiesDesign.CG.LRc.Substructure K) {n : ℕ} (f : WilkiesDesign.CG.LRc.Functions n)
    (xs : Fin n → ↥S) :
    ((@Structure.funMap WilkiesDesign.CG.LRc ↥S _ n f xs : ↥S) : K) =
      @Structure.funMap WilkiesDesign.CG.LRc K _ n f (fun i => (xs i : K)) := rfl

/-! ## 4. The interpretation of the symbols, for an `LEc`-structure -/

/-- The `rexp`-symbol interpreted in an `LEc`-structure is `rexpFromExp`. -/
theorem realize_rexpSymL {M : Type} [WilkiesDesign.CG.LEc.Structure M] (v : M) :
    @Structure.funMap WilkiesDesign.CG.LRc M _ 1 rexpSymL (fun _ : Fin 1 => v) =
      Work.WilC5.rexpFromExp v :=
  realize_rexpSymL_reduct (fun _ : Fin 1 => v)

/-- The addition symbol interpreted in an `LEc`-structure is `addE`. -/
theorem realize_addSymL {M : Type} [WilkiesDesign.CG.LEc.Structure M] (a b : M) :
    @Structure.funMap WilkiesDesign.CG.LRc M _ 2 addSymL ![a, b] = Work.WilC5.addE a b := by
  rw [realize_addSymL_reduct]
  simp

/-- The constant `1` interpreted in an `LEc`-structure is `oneE`. -/
theorem realize_oneSymL {M : Type} [WilkiesDesign.CG.LEc.Structure M] :
    @Structure.funMap WilkiesDesign.CG.LRc M _ 0 oneSymL default = Work.WilC5.oneE :=
  realize_oneSymL_reduct (fun i : Fin 0 => Fin.elim0 i)

/-! ## 5. The interpretation of a symbol in a substructure, explicitly -/

/-- The interpretation of `rexp` in a substructure `↥S`, coerced to `K`. -/
theorem coe_rexpSymL {K : Type} [WilkiesDesign.CG.LEc.Structure K]
    (S : WilkiesDesign.CG.LRc.Substructure K) (u : ↥S) :
    ((@Structure.funMap WilkiesDesign.CG.LRc ↥S _ 1 rexpSymL (fun _ : Fin 1 => u) : ↥S) : K) =
      Work.WilC5.rexpFromExp (u : K) := by
  rw [coe_funMap_substructure]
  exact realize_rexpSymL_reduct (fun _ : Fin 1 => (u : K))

/-- The interpretation of `+` in a substructure `↥S`, coerced to `K`. -/
theorem coe_addSymL {K : Type} [WilkiesDesign.CG.LEc.Structure K]
    (S : WilkiesDesign.CG.LRc.Substructure K) (a b : ↥S) :
    ((@Structure.funMap WilkiesDesign.CG.LRc ↥S _ 2 addSymL ![a, b] : ↥S) : K) =
      Work.WilC5.addE (a : K) (b : K) := by
  rw [coe_funMap_substructure]
  rw [realize_addSymL_reduct]
  simp

/-- The interpretation of `1` in a substructure `↥S`, coerced to `K`. -/
theorem coe_oneSymL {K : Type} [WilkiesDesign.CG.LEc.Structure K]
    (S : WilkiesDesign.CG.LRc.Substructure K) :
    ((@Structure.funMap WilkiesDesign.CG.LRc ↥S _ 0 oneSymL default : ↥S) : K) =
      Work.WilC5.oneE := by
  rw [coe_funMap_substructure]
  exact realize_oneSymL_reduct (fun i : Fin 0 => ((default : Fin 0 → ↥S) i : K))

/-! ## 6. Embeddings commute with the interpretation of the symbols -/

/-- An `LRc`-embedding commutes with the interpretation of `rexp`. -/
theorem map_rexpSymL {K L : Type} [WilkiesDesign.CG.LEc.Structure K]
    [WilkiesDesign.CG.LEc.Structure L] (S : WilkiesDesign.CG.LRc.Substructure K)
    (g : @Embedding WilkiesDesign.CG.LRc ↥S L _ (Work.WilC5.reductStruct L)) (u : ↥S) :
    g (@Structure.funMap WilkiesDesign.CG.LRc ↥S _ 1 rexpSymL (fun _ : Fin 1 => u)) =
      @Structure.funMap WilkiesDesign.CG.LRc L _ 1 rexpSymL (fun _ : Fin 1 => g u) := by
  rw [HomClass.map_fun g rexpSymL (fun _ : Fin 1 => u)]
  congr 1

/-- An `LRc`-embedding commutes with the interpretation of `+`. -/
theorem map_addSymL {K L : Type} [WilkiesDesign.CG.LEc.Structure K]
    [WilkiesDesign.CG.LEc.Structure L] (S : WilkiesDesign.CG.LRc.Substructure K)
    (g : @Embedding WilkiesDesign.CG.LRc ↥S L _ (Work.WilC5.reductStruct L)) (a b : ↥S) :
    g (@Structure.funMap WilkiesDesign.CG.LRc ↥S _ 2 addSymL ![a, b]) =
      @Structure.funMap WilkiesDesign.CG.LRc L _ 2 addSymL ![g a, g b] := by
  rw [HomClass.map_fun g addSymL (![a, b])]
  congr 1
  funext i
  fin_cases i <;> simp

/-- An `LRc`-embedding commutes with the interpretation of `1`. -/
theorem map_oneSymL {K L : Type} [WilkiesDesign.CG.LEc.Structure K]
    [WilkiesDesign.CG.LEc.Structure L] (S : WilkiesDesign.CG.LRc.Substructure K)
    (g : @Embedding WilkiesDesign.CG.LRc ↥S L _ (Work.WilC5.reductStruct L)) :
    g (@Structure.funMap WilkiesDesign.CG.LRc ↥S _ 0 oneSymL default) =
      @Structure.funMap WilkiesDesign.CG.LRc L _ 0 oneSymL default := by
  rw [HomClass.map_fun g oneSymL default]
  congr 1
  exact Subsingleton.elim _ _

/-! ## 7. The theorem -/

theorem logFun_one_add_map_of_modelComplete
    (hMCr : WilkiesDesign.CG.ModelComplete WilkiesDesign.CG.TR)
    {K L : Type} [WilkiesDesign.CG.LEc.Structure K] [WilkiesDesign.CG.LEc.Structure L]
    (hK : FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE)
    (hL : FirstOrder.Language.Theory.Model L WilkiesDesign.CG.TE)
    (S : WilkiesDesign.CG.LRc.Substructure K)
    [hS : @FirstOrder.Language.Theory.Model WilkiesDesign.CG.LRc ↥S _ WilkiesDesign.CG.TR]
    (g : @FirstOrder.Language.Embedding WilkiesDesign.CG.LRc ↥S L _ (Work.WilC5.reductStruct L))
    (δ : ↥S)
    (hδ : Work.WilC5.absLeOne
      (Work.WilC5.mulE (Work.WilC5.addE Work.WilC5.oneE Work.WilC5.oneE) ((δ : K))))
    (hδL : Work.WilC5.absLeOne
      (Work.WilC5.mulE (Work.WilC5.addE Work.WilC5.oneE Work.WilC5.oneE) (g δ)))
    (hlog : Work.WilC5.logFun (Work.WilC5.addE Work.WilC5.oneE ((δ : K))) ∈ (S : Set K)) :
    g ⟨Work.WilC5.logFun (Work.WilC5.addE Work.WilC5.oneE ((δ : K))), hlog⟩ =
      Work.WilC5.logFun (Work.WilC5.addE Work.WilC5.oneE (g δ)) := by
  -- `u = logFun (1+δ)`, the element of `S` which `g` is applied to.
  set u : ↥S := ⟨Work.WilC5.logFun (Work.WilC5.addE Work.WilC5.oneE ((δ : K))), hlog⟩ with hu
  -- `rexp` inverts `logFun` on `[1/2, 3/2]` (in `K`, where all the ingredients live).
  have hKfac : Work.WilC5.rexpFromExp (u : K) = Work.WilC5.addE Work.WilC5.oneE ((δ : K)) := by
    rw [hu]
    exact Work.WilC5.logFun_one_add_rexp hK hδ
  -- The equation `rexp u = 1 + δ`, an atomic `LRc`-statement, holds in the substructure `↥S`.
  have hSfac : (@Structure.funMap WilkiesDesign.CG.LRc ↥S _ 1 rexpSymL (fun _ : Fin 1 => u) :
        ↥S) =
      (@Structure.funMap WilkiesDesign.CG.LRc ↥S _ 2 addSymL
        ![(@Structure.funMap WilkiesDesign.CG.LRc ↥S _ 0 oneSymL default : ↥S), δ] : ↥S) := by
    apply Subtype.ext
    rw [coe_rexpSymL, coe_addSymL, coe_oneSymL, hKfac]
  -- Hence its image under the embedding holds in `L`.
  have hLfac : (@Structure.funMap WilkiesDesign.CG.LRc L _ 1 rexpSymL (fun _ : Fin 1 => g u)) =
      (@Structure.funMap WilkiesDesign.CG.LRc L _ 2 addSymL
        ![(@Structure.funMap WilkiesDesign.CG.LRc L _ 0 oneSymL default), g δ]) := by
    rw [← map_oneSymL S g, ← map_addSymL S g, ← map_rexpSymL S g, hSfac]
  -- i.e. `rexpFromExp (g u) = 1 + g δ` in `L`.
  have hmain : Work.WilC5.rexpFromExp (g u) = Work.WilC5.addE Work.WilC5.oneE (g δ) := by
    rw [← realize_oneSymL, ← realize_addSymL, ← realize_rexpSymL]
    exact hLfac
  -- In `L ⊨ TE` (using `|2·g δ| ≤ 1`) the unique such element is `logFun (1 + g δ)`.
  exact Work.WilC5.logFun_eq_of_rexp_eq hL hδL hmain

end Work.WilC5.StepNoNewAux
