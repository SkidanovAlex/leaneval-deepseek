/-
  WilC4 : area C4 of `annals_wilkies_conjecture` (Wilkie's valuation inequality for `TR`).

  This module fixes the vocabulary of the area.  `WilC4` proves
  `C4_valuation_inequality` (SPEC `WilkiesDesign.CG.C4_valuation_inequality`):
  `OMinModels -> PolyBoundedRExp -> ValIneq`.

  The frozen statement `ValIneq` speaks about a model `M ⊨ TR` (`TR = Th(ℝ_rexp, all reals)`),
  an *elementary* substructure `S ≼ M`, generators `a : Fin k → M`, and elements
  `b : Fin m → M` that are definable from `S ∪ range a` with values that are ℤ-independent
  modulo the values of `S`.  Its conclusion is `m ≤ k`.

  Everything below is phrased so that it can be used for arbitrary *bases*: an elementary
  substructure is only used through the facts that it is `dcl`-closed (`Dcl S ∅ = S`) and that
  it is closed under the field operations.  The intermediate bases in the induction of
  `WilC4.Induction` are definable closures of elementary substructures; those are `dcl`-closed
  but are *not* known to be elementary substructures, so no lemma below requires elementarity
  of the base.

  ## Conventions of the area

  * `IsUnitVal` (frozen, SPEC) : `x` is a *unit* iff `1/(N+1) ≤ |x| ≤ N+1` for some natural
    `N`.  These are exactly the elements of the "Archimedean class of `1`", i.e. the elements
    with value `0`.
  * `ValLE x y`  : `|x| ≤ N |y|`, i.e. `ν x ≥ ν y`.
  * `ValEq x y`  : same Archimedean class: `ValEq 1 x ↔ IsUnitVal x`.
  * `zmono b q`  : the integer monomial `∏ j, b j ^ (q j)`.
  * `ValOf V y`  : the value of `y` is the value of some nonzero element of `V`.
  * `ValDep S b` : a nontrivial integer combination of the `b j` has value in `Γ S`
    (`Γ S := {ν c : c ∈ S, c ≠ 0}`).  `ValIndep S b` is its negation, in the exact shape used
    by the frozen `ValIneq`.
  * `ValSpans S V r` : the values of the elements of `V` are spanned, over `Γ S`, by the values
    of `r` elements (`ℚ`-linearly; the definition keeps the denominators explicit so that no
    divisibility of `Γ S` is ever needed).
  * `Dcl S A` : the set of elements definable from `S ∪ A` (each one individually, by a formula
    with parameters in `S ∪ A`) -- this is the `b j ∈ dcl(S ∪ range a)` of `ValIneq`.
-/
import Submission.Work.Wilkies.CG.Spec

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC4
open WilkiesDesign WilkiesDesign.CG

/-! ## 1. The value vocabulary of an ordered field -/

section Val

variable {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]

/-- `ν x ≥ ν y`, i.e. `x` is dominated by `y`: `|x| ≤ N |y|` for a natural number `N`.
(`ν 0` is `+∞`, so this holds for `x = 0` and any `y`.) -/
def ValLE (x y : M) : Prop := ∃ N : ℕ, |x| ≤ (N : M) * |y|

/-- `x` and `y` have the same value: they are *comparable*, i.e. in the same Archimedean
class. -/
def ValEq (x y : M) : Prop := ∃ N : ℕ, 0 < N ∧ (N : M)⁻¹ * |y| ≤ |x| ∧ |x| ≤ (N : M) * |y|

/-- The integer monomial `∏ j, b j ^ (q j)`. -/
def zmono {m : ℕ} (b : Fin m → M) (q : Fin m → ℤ) : M := ∏ j, b j ^ (q j)

/-- The value of `y` occurs in `V`: `y` is comparable to some nonzero element of `V`.
(This is the value set `{ν c : c ∈ V, c ≠ 0}` of `V`, used as the "base" of a value-rank
statement.) -/
def ValOf (V : Set M) (y : M) : Prop := ∃ c ∈ V, c ≠ 0 ∧ ValEq y c

/-- A nontrivial integer combination of the `b j` has value in `Γ S`: some `c ∈ S \ {0}` makes
`c * ∏ b j ^ (q j)` a unit. -/
def ValDep (S : Set M) {m : ℕ} (b : Fin m → M) : Prop :=
  ∃ q : Fin m → ℤ, q ≠ 0 ∧ ∃ c ∈ S, c ≠ 0 ∧ IsUnitVal (c * zmono b q)

/-- The values of `b` are ℤ-independent modulo `Γ S`.  This is the *verbatim* shape of the
third hypothesis of the frozen `ValIneq`. -/
def ValIndep (S : Set M) {m : ℕ} (b : Fin m → M) : Prop :=
  ∀ q : Fin m → ℤ, (∃ c ∈ S, c ≠ 0 ∧ IsUnitVal (c * zmono b q)) → q = 0

/-- The values of the elements of `V` are spanned over `Γ S` by the values of `r` elements
`x 0, …, x (r-1)`: for every `y` whose value occurs in `V` there are `N ≠ 0`, an integer vector
`q` and `c ∈ S \ {0}` with `c * y^N / ∏ (x i)^(q i)` a unit.

With `Γ S` divisible this says `ν y ∈ ℚ·ν(x 0) + … + ℚ·ν(x (r-1)) + Γ S`; the definition keeps
the denominators explicit so that the induction of `WilC4.Induction` never needs divisibility. -/
def ValSpans (S V : Set M) (r : ℕ) : Prop :=
  ∃ x : Fin r → M, ∀ y : M, y ≠ 0 → ValOf V y →
    ∃ N : ℕ, N ≠ 0 ∧ ∃ q : Fin r → ℤ, ∃ c ∈ S, c ≠ 0 ∧
      IsUnitVal (c * y ^ N / zmono x q)

/-- `S` is a *value base*: the set of values `Γ S = {ν c : c ∈ S, c ≠ 0}` is a subgroup of the
value group.  Concretely: `1 ∈ S` and `S` is closed under multiplication and under inverses.
Every base occurring in the proof of `ValIneq` is a value base: the carrier of an elementary
substructure, and every definable closure `Dcl T A`. -/
def IsValBase (S : Set M) : Prop :=
  (1 : M) ∈ S ∧ (∀ x ∈ S, x ≠ 0 → x⁻¹ ∈ S) ∧ (∀ x ∈ S, ∀ y ∈ S, x * y ∈ S)

/-- `t` is the positive `q`-th power of `x`, in the `LRc`-definable form `t^n = x^p` (with
`q = p/n`) plus positivity.  For `x > 0` this holds exactly for `t = x^q`.  The language `LRc`
has no symbol for real powers, so a statement about `x^q` has to be written with this relation
before it can be transferred between models. -/
def IsRpow (x : M) (q : ℚ) (t : M) : Prop :=
  ∃ (p : ℤ) (n : ℕ), 0 < n ∧ q = (p : ℚ) / (n : ℚ) ∧ t ^ n = x ^ p ∧
    (t = 0 ∨ ∃ w : M, w ≠ 0 ∧ w ^ 2 = t)

end Val

/-! ## 2. Definable closure -/

section Dcl

open FirstOrder FirstOrder.Language

variable {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] [Ring.CompatibleRing M]
  [rexpL.Structure M] [(constantsOn ℝ).Structure M]

/-- `x` is definable from the parameter set `S ∪ A`: the singleton `{x}` is `LRc`-definable with
parameters in `S ∪ A`.  (`Set.definable_iff_exists_formula_sum` turns this into a formula with
parameters; the singleton formulation is exactly what the frozen `ValIneq` uses.) -/
def DefinableElt (S A : Set M) (x : M) : Prop :=
  (S ∪ A).Definable LRc {fun _ : Fin 1 => x}

/-- The definable closure of `S ∪ A`. -/
def Dcl (S A : Set M) : Set M := {x | DefinableElt S A x}

end Dcl

/-! ## 3. The two research inputs, as named statements

  These two `def`s are *interfaces*, not results: they name the two mathematical inputs of C4
  that are still to be proved (`TransferOfPB` is the transfer of the hypothesis `hPB` to every
  model of `TR`, `PreparationStep` is the van den Dries–Speissegger preparation step in the
  power-bounded case).  `WilC4/Assembly.lean` derives the frozen `ValIneq` from them plus the
  induction; that is why they are named here, and their docstrings record the exact content that
  a prover must deliver. -/

section Inputs

open FirstOrder FirstOrder.Language

/-- **The model form of `PolyBoundedRExp`** (the transfer step of the C4 plan): in a model `M`
of `TR`, every `M`-definable family of functions `x ↦ y` (parameters `c`) is, for large `x`,
either eventually `0` or asymptotic to a monomial `α · x^q`; the finite set `Qs` of exponents
depends on the family but *not* on its parameters.

`Qs` is quantified inside the `∀ Y`: a single finite set of exponents cannot serve all definable
families at once (`x ↦ x^n` needs `q = n`), but for a fixed formula it serves all parameter
values, which is exactly what the transfer of the frozen `PolyBoundedRExp` gives. -/
def ModelPB (M : Type) [Field M] [LinearOrder M]
    [IsStrictOrderedRing M] [Ring.CompatibleRing M] [rexpL.Structure M]
    [(constantsOn ℝ).Structure M] : Prop :=
  ∀ (k : ℕ) (Y : Set (Fin (k + 2) → M)), (Set.univ : Set M).Definable LRc Y →
    (∀ (c : Fin k → M) (x y y' : M), Fin.cons x (Fin.cons y c) ∈ Y →
        Fin.cons x (Fin.cons y' c) ∈ Y → y = y') →
    ∃ Qs : Finset ℚ, Qs.Nonempty ∧ ∀ c : Fin k → M,
      (∃ R : M, 0 < R ∧ ∀ x y : M, R ≤ x → Fin.cons x (Fin.cons y c) ∈ Y → y = 0) ∨
      ∃ q ∈ Qs, ∃ α : M, α ≠ 0 ∧ ∀ ε : M, 0 < ε → ∃ R : M, 0 < R ∧ ∀ x y : M, R ≤ x →
        Fin.cons x (Fin.cons y c) ∈ Y →
          ∃ t : M, IsRpow x q t ∧ |y - α * t| ≤ ε * |t|

/-- `TransferOfPB`: the asymptotic statement is *first-order*, so once it is available over `ℝ`
it holds verbatim in every model of `TR`.  This is "step 1" of the C4 plan (`DESIGN.md` §1 C4).
Over `ℝ` the input is the frozen `hPB` together with "every `LRc`-definable set of `ℝⁿ` is
`RExpExist`", which the frozen `hR` gives (`hC0` in the transfer lemma). -/
def TransferOfPB : Prop :=
  ∀ (M : Type) [Field M] [LinearOrder M] [IsStrictOrderedRing M] [Ring.CompatibleRing M]
    [rexpL.Structure M] [(constantsOn ℝ).Structure M], M ⊨ TR → ModelPB M

/-- **The preparation step of van den Dries–Speissegger** in the shape C4 uses it: for a
`dcl`-closed base `T` and `a ∈ M`, the values occurring in `Dcl T {a}` are generated, over
`Γ T`, by the value of a single element `δ`.  (Case `a ∈ T` is trivial, with `δ = 1`.) -/
def PreparationStep : Prop :=
  ∀ (M : Type) [Field M] [LinearOrder M] [IsStrictOrderedRing M] [Ring.CompatibleRing M]
    [rexpL.Structure M] [(constantsOn ℝ).Structure M], M ⊨ TR →
    ∀ (T : Set M), (∀ x : M, DefinableElt T ∅ x ↔ x ∈ T) →
    ∀ a : M, ∃ δ : M, δ ≠ 0 ∧ ValSpans T (Dcl T {a}) 1

end Inputs

end Work.WilC4
