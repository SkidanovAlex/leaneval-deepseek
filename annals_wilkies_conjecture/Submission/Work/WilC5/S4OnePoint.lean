/-
  WilC5 — **the one-element step of vdDMM §4**, the residual of area C5 after the decomposition of
  Theorem 4.1 into its element-by-element iteration.

  The source proves Theorem 4.1 by the single sentence "Theorem 4.1 is now easily obtained by
  iterating lemmas (4.2), (4.3) and (4.4)": one maintains a domain `F ⊆ K` which is a model of
  `T_an` (i.e. `Dcl`-closed, in the reduced language `LRc`) and log-closed, together with a
  log-preserving embedding `σ : F → L` into a saturated `L`, and extends it past one element of `K`
  at a time.  The three lemmas are exactly the three cases of that single step.

  This file states the step (`S4OnePoint`) for the invariant

  * `Work.WilC5.S4Dom A` — `A` is `Dcl`-closed in `K` (hence, by
    `Work.WilC5.model_TR_of_dcl_closed`, a model of `TR`) and closed under the definable logarithm,
  * `Work.WilC5.LogPreserving A hA σ` — `σ` commutes with the definable logarithm,

  and provides the pieces of the iteration that are already proved:

  * `Work.WilC5.dcl_iUnion_chain` (chain unions of `Dcl`-closed sets are `Dcl`-closed),
  * `Work.WilC5.dcl_substructure_subset` and `Work.WilC5.logFun_mem_of_substructure` (the initial
    domain `F₀ ⊨ TE` of Theorem 4.1 satisfies the invariant),
  * `Work.WilC5.expE_of_logFun_preserving` (at the top of the iteration, an `LRc`-embedding of
    models of `TE` preserving `log` preserves `exp`, hence is an `LEc`-embedding).

  The Zorn assembly `S4OnePoint ⟹ S4SubTE` is `Work.WilC5.S4SubTE_of_S4OnePoint` below.
-/
import Submission.Work.WilC5.S4SubTE
import Submission.Work.WilC5.dcl_substructure_subset
import Submission.Work.WilC5.logFun_mem_of_substructure
import Submission.Work.WilC5.dcl_iUnion_chain
import Submission.Work.WilC5.expE_of_logFun_preserving
import Submission.Work.WilC5.LogStructEmbedding
import Submission.Work.WilC5.ReductEmb

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-! The `rexp`-reduct `Work.WilC5.reductStruct` is used as an instance throughout this file: the
domains of the §4 iteration are `LRc`-substructures of a model of `TE` *for the reduct structure*
(so that `Work.WilC5.reduct_model_TR` applies to them), while `exp` and the definable logarithm
come from the ambient `LEc`-structure.  Any file using the definitions below needs the same local
instance. -/
attribute [local instance] Work.WilC5.reductStruct

/-- **Log-closure of a set of parameters**: it contains the definable logarithm of each of its
positive elements (`logFun` is total, and `logFun x = 0` for `x ≤ 0`). -/
def LogClosed {K : Type} [LEc.Structure K] (A : Set K) : Prop :=
  ∀ x ∈ A, logFun x ∈ A

/-- **The invariant on a domain of the §4 iteration**: `Dcl`-closed for the `rexp` language (so,
by `Work.WilC5.model_TR_of_dcl_closed`, a model of `TR`) and closed under the definable
logarithm. -/
structure S4Dom {K : Type} [LEc.Structure K] (A : LRc.Substructure K) : Prop where
  dcl_closed : @Work.WilC2.Dcl K (reductStruct K) (A : Set K) ⊆ (A : Set K)
  log_closed : LogClosed (A : Set K)

/-- **Log-preservation of a partial embedding of the iteration**: `σ` commutes with the definable
logarithm on its domain. -/
def LogPreserving {K L : Type} [LEc.Structure K] [LEc.Structure L]
    (A : LRc.Substructure K) (hA : LogClosed (A : Set K))
    (σ : @Embedding LRc ↥A L _ (reductStruct L)) : Prop :=
  ∀ x : A, σ ⟨logFun (x : K), hA (x : K) x.2⟩ = logFun (σ x)

/-- **The one-element step of vdDMM §4** (*the residual of area C5*).

In the situation of the iteration — `K, L ⊨ TE`, `L` `κ`-saturated with `κ > |K|`, `A ≤ K` an
invariant domain with a log-preserving `LRc`-embedding `σ : A → L` — the embedding extends past any
prescribed `x ∈ K`: there is a larger invariant domain `A' ∋ x` and a log-preserving
`LRc`-embedding `σ' : A' → L` agreeing with `σ` on `A`.

This is the common conclusion of vdDMM's Lemmas 4.2, 4.3 and 4.4 (their `F = F₀(x)`,
`F = F₀(exp x)` and the fortification of Lemma 4.4 respectively); the three lemmas differ in the
hypotheses under which they produce it. -/
def S4OnePoint : Prop :=
  ∀ (K L : Type) [LEc.Structure K] [LEc.Structure L],
    K ⊨ TE → L ⊨ TE →
    ∀ (κ : Cardinal.{0}), Cardinal.mk K < κ →
    @IsSaturated LEc L _ κ →
    ∀ (A : LRc.Substructure K) (hA : S4Dom A)
      (σ : @Embedding LRc ↥A L _ (reductStruct L)),
      LogPreserving A hA.log_closed σ →
      ∀ x : K, x ∉ (A : Set K) →
        ∃ (A' : LRc.Substructure K) (hA' : S4Dom A')
          (σ' : @Embedding LRc ↥A' L _ (reductStruct L)),
          A ≤ A' ∧ (∃ a : A', (a : K) = x) ∧
            (∀ (a : A) (h : (a : K) ∈ A'), σ' ⟨(a : K), h⟩ = σ ⟨a, a.2⟩) ∧
            LogPreserving A' hA'.log_closed σ'

end Work.WilC5
