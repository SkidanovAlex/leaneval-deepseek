/-
  WilC5 — **the case split of the one-element step of vdDMM §4**.

  `Work.WilC5.S4OnePoint` says: in the situation of the iteration, extend the partial embedding past
  any prescribed `x ∈ K`.  The source splits the proof into three lemmas, which share that
  conclusion and differ in the hypotheses under which they produce it:

  * **Lemma 4.2** (no new value): the case where the values of the differences `x - a`, `a ∈ A`,
      lie in `v(A^×)`;
  * **Lemma 4.3** (adjunction of an exponential): the case `x = exp a` with `a ∈ A` — here the image
      is *prescribed*, `σ'(x) = exp (σ a)`, and the cut is computed by
      `Work.WilC5.expE_lt_iff_logFun_lt`;
  * **Lemma 4.4** (general): the remaining case, with the sequence `x_{n+1} = εₙ(log xₙ − βₙ)` and
      Claims 1–5.

  This file records the split into the two cases that can be stated without the value-group
  vocabulary of vdDMM §3 (`IsUnitVal`, `SameArch` of `Values`/`ValArith`):

  * `Work.WilC5.S4OnePoint_exp` — the case of Lemma 4.3, `x = exp a` for some `a ∈ A`; since the
    image of `x` under the extension is then forced, this is the most tractable of the cases;
  * `Work.WilC5.S4OnePoint_general` — everything else, i.e. the content of Lemmas 4.2 and 4.4.

  `Work.WilC5.S4OnePoint_of_cases` proves `S4OnePoint` from the two: the split is by classical case
  analysis on `∃ a : A, x = exp a`.  The finer split of `S4OnePoint_general` into 4.2 and 4.4 (by the
  value-group hypothesis `∀ a ∈ A, v(x - a) ∈ v(A^×)` versus its negation) needs the canonical
  `Field`/`LinearOrder` instances on `K` and `L`, available from `K ⊨ TE` through
  `Work.WilC5.reduct_model_TR` and the `tr_*` lemmas of `TRCanon.lean`; it is the next refinement.
-/
import Submission.Work.WilC5.S4OnePoint

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

attribute [local instance] Work.WilC5.reductStruct

/-- **The case `x = exp a` (`a` in the domain) of the one-element step** — vdDMM Lemma 4.3.

The extension exists and the image of `x` is determined: it must be `exp (σ a)`, whose cut over
`σ(A)` is the image of the cut of `exp a` over `A` by `Work.WilC5.expE_lt_iff_logFun_lt`. -/
def S4OnePoint_exp : Prop :=
  ∀ (K L : Type) [LEc.Structure K] [LEc.Structure L],
    K ⊨ TE → L ⊨ TE →
    ∀ (κ : Cardinal.{0}), Cardinal.mk K < κ →
    @IsSaturated LEc L _ κ →
    ∀ (A : LRc.Substructure K) (hA : S4Dom A)
      (σ : @Embedding LRc ↥A L _ (reductStruct L)),
      LogPreserving A hA.log_closed σ →
      ∀ x : K, x ∉ (A : Set K) → (∃ a : A, x = expE (a : K)) →
        ∃ (A' : LRc.Substructure K) (hA' : S4Dom A')
          (σ' : @Embedding LRc ↥A' L _ (reductStruct L)),
          A ≤ A' ∧ (∃ a : A', (a : K) = x) ∧
            (∀ (a : A) (h : (a : K) ∈ A'), σ' ⟨(a : K), h⟩ = σ ⟨a, a.2⟩) ∧
            LogPreserving A' hA'.log_closed σ'

/-- **The remaining case of the one-element step** — vdDMM Lemmas 4.2 and 4.4: `x` is not the
exponential of an element of the domain.  Its finer split (by whether the values of `x - a`,
`a ∈ A`, are new in `v(A^×)`) needs the value-group vocabulary of vdDMM §3. -/
def S4OnePoint_general : Prop :=
  ∀ (K L : Type) [LEc.Structure K] [LEc.Structure L],
    K ⊨ TE → L ⊨ TE →
    ∀ (κ : Cardinal.{0}), Cardinal.mk K < κ →
    @IsSaturated LEc L _ κ →
    ∀ (A : LRc.Substructure K) (hA : S4Dom A)
      (σ : @Embedding LRc ↥A L _ (reductStruct L)),
      LogPreserving A hA.log_closed σ →
      ∀ x : K, x ∉ (A : Set K) → (∀ a : A, x ≠ expE (a : K)) →
        ∃ (A' : LRc.Substructure K) (hA' : S4Dom A')
          (σ' : @Embedding LRc ↥A' L _ (reductStruct L)),
          A ≤ A' ∧ (∃ a : A', (a : K) = x) ∧
            (∀ (a : A) (h : (a : K) ∈ A'), σ' ⟨(a : K), h⟩ = σ ⟨a, a.2⟩) ∧
            LogPreserving A' hA'.log_closed σ'

/-- **The one-element step from its two cases**: the split is the classical case analysis on whether
`x` is the exponential of an element of the domain. -/
theorem S4OnePoint_of_cases (h1 : S4OnePoint_exp) (h2 : S4OnePoint_general) :
    S4OnePoint := by
  intro K L _ _ hK hL κ hκ hsat A hA σ hlog x hx
  by_cases h : ∃ a : A, x = expE (a : K)
  · exact h1 K L hK hL κ hκ hsat A hA σ hlog x hx h
  · exact h2 K L hK hL κ hκ hsat A hA σ hlog x hx fun a ha => h ⟨a, ha⟩

end Work.WilC5
