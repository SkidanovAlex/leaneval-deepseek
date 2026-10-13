/-
  WilC5 — **vdDMM Lemma 4.3 (adjoining an exponent)**, as an extension step of the §4 iteration.

  Situation (`Work.WilC5.S4Pair`, `S4Setup.lean`): `K, L ⊨ TE`, `L` is `κ`-saturated for `LEc` with
  `κ > |K|`, and `p = (B, τ)` is a partial extension of the §4 iteration: `B ≤ K` is a `Dcl`-closed
  (`rexp`-)substructure closed under the definable logarithm (`S4Dom B`) and `τ : B → L` is a
  log-preserving `LRc`-embedding.

  We are given `a ∈ B` such that `expE a ∉ B` — so the new element `x := expE a` is the
  exponential of an element of the domain, the case that the companion file
  `S4OnePoint_exp_proved.lean` isolates as `Work.WilC5.S4OnePoint_exp` — and the source's *standing
  maximality hypothesis* `hvalnew`: the definable closure of `B ∪ {y}` has a *larger* value group
  than `B` for **every** `y ∉ B` (`v(B(y)^×) ≠ v(B^×)`, the form in which Zorn maximality supplies
  it).  Note this is a statement about the closure, not about the element: the element-level fact
  `v(y) ∉ v(B^×)` that the proof uses is *derived* from `hvalnew` inside the proof (via the
  maximality of the pair, exactly as in the source), and it is false in general without it.

  Claim: there is a partial extension `q ≥ p` whose domain contains `expE a`.

  This is vdDMM Lemma 4.3.  The two ingredients are

  * **the cut of `exp a` over `B` is computed from the cut of `a`**, because
    `w < exp a ↔ log w < a` for `w > 0` (`Work.WilC5.expE_lt_iff_logFun_lt`,
    `expE_lt_iff_logFun_lt.lean`) and `B` is closed under the definable logarithm: so if `y ∈ L`
    realises the image of the cut of `a` over `B` — and, by the induction that maintains the
    iteration, the image of `exp a` must be `expE (τ a)` — then `expE (τ a)` realises the image of
    the cut of `exp a` over `B`.  The extension to the definable closure is
    `Work.WilC5.CutExtendsDcl` (`CutExtendsDcl.lean`).

  * **log-closure and log-preservation**, by the decomposition of vdDMM Lemma 4.2 with one extra
    generator: by the value containment `Work.WilC5.SpanContain` (`SpanContain.lean`, from
    `hVI`), every `w ∈ F = Dcl(B ∪ {exp a})` has the same value as `u · exp(q a)` for some `u ∈ B`
    and `q ∈ ℚ` (the value group of `F` is `v(B^×) ⊕ ℚ·v(exp a)`, the source's (3.7) at
    `g = v(exp a)`), so it decomposes as `w = u' (1+ε) exp(q a)` with `u' ∈ B`, `ε ∈ F`
    infinitesimal (`Work.WilC5.decomposition_of_same_value`); then

        log w = log u' + log(1+ε) + q·a,     log(σ' w) = log(σ' u') + log(1+σ' ε) + q·σ' a,

    and both terms are handled as in Lemma 4.2: `log(1+δ)` is `LRc`-definable for `|2δ| ≤ 1`
    (`Work.WilC5.logFun_one_add_rexp`, `Work.WilC5.logFun_eq_of_rexp_eq`) and the extension is
    `LRc`-elementary on `F` (`model_TR_of_dcl_closed` + `hMCr`), so it commutes with it; the rest is
    log-preservation on `B` and the ring structure.  (The quantifier `exp(q a)` is only notation:
    `expE a ∈ F`, hence its `ℚ`-powers and roots are in `F` since `F` is `Dcl`-closed and real
    closed, and `logFun (expE (q a)) = q a` by `Work.WilC5.logFun_expE`.)

  The element-level fact `v(exp a) ∉ v(B^×)` is *derived* from `hvalnew` — it is vdDMM's first
  claim in Lemma 4.3: if `v(exp a) ∈ v(B^×)` then `v(F^×) = v(B^×)` with
  `F = Dcl(B ∪ {exp a})`, so `exp a = u(1+ε)` with `u ∈ B` and `ε` infinitesimal; then
  `exp(a - log u) = 1+ε` with `a - log u ∈ B` (as `B` is log-closed) and `exp(a - log u) ∈ B`
  (it is the `rexp`-definable function `1 ↦ exp` at the element `a - log u` of `Dcl B`), whence
  `exp a = u · exp(a - log u) ∈ B`, contradiction.  It is stated as a hypothesis here so that this
  lemma can be proved independently of the maximality argument that consumes it.
-/
import Mathlib
import Submission.Work.WilC5.S4StepDefs
import Submission.Work.WilC5.LRcSatOfLEcSat
import Submission.Work.WilC5.StepExp
import Submission.Work.WilC5.CutExtendsDcl
import Submission.Work.WilC5.SpanContain
import Submission.Work.WilC5.dmm42_cut_extend
import Submission.Work.WilC5.realizes_cut
import Submission.Work.WilC5.decomposition_of_same_value
import Submission.Work.WilC5.expE_lt_iff_logFun_lt
import Submission.Work.WilC5.logFun_one_add_rexp
import Submission.Work.WilC5.logFun_eq_of_rexp_eq
import Submission.Work.WilC5.logFun_mul
import Submission.Work.WilC5.logFun_expE
import Submission.Work.WilC5.expE_add_of_model
import Submission.Work.WilC5.expE_of_logFun_preserving
import Submission.Work.WilC5.model_TR_of_dcl_closed
import Submission.Work.WilC5.dclClosed_substructure
import Submission.Work.WilC5.ExistsEmbeddingClosurePoint

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

/-- **vdDMM Lemma 4.3 (adjoining an exponent), as an extension step.**  If `a ∈ B`, `expE a ∉ B`
and the value of `expE a` is new over `B` (`ValueNew`), then the partial extension `p = (B, τ)` of
the §4 iteration extends strictly to a pair whose domain contains `expE a`. -/
theorem S4StepExp
    (hMCr : ModelComplete TR) (hOM : OMinModels) (hVI : ValIneq)
    {K L : Type} [LEc.Structure K] [LEc.Structure L]
    (hK : K ⊨ TE) (hL : L ⊨ TE)
    (κ : Cardinal.{0}) (hκ : Cardinal.mk K < κ)
    (hsat : @IsSaturated LEc L _ κ)
    {A₀ : LRc.Substructure K} {σ₀ : @Embedding LRc ↥A₀ L _ (reductStruct L)}
    (p : S4Pair A₀ σ₀)
    (a : ↥p.dom) (ha : expE (a : K) ∉ (p.dom : Set K))
    (hvalnew : ∀ y : K, y ∉ (p.dom : Set K) →
      ¬ (∀ w : K, w ∈ Work.WilC2.Dcl ((p.dom : Set K) ∪ {y}) →
          ∃ b : ↥p.dom, SameVal K hK (b : K) w)) :
    ∃ q : S4Pair A₀ σ₀, p ≤ q ∧ ∃ b : ↥q.dom, (b : K) = expE (a : K) :=
  StepExp hMCr hOM hVI hK hL κ hκ hsat p a ha hvalnew

end Work.WilC5
