/-
  WilC5 — **vdDMM Lemma 4.4 (the hard step of §4)**, as an extension step of the iteration.

  Situation (`Work.WilC5.S4Pair`, `S4Setup.lean`): `K, L ⊨ TE`, `L` is `κ`-saturated for `LEc` with
  `κ > |K|`, and `p = (B, τ)` is a partial extension of the §4 iteration: `B ≤ K` is a `Dcl`-closed
  (`rexp`-)substructure closed under the definable logarithm (`S4Dom B`) and `τ : B → L` is a
  log-preserving `LRc`-embedding.  We assume the *fortified* situation of the source:

  * `hexp` : `B` is closed under the exponential (`expE b ∈ B` for `b ∈ B`);
  * `hvalnew` : the source's "`v(F₀(y)^×) ≠ v(F₀^×)` for all `y ∈ K \ F₀`", stated at the level of
    the *definable closure*: for every `y ∉ B`, some element of `Dcl (B ∪ {y})` has a value that no
    element of `B` has.  (This is what Zorn maximality gives: if `v(B(y)^×) = v(B^×)` then
    vdDMM's Lemma 4.2 would extend the pair past `y`, contradicting maximality.  The element-level
    form `v(y) ∉ v(B^×)` does *not* follow from it — see the note in `S4StepNoNew.lean` — and is
    derived inside the proof only for the elements it is needed for, as in the source.)

  and we are given `x ∉ B`.

  Claim: there is a partial extension `q ≥ p` whose domain contains `x`.

  This is van den Dries–Macintyre–Marker, *Ann. of Math.* **140** (1994), Lemma 4.4; the text is in
  `sources/wilkiesC/DMM.txt`.  Their construction (with `F₀ = B`, `r = ℝ` the real constants):

  **Normalisation.**  Since `v(x) ∉ v(B^×)`, `x` is neither finite nor infinitesimal; replacing `x`
  by `x⁻¹` if necessary (and then `x` is definable from `x⁻¹` in `Dcl (B ∪ {x⁻¹})`, which is the
  domain one ends up with) we may assume `x > ℝ`, i.e. `x` dominates every real constant.

  **The sequence.**  `F₀(x₀,…,x_{n+1})` always denotes `Dcl (F₀ ∪ {x₀,…,x_{n+1}})`.  Put `x₀ = x`.
  Given `xₙ`:

  * `v(log xₙ) ∉ v(F₀^×)`: otherwise `v(F₀(log xₙ)^×) = v(F₀^×)` and, by the *maximality* encoded in
    `hvalnew` (no element outside `B` has an old value), `log xₙ ∈ F₀`, whence
    `xₙ = exp (log xₙ) ∈ F₀` by `hexp`, contradiction;
  * so (DvD Lemma 3.4, the *approximation* form of their (3.4)) there is `βₙ ∈ F₀` with
    `v(log xₙ - βₙ) > v(log xₙ)`, i.e. with the remainder closer to finite than `log xₙ`; and
    `log xₙ - βₙ` is also value-new over `F₀` (`hvalnew`);
  * `x_{n+1} = εₙ (log xₙ - βₙ)` with `εₙ = ±1`, so that `log xₙ = βₙ + εₙ x_{n+1}`.

  **The claims** (their numbering).

  1. `v(x_{n+1}) < 0`, and `v(xₙ) < v(log xₙ) < v(x_{n+1}) ≤ 0`: the remainders move towards the
     finite world; this is what makes the later cut comparisons work.
  2. `v(x₀), …, v(xₙ)` are `ℚ`-linearly independent modulo `v(F₀^×)`; hence, with the containment
     of `Work.WilC5.SpanContain` (`SpanContain.lean`, applied with `S := F₀` and the generators
     `x₀,…,xₙ` — this is where the valuation inequality `hVI` enters),
     `v(Fₙ₊₁^×) = v(F₀^×) ⊕ ℚv(x₀) ⊕ … ⊕ ℚv(xₙ)`, so every `w ∈ Fₙ₊₁ \ {0}` decomposes as
     `w = u (1+ε) x₀^{q₀} ⋯ xₙ^{qₙ}` with `u ∈ F₀`, `qᵢ ∈ ℚ` and `ε ∈ Fₙ₊₁` infinitesimal
     (`Work.WilC5.decomposition_of_same_value`).
  3. Realising in `L` the image under `τ` of the cut of `x` over `F₀` (`Work.WilC5.realizes_cut`,
     `realizes_cut.lean`, using the saturation of `L`, which transfers from `LEc` to `LRc` by
     `Work.WilC5.lrcSaturated_of_lecSaturated`, `LRcSatOfLEcSat.lean`) and setting
     `y₀ = y`, `y_{n+1} = εₙ (log yₙ - τ(βₙ))`, each `yᵢ` realises the image of the cut of `xᵢ` over
     `F₀`.  The key computation is elementary: for `w ∈ F₀` with `expE w, expE βₙ ∈ F₀` (`hexp`),

         `w < x_{n+1}  ↔  w + βₙ < x_{n+1} + βₙ  ↔  expE w · expE βₙ < xₙ`

     (using `xₙ = expE (βₙ + εₙx_{n+1})` and the multiplicativity/monotonicity of `expE`), and the
     right hand side is the cut of `xₙ` over `F₀`, transported to `yₙ` by the induction.
  4. `τ` extends to `Fₙ = F₀(x₀,…,xₙ)` by `xᵢ ↦ yᵢ`: with the decomposition of Claim 2, the cut of
     `xₙ` over `Fₙ` is computed by the same asymptotics as in Claim 2 (`v(x_{m+1}) < v(log xⱼ)`,
     `v(log(1+δ))` for the generators with `j > m`, so that the smallest index `m` with `q_m ≠ 0`
     decides the sign), and then `Work.WilC5.CutExtendsDcl` (`CutExtendsDcl.lean`) gives the
     extension to `Fₙ₊₁`.
  5. `F := ⋃ₙ Fₙ` is `Dcl`-closed and closed under the logarithm, and `σ := ⋃ₙ σₙ` is log-preserving:
     for `w ∈ Fₙ₊₁` use the decomposition `w = u(1+ε)∏ xᵢ^{qᵢ}` of Claim 2 and

         `log w = log u + log(1+ε) + Σ qᵢ log xᵢ = log u + log(1+ε) + Σ qᵢ (βᵢ + εᵢ x_{i+1})`,
         `log (σ w) = log (σ u) + log(1+σ ε) + Σ qᵢ log yᵢ`

     with `log(1+δ)` `LRc`-definable for `|2δ| ≤ 1` and the extension `LRc`-elementary on `B`
     (`model_TR_of_dcl_closed` + `hMCr`), exactly as in Lemmas 4.2 and 4.3.  Note that all the
     `log xᵢ` occurring here are handled by the *definition* of `x_{i+1}`: nothing needs to be
     known about `log` at infinity beyond the relations `log xᵢ = βᵢ + εᵢx_{i+1}`.

  The upshot is a partial extension `q ≥ p` whose domain contains `x` (and, at every finite stage,
  the `Fₙ` are `Dcl`-closed and log-closed by the claims above).
-/
import Mathlib
import Submission.Work.WilC5.S4StepDefs
import Submission.Work.WilC5.LRcSatOfLEcSat
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
import Submission.Work.WilC5.expE_strictMono
import Submission.Work.WilC5.expE_of_logFun_preserving
import Submission.Work.WilC5.model_TR_of_dcl_closed
import Submission.Work.WilC5.dclClosed_substructure
import Submission.Work.WilC5.dcl_iUnion_chain
import Submission.Work.WilC5.ExistsEmbeddingClosurePoint
import Submission.Work.WilC5.ValProp
import Submission.Work.WilC5.StepSeqTower

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

/-- **vdDMM Lemma 4.4 (the hard step), as an extension step.**  In the fortified situation
(`B` is `Dcl`-closed, log-closed, closed under `expE`, and every element outside `B` is value-new),
any `x ∉ B` extends the partial extension `p = (B, τ)` strictly to a pair whose domain contains
`x`. -/
theorem S4StepNew
    (hMCr : ModelComplete TR) (hOM : OMinModels) (hVI : ValIneq) (hVP : ValProp)
    {K L : Type} [LEc.Structure K] [LEc.Structure L]
    (hK : K ⊨ TE) (hL : L ⊨ TE)
    (κ : Cardinal.{0}) (hκ : Cardinal.mk K < κ)
    (hsat : @IsSaturated LEc L _ κ)
    {A₀ : LRc.Substructure K} {σ₀ : @Embedding LRc ↥A₀ L _ (reductStruct L)}
    (p : S4Pair A₀ σ₀)
    (hexp : ∀ b : ↥p.dom, expE (b : K) ∈ (p.dom : Set K))
    (hvalnew : ∀ y : K, y ∉ (p.dom : Set K) →
      ¬ (∀ w : K, w ∈ Work.WilC2.Dcl ((p.dom : Set K) ∪ {y}) →
          ∃ b : ↥p.dom, SameVal K hK (b : K) w))
    {x : K} (hx : x ∉ (p.dom : Set K)) :
    ∃ q : S4Pair A₀ σ₀, p ≤ q ∧ ∃ b : ↥q.dom, (b : K) = x :=
  StepSeqS4Pair hMCr hOM hVI hVP hK hL κ hκ hsat p hexp hvalnew hx

end Work.WilC5
