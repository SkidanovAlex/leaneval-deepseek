import ChallengeDeps
import Submission.ConvolutionTaylor
import Submission.Work.OneBodyMass
import Submission.Work.Q2Lower
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Statement design — FS `lem:QDecompSimpler` `eq:Q1n0` / `eq:Q2n0` (corpus form)

This module TYPESETS (no proofs) the per-state corpus targets that replay
FS final_v2.tex Lemma `lem:QDecompSimpler` (`eq:Q1n0` line ~1101, `eq:Q2n0`
line ~1111) inside the centred-box machinery.  All objects are expectation
values over a fixed-N state `Φ : X N → ℝ` on the analysis box `abox N ℓ`,
chosen branch (`h : ∃ w, IsRadial w ∧ IsScatteringSolution w v`, `w₀ :=
Classical.choose h`, `g₀ := v(1−w₀)`, `g₂ := g₀(1+w₀)`), dilute regime
`R ≤ ℓ·chiR0`.

## The FS statements (operator level, Λ = box of side ℓ, |Λ| = ℓ³,
χΛ := χ(·/ℓ), ρ₀ := n₀/ℓ³ with n₀ := Σ_i P_i, W₁ := g₀, w₁ = χΛW₁χΛ,
w₂ = w₁(1+ω₀))

    eq:Q1n0   𝒬₁ = (n₀/|Λ| − μ)·Σ_i Q_i·χΛ(W₁⋆χΛ)·P_i
                  + (n₀/|Λ|)·Σ_i Q_i·χΛ((W₁ω₀)⋆χΛ)·P_i   (+ h.c.)
    eq:Q2n0   𝒬₂ ≥ Σ_{i≠j} P_iQ_jw₂P_jQ_i
                  + ½Σ_{i≠j}(P_iP_jw₁Q_jQ_i + h.c.)
                  + ((ρ₀−μ)·Ŵ₁(0) + ρ₀·Ŵ₁ω₀(0))·Σ_i Q_iχΛ²Q_i
                  − C·(μ+ρ₀)·a·(R/ℓ)²·n₊
    with Ŵ₁(0) = ∫W₁ = ∫g₀ = 8πa v (g0_integral), Ŵ₁ω₀(0) = ∫g₀ω₀.

## Corpus transcription and the operator↔expectation caveat (IMPORTANT)
In FS, `ρ₀ = n₀/ℓ³` is an OPERATOR (`n₀ := ΣP_i`) and both displayed
formulas are operator identities/inequalities (their proof derives them from
the pointwise seeds `KernelMean.sumPj_kernel_mean` /
`P_iw₁P_i = ℓ⁻³·(∫_y w₁(x_i,y)dy)·P_i` etc. — the corpus has those seeds).
The corpus works at EXPECTATION level, where `n₀` cannot be replaced by the
scalar `cS1` per state (it sits INSIDE the sandwich).  The intended use is:
after the a-priori particle-number window (`thm:aprioribounds`: states of
interest have `n ≈ μℓ³`, `n₀ ≈ cS1(Φ)` and small `n₊`), one substitutes the
scalar parameter `ρ₀` for `n₀/ℓ³`.  These targets therefore carry `ρ₀` as a
FREE REAL PARAMETER (to be tied to `cS1(Φ)/(ℓ³·J(Φ))`, `J := ∫Φ²`, by the
a-priori argument later), exactly as the μ-tuning design in STATUS.md
requires.  The two per-state lemmas the corpus actually needs to PROVE are:

  * `qmass_fibre_local_lower`  — the fibre-localisation of the one-body
    Q-mass (FS's application of lem:Convolution): the χ-renormalized fibre
    `∫_y w₁(x,·)` is `8πa·χΛ(x)²` up to `(R/ℓ)²` errors, so
        Σ_i∫(Q_iΦ)²·fibre(x_i) ≥ 8πa v·Σ_i∫(Q_iΦ)²·χΛ(x_i)² − C(R/ℓ)²·8πa v·cnPlus
    (this is the `−μ`-coefficient half of the eq:Q2n0 mass combination).
  * the T₂-mass identity — Σ_{i≠j}∫(P_iQ_jΦ)²·w₂(x_i,x_j) carries the
    `+ρ₀(8πa+∫g₀ω₀)`-coefficient half (from `P_i`-constancy in slot `i`,
    i.e. exactly the `sumPj_kernel_mean`/peel pattern of the corpus);
    combined they give the coefficient
    `((ρ₀−μ)·8πa + ρ₀·∫g₀ω₀)·ΣQχΛ²Q − C(μ+ρ₀)·a·(R/ℓ)²·cnPlus`.

The targets below are typeset for those two lemmas (S1 = T₃-side,
S2 = T₂-side), plus the assembled per-state eq:Q2n0-form inequality, and the
eq:Q1n0 identity in pointwise-sum (n₀-realised) form.  EVERY symbol is
traced in the doc-comments; nothing here is proved (deliberately), so the
proof obligations of the next milestone are exactly the bodies of these
Props.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The χΛ²-weighted excited mass `Σ_i∫(Q_iΦ)²·χΛ(x_i)²` (FS `ΣQχΛ²Q`
expectation; `χΛ := chiScale ℓ`). -/
noncomputable def q2MassChi {N : ℕ} (ℓ : ℝ) {Φ : X N → ℝ} : ℝ :=
  ∑ i : Fin N, ∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 * (chiScale ℓ (x i)) ^ 2

/-- The one-body Q-mass `Σ_i∫(Q_iΦ)²·fibre₁(x_i)` with the chosen kernel
`w₁ := wPairC ℓ (g0 v h)` (FS `ΣQ_i∫w₁(x_i,·)Q_i`, the `T₃` mass of
`PotWords.q2word`). -/
noncomputable def qOneMass {N : ℕ} (ℓ : ℝ) {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) {Φ : X N → ℝ} : ℝ :=
  ∑ i : Fin N, ∫ x in abox N ℓ,
    (aQ ℓ i Φ x) ^ 2 * (w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i))

/-- The T₂ pair word with `w₂ := wPairC ℓ (g2 v h)` (the second summand of
`PotWords.q2word`, a square sum since `Q_jP_i = P_iQ_j`). -/
noncomputable def q2PairWord {N : ℕ} (ℓ : ℝ) {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) {Φ : X N → ℝ} : ℝ :=
  ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
    (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aQ ℓ p.2 (aP ℓ p.1 Φ) x) *
      wPairC ℓ (g2 v h) (x p.1) (x p.2)

/-- The T₁ pair word with `w₂` (first summand of `PotWords.q2word`; KEPT
unbounded on the RHS of eq:Q2n0, exactly as in FS). -/
noncomputable def q1PairWord {N : ℕ} (ℓ : ℝ) {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) {Φ : X N → ℝ} : ℝ :=
  ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
    (aP ℓ p.1 (aQ ℓ p.2 Φ) x) * (aP ℓ p.2 (aQ ℓ p.1 Φ) x) *
      wPairC ℓ (g2 v h) (x p.1) (x p.2)

/-- The T₄ pair word with `w₁` (fourth summand of `PotWords.q2word`, FS
`½Σ(P_iP_jw₁Q_jQ_i+h.c.)` expectation; KEPT unbounded on the RHS). -/
noncomputable def q4PairWord {N : ℕ} (ℓ : ℝ) {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) {Φ : X N → ℝ} : ℝ :=
  ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
    (aP ℓ p.1 (aP ℓ p.2 Φ) x) * (aQ ℓ p.2 (aQ ℓ p.1 Φ) x) *
      wPairC ℓ (g0 v h) (x p.1) (x p.2)

/-- The `g₀ω₀` mass `∫_z g₀ v h z · (Classical.choose h) z` (FS `Ŵ₁ω₀(0)`). -/
noncomputable def g0w0Mass {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) : ℝ :=
  ∫ z : ℝ³, g0 v h z * Classical.choose h z

/-- **Target S1 (eq:Q2n0 `−μ`-half; the fibre-localisation lemma).**
For every admissible state and every `μ ≥ 0`, the one-body Q-mass is at
least `μ`-times the χΛ²-mass up to the dilute error:

`qOneMass ≥ (8πa v)·q2MassChi − chiSup·Cχ·(R/ℓ)²·(8πa v)·cnPlus`

(multiply by `μ` for the eq:Q2n0 term `−μ·qOneMass ≤ −μ·8πa·q2MassChi +
μ·C(R/ℓ)²·(8πa v)·cnPlus`).  Proof route: pointwise fibre bound
(`KernelMean.mean_kernel_full` + `KernelMean.kernel_fibre` +
`convScale ≤ 1` [C–S from `chi_L2`] + `ConvolutionTaylor.convolution_approx`
with `f := g0`, `hfeven := g0_even`, `hfsupp := g0_zero_of_norm_ge`) then
integrate against `(Q_iΦ)² ≥ 0` and sum over `i`. -/
def qmass_fibre_local_lower_statement {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ) : Prop :=
  qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ) ≥
    (8 * π * a v) * q2MassChi (ℓ := ℓ) (Φ := Φ)
      - chiSup * (R / ℓ) ^ 2 * (8 * π * a v) * cnPlus ℓ Φ

/-- **Target S2 (eq:Q2n0 `+ρ₀`-half; the T₂-mass identity).**
The T₂ pair word carries the exact condensate-density mass content: for
`ρ₀` the scalar condensate density (to be tied to `cS1/(ℓ³J)` by the
a-priori window) one has, up to the dilute error,

`q2PairWord ≥ ρ₀·(8πa v + g0w0Mass)·q2MassChi − Cρ·ρ₀·(R/ℓ)²·(8πa v)·cnPlus`.

(FS eq:Q2n0 keeps `ΣP_iQ_jw₂P_jQ_i` on the RHS *unbounded* and folds the
`ρ₀(8πa+∫W₁ω₀)ΣQχΛ²Q` mass into the T₂-`−μQ∫w₁Q` combination — in the
corpus word split `q2word = q1PairWord + q2PairWord − μ·qOneMass +
q4PairWord` the content is exactly `q2PairWord − μ·qOneMass ≥ ((ρ₀−μ)·8πa
+ ρ₀·g0w0Mass)·q2MassChi − C(μ+ρ₀)·a·(R/ℓ)²·cnPlus`.)  Proof route:
`P_i`-constancy in slot `i` (`Q0Sector.aP_const_in_coord`, peel integrals)
turns `q2PairWord` into `Σ_j∫(Q_jΦ)²·(condensate-fibre at x_j)` with the
`ρ₀ := cS1-scaled` coefficient, then fibre-localisation as in S1. -/
def q2n0_mass_combination_statement {N : ℕ} {ℓ μ ρ₀ : ℝ} (hℓ : 0 < ℓ)
    (hμ : 0 ≤ μ) (hρ₀ : 0 ≤ ρ₀)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ) : Prop :=
  q2PairWord (ℓ := ℓ) (v := v) h (Φ := Φ) - μ * qOneMass (ℓ := ℓ) (v := v) h (Φ := Φ) ≥
    ((ρ₀ - μ) * (8 * π * a v) + ρ₀ * g0w0Mass (v := v) h) * q2MassChi (ℓ := ℓ) (Φ := Φ)
      - (μ + ρ₀) * (a v) * (R / ℓ) ^ 2 * cnPlus ℓ Φ

/-- **Assembled per-state eq:Q2n0 (corpus form).**  From the exact word split
`q2word = q1PairWord + q2PairWord − μ·qOneMass + q4PairWord`
(`Q2Lower.q2word`-def split, FS `eq:DefQ2`) and S1+S2:

`q2word ≥ q1PairWord + q4PairWord
       + ((ρ₀−μ)·8πa + ρ₀·g0w0Mass)·q2MassChi
       − C·(μ+ρ₀)·a·(R/ℓ)²·cnPlus`

(FS `eq:Q2n0`; the `(μ+ρ₀)·a·(R/ℓ)²·n₊` error is absorbed by the kinetic
gap `KineticBound.kinWord_gap_cnPlus` once `(R/ℓ)²·(μ+ρ₀)·a·36·ℓ² ≤ 1`.)
The constant `C` is a placeholder for the concrete dilute-regime constants
of S1/S2 (chiSup·Cχ etc.). -/
def q2n0_corpus_statement {N : ℕ} {ℓ μ ρ₀ : ℝ} (hℓ : 0 < ℓ)
    (hμ : 0 ≤ μ) (hρ₀ : 0 ≤ ρ₀)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : X N → ℝ} (hΦc : Continuous Φ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
  q2word (N := N) ℓ μ (wPairC ℓ (g0 v h)) (wPairC ℓ (g2 v h)) Φ ≥
    q1PairWord (ℓ := ℓ) (v := v) h (Φ := Φ) + q4PairWord (ℓ := ℓ) (v := v) h (Φ := Φ)
      + ((ρ₀ - μ) * (8 * π * a v) + ρ₀ * g0w0Mass (v := v) h) * q2MassChi (ℓ := ℓ) (Φ := Φ)
      - C * (μ + ρ₀) * (a v) * (R / ℓ) ^ 2 * cnPlus ℓ Φ


/-- **S2 kernel piece (exact per-slot identity, design target).**
With `w₂ := wPairC ℓ (g2 v h)` and fibre `fibre₂(z) := w1Fibre ℓ (wPairC ℓ (g2 v h)) z`,
for each slot `i` the `P`-summed `w₂`-mass against `Q_iΦ` is exact:

`Σ_{j≠i}∫(P_jQ_iΦ)²·w₂(x_j,xᵢ) = ℓ⁻³·∫ (Q_iΦ)·fibre₂(xᵢ)·(Σ_{j≠i}(P_jQ_iΦ))`

(derivation: `⟨P_jQ_iΦ, w₂P_jQ_iΦ⟩ = ⟨Q_iΦ, P_jw₂P_jQ_iΦ⟩` by self-adjointness of
`P_j`, and pointwise `P_j[w₂(x_j,·)·G] = G·ℓ⁻³·fibre₂(xᵢ)` for `G` constant in
slot `j` — `Q0Sector.aP_const_in_coord` + `mean_kernel_full` + symmetry of
`w₂` [g2 even]).  Summing over `i` gives `q2PairWord =
ℓ⁻³·Σ_i∫ (Q_iΦ)·fibre₂(xᵢ)·(Σ_j (P_jQ_iΦ))` — with `n₀ = Σ_jP_j` REALISED
inside the sandwich.  NOTE (scale check, do not attempt as per-state scalar
ρ₀): a per-state `q2PairWord ≥ ρ₀(8πa+∫g₀ω₀)·q2MassChi − err` with FREE
`ρ₀ > 0` is FALSE for fully excited Φ (P_iΦ = 0 ∀i: LHS 0, q2MassChi > 0);
the scalar `ρ₀` substitution belongs to the a-priori/c-number layer (FS §8),
not to a per-state all-Φ inequality. -/
def q2QQ_slot_identity_statement {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) (i : Fin N) {Φ : X N → ℝ} (hΦc : Continuous Φ) : Prop :=
  (∑ j : Fin N, if hij : j ≠ i then
      (∫ x in abox N ℓ, (aP ℓ j (aQ ℓ i Φ) x) ^ 2 *
        wPairC ℓ (g2 v h) (x j) (x i)) else 0)
    = (ℓ ^ 3)⁻¹ * (∫ x in abox N ℓ,
        (aQ ℓ i Φ x) * (w1Fibre ℓ (wPairC ℓ (g2 v h)) (x i)) *
          (∑ j : Fin N, if hij : j ≠ i then aP ℓ j (aQ ℓ i Φ) x else 0))

end BoseGases

end Submission
