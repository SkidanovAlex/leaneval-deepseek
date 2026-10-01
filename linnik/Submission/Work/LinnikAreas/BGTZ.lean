import Mathlib
import Submission.Work.LinnikAreas.SiegelBase
import Submission.Work.ZeroDensity.Defs

/-!
# The Deuring--Heilbronn repulsion *at all heights* (the BGTZ form) and the sound route to AREA 6

## Why this file exists

AREA 6 (`Work.LinnikAreas.area6`) needs the height part of the zero sum,

`Siegel.restHighZeroSum χ₁ β₁ (11/2) (3/10)`, the sum over the pairs `(χ,ρ) ≠ (χ₁,β₁)` with
`|Im ρ| > 1` of `mult(ρ)·‖Hk((1-ρ)𝓛)‖`,

to be `≤ C·λ₁·𝓛^e` (`e < 0`).  The workspace's original route fed this through
`Siegel.DHLogFreeHeightCoupled c` (`Σ_χ N*(σ,T,χ) ≤ C·λ₁·(qT)^{c(1-σ)}`, Bombieri Thm. 14), which is
consumed by `siegelRestHighCoupled`.  **That coupled estimate is not a classical theorem in the
unrestricted form**, and it is *false* in the extreme height range:

* the only known mechanism producing the factor `λ₁` at height `T` is the Deuring--Heilbronn
  repulsion, whose threshold degrades with the height; in the form stated by Heath-Brown
  (1992, §1 Principle 2, after Graham) the repulsion is
  `λ(ρ) ≥ c₂·log(1/δ)/(2+|Im ρ|)` with `c₂ < 3/2` and `δ = 1-β₁`, which is *vacuous* for
  `|Im ρ| ≫ log(1/δ)`, hence gives nothing at heights `≫ 𝓛`;
* the `λ₁`-free log-free density estimates (`FamDensityEpsRange`, HB's (1.4)) are uniform in `T`
  but carry no `λ₁`;
* the coupled statement with a *fixed* exponent `c` therefore asserts, at `t ≍ 𝓛` and heights
  `T ≫ q^{A}`, a bound of size `λ₁·(qT)^{c}·(…)^{…}` for a count that no available estimate
  forces to be small: at `(t,T) = (𝓛, e^{𝓛²})` and `λ₁ ≍ e^{-𝓛/2}` it is smaller than what the
  classical zero-free region leaves open.

By contrast, Bombieri's/Jutila's *own* use of the coupled estimate (Heath-Brown 1992 §13--14) needs
it only in the working region `|γ| ≤ 1`, where it **is** a theorem (the workspace's
`Work.ZeroDensity.Deuring.deuringHeilbronnLogFree`: the λ₁-saving count from the log-free family
count + the repulsion, for `|Im ρ| ≤ 1`).  Heath-Brown then handles the *far* heights with the
`λ₁`-free density estimate only, which forces him to assume `λ₁ ≫ 1` and to delegate the case of
small `λ₁` to [HB90].

The *sound* route implemented here replaces the (dubious) coupled height count by two ingredients
that are both true and classical:

1. the `λ₁`-free log-free family count in the height direction
   (`Work.ZeroDensity.LogFreeFamHeight (5/2) (3/2)`, proved from Jutila + Huxley by
   `Work.ZeroDensity.Assembly.logFreeFamHeight_of_cores`) — this alone gives
   `restHighZeroSum ≤ C𝓛^{-2+ε}`, i.e. `Siegel.RestHighFree` below;
2. the **height-degraded repulsion** in the form in which it is *known* at all heights
   (Benli--Goel--Twiss--Zaman, *Explicit Deuring--Heilbronn phenomenon for Dirichlet L-functions*,
   arXiv:2410.06082, Cor. 1.2): with `D(T) = c₁𝓛 + c₂ log T + c₃` and `δ = 1-β₁ = λ₁/𝓛`,

   `1 - β(ρ) > log(c₄/(δ·D(|Im ρ|))) / D(|Im ρ|)`, i.e. `λ(ρ) ≥ (log(1/λ₁) - log(24(c₁+c₂ξ)))/(c₁+c₂ξ)`

   with `ξ = log(4+|Im ρ|)/𝓛`, `c₁ = 4/3+ε`, `c₂ = 2/3+ε`, `c₃ = 0`, `c₄ = 1/24`.  This is
   the crucial point: unlike Principle 2 of HB92, BGTZ's bound is *not* vacuous at large heights
   (it degrades only logarithmically), and it does give the factor `λ₁` for the high zeros —
   `restHighZeroSum ≤ C𝓛^{-2}λ₁^{1.67}` (`Siegel.RestHighBGTZ` below, from `λ₁ ≤ 1/10`).

Both ingredients are *assumption nodes* only in so far as their formalization is not yet done;
the statements are theorems of the literature (Jutila 1977 + Huxley 1972; BGTZ 2024), in contrast
to `Siegel.DHLogFreeHeightCoupled`, which is not.

## What is defined here

* `Siegel.RepulsionBGTZ` — the all-heights repulsion of BGTZ Cor. 1.2, in λ-units;
* `Siegel.RestHighFreeSpec c e` / `Siegel.RestHighBGTZSpec C e` — the two forms of the high-zero
  bound that the pieces below are stated in (kept as plain `Prop`s so that the requesting files do
  not have to repeat the quantifier block).
-/

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas

open Work.LinnikContract

namespace Siegel

/-- **The Deuring--Heilbronn repulsion at all heights** (Benli--Goel--Twiss--Zaman,
arXiv:2410.06082, Cor. 1.2, with `ε = 1/100` and `B = 1`): if `χ₁` is a real character mod `q` with
an exceptional real zero `β₁` whose `λ₁ = λ(β₁) = (1-β₁)𝓛` satisfies
`1/(q^{1/100}𝓛) < λ₁ ≤ 1/10`, then for every further zero `ρ` (of any character mod `q`,
principal included, the pair `(χ₁,β₁)` excluded) one has

`λ(ρ) ≥ (log(1/λ₁) - log(24·(c₁ + c₂·log(4+|Im ρ|)/𝓛))) / (c₁ + c₂·log(4+|Im ρ|)/𝓛)`,
`c₁ = 4/3 + 1/100`, `c₂ = 2/3 + 1/100`.

(Their Cor. 1.2 gives `β < 1 - log(c₄/(δ D))/D` with `D = c₁𝓛+c₂log T+c₃`, `c₃ = 0`, `c₄ = 1/24`
for `|γ| ≤ T`, `T ≥ 4`, `qT ≥ C(ε)`; multiply by `𝓛 = log q` to pass to `λ = (1-β)𝓛`, use
`δ = λ₁/𝓛` and take `T = max(4,|Im ρ|)`.) -/
def RepulsionBGTZ : Prop :=
  ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
    χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
    1 / ((q : ℝ) ^ ((1 / 100 : ℝ)) * Real.log q) < lamOf q (β₁ : ℂ) →
    lamOf q (β₁ : ℂ) ≤ 1 / 10 →
    ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), zeroMult χ ρ ≠ 0 →
      ¬(χ = χ₁ ∧ ρ = (β₁ : ℂ)) →
      (Real.log (1 / lamOf q (β₁ : ℂ))
          - Real.log (24 * ((4 / 3 + 1 / 100 : ℝ)
              + (2 / 3 + 1 / 100 : ℝ) * (Real.log (5 + |ρ.im|) / Real.log q))))
        / ((4 / 3 + 1 / 100 : ℝ)
            + (2 / 3 + 1 / 100 : ℝ) * (Real.log (5 + |ρ.im|) / Real.log q))
        ≤ lamOf q ρ

/-- **The `λ₁`-free high-zero bound** (Heath-Brown 1992, Lemma 13.2, run with the λ₁-free estimate
`Σ_χ N(σ,T,χ) ≪ (qT)^{(5/2)(1-σ)}T^{3/2}` of Jutila + Huxley): there are `C > 0`, `e < 0`, `q₀`
with, for all `q ≥ q₀` and *all* Siegel data (`λ₁ ≤ 1/2`),

`restHighZeroSum χ₁ β₁ (11/2) (3/10) ≤ C·𝓛^e`

(e.g. `e = -3/2`: the dyadic decomposition in λ and in the log-height gives
`4·(a₀/2.4)·C₂·𝓛^{-2}·Σ_h h^{-1/2} ≪ 𝓛^{-2}`). -/
def RestHighFreeSpec (e : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
    χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
    lamOf q (β₁ : ℂ) ≤ 1 / 2 →
    restHighZeroSum χ₁ (β₁ : ℂ) (11 / 2) (3 / 10) ≤ C * (Real.log q) ^ e

/-- **The `λ₁`-saving high-zero bound**, in the range where the BGTZ repulsion applies
(`λ₁ ≤ 1/10`): there are `C > 0`, `e < 0`, `q₀` with, for all `q ≥ q₀` and all Siegel data with
`λ₁ ≤ 1/10`, `restHighZeroSum ≤ C·λ₁·𝓛^e`.  The proof only needs the λ₁-free height count for the
*counting* and the BGTZ repulsion for the *repulsion*: at log-height `ξ` the zeros have
`λ ≥ (log(1/λ₁) - log(24(c₁+c₂ξ)))/(c₁+c₂ξ)`, so the Abel sum in λ gives
`≤ C₂h^{3/2}·e^{-(a₀-γ)·(log(1/λ₁)-log(24c₁))/c₁}·(a₀/(a₀-γ))` per layer, summing the layers
geometrically. -/
def RestHighBGTZSpec (e : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ₁ : DirichletCharacter ℂ q) (β₁ : ℝ),
    χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β₁ < 1 → zeroMult χ₁ (β₁ : ℂ) ≠ 0 →
    lamOf q (β₁ : ℂ) ≤ 1 / 10 →
    restHighZeroSum χ₁ (β₁ : ℂ) (11 / 2) (3 / 10)
      ≤ C * lamOf q (β₁ : ℂ) * (Real.log q) ^ e

end Siegel

end Work.LinnikAreas
