import ChallengeDeps
import Submission.FUP.Metric
import Submission.FUP.HSLocalize
import Submission.FUP.LocalizeFinal
import Submission.FUP.BoxPorosity
import Submission.FUP.Damping
import Submission.FUP.Growth

open FractalUncertainty MeasureTheory FourierTransform Metric
open Submission.FUP
open scoped ENNReal BigOperators

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-!
# Specification layer for the deep inputs of Cohen's *Fractal uncertainty in higher dimensions*

This module records, as clearly marked *specifications* (never to be imported by
`Submission.lean`), the definitions and theorem statements that the published proof of
Theorem 1.1 uses as black boxes:

* `defn:damping_func_l2` / `defn:damping_func_l1` — what it means for a set to admit a
  damping function (Cohen §"Outline", Han–Schlag Definition 4.1);
* `thm:FUP_conditional_damping` — Han–Schlag's conditional fractal uncertainty
  principle (their Theorem 5.1) and its `ℓ₁` form `thm:han_schlag_original`;
* `thm:higher_dim_BM` — Cohen's higher-dimensional Beurling–Malliavin multiplier theorem;
* `prop:existence_damping` — line porosity produces damping functions.

The *statements* are `sorry`-free definitions.  The single-scale localisation statement
`localization_statement_original` is now **proved** in `Submission.FUP.LocalizeFinal` (from
Han–Schlag's §4 machinery developed in `Submission/FUP/Localize*.lean`), so the only remaining
literature inputs of the development are the `Prop`s below:

* `han_schlag_original : han_schlag_statement` — Han–Schlag's Theorem 5.1;
* (Cohen's `thm:higher_dim_BM` is available as the `Prop` `higher_dim_BM_statement`.)

Everything else in this module is derived: `Submission.FUP.Chain` proves Theorem 1.1 from these
two statements, `Submission.FUP.HanSchlagComparison` derives `FUP_conditional_damping_statement`
from `han_schlag_statement` (Appendix A.1), and `Submission.FUP.BMToDamping` derives
`higher_dim_BM_damping_statement` from `higher_dim_BM_statement`.

## Formalisation conventions

Pointwise bounds such as `|ψ(x)| ≤ ⟨x⟩^{-d}` are, strictly speaking, meaningless for an
`L²` *class*.  We therefore state them almost everywhere with respect to Lebesgue measure
(and, for the decay on `Y`, a.e. with respect to Lebesgue measure, restricted to `Y` by the
hypothesis `x ∈ Y`, which is the standard a.e. formulation for a possibly non-measurable set).
Since the
published theorems are applied to measurable sets, this is the natural measurable
formulation; a Paley–Wiener representative argument upgrades it to a pointwise one.
-/

namespace Submission.FUP.Spec

/-- Cohen's `thm:FUP_conditional_damping`, which is Han–Schlag's Theorem 5.1.

Suppose `X ⊆ [-1,1]^d` is `ν`-porous on balls from scales `h` to `1`, and that `Y` has the
property that all translated dilates `sY + [-4,4]^d + η` (`h < s < 1`,
`η ∈ [-h⁻¹s-5, h⁻¹s+5]^d`) admit an `ℓ₂` damping function with parameters
`c₁ = ν/(20√d)`, `c₂, c₃, α`.  Then there are `β, C̃ > 0` (depending on
`ν, c₂, c₃, d, α`) with `‖f 1_X‖₂ ≤ C̃ h^β ‖f‖₂` for every `f ∈ L²` with
`supp f̂ ⊆ Y`.

The version below is the exact statement used by the main proof: the smallness condition on
`c₃` (`c₃ < c₃*(d)` in Han–Schlag) is recorded as `c₃ ∈ (0, cstar)`.

(The hypothesis `supp f̂ ⊆ Y` is formalised as: the `L²` Fourier transform of `f` vanishes
a.e. off `Y`.  The conclusion is written with `eLpNorm` to match the challenge statement.)

Two harmless restrictions are imposed relative to the paper's statement, both needed for the
appendix comparison with Han–Schlag's original theorem:

* `ν ≤ 1/2`: in the comparison the porosity scale is `L = max 3 ⌈4√d/ν⌉`, and Han–Schlag's
  theorem is only available for damping parameters `c₁ = (2L)^{-1} ≤ 1/6`.  The paper's condition
  `c₁ = ν/(20√d)` therefore has to satisfy `ν ≤ 10√d/3`.  The main proof only ever applies this
  statement with `ν ≤ 1/2` (porosity is monotone in `ν`, see `Assembly`), which is why this
  weaker form suffices.  (Weakening a hypothesis makes the statement easier to prove, so the
  chain is unaffected.)
* `s ∈ (h, 1]` instead of the paper's `s ∈ (h,1)`: the comparison needs the endpoint `s = 1`,
  since Han–Schlag's theorem must be applied to the undilated set `Y` itself.  Again the
  hypothesis gets stronger, so the chain is unaffected. -/
def FUP_conditional_damping_statement : Prop :=
  ∀ (ν : ℝ), 0 < ν → ν ≤ 1 / 2 → ∀ (c₂ α : ℝ), c₂ ∈ Set.Ioo 0 1 → α ∈ Set.Ioo 0 1 →
    ∃ cstar : ℝ, 0 < cstar ∧ ∀ c₃ ∈ Set.Ioo 0 cstar,
      ∃ (β : ℝ) (C : ℝ), β > 0 ∧ C > 0 ∧
        ∀ (h : ℝ) (X Y : Set ℝᵈ), h ∈ Set.Ioo 0 1 →
          X ⊆ cube (-1) 1 → PorousOnBalls ν h 1 X →
          Y ⊆ cube (-h⁻¹) h⁻¹ →
          (∀ s ∈ Set.Ioc h 1, ∀ η : ℝᵈ,
            (∀ i : Fin d, η i ∈ Set.Icc (-h⁻¹ * s - 5) (h⁻¹ * s + 5)) →
            AdmitsL2Damping ((fun z : ℝᵈ => η + z) ''
                (addSet ((fun y : ℝᵈ => s • y) '' Y) (cube (-4) 4)))
              (ν / (20 * Real.sqrt (d : ℝ))) c₂ c₃ α) →
          ∀ f : Lp ℂ 2 (volume : Measure ℝᵈ),
            (∀ᵐ ξ ∂(volume : Measure ℝᵈ),
                ((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ ≠ 0 → ξ ∈ Y) →
            (eLpNorm (X.indicator f) 2).toReal ≤ C * h ^ β * ‖f‖

/-- Han–Schlag's Theorem 5.1 in their own (`ℓ₁` damping, box porosity) form
(Cohen's `thm:han_schlag_original`), with the two structural features of the published
statement: the smallness threshold `c₃ < c₃*(d)` on the damping parameter, and the threshold
`N ≥ N₀` on the scale below which the estimate is asserted.  The constants `β, C, N₀` may
depend on `L, c₂, c₃, α, d`.

**The damping parameter is `(4L)⁻¹` (Session 53).**  In the published Theorem 5.1 the damping
parameter is `(2L)⁻¹`, which equals half the side of the localisation squares of Corollary 4.2.
As explained in `Submission/FUP/HSLocalize.lean` (see `LocalizationStatement`), the proof of
Corollary 4.2 needs the support radius of the damping kernel to be *strictly* smaller than the
square half-side, i.e. a damping parameter `< (2L)⁻¹`; `(4L)⁻¹` (half of it) gives exactly the
factor `2` of room needed.  This is a harmless weakening of the hypothesis: the comparison theorem
`Submission.FUP.HanSchlagComparison` still derives Cohen's Theorem 1.4 from this statement, since
it produces the damping function from the `ℓ₂` damping parameter `ν/(20√d) ≤ (4L)⁻¹` (its
constant `L = max 3 ⌈4√d/ν⌉` satisfies `νL ≤ 5√d`).

`Submission.FUP.HanSchlagComparison` proves Cohen's Theorem 1.4
(`FUP_conditional_damping_statement`) from this statement. -/
def han_schlag_statement : Prop :=
  ∃ cstar : ℝ, 0 < cstar ∧
    ∀ (L : ℕ), 3 ≤ L → ∀ (c₂ c₃ α : ℝ), c₂ ∈ Set.Ioo 0 1 →
      c₃ ∈ Set.Ioo 0 cstar → α ∈ Set.Ioo 0 1 →
      ∃ (β C N₀ : ℝ), β > 0 ∧ C > 0 ∧ 0 < N₀ ∧
        ∀ (N : ℝ), N₀ ≤ N → ∀ (X Y : Set ℝᵈ),
          X ⊆ cube (-1) 1 →
          (∀ n : ℕ, (L : ℝ) ^ (n + 1) ≤ N → BoxPorous L (n + 1) X) →
          Y ⊆ cube (-N) N →
          (∀ n : ℕ, (L : ℝ) ^ (n + 1) ≤ N → ∀ η : ℝᵈ,
            (∀ i : Fin d, η i ∈ Set.Icc (-N * (L : ℝ) ^ (-(n : ℤ)) - 3)
                (N * (L : ℝ) ^ (-(n : ℤ)) + 3)) →
            AdmitsL1Damping ((fun z : ℝᵈ => η + z) ''
              (addSet ((fun y : ℝᵈ => (L : ℝ) ^ (-(n : ℤ)) • y) '' Y) (cube (-4) 4)))
              ((4 * L : ℝ)⁻¹) c₂ c₃ α) →
          ∀ f : Lp ℂ 2 (volume : Measure ℝᵈ),
            (∀ᵐ ξ ∂(volume : Measure ℝᵈ),
                ((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ ≠ 0 → ξ ∈ Y) →
            (eLpNorm (X.indicator f) 2).toReal ≤ C * N ^ (-β) * ‖f‖

/-- Han–Schlag's Theorem 5.1 is now PROVED from the single-scale localisation statement
`Submission.FUP.LocalizationStatement` (Han–Schlag's Corollary 4.2) in
`Submission.FUP.HSFinal.han_schlag_statement_of_localization`.  The literature input has
therefore been shrunk to *one* single-scale statement, recorded here as the only remaining
black box of the development (it lives here because `Submission.FUP.HSFinal` cannot import
this module: it already imports it).  See `Submission/FUP/HSLocalize.lean` for its statement.

**Session 52.**  The statement was corrected: the localisation cubes must be placed in *every*
cell of the grid (one square of side `2c₁` per cell of the `2ℤ^d`-translate), exactly as in
Han–Schlag's Corollary 4.2 (`cor:UPY`).  The earlier version quantified over an arbitrary
*subset* `T` of cells and was **false** (`Submission/FUP/ROADMAP.md`, Sessions 51 §2 and 52).
The §5 induction has been rewired accordingly: the localisation set is now `locSetZ`, one cube
per cell of the rescaled `L`-adic grid (`Submission/FUP/HSCellsZ.lean`), and the hole set is
`UstarZ`, the half-cubes of *all* empty gen-`(mT+1)` cells — which contains a cube of side
`L^{-1}` in every gen-`mT` cell (porosity for the cells meeting `X`, trivially for the others),
so the full-grid statement applies to it directly.

**Session 53.**  The damping parameter of the localisation statement is `c₁/2` (see
`Submission/FUP/HSLocalize.lean`): the published proof needs the damping kernel to be supported
in a cube of radius strictly smaller than the half-side of the localisation squares, and the
published constant role of `c₁` is off by the factor `2`.  This is why the damping parameter of
`han_schlag_statement` above is `(4L)⁻¹` rather than `(2L)⁻¹`; the comparison with Cohen's §6
(`Submission/FUP/HanSchlagComparison.lean`) is unaffected.

The remaining task is proving this statement from the quantitative Logvinenko–Sereda theorem in
dimension `d` (for `d = 1` it is
`Commons.Analysis.Fourier.LogvinenkoSereda.logvinenko_sereda_one_dim`); the reduction is described
in `Submission/FUP/ROADMAP.md`, Session 53. -/
theorem localization_statement_original : LocalizationStatement (d := d) :=
  Submission.FUP.localization_statement (d := d)

/-- Cohen's `thm:higher_dim_BM`: the higher-dimensional Beurling–Malliavin multiplier
theorem.  `ω` is a weight satisfying the regularity condition up to three derivatives
(`eq:regularity_condition_0to3`), vanishing on `B₂`, and with finite growth functional
(`eq:higher_dim_BM_growth_cond`).  Then for every spectral radius `σ` a Fourier-localised
function with the stated bounds exists.

The constants `c, rmin, M` are produced *before* the weight `ω`, i.e. they are uniform in `ω`:
in the paper (`thm:higher_dim_BM`) they are `c = c_d/max(C_reg,C_gr)`,
`r_min = c_d·min(σ,σ⁻¹)` and `C = C_d·max(σ^{-C_d}, e^{3σ})`, all independent of `ω`. -/
def higher_dim_BM_statement : Prop :=
  ∀ (Creg Cgr : ℝ), 0 < Creg → 0 < Cgr → ∀ (σ : ℝ), 0 < σ → σ < 1 →
    ∃ (c rmin M : ℝ), 0 < c ∧ 0 < rmin ∧ 0 < M ∧
      ∀ (ω : ℝᵈ → ℝ), (∀ x, ω x ≤ 0) → (∀ x, ‖x‖ ≤ 2 → ω x = 0) → ContDiff ℝ 3 ω →
        (∀ (a : ℕ), a ≤ 3 → ∀ x : ℝᵈ,
          ‖iteratedFDeriv ℝ a ω x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (a : ℝ)) / 2)) →
        HasFiniteGrowth ω Cgr →
        ∃ f : Lp ℂ 2 (volume : Measure ℝᵈ),
          (∀ᵐ ξ ∂(volume : Measure ℝᵈ), ξ ∉ closedBall (0 : ℝᵈ) σ →
              ((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ = 0) ∧
          (∀ᵐ x ∂((volume : Measure ℝᵈ).restrict (closedBall (0 : ℝᵈ) rmin)),
              (1 / 2 : ℝ) ≤ ‖(f : ℝᵈ → ℂ) x‖) ∧
          (∀ᵐ x ∂(volume : Measure ℝᵈ),
              ‖(f : ℝᵈ → ℂ) x‖ ≤ M * Real.exp (c * σ * ω x))

/-- **The `L²` consequence of `thm:higher_dim_BM` used in §6.1.**  Multiplying the function
produced by `thm:higher_dim_BM` by a fixed Schwartz function whose Fourier transform is
supported in a small ball (Cohen's argument, cf. the paragraph following the statement of
`thm:higher_dim_BM`) turns the global bound `Ce^{cσω}` into the `⟨x⟩^{-d}` bound needed in the
definition of a damping function, at the cost of enlarging `M`; the `L²` normalisation over the
unit ball then follows from the pointwise lower bound.

This statement is recorded separately from `higher_dim_BM_statement` because the formal passage
between them uses the (standard, but missing from Mathlib) fact that the Fourier transform of a
product of an `L²` function with a Schwartz function is supported in the sum of the two
supports. -/
def higher_dim_BM_damping_statement : Prop :=
  ∀ (Creg Cgr : ℝ), 0 < Creg → 0 < Cgr → ∀ (σ : ℝ), 0 < σ → σ < 1 →
    ∃ (c rmin M c₂ : ℝ), 0 < c ∧ 0 < rmin ∧ 0 < M ∧ 0 < c₂ ∧
      ∀ (ω : ℝᵈ → ℝ), (∀ x, ω x ≤ 0) → (∀ x, ‖x‖ ≤ 2 → ω x = 0) → ContDiff ℝ 3 ω →
        (∀ (a : ℕ), a ≤ 3 → ∀ x : ℝᵈ,
          ‖iteratedFDeriv ℝ a ω x‖ ≤ Creg * (1 + ‖x‖ ^ 2) ^ ((1 - (a : ℝ)) / 2)) →
        HasFiniteGrowth ω Cgr →
        ∃ f : Lp ℂ 2 (volume : Measure ℝᵈ),
          (∀ᵐ ξ ∂(volume : Measure ℝᵈ), ξ ∉ closedBall (0 : ℝᵈ) σ →
              ((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ = 0) ∧
          (∀ᵐ x ∂((volume : Measure ℝᵈ).restrict (closedBall (0 : ℝᵈ) rmin)),
              (1 / 2 : ℝ) ≤ ‖(f : ℝᵈ → ℂ) x‖) ∧
          (c₂ ≤ ∫ x in ball (0 : ℝᵈ) 1, ‖(f : ℝᵈ → ℂ) x‖ ^ 2) ∧
          (∀ᵐ x ∂(volume : Measure ℝᵈ),
              ‖(f : ℝᵈ → ℂ) x‖ ≤ M * Real.exp (c * σ * ω x)) ∧
          (∀ᵐ x ∂(volume : Measure ℝᵈ),
              ‖(f : ℝᵈ → ℂ) x‖ ≤ M * (1 + ‖x‖ ^ 2) ^ (-(d : ℝ) / 2))

def existence_damping_statement : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (μ : ℝ), 1 < μ →
    ∃ (α : ℝ) (c₂f c₃f : ℝ → ℝ), α < 1 ∧ 0 < α ∧
      (∀ σ ∈ Set.Ioo 0 1, c₂f σ ∈ Set.Ioo 0 1 ∧ 0 < c₃f σ) ∧
      ∀ (h : ℝ), 0 < h → ∀ (Y : Set ℝᵈ),
        Y ⊆ cube (-(12 * h⁻¹)) (12 * h⁻¹) → PorousOnLines ν μ h⁻¹ Y →
        ∀ σ ∈ Set.Ioo 0 1, AdmitsL2Damping Y σ (c₂f σ) (c₃f σ) α

end Submission.FUP.Spec
