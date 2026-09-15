import Submission.FUP.HSSets
import Submission.FUP.Metric

open FractalUncertainty MeasureTheory FourierTransform Metric Filter Set Pointwise
open scoped ENNReal BigOperators Topology ContDiff

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-!
# Han–Schlag's Corollary 4.2 (`cor:UPY`) as a `Prop`

`Submission/FUP/Spec.lean` records Han–Schlag's Theorem 5.1 as the only remaining literature
input for Cohen's Theorem 1.1.  This module records the *single-scale* statement that Theorem 5.1
is derived from (Han–Schlag, *A higher-dimensional Bourgain–Dyatlov fractal uncertainty
principle*, Anal. PDE **13** (2020), Corollary 4.2), in the normalisation used by the §5 induction
on scales (`Submission/FUP/HSCellsZ.lean`):

* the "cells" are the cubes `box (2n + γ) (2n + γ + 2)` of side `2` of a translate of the
  `2ℤ`-grid (`γ : ℝᵈ` is the translate, needed because the rescaled `L`-adic grid of depth `mT`
  is `-L^{mT} + 2ℤ`);
* the localisation set `S` is a union of *one* cube `box (a n) (a n + 2c₁)` of side `2c₁` inside
  **each** cell of that grid (one cube per `n ∈ ℤ^d`);
* the hypothesis is the damping of `Y + [-2,2]^d + η` for every `η ∈ [-(α₁+1),α₁+1]^d`;
* the conclusion is the localisation estimate `‖f‖ ≤ C_*‖f·1_S‖`.

**Corrected in Session 52.**  An earlier version of this `Prop` quantified the cubes over an
arbitrary *subset* `T` of cells and was **false** (see `Submission/FUP/ROADMAP.md`, Session 51
§2 and Session 52 §0): a function `f` with Fourier support in a small interval `Y` is
concentrated near the origin, so placing the only cube in a far cell makes the estimate fail.
The published Corollary 4.2 places the cubes in *every* cell, and that is exactly what makes `S` a
valid localisation set for the quantitative Logvinenko–Sereda theorem.  The §5 induction has been
rewired accordingly: its localisation set is `locSetZ` (one cube per cell of the rescaled `L`-adic
grid) and its hole set is `UstarZ` (the half-cubes of *all* empty gen-`(mT+1)` cells), which
contains a cube of side `L^{-1}` in every gen-`mT` cell — by porosity for the cells meeting `X`,
and trivially for the cells that miss it.

The plan (see `Submission/FUP/ROADMAP.md`) is to prove the statement below from the quantitative
Logvinenko–Sereda theorem (`Commons.Analysis.Fourier.LogvinenkoSereda.logvinenko_sereda`), which
replaces Han–Schlag §2–§4 (the quantitative subharmonic-function / Cartan-set / conformal-map
machinery) by an elementary real-variable statement.  Session 51 §1 has the full reduction.

Note on the shape of the statement: Han–Schlag state Corollary 4.2 with the fixed unit lattice
`∏ⱼ [nⱼ, nⱼ+1)`; their proof (modulation by `(2ℤ)^d`, then the `L²`-localisation lemma
`lem:mainlem`) only uses that `S` is a union of one square of side `2c₁ ≤ 1` per cell.  The lattice
may be translated, which is why the statement below records a general translate `γ`.
-/

namespace Submission.FUP

/-- **Han–Schlag's Corollary 4.2 (`cor:UPY`), as the single-scale input of the §5 induction.**

*Fix `c₁ ∈ (0,1/2]`, `c₂, c₃, α`, a translation `γ`, and for **every** integer vector
`n ∈ ℤ^d` a square `I_n ⊆ box (2n+γ) (2n+γ+2)` of side length `2c₁`; put
`S := ⋃_{n∈ℤ^d} I_n`.*  If `Y ⊆ cube (-α₁) α₁` has the property that `Y + [-2,2]^d + η` admits an
`ℓ₁` damping function with band radius `c₁/2` (parameters `c₁/2, c₂, c₃, α`) for every
`η ∈ [-(α₁+1), α₁+1]^d`, then every `f ∈ L²` with `supp f̂ ⊆ Y` satisfies
`‖f‖ ≤ C_* ‖f·1_S‖`, with `C_*` depending only on `d, c₁, c₂, c₃, α`.

**The factor `1/2` on the damping parameter (Session 53).**  In the published Corollary 4.2 the
parameter `c₁` plays a double role: it is both the half-side of the localisation squares `I_n` and
the support radius of the damping kernel `ψ` (in our convention: `supp 𝓕ψ ⊆ cube(-c₁,c₁)`, so that
the kernel `𝓕⁻¹ψ` is supported in `cube(-c₁,c₁)`).  The proof (Lemma 4.3 of the paper) needs the
*convolution with the kernel to be supported inside `I_n`*: for `x` in a square `I'_n` of half-side
`t` concentric with `I_n` one has `1_{S'} g = 1_{S'}((1_S f) * ψ)` only if `t + c₁ ≤ c₁`, i.e. only
for `t = 0`.  The published proof is off by this constant (it takes `t = c₁/2` with `r = c₁`), and
the repair is to use a kernel of support radius *strictly* smaller than the square half-side: with
`supp ψ ⊆ cube (-c₁/2, c₁/2)` the paper's `S'` (half-side `c₁/2`) works, since
`c₁/2 + c₁/2 = c₁`.  Hence the damping parameter below is `c₁/2`.  This is a harmless weakening of
the hypothesis: the chain supplies it (`Submission/FUP/HanSchlagComparison.lean`, where the
damping parameter `(4L)⁻¹` is obtained from the `ℓ₂` damping parameter `ν/(20√d) ≤ (4L)⁻¹`).

**The cubes are placed in every cell of the grid** — this is essential (Session 52): an arbitrary
*selection* of cells makes the statement false (`Submission/FUP/ROADMAP.md`, Sessions 51 §2 and
52), while the full grid is exactly what makes `S` a valid localisation set for the quantitative
Logvinenko–Sereda theorem.  The induction then applies the statement to the hole set
`U_{mT+1}` (the half-cubes of *all* empty gen-`(mT+1)` cells), which contains a cube of side
`L^{-1}` in every gen-`(mT)` cell (porosity in the cells meeting `X`, trivially otherwise). -/
def LocalizationStatement : Prop :=
  ∃ cstar : ℝ, 0 < cstar ∧
    ∀ (c₁ : ℝ), 0 < c₁ → c₁ ≤ 1 / 2 →
      ∀ (c₂ : ℝ), c₂ ∈ Set.Ioo 0 1 → ∀ (c₃ : ℝ), c₃ ∈ Set.Ioo 0 cstar →
        ∀ (α : ℝ), α ∈ Set.Ioo 0 1 →
          ∃ Cstar : ℝ, 0 < Cstar ∧
            ∀ (α₁ : ℝ), 1 ≤ α₁ → ∀ (γ : ℝᵈ) (Y : Set ℝᵈ),
              Y ⊆ cube (-α₁) α₁ →
              (∀ η : ℝᵈ, (∀ i : Fin d, η i ∈ Set.Icc (-(α₁ + 1)) (α₁ + 1)) →
                AdmitsL1Damping ((fun z : ℝᵈ => η + z) '' (addSet Y (cube (-2) 2)))
                  (c₁ / 2) c₂ c₃ α) →
              ∀ (a : (Fin d → ℤ) → (Fin d → ℝ)),
                (∀ n : Fin d → ℤ, ∀ i : Fin d,
                  2 * (n i : ℝ) + γ i ≤ a n i ∧ a n i + 2 * c₁ ≤ 2 * (n i : ℝ) + γ i + 2) →
                ∀ (f : Lp ℂ 2 (volume : Measure ℝᵈ)),
                  (∀ᵐ ξ ∂(volume : Measure ℝᵈ),
                      ((𝓕 f : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ ≠ 0 → ξ ∈ Y) →
                  ‖f‖ ≤ Cstar * (eLpNorm
                    ((⋃ n : Fin d → ℤ, box (a n) (fun i => a n i + 2 * c₁)).indicator
                      (f : ℝᵈ → ℂ)) 2 (volume : Measure ℝᵈ)).toReal

end Submission.FUP
