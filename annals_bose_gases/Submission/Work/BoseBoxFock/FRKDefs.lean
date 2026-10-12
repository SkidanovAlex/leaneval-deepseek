import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.KinRowQuant
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.FRKDefs` — the vocabulary of the W-route (window-flatness kinetic row)

`LEAD_DESIGN_formrowkin.md` (2026-10-09) replaces the *false* sharp sampling row `(T)` by the
W-route: the alias of the smoothed kinetic symbol is paid by the **unwindowed** mean-free mass
`G = gapBare ℓ 0 ψ`, using the flatness of the corpus window `χ_Λ` at the sphere.  Its leaves are

* `W0 chiLam_le_cubic_flat` (dispatched, `BoseBoxFock/chiLam_le_cubic_flat`);
* `W1 lattice_symbol_eq_alias`  — polarised Parseval on the cell;
* `W2 norm_symOp_le_of_dist`    — the kernel decay estimate `|z|⁻⁶` (this file's target);
* `W3 windowAlias_le`           — W0 + W1 + W2 against `gapBare`;
* `W4 tauSm_admissible`         — `‖D⁶ tauSm‖₁ ≤ K₆ (2sℓ)`.

The statements of W1–W4 live only in the designer's environment
(`cbc/bose_formrowkin_stmts.lean`, namespace `FRK`); this file fixes the two *definitions* the
route needs so that the leaves can be stated and dispatched inside this workspace:

* `symOp σ g x = (2π)⁻³ ∫_p e^{i⟪p,x⟫} σ(p) ĝ(p) dp` — the (inverse) Fourier multiplier
  `σ(√−Δ)` applied to `g`, in the `p`-convention of `Submission.BoseGases.kinFT`;
* `iterDerivL1 n σ = ∫_p ‖Dⁿ σ(p)‖` — the `L¹`-norm of the `n`-th iterated derivative
  (`n = 6` is the design's `‖D⁶σ‖₁`).

All the leaves are TRUE as stated (design §2(b) and `REVIEW_formrowkin.md` §(c)); W1 additionally
needs the reviewer's extra hypothesis that `D⁶σ` is integrable.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The Fourier multiplier `σ(√−Δ)`: `symOp σ g x = (2π)⁻³ ∫ e^{i⟪p,x⟫} σ p ĝ(p) dp`. -/
noncomputable def symOp (σ : E3 → ℝ) (g : E3 → ℂ) : E3 → ℂ :=
  fun x => (((2 * Real.pi) ^ 3)⁻¹ : ℝ) *
    ∫ p : E3, Complex.exp (Complex.I * (inner ℝ p x : ℂ)) * (σ p : ℂ) *
      Submission.BoseGases.kinFT g p

/-- The `L¹`-norm of the `n`-th iterated derivative of `σ` (the design's `‖Dⁿσ‖₁`). -/
noncomputable def iterDerivL1 (n : ℕ) (σ : E3 → ℝ) : ℝ :=
  ∫ p : E3, ‖iteratedFDeriv ℝ n σ p‖

end Work.BoseBoxFock
