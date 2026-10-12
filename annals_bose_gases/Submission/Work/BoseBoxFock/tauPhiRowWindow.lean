import Mathlib.Analysis.Calculus.ContDiff.Defs
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
# `Work.BoseBoxFock.tauPhiRowWindow` — the `χ_Λ`-windowed form of the lattice/continuum row

This is the *windowed* companion of `Work.BoseBoxFock.tauPhi_row` (the target of the neighbouring
file): the same inequality, but for states of the corpus's windowed class
`g = χ_Λ·h` (`χ_Λ = corpusBox.chiLam ℓ`, `tsupport h ⊆ boxL ℓ`) — the class in which the whole
`deficitAlias_*` machinery (`kinFirst_sub_latMoment_eq_imageSplit`,
`deficitAlias_touching_image_le`, `deficitAlias_far_image_le`,
`deficitAlias_shiftstab`, `freeDirichletBall_complex`) is available and *proved*.

## Why this is the right piece, and why the general target follows from it

Two facts (both recorded in `FINDING_tauPhi_row.md` and `FINDING_tauPhi_row_window.md`):

1. **The full row follows from the windowed row** (the *lift*, done by the reduction, not by
   approximation in the end — see (★) below: the windowed row and the full row are *equivalent* to
   the same sharp criterion, and the criterion does not see the class): for every state
   `g` of the target's class and every `m`, the product `g_m := η_m·g` with `η_m` a smooth bump
   `≡ 1` on `ball 0 (ℓ/2 − 1/m)`, `tsupport η_m ⊆ ball 0 (ℓ/2)`, lies in the windowed class
   (`η_m·g = χ_Λ·(η_m·g/χ_Λ)`, using `0 < χ_Λ` on `ball 0 (ℓ/2)`), and `g_m → g` in `H¹` and
   `ĝ_m → ĝ` *uniformly* on the lattice (indeed `‖ĝ_m − ĝ‖_∞ ≤ ‖g_m − g‖₁ → 0`).  Fatou for the
   nonnegative lattice sum plus the continuity of the continuum form in `H¹` then transfers the
   row to `g`.
2. **The sharp-symbol content.**  Writing `L(h) = Σ_n ℓ⁻³h(‖k_n‖)‖ĝ(k_n)‖²`,
   `C(h) = (2π)⁻³∫h(‖p‖)‖ĝ(p)‖²dp`, `ν = L − C`, `D = C(‖·‖) − L(‖·‖)`, `Θ_c = (c−·)₊²`,
   `δ_c = [·−c]₊² − τ̃_c ≥ 0` and `Σ = δ_c − (c·r − (5/4+C₀)c²) ≥ 0` (supported in frequency on
   `r ≤ 2c`), the windowed row is **equivalent** (via the proved moment identities
   `L(1) = C(1)`, `L((·)²) = C((·)²)`) to

       (★)   L(δ_c) + ν(Θ_c) ≥ 2·c·D ,
       (★★)  c·(3L(‖·‖) − 2C(‖·‖)) + L(Σ) + ν(Θ_c) ≥ (5/4 + C₀)·c²·L(1) ,

   where `C₀ = tauPhiC0 = ∫t²K`.  The *sharp-symbol aliasing inequality* to be proved is the
   statement that the **deficit pays the aliasing deficit exactly**: `C(δ_c) + ν(Σ) + ν(Θ_c) ≥ 3cD`
   — `C(δ_c)` is the payer, `ν(Σ)` is provably tiny (Schwarz kernel at scale `1/c`), and `ν(Θ_c)`
   is the *low-frequency lattice gain* that decides the spread regime.

## Acceptance test (recorded, from the FINDING)

The extremal family is `g = e^{iq₀·x}·(R²−r²)⁶_+` (`ℓ = 1`, `c = 4π`, `q₀ = (kπ,kπ,kπ)`,
‖q₀‖ ≫ c), for which the *row* ratio is `→ 1` from below with the exact asymptotic

    ratio = 1 − c/‖q₀‖   (checked: ‖q₀‖ = 114, 136, 190, 245, 299 give
                          1 − ratio = 0.119, 0.0988, 0.0693, 0.0533, 0.0433; gap·‖q₀‖ = 13.6, 13.4,
                          13.2, 13.0 → c = 4π = 12.57),

matching the *pointwise* ratio `τ̃_c(r)/F_c(r) = (r−3c/2)²/(r−c)² → 1 − c/r`.  So (★) is *sharp*
but not violated; any proof may lose a small factor in the *spread* regime but nothing in the
cancellation of `(★★)`.  (Warning: `L(τ̃_c)` converges only conditionally for states of finite
smoothness — use `C^∞` states for numerics.)
-/

noncomputable section

open scoped Real BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

/-- **The `χ_Λ`-windowed lattice/continuum row** — the piece the fleet can attack with the *proved*
`deficitAlias_*` machinery, from which the general target follows (see the module docstring).
The class hypothesis is copied verbatim from `Work.BoseBoxFock.deficitAlias_shiftstab`. -/
theorem tauPhiRowWindow {ℓ c : ℝ} (hℓ : 0 < ℓ) (hc : 0 < c) (hcℓ : 4 * Real.pi ≤ c * ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hg : ∃ h : EuclideanSpace ℝ (Fin 3) → ℂ, ContDiff ℝ (⊤ : ENat) h ∧ HasCompactSupport h ∧
        tsupport h ⊆ Work.BoseK15.corpusBox.boxL ℓ ∧
        (∀ z, g z = ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) * h z)) :
    (∑' n : Fin 3 → ℤ, (ℓ ^ 3)⁻¹ *
        (c ^ 2 * Work.BoseBoxFock.tauPhi (‖Work.BoseBoxFock.kmomInt ℓ n‖ / c)) *
        ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ *
        (∫ p : EuclideanSpace ℝ (Fin 3),
          Submission.BoseGases.fsKinCoeff c ‖p‖ * ‖Submission.BoseGases.kinFT g p‖ ^ 2) := by
  sorry

end Work.BoseBoxFock
