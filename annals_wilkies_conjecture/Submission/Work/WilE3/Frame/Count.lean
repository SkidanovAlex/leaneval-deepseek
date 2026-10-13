/-
  annals_wilkies_conjecture, AREA E3, the *count* half of the frame step: order ≤ multiplicity.

  This file is the roadmap (and the shared vocabulary) for the second half of
  `Work.WilE3.Identity.E3_identity_proved_of_multiplicity`, mirroring `NOTES.md` §3 step 3.

  ## The two halves

  *Frame half* (`WilE3/Frame/partial_curve_eq_Vword`, `Vword_toC_eq_zero`): if all ordered reduced
  derivatives `opMono c h ι m f` (`m` supported off `ι`) of order `≤ M` vanish at `x`, then all
  ordered frame derivatives of `f` at `x` vanish, and (`partial_curve_eq_Vword`) those are the mixed
  derivatives of the curve function `u ↦ f (Ψ (u|_ιᶜ, 0))`; so by `iteratedDeriv_line_eq_zero` every
  derivative of `t ↦ eaEvalC c f (Ψ (u₀ + t w, 0))` of order `≤ M` vanishes at `0`.

  *Count half* (this file): if that one-variable function has finite order `N` at `0`, then
  `N ≤ M0.eval (Σ_a atomDeg (h a) + atomDeg f) + 3 F`.  Indeed, the `N` simple solutions `t_i` of
  `eaEvalC c f (Ψ (u₀ + t w, 0)) = ε` supplied by
  `Work.WilE3.Frame.exists_card_solutions_simple_tendsto` give `N` zeros `z_i = Ψ (u₀ + t_i w, 0)`
  of the complexified system `(h, L, f - ε)`, where `L` is built from `k - j - 1` real affine forms
  `cutPoly μ x` through `x` annihilating `w` (`exists_cut_forms`).  The `z_i` are *nondegenerate*
  (`curve_zero_isNondeg`, below) and convergence `z_i → x` gives a shrinking ball, so
  `Work.WilE3.MultiplicityBound` bounds `N` by `M0.eval` of the degree sum of `(h, L, f - ε)`; the
  degree sum is `Σ_a atomDeg (h a) + Σ_j atomDeg (L j) + atomDeg f + k` with every `atomDeg (L j) ≤ 2`,
  i.e. at most `Σ_a atomDeg (h a) + atomDeg f + 3 F` (`k + r ≤ F`), and `polynomial_eval_le_eval`
  (`Identity/E3_identity_proved_of_multiplicity.lean`) absorbs the slack.

  Contradiction (`N ≥ M + 1` and `N ≤ M`) forces `f|_{{h = 0}} ≡ 0` near `x`; the branch where the
  curve function vanishes identically for *every* direction `w` is `eq_zero_of_all_lines`.

  ## Remaining pieces (not yet formalised, statements to be written)

  * `curve_zero_isNondeg`: for `t` with `deriv (fun t' => eaEvalC c f (Ψ (u₀ + t' w, 0))) t ≠ 0`, the
    `k × k` matrix with rows `∂h_a (z)`, `∂(cutPoly μ_j x) (z)`, `∂f (z)` at `z = Ψ (u₀ + t w, 0)` is
    invertible: its first `k - 1` rows have one-dimensional common kernel — at `x` by
    `exists_cut_forms` + the frame identity (`Vcoef.lean`), nearby by continuity — which contains the
    non-zero curve tangent (`fderiv_curve_eq_VcoefC`), and `∂f` is non-zero on it by simplicity.
    `det_ne_zero_of_kernel` (contrapositive of `Matrix.exists_mulVec_eq_zero_iff`) concludes.

  * `order_le_multiplicity`: the assembly of the counting lemma with the two preceding items and with
    `MultiplicityBound`, including the shrinking-ball bookkeeping `ρ ε := max_i ‖z_i - x‖ + ‖ε‖`
    (using the `∀ᶠ`-clause of `exists_card_solutions_simple_tendsto` for `ρ ε → 0`).
-/
import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.WilE3.Frame.Setup
import Submission.Work.WilE3.Frame.Vcoef

namespace Work.WilE3.Frame

set_option autoImplicit false
noncomputable section
open Classical Topology Matrix
open WilkiesDesign.E

variable {k r j : ℕ}

/-- The real affine form through `x` whose direction is `μ` in the `ι`-complement coordinates:
`Σ_i μ i · (y_i - x_i)` (only the `ι^c`-coordinates occur). -/
def cutPoly (ι : Fin j → Fin k) (μ : U k ι → ℝ) (x : Fin k → ℝ) : EAPoly k r :=
  ∑ i : U k ι, MvPolynomial.C (μ i) *
    (MvPolynomial.X (Sum.inl i.1) - MvPolynomial.C (x i.1))

/-- The cut form vanishes at `x`. -/
theorem eaEval_cutPoly_self (c : EAChain k r) (ι : Fin j → Fin k) (μ : U k ι → ℝ)
    (x : Fin k → ℝ) : eaEval c (cutPoly ι μ x) x = 0 := by
  simp only [cutPoly, eaEval, map_sum, map_mul, map_sub, MvPolynomial.eval_C,
    MvPolynomial.eval_X]
  simp

end

end Work.WilE3.Frame
