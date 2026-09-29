import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_re_upper
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_re_pole

noncomputable section

namespace Commons.NumberTheory.Zeta

/-!
# Real-part bounds for the logarithmic derivative of ζ

The two standard bounds on `Re(−ζ′/ζ(σ+i·t))` for `1 < σ ≤ 2` and large `|t|`:

1. **away from zeros** — the real part is `O(log(|t|+3))` uniformly in the
   strip `1 < σ ≤ 2`
   (`Commons.NumberTheory.Zeta.zeta_logDeriv_re_upper`); and

2. **immediately above a hypothetical zero `ρ = β+i·t`** (`β ∈ [1/2, 1)`) — the
   contribution `−1/(x + (1−β))` of the pole of `ζ′/ζ` at `ρ` is displayed
   explicitly, with the same `O(log(|t|+3))` error
   (`Commons.NumberTheory.Zeta.zeta_logDeriv_re_pole`).

This file only merges the two estimates into one statement with a common
constant `C` and common height `H` (take `C = C₁+C₂`, `H = max H₁ H₂`).
-/

/-- The logarithmic derivative of ζ at a point of the half-plane `Re s > 1` has real
part bounded above by `C·(log(|t|+3)+1)` uniformly in the strip `1 < σ ≤ 2`; and
directly above a zero `β+i·t` of ζ (`β ∈ [1/2,1)`) the pole contribution
`−1/(x+(1−β))` of `Re(−ζ′/ζ(1+x+i·t))` is made explicit. -/
theorem zeta_logDeriv_re_bounds :
    ∃ C : ℝ, 0 < C ∧ ∃ H : ℝ, (2 : ℝ) ≤ H ∧
      (∀ t : ℝ, H ≤ |t| → ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
        (-deriv riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I)) /
            riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I))).re ≤
          C * (Real.log (|t| + 3) + 1)) ∧
      (∀ t : ℝ, H ≤ |t| → ∀ β : ℝ, (1 / 2 : ℝ) ≤ β → β < 1 →
        riemannZeta (((β : ℂ) + (t : ℂ) * Complex.I)) = 0 →
        ∀ x : ℝ, 0 < x → x ≤ 1 / 2 →
        (-deriv riemannZeta ((((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I)) /
            riemannZeta ((((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I))).re ≤
          - (1 / (x + (1 - β))) + C * (Real.log (|t| + 3) + 1)) := by
  rcases zeta_logDeriv_re_upper with ⟨C1, hC1pos, H1, hH1, hUp⟩
  rcases zeta_logDeriv_re_pole with ⟨C2, hC2pos, H2, hH2, hPo⟩
  refine ⟨C1 + C2, add_pos hC1pos hC2pos, max H1 H2, ?_, ?_, ?_⟩
  · exact le_max_of_le_left hH1
  · intro t ht σ hσ1 hσ2
    have hL0 : (0 : ℝ) ≤ Real.log (|t| + 3) + 1 := by
      have h13 : (1 : ℝ) ≤ |t| + 3 := by nlinarith [abs_nonneg t]
      have hlg : 0 ≤ Real.log (|t| + 3) := Real.log_nonneg h13
      linarith
    have ht1 : H1 ≤ |t| := le_trans (le_max_left H1 H2) ht
    calc
      (-deriv riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I)) /
          riemannZeta (((σ : ℂ) + (t : ℂ) * Complex.I))).re ≤
          C1 * (Real.log (|t| + 3) + 1) := hUp t ht1 σ hσ1 hσ2
      _ ≤ (C1 + C2) * (Real.log (|t| + 3) + 1) := by
        nlinarith
  · intro t ht β hβlo hβ1 hζ x hx0 hx12
    have hL0 : (0 : ℝ) ≤ Real.log (|t| + 3) + 1 := by
      have h13 : (1 : ℝ) ≤ |t| + 3 := by nlinarith [abs_nonneg t]
      have hlg : 0 ≤ Real.log (|t| + 3) := Real.log_nonneg h13
      linarith
    have ht2 : H2 ≤ |t| := le_trans (le_max_right H1 H2) ht
    calc
      (-deriv riemannZeta ((((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I)) /
          riemannZeta ((((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I))).re ≤
          - (1 / (x + (1 - β))) + C2 * (Real.log (|t| + 3) + 1) :=
            hPo t ht2 β hβlo hβ1 hζ x hx0 hx12
      _ ≤ - (1 / (x + (1 - β))) + (C1 + C2) * (Real.log (|t| + 3) + 1) := by
        nlinarith

end Commons.NumberTheory.Zeta
