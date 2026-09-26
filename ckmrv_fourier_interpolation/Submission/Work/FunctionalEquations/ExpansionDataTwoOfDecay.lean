import Mathlib
import Submission.Work.FunctionalEquations.Gap
import Submission.Work.FunctionalEquations.ExpansionData
import Submission.Work.FunctionalEquations.SummableExpansionTerms
import Submission.Work.FunctionalEquations.BasisCoeffsDeltaAux
import Submission.Work.FunctionalEquations.ExpansionDataShiftTwo
import Submission.Work.FunctionalEquations.CoeffOneZeroOfDecay

/-!
# The Leech case: the expansions restart at `m = 2` under the decay hypothesis

`Work.FE.ExpansionData n S basis` expresses `F` and `F̃` as Dirichlet series in `τ` with
coefficients `a_m`, `ã_m`, `b_m`, `b̃_m` indexed from `m ≥ 1`, together with the termwise
radial differentiability of those expansions and polynomial growth of the radial
seminorms.  `Work.FE.TendsToZeroInStrip n 1 S.F` says that `F` is `o(e^{-2π Im τ})` in the
strip `-1 ≤ Re τ ≤ 1` (and likewise for `F̃`).

The decay hypothesis forces the `m = 1` coefficients to vanish: the `m = 1` term of the
expansion is `(a_1 + 2π i τ b_1) e^{2π i τ}`, whose modulus is
`|a_1 + 2π i τ b_1| e^{-2π Im τ}`, while `a_1 + 2π i τ b_1` is a nonzero affine function
of `τ` unless `a_1 = b_1 = 0`.  That analytic step is
`Work.FE.CoeffOneZeroOfDecay`, applied to `F` and to `F̃` (with the rate-weighted
coefficients `b_m`).  Once the four coefficients at `m = 1` vanish, restricting the
coefficient families to the index set `m ≥ 2` gives
`Work.FE.ExpansionDataGen n 2 S basis₂` (`Work.FE.ExpansionDataShiftTwo`), which is the
form in which the Leech-lattice case of the CKMRV interpolation theorem is applied
(`Work.FE.interpolationBasis_two_of_rigidity_and_decay`).
-/

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

/-! ### The main theorem -/

/-- **Decay in the strip turns `ExpansionData` into `ExpansionDataGen n 2`.**
If the generating functions of an `ExpansionData` solution decay like `o(e^{-2π Im τ})`
in the strip `-1 ≤ Re τ ≤ 1`, then the `m = 1` coefficients `a_1, b_1, ã_1, b̃_1` vanish
and the same expansions hold with the sums restricted to `m ≥ 2`, with
`basis₂ (m, j) = basis ((m : ℕ), j)`. -/
theorem ExpansionDataTwoOfDecay {n : ℕ} [NeZero n] (S : FunctionalEquationSolution n)
    (basis : SampleIdx 1 → RSch n) (hExp : ExpansionData n S basis)
    (hdec : TendsToZeroInStrip n 1 S.F) (hdecT : TendsToZeroInStrip n 1 S.Ftilde) :
    ∃ basis₂ : SampleIdx 2 → RSch n, ExpansionDataGen n 2 S basis₂ := by
  obtain ⟨hF, hFt, hdF, hdFt, hgrow⟩ := hExp
  -- polynomial growth of the coefficients, from the growth field at `k = ℓ = 0`
  obtain ⟨C, N, hC, hg⟩ := hgrow 0 0
  have hval : ∀ (j : Fin 4) (m : Set.Ici 1) (y : E n),
      ‖(basis (m, j)).1 y‖ ≤ C * ((m.1 : ℝ) + 1) ^ N := by
    intro j m y
    have hy := hg m j y
    simp only [pow_zero, one_mul] at hy
    have hrad : radialDeriv 0 (⇑(basis (m, j)).1) y = (basis (m, j)).1 y := by
      simp only [radialDeriv, iteratedDeriv_zero]
      exact (basis (m, j)).2 _ _ (by
        rw [Work.Sampling.realIncl_norm, abs_of_nonneg (norm_nonneg y)])
    rwa [hrad] at hy
  have hval' : ∀ (j : Fin 4) (m : Set.Ici 1) (y : E n),
      ‖(basis (m, j)).1 y‖ ≤ C * ((m.1 : ℝ) + 1) ^ (N + 1) := by
    intro j m y
    refine le_trans (hval j m y) ?_
    refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ?_ (Nat.le_succ N)) hC
    have : (0 : ℝ) ≤ (m.1 : ℝ) := Nat.cast_nonneg _
    linarith
  have hrate : ∀ (j : Fin 4) (m : Set.Ici 1) (y : E n),
      ‖(rate m.1 : ℂ) * (basis (m, j)).1 y‖ ≤ C * ((m.1 : ℝ) + 1) ^ (N + 1) := by
    intro j m y
    have hm0 : (0 : ℝ) ≤ (m.1 : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (m.1 : ℝ) := Nat.cast_nonneg _
      linarith
    rw [norm_mul, Complex.norm_real, rate, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    calc rate m.1 * ‖(basis (m, j)).1 y‖
        ≤ ((m.1 : ℝ) + 1) * (C * ((m.1 : ℝ) + 1) ^ N) :=
          mul_le_mul (rate_le_add_one m.1) (hval j m y) (norm_nonneg _) hm0
      _ = C * ((m.1 : ℝ) + 1) ^ (N + 1) := by rw [pow_succ]; ring
  -- the four coefficients at `m = 1` vanish
  have hvanish : ∀ (j : Fin 4) (x : E n), (basis (⟨1, by simp⟩, j)).1 x = 0 := by
    intro j x
    obtain ⟨φ, hφ0, hφ⟩ := hdec x
    obtain ⟨φt, hφt0, hφt⟩ := hdecT x
    have hbound : ∀ τ : ℂ, 0 < τ.im → -1 ≤ τ.re → τ.re ≤ 1 →
        ‖S.F τ x‖ ≤ φ τ.im * Real.exp (-(2 * Real.pi * τ.im)) := by
      intro τ hτ h1 h2
      simpa using hφ τ hτ h1 h2
    have hboundt : ∀ τ : ℂ, 0 < τ.im → -1 ≤ τ.re → τ.re ≤ 1 →
        ‖S.Ftilde τ x‖ ≤ φt τ.im * Real.exp (-(2 * Real.pi * τ.im)) := by
      intro τ hτ h1 h2
      simpa using hφt τ hτ h1 h2
    have hA := CoeffOneZeroOfDecay (F := fun τ => S.F τ x)
        (a := fun m : Set.Ici 1 => (basis (m, 0)).1 x)
        (b := fun m : Set.Ici 1 => (rate m.1 : ℂ) * (basis (m, 2)).1 x)
        (C := C) (N := N + 1) (ψ := φ) hC hφ0
        (fun m => hval' 0 m x) (fun m => hrate 2 m x)
        (fun τ hτ => hF τ x hτ) hbound
    have hB := CoeffOneZeroOfDecay (F := fun τ => S.Ftilde τ x)
        (a := fun m : Set.Ici 1 => (basis (m, 1)).1 x)
        (b := fun m : Set.Ici 1 => (rate m.1 : ℂ) * (basis (m, 3)).1 x)
        (C := C) (N := N + 1) (ψ := φt) hC hφt0
        (fun m => hval' 1 m x) (fun m => hrate 3 m x)
        (fun τ hτ => hFt τ x hτ) hboundt
    fin_cases j
    · exact hA.1
    · exact hB.1
    · exact (mul_eq_zero.mp hA.2).resolve_left (BasisDelta.rate_ne_zero 1 (by norm_num))
    · exact (mul_eq_zero.mp hB.2).resolve_left (BasisDelta.rate_ne_zero 1 (by norm_num))
  exact ExpansionDataShiftTwo S basis ⟨hF, hFt, hdF, hdFt, hgrow⟩ hvanish

end Work.FunctionalEquations
