/-
# The nonvanishing threshold for `P'`

`Work.KMTPlan.A6.PderivR P x = P'(x)` is the derivative of the integer polynomial `P` evaluated at
the real point `x`.  The paper (Krause--Mirek--Tao, §6) integrates by parts with the primitive
`t ↦ Φ(t) / (2π i ξ₂ P'(Nt))`, which requires `P'(Nt) ≠ 0` on the window `t ∈ [1/2, 1]` for all
sufficiently large `N`.  This module supplies exactly that: for a polynomial `P` of degree at least
`2` (so that `P'` is a nonzero real polynomial, whose zero set is finite and hence bounded above)
there is a threshold `B > 0` with `P'(N t) ≠ 0` whenever `N ≥ B` and `t ∈ [1/2, 1]`.

The only ingredients are `Polynomial.derivative_ne_zero` (a polynomial of positive degree over a
domain has nonzero derivative), injectivity of the coefficient extension `ℤ[X] → ℝ[X]`, and
`Polynomial.exists_max_root` (the real roots of a nonzero real polynomial are bounded above).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlDefs

namespace Work.KMTPlan.A6

theorem PderivThreshold (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) :
    ∃ B : ℝ, 0 < B ∧ ∀ (N : ℕ) (t : ℝ), B ≤ (N : ℝ) → t ∈ Set.Icc (1 / 2 : ℝ) 1 →
      Work.KMTPlan.A6.PderivR P ((N : ℝ) * t) ≠ 0 := by
  -- `P'` is a nonzero polynomial, because `P` has positive degree.
  have hP' : P.derivative ≠ 0 := by
    rw [Polynomial.derivative_ne_zero]
    omega
  -- Its extension to `ℝ[X]` (which is what `PderivR P` evaluates) is nonzero as well.
  have hinj : Function.Injective (⇑(Int.castRingHom ℝ) : ℤ → ℝ) := Int.cast_injective
  have hQ : P.derivative.map (Int.castRingHom ℝ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff hinj).mpr hP'
  -- its real roots are bounded above by some `x₀`.
  obtain ⟨x₀, hx₀⟩ := Polynomial.exists_max_root (P.derivative.map (Int.castRingHom ℝ)) hQ
  -- the threshold `2 * (max x₀ 0 + 1)`: then `N t ≥ N/2 ≥ max x₀ 0 + 1 > x₀`.
  refine ⟨2 * (max x₀ 0 + 1), by
    have : (0 : ℝ) ≤ max x₀ 0 := le_max_right _ _
    linarith, ?_⟩
  intro N t hN ht h0
  have hroot : (P.derivative.map (Int.castRingHom ℝ)).IsRoot ((N : ℝ) * t) := by
    simpa [Polynomial.IsRoot, Work.KMTPlan.A6.PderivR] using h0
  have hle : (N : ℝ) * t ≤ x₀ := hx₀ _ hroot
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hB2 : (max x₀ 0 + 1) ≤ (N : ℝ) * (1 / 2) := by
    have : 2 * (max x₀ 0 + 1) ≤ (N : ℝ) := hN
    linarith
  have hNt : (N : ℝ) * (1 / 2) ≤ (N : ℝ) * t := mul_le_mul_of_nonneg_left ht.1 hN0
  have hx0lt : x₀ < max x₀ 0 + 1 := by
    have : x₀ ≤ max x₀ 0 := le_max_left _ _
    linarith
  linarith

end Work.KMTPlan.A6
