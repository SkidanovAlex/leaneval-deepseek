import Mathlib
import Submission.Work.A3.dirichlet_approx_of_not_mem_majorArcSet
import Submission.Work.A3.bracket_le_of_majorGap

/-!
# The minor-arc pointwise bound for the polynomial exponential sum (Area A3)

If `θ` is **not** in the major arcs `Work.A3.majorArcSet Q N η` (the neighbourhoods of radius
`1/(q N^{d/2})`, `d = deg Q`, of the reduced fractions `a/q` with `q ≤ N^η`), then Dirichlet's
approximation theorem at level `N^{d/2}` produces a reduced `a/q` with

  `N^η < q ≤ N^{d/2}`  and  `|θ - a/q| ≤ 1/q²`,

so that Weyl's inequality `hweyl` applies; every term of the Weyl bracket is then at most
`N^{-η}`, and since the bracket is raised to the power `δ = 2^{1-d}` this yields the pointwise
power saving

  `‖S_N(θ)‖ ≤ (CW · 3^δ) · N^{1 + ε - ηδ}`,  `S_N = Work.A3.expSum Q N`.

This is the input to the minor-arc contribution of the circle method
(`Work.A3.minorArc_contribution`).

The two ingredients are proved in the sibling modules
`Work.A3.dirichlet_approx_of_not_mem_majorArcSet` (the Dirichlet step, i.e. the fact that the
outside of the major arcs is where the Dirichlet denominator is `> N^η`) and
`Work.A3.bracket_le_of_majorGap` (the elementary estimate for the three terms of the bracket).
-/

set_option autoImplicit false

namespace Work.A3

/-- **Pointwise Weyl saving off the major arcs.**  From Weyl's inequality under a Dirichlet
approximation `|θ - a/q| ≤ 1/q²` (`hweyl`, the conclusion of `Work.A3.weyl_poly`) we deduce the
power saving `‖S_N(θ)‖ ≤ (CW · 3^δ) N^{1 + ε - ηδ}`, `δ = 2^{1-d}`, for every `θ` outside the
major arcs at level `η`. -/
theorem norm_expSum_le_of_not_mem_majorArcSet (Q : Polynomial ℤ) (hd : 2 ≤ Polynomial.natDegree Q)
    {CW ε η : ℝ} (hCW : 0 < CW) (hε : 0 < ε) (hη : 0 < η) (hη1 : η ≤ 1)
    (hweyl : ∀ (M : ℕ) (a q : ℤ) (θ : ℝ), 1 ≤ M → 1 ≤ q → IsCoprime a q →
      |θ - (a : ℝ) / (q : ℝ)| ≤ 1 / ((q : ℝ) ^ 2) →
      ‖Work.A3.expSum Q M θ‖ ≤ CW * (M : ℝ) ^ (1 + ε) *
        (((q : ℝ)⁻¹ + (M : ℝ)⁻¹ + (q : ℝ) * (M : ℝ) ^ (-((Polynomial.natDegree Q : ℤ))))
          ^ ((1 : ℝ) / (2 : ℝ) ^ (Polynomial.natDegree Q - 1))))
    {N : ℕ} (hN : 1 ≤ N) {θ : ℝ} (hθ : θ ∉ Work.A3.majorArcSet Q N η) :
    ‖Work.A3.expSum Q N θ‖ ≤ (CW * (3 : ℝ) ^ ((1 : ℝ) / (2 : ℝ) ^ (Polynomial.natDegree Q - 1)))
      * (N : ℝ) ^ (1 + ε - η * ((1 : ℝ) / (2 : ℝ) ^ (Polynomial.natDegree Q - 1))) := by
  -- abbreviate the exponent `δ = 2^{1-d}`
  set e : ℝ := (1 : ℝ) / (2 : ℝ) ^ (Polynomial.natDegree Q - 1) with he
  -- Dirichlet's theorem off the major arcs
  obtain ⟨q, hq1, hqden_le, hqgt, herr, hcop⟩ :=
    dirichlet_approx_of_not_mem_majorArcSet Q hN hθ
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hqh : (1 : ℤ) ≤ (q.den : ℤ) := by exact_mod_cast hq1
  -- Weyl's inequality applies to the Dirichlet approximation
  have hW := hweyl N q.num (q.den : ℤ) θ hN hqh hcop (by simpa using herr)
  have hW' : ‖Work.A3.expSum Q N θ‖ ≤ CW * (N : ℝ) ^ (1 + ε) *
      (((q.den : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q.den : ℝ) * (N : ℝ) ^ (-((Polynomial.natDegree Q : ℤ))))
        ^ e) := by
    simpa only [he, Int.cast_natCast] using hW
  -- the bracket is at most `3 N^{-η}`
  have hx1 : (1 : ℝ) ≤ (q.den : ℝ) := by exact_mod_cast hq1
  have hbracket : (((q.den : ℝ)⁻¹ + (N : ℝ)⁻¹
      + (q.den : ℝ) * (N : ℝ) ^ (-((Polynomial.natDegree Q : ℤ)))) ^ e)
      ≤ (3 : ℝ) ^ e * (N : ℝ) ^ (-(η * e)) := by
    simpa only [← he] using bracket_le_of_majorGap hd hη hη1 hN hx1 hqden_le hqgt
  calc ‖Work.A3.expSum Q N θ‖
      ≤ CW * (N : ℝ) ^ (1 + ε) *
        (((q.den : ℝ)⁻¹ + (N : ℝ)⁻¹ + (q.den : ℝ) * (N : ℝ) ^ (-((Polynomial.natDegree Q : ℤ))))
          ^ e) := hW'
    _ ≤ CW * (N : ℝ) ^ (1 + ε) * ((3 : ℝ) ^ e * (N : ℝ) ^ (-(η * e))) := by
        apply mul_le_mul_of_nonneg_left hbracket
        positivity
    _ = CW * (3 : ℝ) ^ e * (N : ℝ) ^ (1 + ε - η * e) := by
        rw [show CW * (N : ℝ) ^ (1 + ε) * ((3 : ℝ) ^ e * (N : ℝ) ^ (-(η * e)))
            = CW * (3 : ℝ) ^ e * ((N : ℝ) ^ (1 + ε) * (N : ℝ) ^ (-(η * e))) by ring,
          ← Real.rpow_add hNpos]
        congr 1

end Work.A3
