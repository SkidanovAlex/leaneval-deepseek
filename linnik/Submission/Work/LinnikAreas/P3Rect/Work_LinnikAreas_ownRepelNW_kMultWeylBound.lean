/-# `Work.LinnikAreas.ownRepelNW.kMultWeylBound`

Weyl-type (inverse-square) zero-sum bound for the non-trivial zeros of `ζ_K = ζ · L(·,χ)` in the
Deuring–Heilbronn repulsion argument, in the own-character range `c ∈ [2,10]`, `|γ'| ≤ 1`.

The summand is the multiplicity `kMult χ u` (the sum of the vanishing orders of `u` as a zero of
the entire completion `Ξ` of `ζ` and of `completedLFunction χ`) times the sum of two shifted
inverse-square kernels

`1/((c - u.re)² + u.im²) + 1/((c - u.re)² + (u.im - γ')²) = 1/‖c - u‖² + 1/‖c + iγ' - u‖²`.

The point is that with `w₁ = c` and `w₂ = c + iγ'` both centres satisfy `Re wᵢ ≥ 2 > 3/2`,
so the two-summand kernel is the sum of the two single-centre kernels to which the already
proved uniform kMult zero sum `Work.LinnikAreas.DhExplicit.zeroSumKMultBound` applies:
`∑_u kMult χ u/‖w-u‖² ≤ C (log q + log(2+‖w‖) + 2)` for every `w` with `Re w ≥ 3/2`, with an
absolute constant `C` (uniform in the level `q` and in the primitive non-trivial character
`χ`).  Summing the two instances and using `‖w₁‖ ≤ 10`, `‖w₂‖ ≤ 11` and `log q ≥ 2`
(for `q ≥ 13`) gives the claim with `C = 8C₀ + 1` and `q₀ = 13`.
--/
import Mathlib
import Submission.Work.LinnikAreas.P3Rect.Work_LinnikAreas_DhExplicit_zeroSumKMultBound

open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas.ownRepelNW

theorem kMultWeylBound : ∃ C : ℝ, 0 < C ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
    (χ : DirichletCharacter ℂ q),
    χ ≠ 1 → χ.IsPrimitive → χ ^ 2 = 1 →
    ∀ {c γ' : ℝ}, 2 ≤ c → c ≤ 10 → |γ'| ≤ 1 →
    Summable (fun u : ℂ => (Work.LinnikAreas.DhK.kMult χ u : ℝ) *
      (1 / ((c - u.re) ^ 2 + u.im ^ 2) + 1 / ((c - u.re) ^ 2 + (u.im - γ') ^ 2))) ∧
    (∑' u : ℂ, (Work.LinnikAreas.DhK.kMult χ u : ℝ) *
      (1 / ((c - u.re) ^ 2 + u.im ^ 2) + 1 / ((c - u.re) ^ 2 + (u.im - γ') ^ 2)))
      ≤ C * Real.log (q : ℝ) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Work.LinnikAreas.DhExplicit.zeroSumKMultBound
  refine ⟨8 * C₀ + 1, by positivity, 13, ?_⟩
  intro q hq _inst χ hχ hχprim _hχsq c γ' hc hc10 hγ'
  have hq2 : 2 ≤ q := by omega
  -- the two centres `c` and `c + iγ'`
  set w₁ : ℂ := (c : ℂ) with hw₁def
  set w₂ : ℂ := (c : ℂ) + (γ' : ℂ) * Complex.I with hw₂def
  have hw₁ : (3 / 2 : ℝ) ≤ w₁.re := by rw [hw₁def]; simp; linarith
  have hw₂ : (3 / 2 : ℝ) ≤ w₂.re := by rw [hw₂def]; simp; linarith
  obtain ⟨hs₁, hb₁⟩ := hC₀ q hq2 χ hχ hχprim w₁ hw₁
  obtain ⟨hs₂, hb₂⟩ := hC₀ q hq2 χ hχ hχprim w₂ hw₂
  -- the two kernels in norm form
  have hker₁ : ∀ u : ℂ, ‖w₁ - u‖ ^ 2 = (c - u.re) ^ 2 + u.im ^ 2 := by
    intro u
    rw [hw₁def, Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hker₂ : ∀ u : ℂ, ‖w₂ - u‖ ^ 2 = (c - u.re) ^ 2 + (u.im - γ') ^ 2 := by
    intro u
    rw [hw₂def, Complex.sq_norm, Complex.normSq_apply]
    simp
    ring
  have hpt : ∀ u : ℂ, (Work.LinnikAreas.DhK.kMult χ u : ℝ) *
        (1 / ((c - u.re) ^ 2 + u.im ^ 2) + 1 / ((c - u.re) ^ 2 + (u.im - γ') ^ 2))
      = (Work.LinnikAreas.DhK.kMult χ u : ℝ) / ‖w₁ - u‖ ^ 2
        + (Work.LinnikAreas.DhK.kMult χ u : ℝ) / ‖w₂ - u‖ ^ 2 := by
    intro u
    rw [hker₁ u, hker₂ u, div_eq_mul_one_div, div_eq_mul_one_div]
    ring
  -- norms of the two centres
  have hw₁norm : ‖w₁‖ ≤ 10 := by
    rw [hw₁def, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    linarith
  have hw₂norm : ‖w₂‖ ≤ 11 := by
    rw [hw₂def]
    calc ‖(c : ℂ) + (γ' : ℂ) * Complex.I‖
          ≤ ‖(c : ℂ)‖ + ‖(γ' : ℂ) * Complex.I‖ := norm_add_le _ _
      _ ≤ 10 + 1 := by
          refine add_le_add ?_ ?_
          · rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith
          · rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
            exact hγ'
      _ ≤ 11 := by norm_num
  -- logarithm bounds for `q ≥ 13`
  have hlog2 : (2 : ℝ) ≤ Real.log (q : ℝ) := by
    have h8 : (8 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 8 ≤ q)
    have hlog8 : (2 : ℝ) ≤ Real.log 8 := by
      have h : Real.log 8 = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
        norm_num
      rw [h]
      linarith [Real.log_two_gt_d9]
    exact le_trans hlog8 (Real.log_le_log (by norm_num) h8)
  have hlogqnn : 0 ≤ Real.log (q : ℝ) := by linarith
  have hlog₁ : Real.log (2 + ‖w₁‖) ≤ Real.log (q : ℝ) := by
    refine Real.log_le_log (by positivity) ?_
    have h12 : (12 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 12 ≤ q)
    linarith
  have hlog₂ : Real.log (2 + ‖w₂‖) ≤ Real.log (q : ℝ) := by
    refine Real.log_le_log (by positivity) ?_
    have h13 : (13 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 13 ≤ q)
    linarith
  have he₁ : C₀ * (Real.log (q : ℝ) + Real.log (2 + ‖w₁‖) + 2)
      ≤ C₀ * (4 * Real.log (q : ℝ)) := by
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hC₀pos)
    linarith
  have he₂ : C₀ * (Real.log (q : ℝ) + Real.log (2 + ‖w₂‖) + 2)
      ≤ C₀ * (4 * Real.log (q : ℝ)) := by
    refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hC₀pos)
    linarith
  refine ⟨?_, ?_⟩
  · exact (hs₁.add hs₂).congr (fun u => (hpt u).symm)
  · rw [tsum_congr hpt, Summable.tsum_add hs₁ hs₂]
    calc (∑' u : ℂ, (Work.LinnikAreas.DhK.kMult χ u : ℝ) / ‖w₁ - u‖ ^ 2)
          + (∑' u : ℂ, (Work.LinnikAreas.DhK.kMult χ u : ℝ) / ‖w₂ - u‖ ^ 2)
        ≤ C₀ * (4 * Real.log (q : ℝ)) + C₀ * (4 * Real.log (q : ℝ)) := by linarith
      _ ≤ (8 * C₀ + 1) * Real.log (q : ℝ) := by
          have h : (8 * C₀ + 1) * Real.log (q : ℝ)
              = C₀ * (4 * Real.log (q : ℝ)) + C₀ * (4 * Real.log (q : ℝ))
                + Real.log (q : ℝ) := by ring
          rw [h]
          linarith

end Work.LinnikAreas.ownRepelNW
