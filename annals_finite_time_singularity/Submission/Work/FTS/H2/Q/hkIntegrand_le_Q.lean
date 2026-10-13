/-
Copyright: work module for the Elgindi finite-time singularity project.

# The pointwise bound of the `ℋ⁴`-integrand in the interior class

`Work.Elliptic.hkIntegrand_le` (in the proof of Proposition `WtoH`, Elgindi, tex 1237) bounds
every summand of `HkIntegrand α 4 f z θ` by the weighted derivative bounds `hA`, `hB` on `f`, for
functions which are *analytic* on a neighbourhood of the closed quadrant.  This file re-proves
the pointwise bound for functions which are only `C^∞` on the *open* quadrant
(`Work.FTS.LocData.SmoothQuad`), with `θ` restricted to `(0,π/2)` (the only place where the
bound is used: on the boundary lines both sides of the inequality are `0`).

The only uses of the stronger hypothesis in the original are the slice smoothness facts
`hsmoothf`, `hsmoothD`, which `SmoothQuad` supplies at interior `θ` through
`Work.FTS.LocData.SmoothQuad.curry_z`; the passage from the `z^j ∂_z^j`-bounds to `D_z^i` is
`Work.FTS.H2.Q.abs_w_DzIter_le_sm`.  All other steps are class-agnostic and are copied verbatim.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.Q.Base
import Submission.Work.Elliptic.WtoH

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.Q

open Work.Spaces

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The pointwise bound for `HkIntegrand` -/

theorem hkIntegrand_le_Q {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.LocData.SmoothQuad f) {Wl : ℝ} (hWl : 0 ≤ Wl)
    (hA : ∀ (m : ℕ), m ≤ 4 → ∀ (z : ℝ), 0 < z → ∀ (θ : ℝ), θ ∈ Set.Ioo 0 (π / 2) →
      |(1 + z) * w z * z ^ m * pzIter m f z θ| ≤ 200000 * Wl)
    (hB : ∀ (i l : ℕ), 1 ≤ i → l + i ≤ 4 → ∀ (z : ℝ), 0 < z → ∀ (θ : ℝ),
      θ ∈ Set.Ioo 0 (π / 2) →
      |(1 + z) * w z * z ^ l * pzIter l (DthIter i f) z θ|
        ≤ 200000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) :
    ∀ (z : ℝ), z ∈ Iz → ∀ (θ : ℝ), θ ∈ Set.Ioo 0 (π / 2) →
      HkIntegrand α 4 f z θ
        ≤ Wl ^ 2 * (1 / (1 + z) ^ 2)
          * (2 * 10 ^ 15 * (Real.sin (2 * θ)) ^ (-(eta))
              + 10 ^ 16 * ((α + Real.sin (2 * θ)) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α))) := by
  intro z hz θ hθ
  have hθI : θ ∈ Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hsin : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθI
  by_cases hz0 : z = 0
  · subst hz0
    rw [HkIntegrand_apply_zero]
    have h1 : 0 ≤ (Real.sin (2 * θ)) ^ (-(eta)) := Real.rpow_nonneg hsin _
    have h2 : 0 ≤ (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) := Real.rpow_nonneg hsin _
    have h3 : 0 ≤ (α + Real.sin (2 * θ)) ^ 2 := sq_nonneg _
    have h4 : (0 : ℝ) ≤ 1 / (1 + 0) ^ 2 := by norm_num
    have h5 : (0 : ℝ) ≤ 2 * 10 ^ 15 * (Real.sin (2 * θ)) ^ (-(eta))
        + 10 ^ 16 * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)) :=
      add_nonneg (mul_nonneg (by norm_num) h1)
        (mul_nonneg (by norm_num) (mul_nonneg h3 h2))
    exact mul_nonneg (mul_nonneg (sq_nonneg _) h4) h5
  · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
    have hz1 : (0 : ℝ) < 1 + z := by linarith
    have hzIoi : z ∈ Set.Ioi (-1) := by simp only [Set.mem_Ioi]; linarith
    have hwnn : 0 ≤ w z := div_nonneg (sq_nonneg _) (sq_nonneg _)
    have hsmoothf : ContDiffOn ℝ Work.Stability.smoothOrder (fun z => f z θ) (Set.Ioi (-1)) :=
      Work.FTS.LocData.SmoothQuad.curry_z hsm hθ
    have hsmoothD : ∀ (i : ℕ),
        ContDiffOn ℝ Work.Stability.smoothOrder (fun z => DthIter i f z θ) (Set.Ioi (-1)) :=
      fun i => Work.FTS.LocData.SmoothQuad.curry_z
        (Work.FTS.LocData.SmoothQuad.DthIter hsm i) hθ
    -- per-term bound: pure D_z-family
    have hZ : ∀ i ≤ 4,
        (DzIter i f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2
          ≤ (20000000 * Wl / (1 + z)) ^ 2 * (Real.sin (2 * θ)) ^ (-(eta)) := by
      intro i hi
      have hb : ∀ k ≤ i, |w z * (z ^ k * pzIter k f z θ)| ≤ 200000 * Wl / (1 + z) := by
        intro k hk
        have h1 := hA k (le_trans hk hi) z hzpos θ hθ
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos hz1, abs_of_nonneg hwnn,
          abs_of_nonneg (pow_nonneg hzpos.le k)] at h1
        rw [abs_mul, abs_of_nonneg hwnn, abs_mul, abs_of_nonneg (pow_nonneg hzpos.le k),
          le_div_iff₀ hz1]
        linarith [h1]
      have hsq : (w z * DzIter i f z θ) ^ 2 ≤ (20000000 * Wl / (1 + z)) ^ 2 := by
        have h2 : |w z * DzIter i f z θ| ≤ 100 * (200000 * Wl / (1 + z)) :=
          abs_w_DzIter_le_sm hsmoothf hzIoi (by positivity) hi hb
        have h3 : |w z * DzIter i f z θ| ≤ 20000000 * Wl / (1 + z) := by
          convert h2 using 1; ring
        rw [sq_le_sq, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 20000000 * Wl / (1 + z))]
        exact h3
      rw [Work.Elliptic.sq_mul_div_sin hθI]
      exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hsin _)
    -- angular bookkeeping for the mixed family
    have hsq5 : ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 = (Real.sin (2 * θ)) ^ (2 * α / 5) := by
      have hne : α / 5 + α / 5 ≠ 0 := by intro h; have := hα; linarith
      rw [pow_two, Work.Elliptic.sin_two_rpow_mul' hθI hne, show α / 5 + α / 5 = 2 * α / 5 by ring]
    have hcomb : ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))
        = (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) := by
      have hne : 2 * α / 5 + -(gam α) ≠ 0 := by
        rw [gam]; intro h; linarith
      rw [hsq5, Work.Elliptic.sin_two_rpow_mul' hθI hne]
      ring_nf
    -- per-term bound: mixed family
    have hM : ∀ (i j : ℕ), 1 ≤ i → i + j ≤ 4 →
        (mixed j i f z θ * Wt α z θ) ^ 2
          ≤ (20000000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
              / (1 + z)) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) := by
      intro i j hi hij
      have hb : ∀ l ≤ j,
          |w z * (z ^ l * pzIter l (DthIter i f) z θ)|
            ≤ 200000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) / (1 + z) := by
        intro l hl
        have h1 := hB i l hi (by omega) z hzpos θ hθ
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos hz1, abs_of_nonneg hwnn,
          abs_of_nonneg (pow_nonneg hzpos.le l)] at h1
        rw [abs_mul, abs_of_nonneg hwnn, abs_mul, abs_of_nonneg (pow_nonneg hzpos.le l),
          le_div_iff₀ hz1]
        linarith [h1]
      have hsq : (w z * mixed j i f z θ) ^ 2
          ≤ (20000000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
              / (1 + z)) ^ 2 := by
        have h2 : |w z * DzIter j (DthIter i f) z θ|
            ≤ 100 * (200000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
                / (1 + z)) :=
          abs_w_DzIter_le_sm (hsmoothD i) hzIoi (by positivity) (by omega) hb
        have h3 : |w z * mixed j i f z θ|
            ≤ 20000000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
                / (1 + z) := by
          rw [show mixed j i f = DzIter j (DthIter i f) from rfl]
          convert h2 using 1; ring
        rw [sq_le_sq,
          abs_of_nonneg (by positivity : (0 : ℝ)
            ≤ 20000000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
                / (1 + z))]
        exact h3
      have hWt : (mixed j i f z θ * Wt α z θ) ^ 2
          = (w z * mixed j i f z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) := by
        rw [mul_pow, bt_Wt_sq α z θ hα hθI]
        ring
      rw [hWt]
      exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hsin _)
    -- assemble the two sums
    rw [HkIntegrand]
    have hZsum : ∑ i ∈ Finset.range (4 + 1),
        (DzIter i f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2
        ≤ (2 * 10 ^ 15) * (Wl ^ 2 * (1 / (1 + z) ^ 2) * (Real.sin (2 * θ)) ^ (-(eta))) := by
      calc ∑ i ∈ Finset.range (4 + 1),
            (DzIter i f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2
          ≤ ∑ _i ∈ Finset.range (4 + 1),
              (20000000 * Wl / (1 + z)) ^ 2 * (Real.sin (2 * θ)) ^ (-(eta)) :=
            Finset.sum_le_sum fun i hi => hZ i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
        _ = 5 * ((20000000 * Wl / (1 + z)) ^ 2 * (Real.sin (2 * θ)) ^ (-(eta))) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
        _ = (2 * 10 ^ 15) * (Wl ^ 2 * (1 / (1 + z) ^ 2) * (Real.sin (2 * θ)) ^ (-(eta))) := by
            rw [div_pow]; ring
    have hMsum : ∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
        (if 1 ≤ i ∧ i + j ≤ 4 then (mixed j i f z θ * Wt α z θ) ^ 2 else 0)
        ≤ (10 ^ 16) * (Wl ^ 2 * (1 / (1 + z) ^ 2)
            * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α))) := by
      set Yv : ℝ := (20000000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
              / (1 + z)) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α)) with hYv
      have hYvnn : 0 ≤ Yv := by rw [hYv]; positivity
      calc ∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
            (if 1 ≤ i ∧ i + j ≤ 4 then (mixed j i f z θ * Wt α z θ) ^ 2 else 0)
          ≤ ∑ _i ∈ Finset.range (4 + 1), ∑ _j ∈ Finset.range (4 + 1), Yv := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
            by_cases h : 1 ≤ i ∧ i + j ≤ 4
            · rw [if_pos h]; exact hM i j h.1 h.2
            · rw [if_neg h]; exact hYvnn
        _ = 25 * Yv := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            ring
        _ = (10 ^ 16) * (Wl ^ 2 * (1 / (1 + z) ^ 2)
            * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α))) := by
            rw [hYv]
            have hexp :
                (20000000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
                    / (1 + z)) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))
                  = (20000000 : ℝ) ^ 2 * Wl ^ 2 * (α + Real.sin (2 * θ)) ^ 2 / (1 + z) ^ 2
                    * (((Real.sin (2 * θ)) ^ (α / 5)) ^ 2
                        * (Real.sin (2 * θ)) ^ (-(gam α))) := by
              rw [div_pow, mul_pow, mul_pow, mul_pow]
              ring
            rw [hexp, hcomb]
            ring
    calc ∑ i ∈ Finset.range (4 + 1),
            (DzIter i f z θ * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2
          + ∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
              (if 1 ≤ i ∧ i + j ≤ 4 then (mixed j i f z θ * Wt α z θ) ^ 2 else 0)
        ≤ (2 * 10 ^ 15) * (Wl ^ 2 * (1 / (1 + z) ^ 2) * (Real.sin (2 * θ)) ^ (-(eta)))
          + (10 ^ 16) * (Wl ^ 2 * (1 / (1 + z) ^ 2)
              * ((α + Real.sin (2 * θ)) ^ 2 * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α))) :=
          add_le_add hZsum hMsum
      _ = Wl ^ 2 * (1 / (1 + z) ^ 2)
            * (2 * 10 ^ 15 * (Real.sin (2 * θ)) ^ (-(eta))
                + 10 ^ 16 * ((α + Real.sin (2 * θ)) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α))) := by ring


end Work.FTS.H2.Q
