/-
# `OpenPkg/WtohWin/Aux` — the pointwise `ℋ⁴`-integrand bound in the open-quadrant class

This module ports the two class-dependent lemmas of the `WtoH` chain from
`Work.FTS.LocData.SmoothQuad` (smoothness on `(-1,∞) × (0,π/2)`) to the open-quadrant class
`Work.FTS.EllipticEst.SmoothOpen` (smoothness on `(0,∞) × (0,π/2)` only), which is the class of
the primed interfaces `Work.FTS.OpenPkg.N4Norm'`:

* `abs_w_DzIter_le_open` — the open-half-line instance of `Work.FTS.H2.Q.abs_w_DzIter_le_sm`
  (`|w(z)·D_z^i h| ≤ 100 M` from the `z^k ∂_z^k`-bounds), using the Stirling expansion
  `Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open` on `(0,∞)` instead of the `(-1,∞)` expansion;
* `hkIntegrand_le_open` — the open-quadrant instance of `Work.FTS.H2.Q.hkIntegrand_le_Q`,
  which is the pointwise domination of the whole `ℋ⁴`-integrand by
  `W²(1+z)^{-2}(2·10¹⁵ sin(2θ)^{-η} + 10¹⁶(α+sin2θ)² sin(2θ)^{2α/5-γ})`.

The remaining inputs of `hkIntegrand_le_Q` are class-agnostic (`Work.Elliptic.sq_mul_div_sin`,
`Work.Spaces.bt_Wt_sq`, the weights `Work.Spaces.HkIntegrand`), so only the two smoothness
witnesses (`hsmoothf`, `hsmoothD`, taken at `θ ∈ (0,π/2)`) and the evaluation point `z > 0`
change: `Work.FTS.OpenPkg.smoothOpen_slice_z`, `...smoothOpen_DthIter_slice_z` supply exactly
what the `(-1,∞)`-versions supplied before.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.OpenPkg.ScoefOpen
import Submission.Work.FTS.H2.Q.hkIntegrand_le_Q

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg.WtohWin

open Work.Spaces

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **`D_z`-derivatives are bounded by the `z^j ∂_z^j`-bounds on the open half-line**: if
`|w(z)·z^j ∂_z^j h| ≤ M` for `j ≤ i ≤ 4` at `(z,θ)`, then `|w(z)·D_z^i h| ≤ 100 M`.  This is
the open-quadrant (`SmoothOpen`) companion of `Work.FTS.H2.Q.abs_w_DzIter_le_sm`, and only
differs from it by using the Stirling expansion on `(0,∞)`
(`Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open`) and the evaluation point `z > 0`. -/
theorem abs_w_DzIter_le_open {h : ℝ → ℝ → ℝ} {z θ M : ℝ} {i : ℕ}
    (hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder (fun z => h z θ) (Set.Ioi 0))
    (hz : z ∈ Set.Ioi 0) (hM : 0 ≤ M) (hi : i ≤ 4)
    (hbound : ∀ k ≤ i, |w z * (z ^ k * pzIter k h z θ)| ≤ M) :
    |w z * DzIter i h z θ| ≤ 100 * M := by
  have h1 : w z * DzIter i h z θ
      = ∑ k ∈ Finset.range (i + 1),
          (scoef i k : ℝ) * (w z * (z ^ k * pzIter k h z θ)) := by
    rw [Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open hsmooth i z hz, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [h1]
  calc |∑ k ∈ Finset.range (i + 1), (scoef i k : ℝ) * (w z * (z ^ k * pzIter k h z θ))|
      ≤ (bell i : ℝ) * M := abs_sum_scoef_mul_le i M _ (fun k hk => hbound k hk)
    _ ≤ 100 * M := mul_le_mul_of_nonneg_right (by exact_mod_cast bell_le i hi) hM

/-! ## The pointwise bound of the `ℋ⁴`-integrand in the open-quadrant class -/

/-- **The open-quadrant pointwise `ℋ⁴`-integrand bound.**  This is
`Work.FTS.H2.Q.hkIntegrand_le_Q` with the hypothesis `SmoothQuad f` replaced by
`SmoothOpen f`; the conclusion is identical. -/
theorem hkIntegrand_le_open {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) {Wl : ℝ} (hWl : 0 ≤ Wl)
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
    have hzIoi : z ∈ Set.Ioi (0 : ℝ) := hzpos
    have hwnn : 0 ≤ w z := div_nonneg (sq_nonneg _) (sq_nonneg _)
    have hsmoothf : ContDiffOn ℝ Work.Stability.smoothOrder (fun z => f z θ) (Set.Ioi 0) :=
      Work.FTS.OpenPkg.smoothOpen_slice_z hsm hθ
    have hsmoothD : ∀ (i : ℕ),
        ContDiffOn ℝ Work.Stability.smoothOrder (fun z => DthIter i f z θ) (Set.Ioi 0) :=
      fun i => Work.FTS.OpenPkg.smoothOpen_DthIter_slice_z hsm i hθ
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
          abs_w_DzIter_le_open hsmoothf hzIoi (by positivity) hi hb
        have h3 : |w z * DzIter i f z θ| ≤ 20000000 * Wl / (1 + z) := by
          convert h2 using 1; ring
        rw [sq_le_sq, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 20000000 * Wl / (1 + z))]
        exact h3
      rw [Work.Elliptic.sq_mul_div_sin hθI]
      exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hsin _)
    -- angular bookkeeping for the mixed family
    have hsq5 : ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 = (Real.sin (2 * θ)) ^ (2 * α / 5) := by
      have hne : α / 5 + α / 5 ≠ 0 := by intro h; have := hα; linarith
      rw [pow_two, Work.Elliptic.sin_two_rpow_mul' hθI hne,
        show α / 5 + α / 5 = 2 * α / 5 by ring]
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
            ≤ 200000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
                / (1 + z) := by
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
            ≤ 100 * (200000 * (Wl * ((α + Real.sin (2 * θ))
                * (Real.sin (2 * θ)) ^ (α / 5))) / (1 + z)) :=
          abs_w_DzIter_le_open (hsmoothD i) hzIoi (by positivity) (by omega) hb
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
      set Yv : ℝ := (20000000 * (Wl * ((α + Real.sin (2 * θ))
              * (Real.sin (2 * θ)) ^ (α / 5))) / (1 + z)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(gam α)) with hYv
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

end Work.FTS.OpenPkg.WtohWin
