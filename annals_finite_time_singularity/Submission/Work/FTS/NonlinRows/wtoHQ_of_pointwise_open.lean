import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.Nonlinear.Pieces.RNP.wtoHQ_of_pointwise
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.H2.Q.hkIntegrand_le_Q
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.OpenPkg.ScoefOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The `D_z`-bound from pointwise `z^k ∂_z^k`-bounds on the open half-line

The class-dependent input of the port: `Work.FTS.H2.Q.abs_w_DzIter_le_sm` requires smoothness
of the `z`-slice on `(-1,∞)`, which `SmoothOpen` does not provide (it gives `(0,∞)` only); the
open-half-line Stirling expansion `Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open` does. -/

private theorem abs_w_DzIter_le_open {h : ℝ → ℝ → ℝ} {z θ M : ℝ} {i : ℕ}
    (hsmooth : ContDiffOn ℝ Work.Stability.smoothOrder (fun z => h z θ) (Set.Ioi 0))
    (hz : z ∈ Set.Ioi 0) (hM : 0 ≤ M) (hi : i ≤ 4)
    (hbound : ∀ k ≤ i, |Work.Spaces.w z * (z ^ k * Work.Spaces.pzIter k h z θ)| ≤ M) :
    |Work.Spaces.w z * Work.Spaces.DzIter i h z θ| ≤ 100 * M := by
  have h1 : Work.Spaces.w z * Work.Spaces.DzIter i h z θ
      = ∑ k ∈ Finset.range (i + 1),
          (Work.Spaces.scoef i k : ℝ)
            * (Work.Spaces.w z * (z ^ k * Work.Spaces.pzIter k h z θ)) := by
    rw [Work.FTS.OpenPkg.DzIter_eq_sum_scoef_open hsmooth i z hz, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [h1]
  calc |∑ k ∈ Finset.range (i + 1),
        (Work.Spaces.scoef i k : ℝ)
          * (Work.Spaces.w z * (z ^ k * Work.Spaces.pzIter k h z θ))|
      ≤ (Work.Spaces.bell i : ℝ) * M :=
        Work.Spaces.abs_sum_scoef_mul_le i M _ (fun k hk => hbound k hk)
    _ ≤ 100 * M :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Work.Spaces.bell_le i hi) hM

/-! ## The pointwise bound for `HkIntegrand` in the open-quadrant class

Verbatim port of `Work.FTS.H2.Q.hkIntegrand_le_Q` from `SmoothQuad` to `SmoothOpen`: the only
class-dependent steps (`hsmoothf`, `hsmoothD` and the two applications of
`abs_w_DzIter_le_sm`) are replaced by their open-half-line counterparts. -/

theorem hkIntegrand_le_QO {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) {Wl : ℝ} (hWl : 0 ≤ Wl)
    (hA : ∀ (m : ℕ), m ≤ 4 → ∀ (z : ℝ), 0 < z → ∀ (θ : ℝ), θ ∈ Set.Ioo 0 (π / 2) →
      |(1 + z) * Work.Spaces.w z * z ^ m * Work.Spaces.pzIter m f z θ| ≤ 200000 * Wl)
    (hB : ∀ (i l : ℕ), 1 ≤ i → l + i ≤ 4 → ∀ (z : ℝ), 0 < z → ∀ (θ : ℝ),
      θ ∈ Set.Ioo 0 (π / 2) →
      |(1 + z) * Work.Spaces.w z * z ^ l * Work.Spaces.pzIter l (Work.Spaces.DthIter i f) z θ|
        ≤ 200000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) :
    ∀ (z : ℝ), z ∈ Work.Spaces.Iz → ∀ (θ : ℝ), θ ∈ Set.Ioo 0 (π / 2) →
      Work.Spaces.HkIntegrand α 4 f z θ
        ≤ Wl ^ 2 * (1 / (1 + z) ^ 2)
          * (2 * 10 ^ 15 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
              + 10 ^ 16 * ((α + Real.sin (2 * θ)) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) := by
  intro z hz θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hsin : 0 ≤ Real.sin (2 * θ) := by
    refine Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], ?_⟩
    linarith [hθ.2, Real.pi_pos]
  by_cases hz0 : z = 0
  · subst hz0
    rw [Work.FTS.LocData.HkIntegrand_zero_fst]
    have h1 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := Real.rpow_nonneg hsin _
    have h2 : 0 ≤ (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) :=
      Real.rpow_nonneg hsin _
    have h3 : 0 ≤ (α + Real.sin (2 * θ)) ^ 2 := sq_nonneg _
    have h4 : (0 : ℝ) ≤ 1 / (1 + 0) ^ 2 := by norm_num
    have h5 : (0 : ℝ) ≤ 2 * 10 ^ 15 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
        + 10 ^ 16 * ((α + Real.sin (2 * θ)) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) :=
      add_nonneg (mul_nonneg (by norm_num) h1)
        (mul_nonneg (by norm_num) (mul_nonneg h3 h2))
    exact mul_nonneg (mul_nonneg (sq_nonneg _) h4) h5
  · have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
    have hz1 : (0 : ℝ) < 1 + z := by linarith
    have hzIoi : z ∈ Set.Ioi (0 : ℝ) := hzpos
    have hwnn : 0 ≤ Work.Spaces.w z :=
      div_nonneg (sq_nonneg _) (sq_nonneg _)
    have hsmoothf : ContDiffOn ℝ Work.Stability.smoothOrder (fun z => f z θ) (Set.Ioi 0) :=
      Work.FTS.EllipticEst.SmoothOpen.curry_z hsm hθ
    have hsmoothD : ∀ (i : ℕ), ContDiffOn ℝ Work.Stability.smoothOrder
        (fun z => Work.Spaces.DthIter i f z θ) (Set.Ioi 0) :=
      fun i => Work.FTS.EllipticEst.SmoothOpen.curry_z
        (Work.FTS.EllipticEst.SmoothOpen.DthIter hsm i) hθ
    -- per-term bound: pure `D_z`-family
    have hZ : ∀ i ≤ 4,
        (Work.Spaces.DzIter i f z θ * (Work.Spaces.w z
            / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ (20000000 * Wl / (1 + z)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by
      intro i hi
      have hb : ∀ k ≤ i,
          |Work.Spaces.w z * (z ^ k * Work.Spaces.pzIter k f z θ)| ≤ 200000 * Wl / (1 + z) := by
        intro k hk
        have h1 := hA k (le_trans hk hi) z hzpos θ hθ
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos hz1, abs_of_nonneg hwnn,
          abs_of_nonneg (pow_nonneg hzpos.le k)] at h1
        rw [abs_mul, abs_of_nonneg hwnn, abs_mul, abs_of_nonneg (pow_nonneg hzpos.le k),
          le_div_iff₀ hz1]
        linarith [h1]
      have hsq : (Work.Spaces.w z * Work.Spaces.DzIter i f z θ) ^ 2
          ≤ (20000000 * Wl / (1 + z)) ^ 2 := by
        have h2 : |Work.Spaces.w z * Work.Spaces.DzIter i f z θ|
            ≤ 100 * (200000 * Wl / (1 + z)) :=
          abs_w_DzIter_le_open hsmoothf hzIoi (by positivity) hi hb
        have h3 : |Work.Spaces.w z * Work.Spaces.DzIter i f z θ|
            ≤ 20000000 * Wl / (1 + z) := by
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
    have hcomb : ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        = (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) := by
      have hne : 2 * α / 5 + -(Work.Spaces.gam α) ≠ 0 := by
        rw [Work.Spaces.gam]; intro h; linarith
      rw [hsq5, Work.Elliptic.sin_two_rpow_mul' hθI hne]
      ring_nf
    -- per-term bound: mixed family
    have hM : ∀ (i j : ℕ), 1 ≤ i → i + j ≤ 4 →
        (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ (20000000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
              / (1 + z)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
      intro i j hi hij
      have hb : ∀ l ≤ j,
          |Work.Spaces.w z * (z ^ l * Work.Spaces.pzIter l (Work.Spaces.DthIter i f) z θ)|
            ≤ 200000 * (Wl * ((α + Real.sin (2 * θ))
                * (Real.sin (2 * θ)) ^ (α / 5))) / (1 + z) := by
        intro l hl
        have h1 := hB i l hi (by omega) z hzpos θ hθ
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos hz1, abs_of_nonneg hwnn,
          abs_of_nonneg (pow_nonneg hzpos.le l)] at h1
        rw [abs_mul, abs_of_nonneg hwnn, abs_mul, abs_of_nonneg (pow_nonneg hzpos.le l),
          le_div_iff₀ hz1]
        linarith [h1]
      have hsq : (Work.Spaces.w z * Work.Spaces.mixed j i f z θ) ^ 2
          ≤ (20000000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
              / (1 + z)) ^ 2 := by
        have h2 : |Work.Spaces.w z * Work.Spaces.DzIter j (Work.Spaces.DthIter i f) z θ|
            ≤ 100 * (200000 * (Wl * ((α + Real.sin (2 * θ))
                * (Real.sin (2 * θ)) ^ (α / 5))) / (1 + z)) :=
          abs_w_DzIter_le_open (hsmoothD i) hzIoi (by positivity) (by omega) hb
        have h3 : |Work.Spaces.w z * Work.Spaces.mixed j i f z θ|
            ≤ 20000000 * (Wl * ((α + Real.sin (2 * θ))
                * (Real.sin (2 * θ)) ^ (α / 5))) / (1 + z) := by
          rw [show Work.Spaces.mixed j i f = Work.Spaces.DzIter j (Work.Spaces.DthIter i f)
            from rfl]
          convert h2 using 1; ring
        rw [sq_le_sq, abs_of_nonneg (by positivity : (0 : ℝ)
            ≤ 20000000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
                / (1 + z))]
        exact h3
      have hWt : (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
          = (Work.Spaces.w z * Work.Spaces.mixed j i f z θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
        rw [mul_pow, Work.Spaces.bt_Wt_sq α z θ hα hθI]
        ring
      rw [hWt]
      exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hsin _)
    -- assemble the two sums
    rw [Work.Spaces.HkIntegrand]
    have hZsum : ∑ i ∈ Finset.range (4 + 1),
        (Work.Spaces.DzIter i f z θ * (Work.Spaces.w z
            / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ (2 * 10 ^ 15) * (Wl ^ 2 * (1 / (1 + z) ^ 2)
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
      calc ∑ i ∈ Finset.range (4 + 1),
            (Work.Spaces.DzIter i f z θ * (Work.Spaces.w z
              / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          ≤ ∑ _i ∈ Finset.range (4 + 1),
              (20000000 * Wl / (1 + z)) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) :=
            Finset.sum_le_sum fun i hi => hZ i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
        _ = 5 * ((20000000 * Wl / (1 + z)) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; norm_num
        _ = (2 * 10 ^ 15) * (Wl ^ 2 * (1 / (1 + z) ^ 2)
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) := by
            rw [div_pow]; ring
    have hMsum : ∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
        (if 1 ≤ i ∧ i + j ≤ 4
          then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ (10 ^ 16) * (Wl ^ 2 * (1 / (1 + z) ^ 2)
            * ((α + Real.sin (2 * θ)) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) := by
      set Yv : ℝ := (20000000 * (Wl * ((α + Real.sin (2 * θ))
              * (Real.sin (2 * θ)) ^ (α / 5))) / (1 + z)) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) with hYv
      have hYvnn : 0 ≤ Yv := by rw [hYv]; positivity
      calc ∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
            (if 1 ≤ i ∧ i + j ≤ 4
              then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
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
            * ((α + Real.sin (2 * θ)) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) := by
            rw [hYv]
            have hexp :
                (20000000 * (Wl * ((α + Real.sin (2 * θ))
                    * (Real.sin (2 * θ)) ^ (α / 5))) / (1 + z)) ^ 2
                  * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
                  = (20000000 : ℝ) ^ 2 * Wl ^ 2 * (α + Real.sin (2 * θ)) ^ 2 / (1 + z) ^ 2
                    * (((Real.sin (2 * θ)) ^ (α / 5)) ^ 2
                        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
              rw [div_pow, mul_pow, mul_pow, mul_pow]
              ring
            rw [hexp, hcomb]
            ring
    calc ∑ i ∈ Finset.range (4 + 1),
            (Work.Spaces.DzIter i f z θ * (Work.Spaces.w z
              / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          + ∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
              (if 1 ≤ i ∧ i + j ≤ 4
                then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)
        ≤ (2 * 10 ^ 15) * (Wl ^ 2 * (1 / (1 + z) ^ 2)
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          + (10 ^ 16) * (Wl ^ 2 * (1 / (1 + z) ^ 2)
              * ((α + Real.sin (2 * θ)) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) :=
          add_le_add hZsum hMsum
      _ = Wl ^ 2 * (1 / (1 + z) ^ 2)
            * (2 * 10 ^ 15 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
                + 10 ^ 16 * ((α + Real.sin (2 * θ)) ^ 2
                    * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) := by ring

/-! ## The angular majorant and its vanishing at the endpoints -/

/-- The angular majorant of the `WtoH` estimates. -/
private def angMaj (α θ : ℝ) : ℝ :=
  2 * 10 ^ 15 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
    + 10 ^ 16 * ((α + Real.sin (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))

/-- The pointwise majorant of the `ℋ⁴`-integrand. -/
private def majr (α W z θ : ℝ) : ℝ := W ^ 2 * (1 / (1 + z) ^ 2) * angMaj α θ

/-- The angular majorant vanishes at the two endpoints `θ = 0`, `θ = π/2`. -/
private theorem angMaj_eq_zero {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {θ : ℝ}
    (hsin : Real.sin (2 * θ) = 0) : angMaj α θ = 0 := by
  have h1 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) = 0 := by
    rw [hsin, Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)]
  have h2 : (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α) = 0 := by
    rw [hsin, Real.zero_rpow]
    intro h
    rw [Work.Spaces.gam] at h
    linarith
  simp only [angMaj]
  rw [h1, h2]
  ring

/-- The `ℋ⁴`-integrand vanishes where `sin(2θ) = 0` (both weights degenerate). -/
private theorem HkIntegrand_eq_zero_of_sin_eq_zero {α : ℝ} (hα : 0 < α) (k : ℕ)
    (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hsin : Real.sin (2 * θ) = 0) :
    Work.Spaces.HkIntegrand α k f z θ = 0 := by
  have h1 : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
    rw [hsin, Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)]
  have h2 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) = 0 := by
    rw [hsin, Real.zero_rpow]
    intro h
    rw [Work.Spaces.gam] at h
    have := hα
    linarith
  have hWt : Work.Spaces.Wt α z θ = 0 := by
    simp only [Work.Spaces.Wt, Work.Spaces.wTheta, h2, mul_zero]
  have hw : ∀ i : ℕ, (Work.Spaces.DzIter i f z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 = 0 := by
    intro i
    rw [h1, div_zero, mul_zero]
    ring
  have hm : ∀ i j : ℕ, (if 1 ≤ i ∧ i + j ≤ k
      then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0) = 0 := by
    intro i j
    by_cases hp : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos hp, hWt, mul_zero]; ring
    · rw [if_neg hp]
  have hA : (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i f z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 :=
    Finset.sum_eq_zero fun i _ => hw i
  have hB : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k
        then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => hm i j
  rw [Work.Spaces.HkIntegrand, hA, hB, add_zero]

/- Port of `Work.FTS.Nonlinear.Pieces.RNP.wtoHQ_of_pointwise` from `SmoothQuad` to the
open-quadrant class `Work.FTS.EllipticEst.SmoothOpen` (the class of the primed interfaces), with
the `ℋ⁴`-honesty (`HkMem α 4 f`) added to the conclusion — that conjunct is what the primed
`N4Extra'` clauses and the `PiecesHk` table consume, and it is exactly what the primed rows
10/11/15/19 (`Submission/Work/FTS/NonlinRows/`) must produce.  The pointwise hypotheses `hA`,
`hB` are verbatim those of the existing (proved) SmoothQuad version. -/
theorem wtoHQ_of_pointwise_open : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (W : ℝ),
    0 < α → α ≤ 1 → 0 ≤ W → Work.FTS.EllipticEst.SmoothOpen f →
    (∀ m : ℕ, m ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |(1 + z) * Work.Spaces.w z * z ^ m * Work.Spaces.pzIter m f z θ| ≤ 200000 * W) →
    (∀ i l : ℕ, 1 ≤ i → l + i ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |(1 + z) * Work.Spaces.w z * z ^ l * Work.Spaces.pzIter l
          (Work.Spaces.DthIter i f) z θ|
        ≤ 200000 * (W * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) →
    Work.Spaces.HkMem α 4 f ∧ Work.FTS.Nonlin.Xn α f ≤ C * W := by
  refine ⟨10 ^ 10, by norm_num, ?_⟩
  intro α f W hα hα1 hW hsm hA hB
  -- the pointwise bound of the `ℋ⁴`-integrand
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Set.Ioo 0 (π / 2),
      Work.Spaces.HkIntegrand α 4 f z θ ≤ majr α W z θ :=
    fun z hz θ hθ => by
      have h := hkIntegrand_le_QO (f := f) hα hα1 hsm hW hA hB z hz θ hθ
      simpa only [majr, angMaj, Pi.add_apply] using h
  -- the `ℋ⁴`-membership, by domination
  have hmem : Work.Spaces.HkMem α 4 f := by
    refine Work.FTS.LocData.HkMem_of_majorant α 4
      (M := majr α W) ?_ ?_ ?_ ?_
    · simpa only [Work.FTS.EllipticEst.Q0] using hsm.continuousOn_HkIntegrand α 4
    · -- integrable `θ`-slices of the majorant
      intro z hz
      have hS1 : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          Work.Spaces.Iθ :=
        (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
          (by rw [Work.Spaces.eta]; norm_num)
          (by rw [Work.Spaces.eta]; norm_num)).1
      have hS2 : IntegrableOn (fun θ : ℝ => (α + Real.sin (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) Work.Spaces.Iθ :=
        Work.Spaces.integrableOn_angular_weight' hα hα1
      have h := ((hS1.const_mul (2 * 10 ^ 15)).add (hS2.const_mul (10 ^ 16))).const_mul
        (W ^ 2 * (1 / (1 + z) ^ 2))
      simpa only [majr, angMaj, Pi.add_apply, IntegrableOn] using h
    · -- integrability of the `z`-integral of the slices
      have hKval : IntegrableOn (fun z : ℝ => W ^ 2 * (1 / (1 + z) ^ 2)
          * (∫ θ in Work.Spaces.Iθ, angMaj α θ)) Work.Spaces.Iz := by
        refine (Work.Elliptic.WtoH_IntZ.1.mul_const (W ^ 2 * (∫ θ in Work.Spaces.Iθ,
          angMaj α θ))).congr ?_
        filter_upwards with z
        ring
      have heq : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, majr α W z θ)
          = fun z : ℝ => W ^ 2 * (1 / (1 + z) ^ 2)
              * (∫ θ in Work.Spaces.Iθ, angMaj α θ) := by
        funext z
        simp only [majr]
        rw [MeasureTheory.integral_const_mul]
      rw [heq]
      exact hKval
    · -- the domination on the *closed* interval
      intro z hz θ hθ
      rcases eq_or_lt_of_le hθ.1 with h0 | hθ0
      · subst h0
        have hsin : Real.sin (2 * (0 : ℝ)) = 0 := by simp
        refine le_of_eq ?_
        rw [HkIntegrand_eq_zero_of_sin_eq_zero hα 4 f hsin, majr,
          angMaj_eq_zero hα hα1 hsin]
        simp only [mul_zero]
      · rcases eq_or_lt_of_le hθ.2 with h2 | hθ2
        · subst h2
          have hsin : Real.sin (2 * (π / 2)) = 0 := by
            rw [show 2 * (π / 2) = π by ring, Real.sin_pi]
          refine le_of_eq ?_
          rw [HkIntegrand_eq_zero_of_sin_eq_zero hα 4 f hsin, majr,
            angMaj_eq_zero hα hα1 hsin]
          simp only [mul_zero]
        · exact hpt z hz θ ⟨hθ0, hθ2⟩
  refine ⟨hmem, ?_⟩
  -- the angular integral
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
        ≤ W ^ 2 * (1 / (1 + z) ^ 2) * (2 * 10 ^ 15 * 10 ^ 4 + 10 ^ 16 * 700) := by
    intro z hz
    have hS1 : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ :=
      (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
        (by rw [Work.Spaces.eta]; norm_num)
        (by rw [Work.Spaces.eta]; norm_num)).1
    have hS2 : IntegrableOn (fun θ : ℝ => (α + Real.sin (2 * θ)) ^ 2
        * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) Work.Spaces.Iθ :=
      Work.Spaces.integrableOn_angular_weight' hα hα1
    have hmaj : Integrable (fun θ : ℝ => majr α W z θ)
        (volume.restrict Work.Spaces.Iθ) := by
      have h := ((hS1.const_mul (2 * 10 ^ 15)).add (hS2.const_mul (10 ^ 16))).const_mul
        (W ^ 2 * (1 / (1 + z) ^ 2))
      simpa only [majr, angMaj, Pi.add_apply] using h
    have hIoo : volume.restrict Work.Spaces.Iθ
        = volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) := by
      have haeeq : Set.Ioo (0 : ℝ) (π / 2) =ᵐ[volume] Work.Spaces.Iθ :=
        MeasureTheory.Ioo_ae_eq_Icc
      exact Measure.restrict_congr_set haeeq.symm
    have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        Work.Spaces.HkIntegrand α 4 f z θ ≤ majr α W z θ := by
      rw [hIoo]
      exact ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => hpt z hz θ hθ)
    calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, majr α W z θ :=
          integral_mono_of_nonneg
            (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ) hmaj hae
      _ = W ^ 2 * (1 / (1 + z) ^ 2) * (∫ θ in Work.Spaces.Iθ, angMaj α θ) := by
          simp only [majr]
          rw [MeasureTheory.integral_const_mul]
      _ ≤ W ^ 2 * (1 / (1 + z) ^ 2) * (2 * 10 ^ 15 * 10 ^ 4 + 10 ^ 16 * 700) := by
          refine mul_le_mul_of_nonneg_left ?_
            (mul_nonneg (sq_nonneg _) (div_nonneg (by norm_num) (sq_nonneg _)))
          simpa only [angMaj] using
            Work.Elliptic.WtoH_Angular (α := α) (A := 2 * 10 ^ 15) (B := 10 ^ 16)
              hα hα1 (by norm_num) (by norm_num)
  -- the radial integral
  have houter : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 f z θ)
      ≤ (2 * 10 ^ 15 * 10 ^ 4 + 10 ^ 16 * 700) * 2 * W ^ 2 := by
    set K : ℝ := 2 * 10 ^ 15 * 10 ^ 4 + 10 ^ 16 * 700 with hK
    have hI : IntegrableOn (fun z : ℝ => W ^ 2 * (1 / (1 + z) ^ 2) * K) Work.Spaces.Iz := by
      refine (Work.Elliptic.WtoH_IntZ.1.mul_const (W ^ 2 * K)).congr ?_
      filter_upwards with z
      ring
    calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ)
        ≤ ∫ z in Work.Spaces.Iz, W ^ 2 * (1 / (1 + z) ^ 2) * K :=
          integral_mono_of_nonneg
            (Eventually.of_forall fun z =>
              integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 f z θ)
            hI (ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => hinner z hz))
      _ = (∫ z in Work.Spaces.Iz, 1 / (1 + z) ^ 2) * (W ^ 2 * K) := by
          rw [show (fun z : ℝ => W ^ 2 * (1 / (1 + z) ^ 2) * K)
              = fun z : ℝ => (1 / (1 + z) ^ 2) * (W ^ 2 * K) from by funext z; ring]
          rw [MeasureTheory.integral_mul_const]
      _ ≤ 2 * (W ^ 2 * K) :=
          mul_le_mul_of_nonneg_right Work.Elliptic.WtoH_IntZ.2
            (mul_nonneg (sq_nonneg _) (by rw [hK]; norm_num))
      _ = K * 2 * W ^ 2 := by rw [hK]; ring
  have hSq : Work.Spaces.HkSq α 4 f ≤ 10 ^ 20 * W ^ 2 := by
    rw [Work.Spaces.HkSq]
    have hK2 : (2 * 10 ^ 15 * 10 ^ 4 + 10 ^ 16 * 700) * 2 * W ^ 2 ≤ 10 ^ 20 * W ^ 2 := by
      nlinarith [sq_nonneg W]
    linarith [houter]
  have hmain : Real.sqrt (Work.Spaces.HkSq α 4 f) ≤ 10 ^ 10 * W := by
    calc Real.sqrt (Work.Spaces.HkSq α 4 f) ≤ Real.sqrt (10 ^ 20 * W ^ 2) :=
          Real.sqrt_le_sqrt hSq
      _ = 10 ^ 10 * W := by
          rw [show (10 : ℝ) ^ 20 * W ^ 2 = (10 ^ 10 * W) ^ 2 by ring]
          exact Real.sqrt_sq (mul_nonneg (by norm_num) hW)
  simpa only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm] using hmain

end Work.FTS.NonlinRows
