/-
Copyright: work module for the Elgindi finite-time singularity project.

# The transfer `𝒲^{4,∞} → ℋ⁴` (Proposition `WtoH`)

Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021),
Proposition `WtoH`: there is a universal constant `C > 0` with

  `|f|_{ℋ⁴} ≤ C · |(z+1)³/z² · f|_{𝒲^{4,∞}}`

for every smooth `f`.  This file assembles the proof from the pieces:

* `Work.Elliptic.WtoH_Radial`, `Work.Elliptic.WtoH_Mixed`: the two pointwise
  estimates `|(1+z) w z^m ∂_z^m f| ≤ 2·10^5 |g|_𝒲` and
  `|(1+z) w z^l ∂_z^l D_θ^i f| ≤ 2·10^5 |g|_𝒲 (α+sin 2θ) sin(2θ)^{α/5}`
  (`g = (z+1)³/z² f`), proved from the triangular estimate `tri_bound` of
  `Work.Elliptic.WtoHAux`;
* `Work.Elliptic.WtoH_IntZ`: `∫_{[0,∞)} 1/(1+z)² ≤ 2`;
* `Work.Elliptic.WtoH_Angular`: the angular integrals `≤ A·10^4 + B·700`.

`HkIntegrand` is dominated by `|g|_𝒲² (1+z)^{-2}` times those two angular
profiles, whose integral is finite; taking square roots gives the statement
with `C = 10^10`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Elliptic.WtoHAux
import Submission.Work.Elliptic.WtoH_Radial
import Submission.Work.Elliptic.WtoH_Mixed
import Submission.Work.Elliptic.WtoH_IntZ
import Submission.Work.Elliptic.WtoH_Angular
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.bt_aux
import Submission.Work.Spaces.SmoothCompact_Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic
open Work.Spaces

/-! ## Angular power bookkeeping -/

theorem sin_two_rpow_mul' {θ a b : ℝ} (hθ : θ ∈ Iθ) (h : a + b ≠ 0) :
    (Real.sin (2 * θ)) ^ a * (Real.sin (2 * θ)) ^ b = (Real.sin (2 * θ)) ^ (a + b) :=
  (Real.rpow_add' (sin_two_nonneg_Iθ hθ) h).symm

/-- `(a * (w z / sin(2θ)^{η/2}))² = (w z * a)² * sin(2θ)^{-η}`. -/
theorem sq_mul_div_sin {z θ a : ℝ} (hθ : θ ∈ Iθ) :
    (a * (w z / (Real.sin (2 * θ)) ^ (eta / 2))) ^ 2
      = (w z * a) ^ 2 * (Real.sin (2 * θ)) ^ (-(eta)) := by
  have hs : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  have hne : eta / 2 + eta / 2 ≠ 0 := by
    rw [show eta / 2 + eta / 2 = eta by ring]; exact ne_of_gt eta_pos
  have h2 : ((Real.sin (2 * θ)) ^ (eta / 2)) ^ 2 = (Real.sin (2 * θ)) ^ eta := by
    rw [pow_two, ← Real.rpow_add' hs hne, show eta / 2 + eta / 2 = eta by ring]
  rw [mul_pow, div_pow, h2, div_eq_mul_inv, Real.rpow_neg hs]
  ring

/-! ## The weighted `D_z`-bound -/

theorem abs_w_DzIter_le {h : ℝ → ℝ → ℝ} {z θ M : ℝ} {i : ℕ}
    (hsmooth : ∀ θ ∈ Iθ, ContDiffOn ℝ ⊤ (fun z => h z θ) (Set.Ioi (-1)))
    (hz : z ∈ Set.Ioi (-1)) (hθ : θ ∈ Iθ) (hM : 0 ≤ M) (hi : i ≤ 4)
    (hbound : ∀ k ≤ i, |w z * (z ^ k * pzIter k h z θ)| ≤ M) :
    |w z * DzIter i h z θ| ≤ 100 * M := by
  have h1 : w z * DzIter i h z θ
      = ∑ k ∈ Finset.range (i + 1), (scoef i k : ℝ) * (w z * (z ^ k * pzIter k h z θ)) := by
    rw [DzIter_eq_sum_scoef hsmooth i z hz θ hθ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [h1]
  calc |∑ k ∈ Finset.range (i + 1), (scoef i k : ℝ) * (w z * (z ^ k * pzIter k h z θ))|
      ≤ (bell i : ℝ) * M :=
        abs_sum_scoef_mul_le i M _ (fun k hk => hbound k hk)
    _ ≤ 100 * M := mul_le_mul_of_nonneg_right (by exact_mod_cast bell_le i hi) hM

/-! ## The pointwise bound for `HkIntegrand` -/

theorem hkIntegrand_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsm : SmoothNbhd f) {Wl : ℝ} (hWl : 0 ≤ Wl)
    (hA : ∀ (m : ℕ), m ≤ 4 → ∀ (z : ℝ), 0 < z → ∀ (θ : ℝ), θ ∈ Iθ →
      |(1 + z) * w z * z ^ m * pzIter m f z θ| ≤ 200000 * Wl)
    (hB : ∀ (i l : ℕ), 1 ≤ i → l + i ≤ 4 → ∀ (z : ℝ), 0 < z → ∀ (θ : ℝ), θ ∈ Iθ →
      |(1 + z) * w z * z ^ l * pzIter l (DthIter i f) z θ|
        ≤ 200000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) :
    ∀ (z : ℝ), z ∈ Iz → ∀ (θ : ℝ), θ ∈ Iθ →
      HkIntegrand α 4 f z θ
        ≤ Wl ^ 2 * (1 / (1 + z) ^ 2)
          * (2 * 10 ^ 15 * (Real.sin (2 * θ)) ^ (-(eta))
              + 10 ^ 16 * ((α + Real.sin (2 * θ)) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α))) := by
  intro z hz θ hθ
  have hsin : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
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
    have hsmoothf : ∀ θ ∈ Iθ, ContDiffOn ℝ ⊤ (fun z => f z θ) (Set.Ioi (-1)) :=
      (SmoothInt.of_smoothNbhd hsm).2
    have hsmoothD : ∀ (i : ℕ) (θ' : ℝ), θ' ∈ Iθ →
        ContDiffOn ℝ ⊤ (fun z => DthIter i f z θ') (Set.Ioi (-1)) :=
      fun i θ' hθ' => DthIter_contDiffOn_slice' (SmoothInt.of_smoothNbhd hsm) i θ' hθ'
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
          abs_w_DzIter_le hsmoothf hzIoi hθ (by positivity) hi hb
        have h3 : |w z * DzIter i f z θ| ≤ 20000000 * Wl / (1 + z) := by
          convert h2 using 1; ring
        rw [sq_le_sq, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 20000000 * Wl / (1 + z))]
        exact h3
      rw [sq_mul_div_sin hθ]
      exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg hsin _)
    -- angular bookkeeping for the mixed family
    have hsq5 : ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 = (Real.sin (2 * θ)) ^ (2 * α / 5) := by
      have hne : α / 5 + α / 5 ≠ 0 := by intro h; have := hα; linarith
      rw [pow_two, sin_two_rpow_mul' hθ hne, show α / 5 + α / 5 = 2 * α / 5 by ring]
    have hcomb : ((Real.sin (2 * θ)) ^ (α / 5)) ^ 2 * (Real.sin (2 * θ)) ^ (-(gam α))
        = (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α) := by
      have hne : 2 * α / 5 + -(gam α) ≠ 0 := by
        rw [gam]; intro h; linarith
      rw [hsq5, sin_two_rpow_mul' hθ hne]
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
          abs_w_DzIter_le (hsmoothD i) hzIoi hθ (by positivity) (by omega) hb
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
        rw [mul_pow, bt_Wt_sq α z θ hα hθ]
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

/-! ## The inner angular integral -/

theorem inner_integral_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsm : SmoothNbhd f) {Wl : ℝ} (hWl : 0 ≤ Wl)
    (hA : ∀ (m : ℕ), m ≤ 4 → ∀ (z : ℝ), 0 < z → ∀ (θ : ℝ), θ ∈ Iθ →
      |(1 + z) * w z * z ^ m * pzIter m f z θ| ≤ 200000 * Wl)
    (hB : ∀ (i l : ℕ), 1 ≤ i → l + i ≤ 4 → ∀ (z : ℝ), 0 < z → ∀ (θ : ℝ), θ ∈ Iθ →
      |(1 + z) * w z * z ^ l * pzIter l (DthIter i f) z θ|
        ≤ 200000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) :
    ∀ z ∈ Iz, ∫ θ in Iθ, HkIntegrand α 4 f z θ
      ≤ Wl ^ 2 * (1 / (1 + z) ^ 2) * (2 * 10 ^ 15 * 10 ^ 4 + 10 ^ 16 * 700) := by
  intro z hz
  have hS1 : IntegrableOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(eta))) Iθ :=
    (sin_two_rpow (-(eta)) (by linarith [eta_lt_one]) (by linarith [eta_nonneg])).1
  have hS2 : IntegrableOn (fun θ : ℝ => (α + Real.sin (2 * θ)) ^ 2
      * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)) Iθ := integrableOn_angular_weight' hα hα1
  have hmaj : IntegrableOn (fun θ : ℝ => Wl ^ 2 * (1 / (1 + z) ^ 2)
      * (2 * 10 ^ 15 * (Real.sin (2 * θ)) ^ (-(eta))
          + 10 ^ 16 * ((α + Real.sin (2 * θ)) ^ 2
              * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)))) Iθ :=
    ((hS1.const_mul (2 * 10 ^ 15)).add (hS2.const_mul (10 ^ 16))).const_mul _
  calc ∫ θ in Iθ, HkIntegrand α 4 f z θ
      ≤ ∫ θ in Iθ, Wl ^ 2 * (1 / (1 + z) ^ 2)
          * (2 * 10 ^ 15 * (Real.sin (2 * θ)) ^ (-(eta))
              + 10 ^ 16 * ((α + Real.sin (2 * θ)) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α))) :=
        integral_mono_of_nonneg (Eventually.of_forall fun θ => HkIntegrand_nonneg α 4 f z θ)
          hmaj (ae_restrict_of_forall_mem measurableSet_Icc
            (fun θ hθ => hkIntegrand_le hα hα1 hsm hWl hA hB z hz θ hθ))
    _ = Wl ^ 2 * (1 / (1 + z) ^ 2)
          * (∫ θ in Iθ, (2 * 10 ^ 15 * (Real.sin (2 * θ)) ^ (-(eta))
              + 10 ^ 16 * ((α + Real.sin (2 * θ)) ^ 2
                  * (Real.sin (2 * θ)) ^ (2 * α / 5 - gam α)))) := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ Wl ^ 2 * (1 / (1 + z) ^ 2) * (2 * 10 ^ 15 * 10 ^ 4 + 10 ^ 16 * 700) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact WtoH_Angular hα hα1 (by norm_num) (by norm_num)

/-! ## The outer radial integral -/

theorem outer_integral_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsm : SmoothNbhd f) {Wl : ℝ} (hWl : 0 ≤ Wl)
    (hA : ∀ (m : ℕ), m ≤ 4 → ∀ (z : ℝ), 0 < z → ∀ (θ : ℝ), θ ∈ Iθ →
      |(1 + z) * w z * z ^ m * pzIter m f z θ| ≤ 200000 * Wl)
    (hB : ∀ (i l : ℕ), 1 ≤ i → l + i ≤ 4 → ∀ (z : ℝ), 0 < z → ∀ (θ : ℝ), θ ∈ Iθ →
      |(1 + z) * w z * z ^ l * pzIter l (DthIter i f) z θ|
        ≤ 200000 * (Wl * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) :
    ∫ z in Iz, ∫ θ in Iθ, HkIntegrand α 4 f z θ
      ≤ (2 * 10 ^ 15 * 10 ^ 4 + 10 ^ 16 * 700) * 2 * Wl ^ 2 := by
  set K : ℝ := 2 * 10 ^ 15 * 10 ^ 4 + 10 ^ 16 * 700 with hK
  have hKnn : 0 ≤ K := by rw [hK]; norm_num
  have hI : IntegrableOn (fun z : ℝ => Wl ^ 2 * (1 / (1 + z) ^ 2) * K) Iz := by
    refine (WtoH_IntZ.1.mul_const (Wl ^ 2 * K)).congr ?_
    filter_upwards with z
    ring
  calc ∫ z in Iz, ∫ θ in Iθ, HkIntegrand α 4 f z θ
      ≤ ∫ z in Iz, Wl ^ 2 * (1 / (1 + z) ^ 2) * K :=
        integral_mono_of_nonneg
          (Eventually.of_forall fun z => integral_nonneg fun θ => HkIntegrand_nonneg α 4 f z θ)
          hI (ae_restrict_of_forall_mem measurableSet_Ici
            (fun z hz => inner_integral_le hα hα1 hsm hWl hA hB z hz))
    _ = (∫ z in Iz, 1 / (1 + z) ^ 2) * (Wl ^ 2 * K) := by
        rw [show (fun z : ℝ => Wl ^ 2 * (1 / (1 + z) ^ 2) * K)
            = fun z : ℝ => (1 / (1 + z) ^ 2) * (Wl ^ 2 * K) from by funext z; ring]
        rw [MeasureTheory.integral_mul_const]
    _ ≤ 2 * (Wl ^ 2 * K) := mul_le_mul_of_nonneg_right WtoH_IntZ.2 (by positivity)
    _ = (2 * 10 ^ 15 * 10 ^ 4 + 10 ^ 16 * 700) * 2 * Wl ^ 2 := by rw [hK]; ring


/-! ## The main theorem -/

theorem WtoH_main {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hsm : SmoothNbhd f)
    (hmem : WlInfMem α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ)) :
    HkNorm α 4 f ≤ 10 ^ 10 * WlInf α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) := by
  set g : ℝ → ℝ → ℝ := fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ with hg
  set Wl : ℝ := WlInf α 4 g with hWl
  have hWlnn : 0 ≤ Wl := by
    rw [hWl]
    exact add_nonneg (wlZSum_nonneg α 4 g hmem) (wlThSum_nonneg α 4 g hmem)
  have hWlfun : WlInf α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) = Wl := by
    rw [hWl]
  have hA := WtoH_Radial hα hα1 hsm hmem
  have hB := WtoH_Mixed hα hα1 hsm hmem
  rw [hWlfun] at hA hB
  have hout := outer_integral_le hα hα1 hsm hWlnn hA hB
  have hSq : HkSq α 4 f ≤ 10 ^ 20 * Wl ^ 2 := by
    rw [HkSq]
    have hK : (2 * 10 ^ 15 * 10 ^ 4 + 10 ^ 16 * 700) * 2 * Wl ^ 2 ≤ 10 ^ 20 * Wl ^ 2 := by
      nlinarith [sq_nonneg Wl]
    linarith [hout]
  rw [HkNorm]
  calc Real.sqrt (HkSq α 4 f) ≤ Real.sqrt (10 ^ 20 * Wl ^ 2) := Real.sqrt_le_sqrt hSq
    _ = 10 ^ 10 * Wl := by
        rw [show (10 : ℝ) ^ 20 * Wl ^ 2 = (10 ^ 10 * Wl) ^ 2 by ring]
        exact Real.sqrt_sq (by positivity)

theorem WtoH : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.Spaces.SmoothNbhd f →
    Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) →
    Work.Spaces.HkMem α 4 f →
    Work.Spaces.HkNorm α 4 f ≤ C * Work.Spaces.WlInf α 4
      (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) := by
  refine ⟨10 ^ 10, by norm_num, ?_⟩
  intro α f hα hα1 hsm hmem _
  exact WtoH_main hα hα1 hsm hmem

end Work.Elliptic
