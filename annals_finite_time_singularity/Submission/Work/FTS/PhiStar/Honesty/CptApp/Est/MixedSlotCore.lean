import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstDefs
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstAux.ZetaBound
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.PhiStar.Honesty.CptApp.Est.MixedSlotAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CptApp.Est

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- **The termwise bound.** For `a ≤ i`, `b ≤ j`, the product
`D_z^bD_θ^a(χζ-1) · D_z^{j-b}D_θ^{i-a}F · Wt` is bounded in square by `Base · Good`, where
`Base` dominates both coefficient bounds `(1+K b²)(1+L a²)`.  Three cases: (i) `a=b=0`, where
`(χζ-1)² ≤ omegaInd` and the `F`-factor is an `ℋ^k`-slot; (ii) `i - a = 0` (so `a = i ≥ 1`),
where the coefficient bound with `thShrink` is used and the `F`-factor is a pure `D_z`-slot,
absorbed by the second group of `Good`; (iii) `1 ≤ i - a`, where both factors are
`Ω_n`-supported slots. -/
theorem ems_core_le (k : ℕ) {Base : ℝ} (hBase : 1 ≤ Base)
    (hCoeffInd : ∀ (n a b : ℕ), 2 ≤ n → 1 ≤ a + b → a ≤ k → b ≤ k → ∀ z θ : ℝ,
      (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
          * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ) ^ 2
        ≤ Base * Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ)
    (hCoeffTs : ∀ (n a b : ℕ), 2 ≤ n → 1 ≤ a → a ≤ k → b ≤ k → ∀ z θ : ℝ,
      (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
          * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ) ^ 2
        ≤ Base * Work.FTS.PhiStar.Honesty.CptApp.thShrink n θ)
    {α : ℝ} {n : ℕ} {F : ℝ → ℝ → ℝ} (hn : 2 ≤ n) {i j : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ k)
    {a b : ℕ} (ha : a ≤ i) (hb : b ≤ j) {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
          * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ
        * Work.Spaces.mixed (j - b) (i - a) F z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ Base * Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ := by
  have hBase0 : 0 ≤ Base := le_trans zero_le_one hBase
  have hG : 0 ≤ Good α k n F z θ := Good_nonneg α k n F hθ
  have hgnn : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_of_mem_Iθ hθ
  by_cases h0 : a + b = 0
  · have ha0 : a = 0 := by omega
    have hb0 : b = 0 := by omega
    subst ha0; subst hb0
    have h1 : (Work.FTS.PhiStar.Honesty.CptApp.chiR n z
        * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) ^ 2 ≤ omegaInd n z θ :=
      chiR_zetaR_sub_one_sq_le hn z θ
    have h2 : (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α k F z θ :=
      Work.Spaces.sq_le_HkIntegrand_mixed α k F z θ i j hi hij
    have h3 : ((Work.FTS.PhiStar.Honesty.CptApp.chiR n z
          * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1)
        * Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ omegaInd n z θ * Work.Spaces.HkIntegrand α k F z θ := by
      rw [show ((Work.FTS.PhiStar.Honesty.CptApp.chiR n z
            * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1)
          * Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2
          = (Work.FTS.PhiStar.Honesty.CptApp.chiR n z
              * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) ^ 2
            * (Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2 from by ring]
      exact mul_le_mul h1 h2 (sq_nonneg _) (omegaInd_nonneg n z θ)
    calc ((Work.FTS.PhiStar.Honesty.CptApp.chiR n z
            * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1)
          * Work.Spaces.mixed j i F z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ omegaInd n z θ * Work.Spaces.HkIntegrand α k F z θ := h3
      _ = omegaPart α k n F z θ := ems_omegaInd_mul_HkIntegrand α k n F z θ
      _ ≤ Good α k n F z θ := ems_omegaPart_le_Good α k n F hθ
      _ ≤ Base * Good α k n F z θ := le_mul_of_one_le_left hG hBase
  · have hab : 1 ≤ a + b := by omega
    have hWt2 := ems_Wt_sq (α := α) (z := z) (θ := θ) hgnn
    by_cases hia : i - a = 0
    · -- the coefficient carries the full angular weight: use the `thShrink` bound
      have ha1 : 1 ≤ a := by omega
      have hs : j - b < k := by omega
      have hX : (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
            * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ) ^ 2
          ≤ Base * thShrink n θ := hCoeffTs n a b hn ha1 (by omega) (by omega) z θ
      have hYeq : Work.Spaces.mixed (j - b) (i - a) F z θ
          = Work.Spaces.DzIter (j - b) F z θ := by
        rw [hia, Work.Spaces.mixed_zero_right]
      have hYb : thShrink n θ
            * (Work.Spaces.mixed (j - b) (i - a) F z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ thShrink n θ * (∑ s ∈ Finset.range k, (Work.Spaces.DzIter s F z θ) ^ 2
              * (Work.Spaces.w z) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
        rw [hYeq, show (Work.Spaces.DzIter (j - b) F z θ * Work.Spaces.Wt α z θ) ^ 2
            = (Work.Spaces.DzIter (j - b) F z θ) ^ 2 * (Work.Spaces.w z) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) from by
          rw [mul_pow, hWt2]; ring]
        exact ems_zslot_le_thShrinkSum (F := F) (α := α) (n := n) hs hθ
      calc (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
                * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ
              * Work.Spaces.mixed (j - b) (i - a) F z θ * Work.Spaces.Wt α z θ) ^ 2
          = (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
                * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ) ^ 2
              * (Work.Spaces.mixed (j - b) (i - a) F z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
        _ ≤ (Base * thShrink n θ)
              * (Work.Spaces.mixed (j - b) (i - a) F z θ * Work.Spaces.Wt α z θ) ^ 2 :=
            mul_le_mul_of_nonneg_right hX (sq_nonneg _)
        _ = Base * (thShrink n θ
              * (Work.Spaces.mixed (j - b) (i - a) F z θ * Work.Spaces.Wt α z θ) ^ 2) := by ring
        _ ≤ Base * (thShrink n θ * (∑ s ∈ Finset.range k, (Work.Spaces.DzIter s F z θ) ^ 2
              * (Work.Spaces.w z) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) :=
            mul_le_mul_of_nonneg_left hYb hBase0
        _ ≤ Base * Good α k n F z θ :=
            mul_le_mul_of_nonneg_left (ems_thShrink_sum_le_Good α k n F hθ) hBase0
    · have hia1 : 1 ≤ i - a := by omega
      have hX : (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
            * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ) ^ 2
          ≤ Base * omegaInd n z θ := hCoeffInd n a b hn hab (by omega) (by omega) z θ
      have hY : (Work.Spaces.mixed (j - b) (i - a) F z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α k F z θ :=
        Work.Spaces.sq_le_HkIntegrand_mixed α k F z θ (i - a) (j - b) hia1 (by omega)
      calc (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
                * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ
              * Work.Spaces.mixed (j - b) (i - a) F z θ * Work.Spaces.Wt α z θ) ^ 2
          = (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
                * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ) ^ 2
              * (Work.Spaces.mixed (j - b) (i - a) F z θ * Work.Spaces.Wt α z θ) ^ 2 := by ring
        _ ≤ (Base * omegaInd n z θ) * Work.Spaces.HkIntegrand α k F z θ :=
            mul_le_mul hX hY (sq_nonneg _) (mul_nonneg hBase0 (omegaInd_nonneg n z θ))
        _ = Base * omegaPart α k n F z θ := by
            rw [mul_assoc, ems_omegaInd_mul_HkIntegrand α k n F z θ]
        _ ≤ Base * Good α k n F z θ :=
            mul_le_mul_of_nonneg_left (ems_omegaPart_le_Good α k n F hθ) hBase0

/-- **The `(χζ-1)·F` group of the expansion.** The full double sum of Leibniz terms of
`(χζ-1)·F` is bounded in square, after multiplication by `Wt`, by `C · Good`. -/
theorem ems_prod_sq_le (k : ℕ) (Base : ℝ) (hBase : 1 ≤ Base)
    (hCoeffInd : ∀ (n a b : ℕ), 2 ≤ n → 1 ≤ a + b → a ≤ k → b ≤ k → ∀ z θ : ℝ,
      (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
          * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ) ^ 2
        ≤ Base * Work.FTS.PhiStar.Honesty.CptApp.omegaInd n z θ)
    (hCoeffTs : ∀ (n a b : ℕ), 2 ≤ n → 1 ≤ a → a ≤ k → b ≤ k → ∀ z θ : ℝ,
      (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
          * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ) ^ 2
        ≤ Base * Work.FTS.PhiStar.Honesty.CptApp.thShrink n θ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ) (n : ℕ) (F : ℝ → ℝ → ℝ), 0 < α → 2 ≤ n →
        ∀ (i j : ℕ), 1 ≤ i → i + j ≤ k → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
          ((∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              ((i.choose a : ℝ) * (j.choose b : ℝ))
                * (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
                      * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ
                   * Work.Spaces.mixed (j - b) (i - a) F z θ))
            * Work.Spaces.Wt α z θ) ^ 2
          ≤ C * Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ := by
  refine ⟨((k : ℝ) + 1) ^ 8 * (16 : ℝ) ^ k * Base + 1, by positivity, ?_⟩
  intro α n F hα hn i j hi hij z hz θ hθ
  have hBase0 : 0 ≤ Base := le_trans zero_le_one hBase
  have hG : 0 ≤ Good α k n F z θ := Good_nonneg α k n F hθ
  have h16 : 0 ≤ (16 : ℝ) ^ k := by positivity
  have hcoef : ∀ a b : ℕ, a ≤ i → b ≤ j →
      ((i.choose a : ℝ) * (j.choose b : ℝ)) ^ 2 ≤ (16 : ℝ) ^ k := by
    intro a b ha hb
    have h1 : i.choose a ≤ 2 ^ i := Nat.choose_le_two_pow i a
    have h2 : j.choose b ≤ 2 ^ j := Nat.choose_le_two_pow j b
    have h3 : (i.choose a : ℝ) * (j.choose b : ℝ) ≤ (2 : ℝ) ^ k := by
      have h4 : (i.choose a : ℝ) * (j.choose b : ℝ)
          ≤ (2 : ℝ) ^ i * (2 : ℝ) ^ j := by
        refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
        · exact_mod_cast h1
        · exact_mod_cast h2
      have h5 : (2 : ℝ) ^ i * (2 : ℝ) ^ j = (2 : ℝ) ^ (i + j) := by rw [← pow_add]
      have h6 : (2 : ℝ) ^ (i + j) ≤ (2 : ℝ) ^ k :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      rw [h5] at h4
      exact le_trans h4 h6
    have h7 : ((2 : ℝ) ^ k) ^ 2 ≤ (16 : ℝ) ^ k := by
      rw [← pow_mul]
      rw [show (16 : ℝ) = 2 ^ 4 from by norm_num, ← pow_mul]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    calc ((i.choose a : ℝ) * (j.choose b : ℝ)) ^ 2 ≤ ((2 : ℝ) ^ k) ^ 2 :=
          pow_le_pow_left₀ (by positivity) h3 2
      _ ≤ (16 : ℝ) ^ k := h7
  let T : ℕ → ℕ → ℝ := fun a b => ((i.choose a : ℝ) * (j.choose b : ℝ))
      * (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
            * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ
         * Work.Spaces.mixed (j - b) (i - a) F z θ) * Work.Spaces.Wt α z θ
  have hterm : ∀ a b : ℕ, a ≤ i → b ≤ j →
      (T a b) ^ 2 ≤ ((i.choose a : ℝ) * (j.choose b : ℝ)) ^ 2
        * (Base * Good α k n F z θ) := by
    intro a b ha hb
    have hc : (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
          * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ
        * Work.Spaces.mixed (j - b) (i - a) F z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Base * Work.FTS.PhiStar.Honesty.CptApp.Good α k n F z θ :=
      ems_core_le k (Base := Base) hBase hCoeffInd hCoeffTs (α := α) (F := F) hn hi hij ha hb
        (z := z) hθ
    calc (T a b) ^ 2 = ((i.choose a : ℝ) * (j.choose b : ℝ)) ^ 2
          * (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
                * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ
              * Work.Spaces.mixed (j - b) (i - a) F z θ * Work.Spaces.Wt α z θ) ^ 2 := by
          simp only [T]; ring
      _ ≤ ((i.choose a : ℝ) * (j.choose b : ℝ)) ^ 2 * (Base * Good α k n F z θ) :=
          mul_le_mul_of_nonneg_left hc (sq_nonneg _)
  have hSsplit : (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
        ((i.choose a : ℝ) * (j.choose b : ℝ))
          * (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
                * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ
             * Work.Spaces.mixed (j - b) (i - a) F z θ)) * Work.Spaces.Wt α z θ
      = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), T a b := by
    simp only [Finset.sum_mul, T]
  have hcs : (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), T a b) ^ 2
      ≤ (((i : ℝ) + 1) * ((j : ℝ) + 1))
        * (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), (T a b) ^ 2) := by
    have h1 := sq_sum_le_card_mul_sum_sq (s := Finset.range (i + 1))
      (f := fun a => ∑ b ∈ Finset.range (j + 1), T a b)
    have h1' : (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), T a b) ^ 2
        ≤ ((i : ℝ) + 1) * ∑ a ∈ Finset.range (i + 1),
            (∑ b ∈ Finset.range (j + 1), T a b) ^ 2 := by
      simpa only [Finset.card_range, Nat.cast_add, Nat.cast_one] using h1
    have h2 : ∀ a : ℕ, (∑ b ∈ Finset.range (j + 1), T a b) ^ 2
        ≤ ((j : ℝ) + 1) * ∑ b ∈ Finset.range (j + 1), (T a b) ^ 2 := by
      intro a
      have h := sq_sum_le_card_mul_sum_sq (s := Finset.range (j + 1)) (f := fun b => T a b)
      simpa only [Finset.card_range, Nat.cast_add, Nat.cast_one] using h
    calc (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), T a b) ^ 2
        ≤ ((i : ℝ) + 1) * ∑ a ∈ Finset.range (i + 1),
            (∑ b ∈ Finset.range (j + 1), T a b) ^ 2 := h1'
      _ ≤ ((i : ℝ) + 1) * ∑ a ∈ Finset.range (i + 1),
            (((j : ℝ) + 1) * ∑ b ∈ Finset.range (j + 1), (T a b) ^ 2) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => h2 a) (by positivity)
      _ = (((i : ℝ) + 1) * ((j : ℝ) + 1))
            * ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), (T a b) ^ 2 := by
          rw [← Finset.mul_sum]; ring
  have hsum2 : (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), (T a b) ^ 2)
      ≤ ((i : ℝ) + 1) * (((j : ℝ) + 1) * ((16 : ℝ) ^ k * (Base * Good α k n F z θ))) := by
    have hper : ∀ a ∈ Finset.range (i + 1), ∀ b ∈ Finset.range (j + 1),
        (T a b) ^ 2 ≤ (16 : ℝ) ^ k * (Base * Good α k n F z θ) := by
      intro a ha b hb
      have hai : a ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
      have hbj : b ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
      exact le_trans (hterm a b hai hbj)
        (mul_le_mul_of_nonneg_right (hcoef a b hai hbj) (mul_nonneg hBase0 hG))
    calc (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), (T a b) ^ 2)
        ≤ ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            ((16 : ℝ) ^ k * (Base * Good α k n F z θ)) :=
          Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hper a ha b hb
      _ = ((i : ℝ) + 1) * (((j : ℝ) + 1) * ((16 : ℝ) ^ k * (Base * Good α k n F z θ))) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hNle : ((i : ℝ) + 1) * ((j : ℝ) + 1) ≤ ((k : ℝ) + 1) * ((k : ℝ) + 1) := by
    have hi1 : (i : ℝ) + 1 ≤ (k : ℝ) + 1 := by
      have : i + 1 ≤ k + 1 := by omega
      exact_mod_cast this
    have hj1 : (j : ℝ) + 1 ≤ (k : ℝ) + 1 := by
      have : j + 1 ≤ k + 1 := by omega
      exact_mod_cast this
    exact mul_le_mul hi1 hj1 (by positivity) (by positivity)
  have hN2 : (((i : ℝ) + 1) * ((j : ℝ) + 1)) ^ 2 ≤ ((k : ℝ) + 1) ^ 4 := by
    calc (((i : ℝ) + 1) * ((j : ℝ) + 1)) ^ 2
        ≤ (((k : ℝ) + 1) * ((k : ℝ) + 1)) ^ 2 := pow_le_pow_left₀ (by positivity) hNle 2
      _ = ((k : ℝ) + 1) ^ 4 := by ring
  have hpow : ((k : ℝ) + 1) ^ 4 ≤ ((k : ℝ) + 1) ^ 8 := by
    have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    have h1 : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 4 := one_le_pow₀ hk1
    calc ((k : ℝ) + 1) ^ 4 = ((k : ℝ) + 1) ^ 4 * 1 := by ring
      _ ≤ ((k : ℝ) + 1) ^ 4 * ((k : ℝ) + 1) ^ 4 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ((k : ℝ) + 1) ^ 8 := by ring
  calc ((∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ((i.choose a : ℝ) * (j.choose b : ℝ))
            * (Work.Spaces.mixed b a (fun z θ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z
                  * Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ - 1) z θ
               * Work.Spaces.mixed (j - b) (i - a) F z θ))
        * Work.Spaces.Wt α z θ) ^ 2
      = (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), T a b) ^ 2 := by rw [hSsplit]
    _ ≤ (((i : ℝ) + 1) * ((j : ℝ) + 1))
          * (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), (T a b) ^ 2) := hcs
    _ ≤ (((i : ℝ) + 1) * ((j : ℝ) + 1))
          * (((i : ℝ) + 1) * (((j : ℝ) + 1)
              * ((16 : ℝ) ^ k * (Base * Good α k n F z θ)))) :=
        mul_le_mul_of_nonneg_left hsum2 (by positivity)
    _ = ((((i : ℝ) + 1) * ((j : ℝ) + 1)) ^ 2)
          * ((16 : ℝ) ^ k * (Base * Good α k n F z θ)) := by ring
    _ ≤ (((k : ℝ) + 1) ^ 4) * ((16 : ℝ) ^ k * (Base * Good α k n F z θ)) :=
        mul_le_mul_of_nonneg_right hN2 (mul_nonneg h16 (mul_nonneg hBase0 hG))
    _ ≤ (((k : ℝ) + 1) ^ 8) * ((16 : ℝ) ^ k * (Base * Good α k n F z θ)) :=
        mul_le_mul_of_nonneg_right hpow (mul_nonneg h16 (mul_nonneg hBase0 hG))
    _ ≤ ((((k : ℝ) + 1) ^ 8 * (16 : ℝ) ^ k * Base + 1))
          * Good α k n F z θ := by nlinarith [h16, hBase0, hG]

end Work.FTS.PhiStar.Honesty.CptApp.Est
