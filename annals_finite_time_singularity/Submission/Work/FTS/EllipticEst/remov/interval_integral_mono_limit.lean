import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open MeasureTheory Filter

/-- For `a ≤ b` the interval integral `∫ x in a..b, f x` agrees with the set integral over the
open interval `(a, b)`. -/
theorem intervalIntegral_eq_setIntegral_Ioo {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) :
    (∫ x in a..b, f x) = ∫ x in Set.Ioo a b, f x := by
  rw [intervalIntegral.integral_of_le hab, MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- If `f` is nonnegative on `s`, strongly measurable there, and its upper Lebesgue integral
`∫⁻ x in s, ofReal (f x)` is bounded by `ofReal K` with `0 ≤ K`, then `f` is integrable on `s`
and its Bochner integral is at most `K`. -/
theorem integrable_of_lintegral_ofReal_le' {f : ℝ → ℝ} {s : Set ℝ} {K : ℝ}
    (hs : MeasurableSet s) (hK : 0 ≤ K)
    (haesm : AEStronglyMeasurable f (volume.restrict s))
    (hnn : ∀ x ∈ s, 0 ≤ f x)
    (hint : ∫⁻ x in s, ENNReal.ofReal (f x) ≤ ENNReal.ofReal K) :
    IntegrableOn f s ∧ (∫ x in s, f x) ≤ K := by
  have hnn_ae : 0 ≤ᵐ[volume.restrict s] f :=
    (ae_restrict_iff' hs).mpr (Eventually.of_forall (fun x hx => hnn x hx))
  have hfin : HasFiniteIntegral f (volume.restrict s) :=
    (hasFiniteIntegral_iff_ofReal hnn_ae).mpr (lt_of_le_of_lt hint ENNReal.ofReal_lt_top)
  have hintg : Integrable f (volume.restrict s) := ⟨haesm, hfin⟩
  refine ⟨hintg, ?_⟩
  have h1 : ENNReal.ofReal (∫ x in s, f x) = ∫⁻ x in s, ENNReal.ofReal (f x) :=
    ofReal_integral_eq_lintegral_ofReal hintg hnn_ae
  exact (ENNReal.ofReal_le_ofReal_iff hK).mp (h1.trans_le hint)

/-- **Monotone convergence for a family of interval integrals.**  If `f ≥ 0` is continuous on
`(a, β)`, is *honestly* integrable on each `(a, b)` with `b < β` (this hypothesis is needed: for a
non-integrable `f` the Bochner interval integral is `0`, so the conclusion's first conjunct could
not follow), and all those interval integrals are `≤ K`, then `f` is integrable on `(a, β)` and
`∫_{(a,β)} f ≤ K`.  (The sibling `interval_integral_le_of_forall_le` is the same lemma *without*
the `hint` hypothesis, and is false as shown there by the counterexample `f x = x^{-2}` on `(0,1)`.) -/
theorem interval_integral_mono_limit {a β : ℝ} (ha : a < β) {f : ℝ → ℝ} {K : ℝ}
    (hcont : ContinuousOn f (Set.Ioo a β))
    (hnn : ∀ x ∈ Set.Ioo a β, 0 ≤ f x)
    (hint : ∀ b ∈ Set.Ioo a β, MeasureTheory.IntegrableOn f (Set.Ioo a b))
    (hK : ∀ b ∈ Set.Ioo a β, (∫ x in a..b, f x) ≤ K) :
    MeasureTheory.IntegrableOn f (Set.Ioo a β) ∧ (∫ x in Set.Ioo a β, f x) ≤ K := by
  -- An increasing sequence `b n ↑ β` (`b n ∈ (a, β)`) exhausting `(a, β)`.
  set b : ℕ → ℝ := fun n => a + (β - a) * (1 - (1/2 : ℝ)^(n+1)) with hb
  have hβa : 0 < β - a := sub_pos.mpr ha
  have hpowpos : ∀ n : ℕ, 0 < (1/2 : ℝ)^(n+1) := fun n => pow_pos (by norm_num) _
  have hpowlt : ∀ n : ℕ, (1/2 : ℝ)^(n+1) < 1 :=
    fun n => pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero n)
  have ha_lt : ∀ n, a < b n := by
    intro n
    have h : 0 < (β - a) * (1 - (1/2 : ℝ)^(n+1)) :=
      mul_pos hβa (sub_pos.mpr (hpowlt n))
    simp only [hb]
    linarith
  have hlt_β : ∀ n, b n < β := by
    intro n
    have h1 : (1 : ℝ) - (1/2 : ℝ)^(n+1) < 1 := by have := hpowpos n; linarith
    have h2 : (β - a) * (1 - (1/2 : ℝ)^(n+1)) < (β - a) * 1 :=
      mul_lt_mul_of_pos_left h1 hβa
    simp only [hb]
    linarith
  have hmono : Monotone b := by
    intro m n hmn
    have hp : (1/2 : ℝ)^(n+1) ≤ (1/2 : ℝ)^(m+1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.succ_le_succ hmn)
    have h3 : (1 : ℝ) - (1/2 : ℝ)^(m+1) ≤ 1 - (1/2 : ℝ)^(n+1) := by linarith
    have h4 := mul_le_mul_of_nonneg_left h3 (le_of_lt hβa)
    simp only [hb]
    linarith
  have h0 : Tendsto (fun n : ℕ => (1/2 : ℝ)^(n+1)) atTop (nhds 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (show (0:ℝ) ≤ 1/2 by norm_num)
        (show (1/2:ℝ) < 1 by norm_num)).const_mul ((1/2 : ℝ))
    simpa [pow_succ'] using h
  have htend : Tendsto b atTop (nhds β) := by
    have h1 : Tendsto (fun n : ℕ => 1 - (1/2 : ℝ)^(n+1)) atTop (nhds 1) := by
      have hc : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
      simpa using hc.sub h0
    have h2 : Tendsto (fun n : ℕ => (β - a) * (1 - (1/2 : ℝ)^(n+1))) atTop
        (nhds ((β - a) * 1)) := h1.const_mul (β - a)
    have h3 : Tendsto (fun n : ℕ => a + (β - a) * (1 - (1/2 : ℝ)^(n+1))) atTop
        (nhds (a + (β - a) * 1)) := h2.const_add a
    have h4 : a + (β - a) * 1 = β := by ring
    rw [h4] at h3
    simpa [hb] using h3
  -- the `b n` exhaust `(a, β)`
  have hunion : (⋃ n : ℕ, Set.Ioo a (b n)) = Set.Ioo a β := by
    apply Set.Subset.antisymm
    · intro x hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨n, hn⟩ := hx
      exact ⟨hn.1, lt_of_lt_of_le hn.2 (le_of_lt (hlt_β n))⟩
    · intro x hx
      have hev : ∀ᶠ n in atTop, x < b n := htend.eventually (Ioi_mem_nhds hx.2)
      obtain ⟨n, hn⟩ := hev.exists
      rw [Set.mem_iUnion]
      exact ⟨n, hx.1, hn⟩
  have hdir : Directed (· ⊆ ·) (fun n : ℕ => Set.Ioo a (b n)) := by
    intro m n
    exact ⟨max m n, Set.Ioo_subset_Ioo_right (hmono (le_max_left m n)),
      Set.Ioo_subset_Ioo_right (hmono (le_max_right m n))⟩
  -- the upper Lebesgue integral over `(a, β)` is the supremum of those over `(a, b n)`
  have hbound : ∫⁻ x in Set.Ioo a β, ENNReal.ofReal (f x) ≤ ENNReal.ofReal K := by
    rw [← hunion]
    rw [MeasureTheory.setLIntegral_iUnion_of_directed (fun x => ENNReal.ofReal (f x)) hdir]
    refine iSup_le fun n => ?_
    have hn_mem : b n ∈ Set.Ioo a β := ⟨ha_lt n, hlt_β n⟩
    have hnn_ae : 0 ≤ᵐ[volume.restrict (Set.Ioo a (b n))] f :=
      (ae_restrict_iff' measurableSet_Ioo).mpr
        (Eventually.of_forall (fun x hx => hnn x ⟨hx.1, lt_trans hx.2 (hlt_β n)⟩))
    have hstep : ∫⁻ x in Set.Ioo a (b n), ENNReal.ofReal (f x)
        = ENNReal.ofReal (∫ x in Set.Ioo a (b n), f x) :=
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hint (b n) hn_mem) hnn_ae).symm
    calc ∫⁻ x in Set.Ioo a (b n), ENNReal.ofReal (f x)
        = ENNReal.ofReal (∫ x in Set.Ioo a (b n), f x) := hstep
      _ = ENNReal.ofReal (∫ x in a..b n, f x) := by
            rw [intervalIntegral_eq_setIntegral_Ioo (le_of_lt (ha_lt n))]
      _ ≤ ENNReal.ofReal K := ENNReal.ofReal_le_ofReal (hK (b n) hn_mem)
  -- `K` is nonnegative, since the interval integrals are nonnegative
  have hKnn : 0 ≤ K := by
    have hb0 : b 0 ∈ Set.Ioo a β := ⟨ha_lt 0, hlt_β 0⟩
    have h1 : (0 : ℝ) ≤ ∫ x in a..b 0, f x := by
      rw [intervalIntegral_eq_setIntegral_Ioo (le_of_lt (ha_lt 0))]
      exact setIntegral_nonneg measurableSet_Ioo
        (fun x hx => hnn x ⟨hx.1, lt_trans hx.2 (hlt_β 0)⟩)
    linarith [h1, hK (b 0) hb0]
  exact integrable_of_lintegral_ofReal_le' measurableSet_Ioo hKnn
    (hcont.aestronglyMeasurable measurableSet_Ioo) hnn hbound

end Work.FTS.EllipticEst.remov
