import Mathlib
import Submission.Work.BMF.parseval.Defs
import Submission.Work.BMF.stepKern_continuousOn
import Submission.Work.BMF.stepKern_uniform_bound
import Submission.Work.BMF.fatou_interval
import Submission.Work.BMF.norm_window_avg_le
import Submission.Work.BMF.aemeasurable_window_avg

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The single-window Perron reduction

The mean square of the short-interval window average
`winAvgS a h x = (1/h) ∑_{n ∈ [x, x+h]} a n` over `x ∈ [X, 2X]` is bounded by the
supremum, over the truncation parameter `T ≥ 1`, of the mean square of the truncated
Perron integral `perronP a X h T x = (2π)⁻¹ ∫_{-T}^{T} A(1+it) x^{it} Θ(h/x,t) dt`.

The proof is the same as for the two-window reduction: the per-term Perron identity
`x^{it} Θ(h/x,t) = ((x+h)^{1+it} - x^{1+it})/(h(1+it))` writes the truncated integral as a
difference of step kernels, the truncation error tends to `0` (the classical Perron step),
so that `perronP a X h T x → winAvgS a h x` as `T → ∞` for every `x` outside the countable
set `ℤ ∪ (ℤ - h)`; Fatou's lemma on the bounded interval `[X, 2X]`, together with the
uniform bound on `perronP`, then gives the claim.
-/

namespace Work.BMF

open MeasureTheory intervalIntegral Filter
open scoped BigOperators Topology

noncomputable section

/-! ## Definitions -/

/-- The explicit constant bound for the truncated single-window Perron integral. -/
private def Ub3 (X : ℝ) : ℝ := 4 * ((3 * X + 1) * (1 + 96 / (2 * Real.pi)))

/-- `∑_{n ∈ [X,3X]} a n · stepKern 1 T (y/n)`. -/
private def stepSum3 (a : ℕ → ℂ) (X T y : ℝ) : ℂ :=
  ∑ n ∈ natIcc X (3 * X), a n * Commons.Analysis.Complex.stepKern 1 T (y / (n : ℝ))

/-- The partial sum `∑_{n ∈ [X,3X], n < y} a n`. -/
private def stepLim3 (a : ℕ → ℂ) (X y : ℝ) : ℂ :=
  ∑ n ∈ (natIcc X (3 * X)).filter (fun n : ℕ => (n : ℝ) < y), a n

/-! ## Elementary helpers -/

private lemma one_add_I_mul_ne_zero (t : ℝ) : (1 + Complex.I * (t : ℂ)) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this

private lemma one_le_of_mem_natIcc {a b : ℝ} (ha : 1 ≤ a) {n : ℕ} (hn : n ∈ natIcc a b) :
    1 ≤ n := by
  have h1 : (⌈a⌉₊ : ℕ) ≤ n := (Finset.mem_Icc.mp hn).1
  have h2 : (1 : ℝ) ≤ (⌈a⌉₊ : ℝ) := le_trans ha (Nat.le_ceil a)
  have h3 : (1 : ℕ) ≤ ⌈a⌉₊ := by exact_mod_cast h2
  exact le_trans h3 h1

private lemma mem_natIcc {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {n : ℕ} :
    n ∈ natIcc a b ↔ a ≤ (n : ℝ) ∧ (n : ℝ) ≤ b := by
  rw [natIcc, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨le_trans (Nat.le_ceil a) (by exact_mod_cast h1),
      le_trans (by exact_mod_cast h2) (Nat.floor_le hb)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨Nat.ceil_le.mpr h1, Nat.le_floor h2⟩

/-- Norm of `(1/c) * v` for `c ≥ 1`. -/
private lemma norm_one_div_mul (c : ℝ) (hc : 1 ≤ c) (v : ℂ) :
    ‖(1 / (c : ℂ)) * v‖ ≤ ‖v‖ := by
  have hcpos : (0 : ℝ) < c := by linarith
  have hcinv : (1 : ℝ) / c ≤ 1 := by rw [div_le_one hcpos]; exact hc
  rw [norm_mul, norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg hcpos.le]
  calc (1 / c) * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hcinv (norm_nonneg v)
    _ = ‖v‖ := one_mul _

/-- `dirP a X ·` is continuous in `t`. -/
private lemma dirP_continuous (a : ℕ → ℂ) (X : ℝ) :
    Continuous (fun t : ℝ => dirP a X t) := by
  have hcont : Continuous
      (fun t : ℝ => ∑ n ∈ natIcc X (3 * X),
        a n * (n : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))) := by
    apply continuous_finsetSum
    intro n _
    have hf : Continuous (fun t : ℝ => -(1 + Complex.I * (t : ℂ))) := by fun_prop
    exact continuous_const.mul (hf.const_cpow (Or.inr (fun t => by
      intro h; have := congrArg Complex.re h; simp at this)))
  simpa only [dirP] using hcont

/-! ## The Perron identity -/

/-- `perronP a X h T x = (1/h) (stepSum3 (x+h) - stepSum3 x)`. -/
private lemma perronP_eq (a : ℕ → ℂ) {X h x T : ℝ}
    (hX : 1 ≤ X) (hx : 0 < x) (hh : 0 < h) (hT : 0 < T) :
    perronP a X h T x = (1 / h) * (stepSum3 a X T (x + h) - stepSum3 a X T x) := by
  have hpt : ∀ t : ℝ, (dirP a X t) * ((x : ℂ) ^ (Complex.I * (t : ℂ))) * (Theta (h / x) t)
      = (fun s : ℝ => (1 / h) * ((dirP a X s)
              * (((x + h : ℝ) : ℂ) ^ (1 + Complex.I * (s : ℂ))) / (1 + Complex.I * (s : ℂ))
            - (dirP a X s) * ((x : ℂ) ^ (1 + Complex.I * (s : ℂ)))
              / (1 + Complex.I * (s : ℂ)))) t := by
    intro t
    rw [mul_assoc, cpow_theta_identity h x t hx hh]
    have ht : (1 + Complex.I * (t : ℂ)) ≠ 0 := one_add_I_mul_ne_zero t
    have hhc : ((h : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
    field_simp
  have hint (y : ℝ) (hy : 0 < y) : IntervalIntegrable (fun s : ℝ =>
      (dirP a X s) * ((y : ℂ) ^ (1 + Complex.I * (s : ℂ))) / (1 + Complex.I * (s : ℂ)))
      volume (-T) T :=
    (Continuous.div
      ((dirP_continuous a X).mul
        ((by fun_prop : Continuous fun s : ℝ => (1 : ℂ) + Complex.I * (s : ℂ)).const_cpow
          (Or.inl (Complex.ofReal_ne_zero.mpr hy.ne'))))
      (by fun_prop) (fun s => one_add_I_mul_ne_zero s)).intervalIntegrable _ _
  unfold perronP
  rw [intervalIntegral.integral_congr (fun t _ => hpt t)]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_sub (hint (x + h) (by linarith)) (hint x hx)]
  have e1 := dirP_perron_integral a hX (by linarith : 0 < x + h) hT
  have e0 := dirP_perron_integral a hX hx hT
  simp only [stepSum3] at e1 e0 ⊢
  rw [← e1, ← e0]
  ring

/-! ## Continuity, bounds, convergence -/

private lemma stepSum3_continuousOn (a : ℕ → ℂ) {X T : ℝ} (hX : 1 ≤ X) :
    ContinuousOn (fun y : ℝ => stepSum3 a X T y) (Set.Ioi 0) := by
  unfold stepSum3
  refine continuousOn_finsetSum _ (fun n hn => ?_)
  have hn1 : 1 ≤ n := one_le_of_mem_natIcc hX hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hc : ContinuousOn (fun y : ℝ => Commons.Analysis.Complex.stepKern 1 T (y / (n : ℝ)))
      (Set.Ioi 0) :=
    (stepKern_continuousOn 1 T one_pos).comp (by fun_prop) (fun y hy => by
      rw [Set.mem_Ioi] at hy ⊢
      exact div_pos hy hnpos)
  exact hc.const_mul (a n)

private lemma perronP_continuousOn (a : ℕ → ℂ) {X h T : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hT : 0 < T) :
    ContinuousOn (fun x : ℝ => perronP a X h T x) (Set.Ioi 0) := by
  have hA : ContinuousOn (fun x : ℝ => stepSum3 a X T (x + h)) (Set.Ioi 0) :=
    (stepSum3_continuousOn a hX).comp (by fun_prop) (fun x hx => by
      rw [Set.mem_Ioi] at hx ⊢
      linarith)
  have h0 : ContinuousOn (fun x : ℝ => stepSum3 a X T x) (Set.Ioi 0) :=
    stepSum3_continuousOn a hX
  refine ContinuousOn.congr
    (f := fun x : ℝ => (1 / h) * (stepSum3 a X T (x + h) - stepSum3 a X T x)) ?_ ?_
  · exact (hA.sub h0).const_mul (1 / h)
  · intro x hx
    exact perronP_eq a hX hx hh hT

private lemma perronP_aemeasurable (a : ℕ → ℂ) {X h T : ℝ}
    (hX : 1 ≤ X) (hh : 0 < h) (hT : 0 < T) :
    AEMeasurable (fun x : ℝ => perronP a X h T x)
      (volume.restrict (Set.Ioc X (2 * X))) := by
  refine ContinuousOn.aemeasurable ?_ measurableSet_Ioc
  exact (perronP_continuousOn a hX hh hT).mono (fun x hx => by
    rw [Set.mem_Ioc] at hx
    rw [Set.mem_Ioi]
    linarith [hx.1, hX])

private lemma aemeasurable_winAvgS (a : ℕ → ℂ) (X h : ℝ) :
    AEMeasurable (fun x : ℝ => winAvgS a h x)
      (MeasureTheory.volume.restrict (Set.Ioc X (2 * X))) := by
  have hsub : Measurable (fun x : ℝ => winAvgS a h x) := by
    unfold winAvgS
    exact (measurable_window_sum a h).const_mul (1 / h)
  exact hsub.aemeasurable

private lemma stepSum3_bound (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) {X T y : ℝ} (hX : 1 ≤ X)
    (hT : 0 < T) (hy : 0 < y) (hy3 : y ≤ 3 * X) :
    ‖stepSum3 a X T y‖ ≤ (3 * X + 1) * (1 + 96 / (2 * Real.pi)) := by
  have hXpos : 0 < X := by linarith
  have hterm : ∀ n ∈ natIcc X (3 * X),
      ‖a n * Commons.Analysis.Complex.stepKern 1 T (y / (n : ℝ))‖
        ≤ 1 + 96 / (2 * Real.pi) := by
    intro n hn
    have hn1 : 1 ≤ n := one_le_of_mem_natIcc hX hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hyn : 0 < y / (n : ℝ) := div_pos hy hnpos
    have hXn : X ≤ (n : ℝ) :=
      (mem_natIcc hXpos.le (by linarith : (0 : ℝ) ≤ 3 * X)).mp hn |>.1
    have hy3' : y / (n : ℝ) ≤ 3 := by
      rw [div_le_iff₀ hnpos]
      linarith
    have hb := stepKern_uniform_bound 1 T (y / (n : ℝ)) one_pos hT hyn
    rw [Real.rpow_one] at hb
    rw [norm_mul]
    calc ‖a n‖ * ‖Commons.Analysis.Complex.stepKern 1 T (y / (n : ℝ))‖
        ≤ 1 * ‖Commons.Analysis.Complex.stepKern 1 T (y / (n : ℝ))‖ :=
          mul_le_mul_of_nonneg_right (ha n) (norm_nonneg _)
      _ ≤ 1 * (1 + (32 / (2 * Real.pi)) * (y / (n : ℝ))) :=
          mul_le_mul_of_nonneg_left hb (by norm_num)
      _ ≤ 1 * (1 + 96 / (2 * Real.pi)) := by
          have h32 : 0 ≤ 32 / (2 * Real.pi) := by positivity
          have h1' := mul_le_mul_of_nonneg_left hy3' h32
          have heq : (32 / (2 * Real.pi)) * 3 = 96 / (2 * Real.pi) := by ring
          linarith
      _ = 1 + 96 / (2 * Real.pi) := by ring
  have hcard : ((natIcc X (3 * X)).card : ℝ) ≤ 3 * X + 1 := by
    have h1 : (natIcc X (3 * X)).card ≤ ⌊3 * X⌋₊ + 1 := by
      calc (natIcc X (3 * X)).card ≤ (Finset.range (⌊3 * X⌋₊ + 1)).card := by
            refine Finset.card_le_card ?_
            intro n hn
            rw [natIcc, Finset.mem_Icc] at hn
            rw [Finset.mem_range]
            omega
        _ = ⌊3 * X⌋₊ + 1 := Finset.card_range _
    have h2 : ((⌊3 * X⌋₊ : ℕ) : ℝ) ≤ 3 * X := Nat.floor_le (a := 3 * X) (by linarith)
    calc ((natIcc X (3 * X)).card : ℝ) ≤ (⌊3 * X⌋₊ : ℝ) + 1 := by exact_mod_cast h1
      _ ≤ 3 * X + 1 := by linarith
  calc ‖stepSum3 a X T y‖
      ≤ ∑ n ∈ natIcc X (3 * X),
          ‖a n * Commons.Analysis.Complex.stepKern 1 T (y / (n : ℝ))‖ := by
        rw [stepSum3]; exact norm_sum_le _ _
    _ ≤ ∑ _n ∈ natIcc X (3 * X), (1 + 96 / (2 * Real.pi)) := Finset.sum_le_sum hterm
    _ = ((natIcc X (3 * X)).card : ℝ) * (1 + 96 / (2 * Real.pi)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (3 * X + 1) * (1 + 96 / (2 * Real.pi)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)

private lemma perronP_bound (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) {X h T x : ℝ}
    (hX : 1 ≤ X) (hh : 1 ≤ h) (hhX : h ≤ X) (hT : 0 < T) (hxX : X ≤ x) (hx2 : x ≤ 2 * X) :
    ‖perronP a X h T x‖ ≤ Ub3 X := by
  have hx0 : 0 < x := by linarith
  have h1pos : 0 < h := by linarith
  have hC : 0 ≤ (3 * X + 1) * (1 + 96 / (2 * Real.pi)) := by positivity
  have hS1 : ‖stepSum3 a X T (x + h)‖ ≤ (3 * X + 1) * (1 + 96 / (2 * Real.pi)) :=
    stepSum3_bound a ha hX hT (by linarith) (by linarith)
  have hS0 : ‖stepSum3 a X T x‖ ≤ (3 * X + 1) * (1 + 96 / (2 * Real.pi)) :=
    stepSum3_bound a ha hX hT hx0 (by linarith)
  rw [perronP_eq a hX hx0 h1pos hT, Ub3]
  have h1' := norm_one_div_mul h hh (stepSum3 a X T (x + h) - stepSum3 a X T x)
  have hb1 := norm_sub_le (stepSum3 a X T (x + h)) (stepSum3 a X T x)
  calc ‖(1 / h) * (stepSum3 a X T (x + h) - stepSum3 a X T x)‖
      ≤ ‖stepSum3 a X T (x + h) - stepSum3 a X T x‖ := h1'
    _ ≤ (3 * X + 1) * (1 + 96 / (2 * Real.pi)) + (3 * X + 1) * (1 + 96 / (2 * Real.pi)) := by
        linarith
    _ ≤ 4 * ((3 * X + 1) * (1 + 96 / (2 * Real.pi))) := by linarith

private lemma stepSum3_tendsto (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) {X y : ℝ} (hX : 1 ≤ X)
    (hy : 0 < y) (hne : ∀ n ∈ natIcc X (3 * X), (n : ℝ) ≠ y) :
    Tendsto (fun T : ℝ => stepSum3 a X T y) atTop (𝓝 (stepLim3 a X y)) := by
  have hconv : Tendsto (fun T : ℝ => stepSum3 a X T y - stepLim3 a X y) atTop (𝓝 0) := by
    rw [stepLim3]
    refine squeeze_zero_norm' ?_ (perron_error_tendsto y hy (natIcc X (3 * X)) hne)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hsum : stepSum3 a X T y
          - (∑ n ∈ (natIcc X (3 * X)).filter (fun n : ℕ => (n : ℝ) < y), a n)
        = ∑ n ∈ natIcc X (3 * X), a n * (Commons.Analysis.Complex.stepKern 1 T (y / (n : ℝ))
            - (if (n : ℝ) < y then (1 : ℂ) else 0)) := by
      rw [stepSum3, Finset.sum_filter, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun n _ => ?_)
      by_cases h : (n : ℝ) < y <;> simp only [h, if_true, if_false, sub_zero] <;> ring
    rw [hsum]
    calc ‖∑ n ∈ natIcc X (3 * X), a n * (Commons.Analysis.Complex.stepKern 1 T (y / (n : ℝ))
            - (if (n : ℝ) < y then (1 : ℂ) else 0))‖
        ≤ ∑ n ∈ natIcc X (3 * X),
            ‖a n * (Commons.Analysis.Complex.stepKern 1 T (y / (n : ℝ))
              - (if (n : ℝ) < y then (1 : ℂ) else 0))‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ natIcc X (3 * X),
            (32 / (2 * Real.pi)) * (y / (n : ℝ)) * min 1 (1 / (T * |Real.log (y / (n : ℝ))|)) := by
          refine Finset.sum_le_sum (fun n hn => ?_)
          have hn1 : 1 ≤ n := one_le_of_mem_natIcc hX hn
          have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
          have hz : 0 < y / (n : ℝ) := div_pos hy hnpos
          have hz1 : y / (n : ℝ) ≠ 1 := by
            intro hh
            apply hne n hn
            have h' := congrArg (fun z : ℝ => z * (n : ℝ)) hh
            rw [div_mul_cancel₀ _ hnpos.ne'] at h'
            simpa using h'.symm
          have hdev := Commons.Analysis.Complex.perronStep_deviation_pos 1 T (y / (n : ℝ))
            one_pos hT hz hz1
          have hiff : (1 < y / (n : ℝ)) ↔ ((n : ℝ) < y) := by
            rw [lt_div_iff₀ hnpos, one_mul]
          have hdev' : ‖Commons.Analysis.Complex.stepKern 1 T (y / (n : ℝ))
                - (if (n : ℝ) < y then (1 : ℂ) else 0)‖
              ≤ (32 / (2 * Real.pi)) * (y / (n : ℝ))
                * min 1 (1 / (T * |Real.log (y / (n : ℝ))|)) := by
            rw [if_congr hiff rfl rfl, Real.rpow_one] at hdev
            exact hdev
          rw [norm_mul]
          calc ‖a n‖ * ‖Commons.Analysis.Complex.stepKern 1 T (y / (n : ℝ))
                - (if (n : ℝ) < y then (1 : ℂ) else 0)‖
              ≤ 1 * ((32 / (2 * Real.pi)) * (y / (n : ℝ))
                  * min 1 (1 / (T * |Real.log (y / (n : ℝ))|))) :=
                mul_le_mul (ha n) hdev' (norm_nonneg _) (by norm_num)
            _ = (32 / (2 * Real.pi)) * (y / (n : ℝ))
                  * min 1 (1 / (T * |Real.log (y / (n : ℝ))|)) := by ring
  simpa using hconv.add_const (stepLim3 a X y)

private lemma stepLim3_sub (a : ℕ → ℂ) {X h x : ℝ} (hX : 1 ≤ X) (hh0 : 0 < h) (hh : h ≤ X)
    (hxX : X ≤ x) (hx2 : x ≤ 2 * X) (hxh : ∀ k : ℤ, (k : ℝ) ≠ x + h) :
    stepLim3 a X (x + h) - stepLim3 a X x = ∑ n ∈ natIcc x (x + h), a n := by
  have hxpos : 0 < x := by linarith
  have hsub : (natIcc X (3 * X)).filter (fun n : ℕ => (n : ℝ) < x)
      ⊆ (natIcc X (3 * X)).filter (fun n : ℕ => (n : ℝ) < x + h) := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, by linarith [hn.2]⟩
  have hset : (natIcc X (3 * X)).filter (fun n : ℕ => (n : ℝ) < x + h)
        \ (natIcc X (3 * X)).filter (fun n : ℕ => (n : ℝ) < x)
      = natIcc x (x + h) := by
    ext n
    rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter,
      mem_natIcc hxpos.le (by linarith : (0 : ℝ) ≤ x + h)]
    constructor
    · rintro ⟨⟨hF, hlt⟩, hnx⟩
      have hnx' : ¬ ((n : ℝ) < x) := fun h => hnx ⟨hF, h⟩
      exact ⟨not_lt.mp hnx', le_of_lt hlt⟩
    · rintro ⟨h1, h2⟩
      have hnF : n ∈ natIcc X (3 * X) :=
        (mem_natIcc (by linarith : (0 : ℝ) ≤ X) (by linarith : (0 : ℝ) ≤ 3 * X)).mpr
          ⟨le_trans hxX h1, by linarith⟩
      exact ⟨⟨hnF, lt_of_le_of_ne h2 (by simpa using hxh (n : ℤ))⟩,
        by rintro ⟨-, hlt⟩; linarith⟩
  have hsd := Finset.sum_sdiff (f := a) hsub
  rw [stepLim3, stepLim3, ← hsd, hset]
  ring

private lemma perronP_tendsto (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) {X h x : ℝ}
    (hX : 1 ≤ X) (hh1 : 1 ≤ h) (hhX : h ≤ X)
    (hxX : X ≤ x) (hx2 : x ≤ 2 * X) (hxZ : ∀ k : ℤ, (k : ℝ) ≠ x)
    (hxhZ : ∀ k : ℤ, (k : ℝ) ≠ x + h) :
    Tendsto (fun T : ℝ => perronP a X h T x) atTop (𝓝 (winAvgS a h x)) := by
  have hx0 : 0 < x := by linarith
  have hhpos : 0 < h := by linarith
  have hlim1 : Tendsto (fun T : ℝ => stepSum3 a X T (x + h)) atTop
      (𝓝 (stepLim3 a X (x + h))) :=
    stepSum3_tendsto a ha hX (by linarith) (fun n hn => by simpa using hxhZ (n : ℤ))
  have hlim0 : Tendsto (fun T : ℝ => stepSum3 a X T x) atTop (𝓝 (stepLim3 a X x)) :=
    stepSum3_tendsto a ha hX hx0 (fun n hn => by simpa using hxZ (n : ℤ))
  have hlim : Tendsto (fun T : ℝ => (1 / h) * (stepSum3 a X T (x + h) - stepSum3 a X T x))
      atTop (𝓝 ((1 / h) * (stepLim3 a X (x + h) - stepLim3 a X x))) :=
    (hlim1.sub hlim0).const_mul _
  have hev : (fun T : ℝ => (1 / h) * (stepSum3 a X T (x + h) - stepSum3 a X T x))
      =ᶠ[atTop] (fun T : ℝ => perronP a X h T x) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    exact (perronP_eq a hX hx0 hhpos (by linarith)).symm
  have hval : (1 / h) * (stepLim3 a X (x + h) - stepLim3 a X x) = winAvgS a h x := by
    rw [winAvgS, stepLim3_sub a hX hhpos hhX hxX hx2 hxhZ]
  rw [hval] at hlim
  exact hlim.congr' hev

private lemma ae_notMem_countable (s : Set ℝ) (hs : s.Countable) :
    ∀ᵐ x ∂(volume), x ∉ s := by
  rw [MeasureTheory.ae_iff]
  have h : {x : ℝ | ¬ x ∉ s} = s := by ext x; simp
  rw [h]
  exact hs.measure_zero volume

private lemma notMem_intSet (h y : ℝ) :
    ∀ᵐ x ∂(volume.restrict (Set.Ioc y (2 * y))),
      (∀ k : ℤ, (k : ℝ) ≠ x) ∧ (∀ k : ℤ, (k : ℝ) ≠ x + h) := by
  have hcount : (Set.range ((↑) : ℤ → ℝ)).Countable := Set.countable_range _
  have h1 : ({x : ℝ | ∃ k : ℤ, (k : ℝ) = x + h}).Countable := by
    have hpre := hcount.preimage (f := fun x : ℝ => x + h) (fun a b hab => by linarith)
    simpa [Set.preimage] using hpre
  have h0 : (Set.range ((↑) : ℤ → ℝ) ∪ {x : ℝ | ∃ k : ℤ, (k : ℝ) = x + h}).Countable :=
    hcount.union h1
  have hae := ae_notMem_countable _ h0
  refine (MeasureTheory.ae_restrict_of_ae hae).mono (fun x hx => ?_)
  constructor
  · intro k hk
    apply hx
    rw [Set.mem_union]
    exact Or.inl ⟨k, hk⟩
  · intro k hk
    apply hx
    rw [Set.mem_union]
    exact Or.inr ⟨k, hk⟩

private lemma perronP_tendsto_ae (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) {X h : ℝ}
    (hX : 1 ≤ X) (hh1 : 1 ≤ h) (hhX : h ≤ X) :
    ∀ᵐ x ∂(volume.restrict (Set.Ioc X (2 * X))),
      Tendsto (fun n : ℕ => perronP a X h ((n : ℝ) + 1) x) atTop (𝓝 (winAvgS a h x)) := by
  have hmem : ∀ᵐ x ∂(volume.restrict (Set.Ioc X (2 * X))), x ∈ Set.Ioc X (2 * X) :=
    MeasureTheory.ae_restrict_mem measurableSet_Ioc
  filter_upwards [notMem_intSet h X, hmem] with x hx1 hx
  exact (perronP_tendsto a ha hX hh1 hhX (le_of_lt hx.1) hx.2 hx1.1 hx1.2).comp
    (tendsto_atTop_add_const_right _ (1 : ℝ) (tendsto_natCast_atTop_atTop (R := ℝ)))

/-! ## The main theorem -/

theorem perron_reduction_single :
    ∀ (a : ℕ → ℂ), (∀ n, ‖a n‖ ≤ 1) → ∀ (X h : ℝ), 1 ≤ X → 1 ≤ h → h ≤ X →
      (1/X) * (∫ x in X..(2*X), ‖winAvgS a h x‖^2)
        ≤ ⨆ (T : {T : ℝ // 1 ≤ T}), (1/X) * (∫ x in X..(2*X), ‖perronP a X h T.1 x‖^2) := by
  intro a ha X h hX hh1 hhX
  have hXpos : 0 < X := by linarith
  have hhpos : 0 < h := by linarith
  have hge1 : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 1 := fun n => by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hpos1 : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hD : ∀ x ∈ Set.Ioc X (2 * X), ‖winAvgS a h x‖ ≤ 4 := by
    intro x hx
    have hx0 : 0 ≤ x := by linarith [hx.1, hXpos]
    have hA := norm_window_avg_le a ha x h hx0 hh1
    rw [winAvgS]
    linarith [hA]
  have hF : ∀ T : ℝ, 1 ≤ T → ∀ x ∈ Set.Ioc X (2 * X), ‖perronP a X h T x‖ ≤ Ub3 X := by
    intro T hT x hx
    exact perronP_bound a ha hX hh1 hhX (by linarith) (le_of_lt hx.1) hx.2
  have hfat := fatou_interval (a := X) (b := 2 * X) (by linarith) (max 4 (Ub3 X))
      (le_trans (by norm_num) (le_max_left _ _))
      (winAvgS a h) (fun n : ℕ => perronP a X h ((n : ℝ) + 1))
      (fun x hx => le_trans (hD x hx) (le_max_left _ _))
      (fun n x hx => le_trans (hF _ (hge1 n) x hx) (le_max_right _ _))
      (fun n => perronP_aemeasurable a hX hhpos (hpos1 n))
      (aemeasurable_winAvgS a X h)
      (perronP_tendsto_ae a ha hX hh1 hhX)
  have hUbint : ∀ T : {T : ℝ // 1 ≤ T},
      ∫ x in X..(2 * X), ‖perronP a X h T.1 x‖ ^ 2 ≤ (Ub3 X) ^ 2 * X := by
    intro T
    have hcont : ContinuousOn (fun x : ℝ => ‖perronP a X h T.1 x‖ ^ 2)
        (Set.uIcc X (2 * X)) := by
      have hc := perronP_continuousOn a hX hhpos (by linarith [T.2] : (0 : ℝ) < T.1)
      exact (hc.norm.pow 2).mono (fun x hx => by
        have hx' : X ≤ x := by
          have hh := hx
          rw [Set.uIcc_of_le (by linarith : X ≤ 2 * X), Set.mem_Icc] at hh
          exact hh.1
        rw [Set.mem_Ioi]
        linarith [hx', hXpos])
    calc ∫ x in X..(2 * X), ‖perronP a X h T.1 x‖ ^ 2
        ≤ ∫ x in X..(2 * X), (Ub3 X) ^ 2 := by
          refine intervalIntegral.integral_mono_on (by linarith) hcont.intervalIntegrable
            intervalIntegrable_const (fun x hx => ?_)
          have hb := perronP_bound a ha hX hh1 hhX (by linarith [T.2] : (0 : ℝ) < T.1) hx.1 hx.2
          nlinarith [hb, norm_nonneg (perronP a X h T.1 x)]
      _ = (Ub3 X) ^ 2 * X := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          ring
  have hbB : BddAbove (Set.range (fun T : {T : ℝ // 1 ≤ T} =>
      ∫ x in X..(2 * X), ‖perronP a X h T.1 x‖ ^ 2)) :=
    ⟨(Ub3 X) ^ 2 * X, by rintro y ⟨T, rfl⟩; exact hUbint T⟩
  have hbS : BddAbove (Set.range (fun T : {T : ℝ // 1 ≤ T} =>
      (1 / X) * ∫ x in X..(2 * X), ‖perronP a X h T.1 x‖ ^ 2)) :=
    ⟨(1 / X) * ((Ub3 X) ^ 2 * X), by
      rintro y ⟨T, rfl⟩
      exact mul_le_mul_of_nonneg_left (hUbint T) (by positivity)⟩
  have hmono : (⨆ n : ℕ, ∫ x in X..(2 * X), ‖perronP a X h ((n : ℝ) + 1) x‖ ^ 2)
      ≤ (⨆ T : {T : ℝ // 1 ≤ T}, ∫ x in X..(2 * X), ‖perronP a X h T.1 x‖ ^ 2) := by
    refine ciSup_le (fun n => ?_)
    exact le_ciSup hbB ⟨(n : ℝ) + 1, hge1 n⟩
  have hstep : (⨆ T : {T : ℝ // 1 ≤ T}, ∫ x in X..(2 * X), ‖perronP a X h T.1 x‖ ^ 2)
      ≤ X * (⨆ T : {T : ℝ // 1 ≤ T},
          (1 / X) * ∫ x in X..(2 * X), ‖perronP a X h T.1 x‖ ^ 2) := by
    refine ciSup_le (fun T => ?_)
    have h1' : (1 / X) * (∫ x in X..(2 * X), ‖perronP a X h T.1 x‖ ^ 2)
        ≤ (⨆ T : {T : ℝ // 1 ≤ T},
          (1 / X) * ∫ x in X..(2 * X), ‖perronP a X h T.1 x‖ ^ 2) := le_ciSup hbS T
    have h2' : ∫ x in X..(2 * X), ‖perronP a X h T.1 x‖ ^ 2
        = X * ((1 / X) * ∫ x in X..(2 * X), ‖perronP a X h T.1 x‖ ^ 2) := by
      field_simp
    rw [h2']
    exact mul_le_mul_of_nonneg_left h1' hXpos.le
  have hmain : ∫ x in X..(2 * X), ‖winAvgS a h x‖ ^ 2
      ≤ X * (⨆ T : {T : ℝ // 1 ≤ T},
          (1 / X) * ∫ x in X..(2 * X), ‖perronP a X h T.1 x‖ ^ 2) :=
    le_trans (le_trans hfat hmono) hstep
  have hfin : (1 / X) * (∫ x in X..(2 * X), ‖winAvgS a h x‖ ^ 2)
      ≤ (⨆ T : {T : ℝ // 1 ≤ T},
          (1 / X) * ∫ x in X..(2 * X), ‖perronP a X h T.1 x‖ ^ 2) := by
    calc (1 / X) * (∫ x in X..(2 * X), ‖winAvgS a h x‖ ^ 2)
        ≤ (1 / X) * (X * (⨆ T : {T : ℝ // 1 ≤ T},
            (1 / X) * ∫ x in X..(2 * X), ‖perronP a X h T.1 x‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hmain (by positivity)
      _ = (⨆ T : {T : ℝ // 1 ≤ T},
            (1 / X) * ∫ x in X..(2 * X), ‖perronP a X h T.1 x‖ ^ 2) := by
          field_simp
  exact hfin

end

end Work.BMF
