import Mathlib
import Submission.Work.OddVolterra.Window.krad_data
import Submission.Work.OddVolterra.Window.TWU_aux

/-!
# The uniform `krad` window data on the transition window `[7/10, 19/20]`

The requested lemma `krad_window_data` is the `[7/10, 19/20]`-window version of
`krad_data`: on the box
`σ, a ∈ [7/10, 19/20]`, `|t| ∈ [1/5, 2]`, a `C^∞` perturbation `h` with
`|h^{(k)}| ≤ 1/100` for `k ≤ n + 2` has

`1/100 ≤ krad h σ t a ≤ 10`,  `|∂_a krad h σ t a| ≤ 5`.

The proof reuses the two quantitative lemmas of `Window/krad_data.lean`:

* `krad_pointwise_data` (lower/upper bound and `O(δ)`-closeness to the
  unperturbed radicand) — it is stated for `a ≤ σ`, so for `a > σ` we transfer it
  through the **symmetry** `krad h σ t a = krad h a t σ`;
* `krad_lipschitz_window` — its `5`-Lipschitz bound on the box `[3/8, 3/2]` is
  uniform in the relative position of `a` and `σ`, so it applies verbatim here
  and yields the `deriv` bound through the mean value inequality.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.Window

noncomputable section

/-! ## The symmetry of the radicand in its two slope slots -/

/-- The divided difference `hquot h u σ = ∫_0^1 h'(u + τ(σ-u)) dτ` is symmetric in
`u, σ`. -/
lemma krad_window_hquot_comm (h : ℝ → ℝ) (u σ : ℝ) :
    Work.OddVolterra.hquot h u σ = Work.OddVolterra.hquot h σ u := by
  have h1 : (∫ x in (0:ℝ)..1, deriv h (u + (1 - x) * (σ - u)))
      = ∫ x in (0:ℝ)..1, deriv h (σ + x * (u - σ)) := by
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    congr 1
    ring
  have h2 : (∫ x in (0:ℝ)..1, deriv h (u + (1 - x) * (σ - u)))
      = ∫ x in (0:ℝ)..1, deriv h (u + x * (σ - u)) := by
    have h3 := intervalIntegral.integral_comp_sub_left
      (f := fun x : ℝ => deriv h (u + x * (σ - u))) (a := (0:ℝ)) (b := 1) 1
    simpa using h3
  rw [Work.OddVolterra.hquot, Work.OddVolterra.hquot, ← h2]
  exact h1

/-- `krad` is symmetric in its two slope slots. -/
lemma krad_window_comm (h : ℝ → ℝ) (σ t u : ℝ) :
    Work.OddVolterra.krad h σ t u = Work.OddVolterra.krad h u t σ := by
  rw [Work.OddVolterra.krad_apply, Work.OddVolterra.krad_apply,
    krad_window_hquot_comm h u σ]
  unfold Work.OddVolterra.line
  ring

/-! ## The requested data -/

theorem krad_window_data {h : ℝ → ℝ} {n : ℕ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hjet : ∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {σ t a : ℝ} (hσ : σ ∈ Set.Icc (7 / 10 : ℝ) (19 / 20))
    (ha : a ∈ Set.Icc (7 / 10 : ℝ) (19 / 20))
    (ht1 : 1 / 5 ≤ |t|) (ht2 : |t| ≤ 2) :
    1 / 100 ≤ Work.OddVolterra.krad h σ t a ∧ Work.OddVolterra.krad h σ t a ≤ 10 ∧
    |deriv (fun a' : ℝ => Work.OddVolterra.krad h σ t a') a| ≤ 5 := by
  have hσ1 : (7 / 10 : ℝ) ≤ σ := hσ.1
  have hσle1 : σ ≤ 1 := by linarith [hσ.2]
  have hσ9 : (9 / 20 : ℝ) ≤ σ := by linarith [hσ.1]
  have ha1 : (7 / 10 : ℝ) ≤ a := ha.1
  have hale1 : a ≤ 1 := by linarith [ha.2]
  have ha9 : (9 / 20 : ℝ) ≤ a := by linarith [ha.1]
  -- the three jet bounds at orders `0`, `1`, `2`
  have h0 : ∀ x : ℝ, |h x| ≤ 1 / 100 := fun x => by
    have hx := hjet 0 (by omega) x
    rwa [iteratedDeriv_zero] at hx
  have h1 : ∀ x : ℝ, |deriv h x| ≤ 1 / 100 := fun x => by
    have hx := hjet 1 (by omega) x
    rwa [iteratedDeriv_one] at hx
  have h2 : ∀ x : ℝ, |deriv (deriv h) x| ≤ 1 / 100 := fun x => by
    have hx := hjet 2 (by omega) x
    rwa [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one] at hx
  have hd : ContDiff ℝ (⊤ : ℕ∞) (deriv h) := by
    simpa only [Function.iterate_one] using hh.iterate_deriv 1
  have hliph : ∀ x y : ℝ, |h x - h y| ≤ (1 / 100) * |x - y| :=
    abs_sub_le_mul_of_deriv_bound (f := h) (C := 1 / 100)
      (fun x => hh.differentiable (by simp) x) h1
  have hlipd : ∀ x y : ℝ, |deriv h x - deriv h y| ≤ (1 / 100) * |x - y| :=
    abs_sub_le_mul_of_deriv_bound (f := deriv h) (C := 1 / 100)
      (fun x => hd.differentiable (by simp) x) h2
  have hlipq : ∀ x y : ℝ, |hquot h x σ - hquot h y σ| ≤ (1 / 100) * |x - y| :=
    abs_hquot_sub_le (by norm_num) hd.continuous hlipd
  obtain ⟨hlip1, -⟩ := krad_lipschitz_window (h := h) (δ := 1 / 100) (σ := σ) (t := t)
    (by norm_num) (by norm_num) h0 h1 hliph hlipq hσ1 hσle1 ht2
  -- value bounds: use `krad_pointwise_data`, transferring the case `a > σ` through symmetry
  have hval : 1 / 100 ≤ krad h σ t a ∧ krad h σ t a ≤ 10 := by
    rcases le_total a σ with hle | hle
    · obtain ⟨hp, hu, -⟩ :=
        krad_pointwise_data (h := h) (δ := 1 / 100) (σ := σ) (t := t) (a := a)
          (by norm_num) (by norm_num) h0 h1 hσ1 hσle1 ht1 ht2 ha9 hle
      exact ⟨hp, hu⟩
    · obtain ⟨hp, hu, -⟩ :=
        krad_pointwise_data (h := h) (δ := 1 / 100) (σ := a) (t := t) (a := σ)
          (by norm_num) (by norm_num) h0 h1 ha1 hale1 ht1 ht2 hσ9 hle
      rw [krad_window_comm h a t σ] at hp hu
      exact ⟨hp, hu⟩
  refine ⟨hval.1, hval.2, ?_⟩
  -- the derivative bound: `5`-Lipschitz on the enclosing box `[3/8, 3/2]`
  have haS : a ∈ Set.Icc (3 / 8 : ℝ) (3 / 2) := ⟨by linarith [ha1], by linarith [ha.2]⟩
  have hmem : Set.Icc (3 / 8 : ℝ) (3 / 2) ∈ 𝓝 a :=
    Icc_mem_nhds (by linarith [ha1]) (by linarith [ha.2])
  have hlip : ∀ᶠ x in 𝓝 a, ‖krad h σ t x - krad h σ t a‖ ≤ 5 * ‖x - a‖ := by
    filter_upwards [hmem] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact hlip1 x hx a haS
  have hd5 := norm_deriv_le_of_lip' (f := fun a' : ℝ => krad h σ t a') (C := 5)
    (by norm_num) hlip
  rw [Real.norm_eq_abs] at hd5
  linarith

end

end Work.OddVolterra.Window
