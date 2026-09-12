import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Layercake

noncomputable section

open MeasureTheory Set
open scoped Real Topology

namespace Submission.HalflineBound

/-! ## Auxiliary lemmas for the halfline estimates -/

/-- `√2 ≤ 4096` (very loose, purely for convenience). -/
private lemma sqrt_two_le_4096 : Real.sqrt 2 ≤ 4096 := by
  calc
    (Real.sqrt 2 : ℝ) ≤ Real.sqrt (4096 ^ 2 : ℝ) := Real.sqrt_le_sqrt (by norm_num)
    _ = 4096 := by rw [Real.sqrt_sq_eq_abs]; norm_num

/-- `√(2·r) ≤ 4096 · √r` for `0 ≤ r`. -/
private lemma sqrt_two_mul_le {r : ℝ} (hr0 : 0 ≤ r) : Real.sqrt (2 * r) ≤ 4096 * Real.sqrt r := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) r]
  exact mul_le_mul_of_nonneg_right sqrt_two_le_4096 (Real.sqrt_nonneg r)

/-- The `(0, L]` piece is integrable over `(0, ∞)`. -/
private lemma integrableOn_env1_Ioi (L c1 : ℝ) :
    IntegrableOn ((Set.Ioc (0 : ℝ) L).indicator (fun _ : ℝ => c1)) (Set.Ioi (0 : ℝ)) := by
  rw [integrableOn_indicator_iff (hs := measurableSet_Ioc (a := (0 : ℝ)) (b := L))]
  rw [show Set.Ioc (0 : ℝ) L ∩ Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) L by
    ext x
    constructor
    · intro hx; exact hx.1
    · intro hx; exact ⟨hx, hx.1⟩]
  exact integrableOn_const (μ := volume) (s := Set.Ioc (0 : ℝ) L)
    (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top.ne)

/-- The `(L, ∞)` piece is integrable over `(0, ∞)` when `0 ≤ L`. -/
private lemma integrableOn_env2_Ioi (L c2 : ℝ) (hL0 : 0 ≤ L) :
    IntegrableOn ((Set.Ioi L).indicator (fun s : ℝ => c2 * Real.exp (-s / 2)))
      (Set.Ioi (0 : ℝ)) := by
  rw [integrableOn_indicator_iff (hs := measurableSet_Ioi (a := L))]
  rw [show Set.Ioi L ∩ Set.Ioi (0 : ℝ) = Set.Ioi L by
    ext x
    constructor
    · intro hx; exact hx.1
    · intro hx; exact ⟨hx, lt_of_le_of_lt hL0 hx⟩]
  have hφ' : (fun x : ℝ => c2 * Real.exp (-x / 2))
      = fun x : ℝ => c2 * Real.exp ((-(1 / 2 : ℝ)) * x) := by
    funext x
    have hx' : Real.exp (-x / 2) = Real.exp ((-(1 / 2 : ℝ)) * x) := by
      congr 1
      ring
    rw [hx']
  rw [hφ']
  exact Integrable.const_mul
    (integrableOn_exp_mul_Ioi (a := -(1 / 2 : ℝ)) (by norm_num) L) c2

/-- Pointwise domination of the integrand by the sum of the two envelope pieces. -/
private lemma sqrtmin_le_env (r L : ℝ) :
    ∀ s : ℝ, 0 < s →
      Real.sqrt (2 * min r (Real.exp (-s)))
        ≤ (Set.Ioc (0 : ℝ) L).indicator (fun _ : ℝ => Real.sqrt (2 * r)) s
          + (Set.Ioi L).indicator (fun s : ℝ => Real.sqrt 2 * Real.exp (-s / 2)) s := by
  intro s hs
  by_cases hsL : s ≤ L
  · have h1s : (Set.Ioc (0 : ℝ) L).indicator (fun _ : ℝ => Real.sqrt (2 * r)) s
        = Real.sqrt (2 * r) := by
      simp [hsL, hs]
    have hf_c1 : Real.sqrt (2 * min r (Real.exp (-s))) ≤ Real.sqrt (2 * r) := by
      refine Real.sqrt_le_sqrt ?_
      exact mul_le_mul_of_nonneg_left (min_le_left r (Real.exp (-s))) (by norm_num : (0 : ℝ) ≤ 2)
    calc
      Real.sqrt (2 * min r (Real.exp (-s))) ≤ Real.sqrt (2 * r) := hf_c1
      _ ≤ (Set.Ioc (0 : ℝ) L).indicator (fun _ : ℝ => Real.sqrt (2 * r)) s
          + (Set.Ioi L).indicator (fun s : ℝ => Real.sqrt 2 * Real.exp (-s / 2)) s := by
        rw [h1s]
        have h2nonneg : 0 ≤
            (Set.Ioi L).indicator (fun s : ℝ => Real.sqrt 2 * Real.exp (-s / 2)) s := by
          by_cases hms : s ∈ Set.Ioi L
          · simp [hms]
            positivity
          · simp [hms]
        linarith
  · have hsL' : L < s := lt_of_not_ge hsL
    have h1s : (Set.Ioc (0 : ℝ) L).indicator (fun _ : ℝ => Real.sqrt (2 * r)) s = 0 := by
      simp [hsL]
    have h2s : (Set.Ioi L).indicator (fun s : ℝ => Real.sqrt 2 * Real.exp (-s / 2)) s
        = Real.sqrt 2 * Real.exp (-s / 2) := by
      simp [hsL']
    have hf_c2 : Real.sqrt (2 * min r (Real.exp (-s)))
        ≤ Real.sqrt 2 * Real.exp (-s / 2) := by
      have h1' : Real.sqrt (2 * min r (Real.exp (-s)))
          ≤ Real.sqrt (2 * Real.exp (-s)) := by
        refine Real.sqrt_le_sqrt ?_
        exact mul_le_mul_of_nonneg_left (min_le_right r (Real.exp (-s))) (by norm_num : (0 : ℝ) ≤ 2)
      calc
        Real.sqrt (2 * min r (Real.exp (-s))) ≤ Real.sqrt (2 * Real.exp (-s)) := h1'
        _ = Real.sqrt 2 * Real.exp (-s / 2) := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) (Real.exp (-s))]
          rw [← Real.exp_half (-s)]
    calc
      Real.sqrt (2 * min r (Real.exp (-s)))
          ≤ Real.sqrt 2 * Real.exp (-s / 2) := hf_c2
      _ ≤ (Set.Ioc (0 : ℝ) L).indicator (fun _ : ℝ => Real.sqrt (2 * r)) s
          + (Set.Ioi L).indicator (fun s : ℝ => Real.sqrt 2 * Real.exp (-s / 2)) s := by
        rw [h1s, h2s]
        simp

/-- Integral over `(0, ∞)` of the `(0, L]`-piece equals `√(2r)·L` (when `0 ≤ L`). -/
private lemma integral_env1_Ioi (L r : ℝ) (hL0 : 0 ≤ L) :
    (∫ x : ℝ in Set.Ioi (0 : ℝ),
        (Set.Ioc (0 : ℝ) L).indicator (fun _ : ℝ => Real.sqrt (2 * r)) x)
      = Real.sqrt (2 * r) * L := by
  rw [MeasureTheory.setIntegral_indicator]
  · rw [show Set.Ioi (0 : ℝ) ∩ Set.Ioc (0 : ℝ) L = Set.Ioc (0 : ℝ) L by
      ext x
      constructor
      · intro hx; exact hx.2
      · intro hx; exact ⟨hx.1, hx⟩]
    rw [← intervalIntegral.integral_of_le hL0]
    rw [intervalIntegral.integral_const]
    simp
    ring
  · exact measurableSet_Ioc

/-- Integral over `(0, ∞)` of the `(L, ∞)`-piece equals `√2 · (2 · exp (-L/2))`
(when `0 ≤ L`). -/
private lemma integral_env2_Ioi (L : ℝ) (hL0 : 0 ≤ L) :
    (∫ x : ℝ in Set.Ioi (0 : ℝ),
        (Set.Ioi L).indicator (fun s : ℝ => Real.sqrt 2 * Real.exp (-s / 2)) x)
      = Real.sqrt 2 * (2 * Real.exp (-L / 2)) := by
  rw [MeasureTheory.setIntegral_indicator]
  · rw [show Set.Ioi (0 : ℝ) ∩ Set.Ioi L = Set.Ioi L by
      ext x
      constructor
      · intro hx; exact hx.2
      · intro hx; exact ⟨lt_of_le_of_lt hL0 hx, hx⟩]
    rw [integral_const_mul]
    have hφ : (fun x : ℝ => Real.exp (-x / 2)) = fun x : ℝ => Real.exp (-(1 / 2 : ℝ) * x) := by
      funext x
      congr 1
      ring
    rw [hφ]
    rw [integral_exp_mul_Ioi (a := -(1 / 2 : ℝ)) (by norm_num) L]
    ring_nf
  · exact measurableSet_Ioi

/-- The envelope `s ↦ √(2·min(r, exp(-s)))` is integrable over `(0,∞)`. -/
theorem integrableOn_sqrtmin_Ioi {r : ℝ} (hr0 : 0 < r) :
    IntegrableOn (fun s : ℝ => Real.sqrt (2 * min r (Real.exp (-s)))) (Set.Ioi (0 : ℝ)) volume := by
  let L : ℝ := |Real.log r|
  have hL0 : 0 ≤ L := abs_nonneg _
  have h1i : IntegrableOn ((Set.Ioc (0 : ℝ) L).indicator (fun _ : ℝ => Real.sqrt (2 * r)))
      (Set.Ioi (0 : ℝ)) := integrableOn_env1_Ioi L (Real.sqrt (2 * r))
  have h2i : IntegrableOn ((Set.Ioi L).indicator
      (fun s : ℝ => Real.sqrt 2 * Real.exp (-s / 2))) (Set.Ioi (0 : ℝ)) :=
    integrableOn_env2_Ioi L (Real.sqrt 2) hL0
  have hdom : ∀ s : ℝ, 0 < s →
      Real.sqrt (2 * min r (Real.exp (-s)))
        ≤ (Set.Ioc (0 : ℝ) L).indicator (fun _ : ℝ => Real.sqrt (2 * r)) s
          + (Set.Ioi L).indicator (fun s : ℝ => Real.sqrt 2 * Real.exp (-s / 2)) s :=
    sqrtmin_le_env r L
  have hfc : Continuous (fun s : ℝ => Real.sqrt (2 * min r (Real.exp (-s)))) := by
    exact Real.continuous_sqrt.comp (continuous_const.mul
      (Continuous.min continuous_const (Real.continuous_exp.comp continuous_neg)))
  have hf_ae : AEStronglyMeasurable (fun s : ℝ => Real.sqrt (2 * min r (Real.exp (-s))))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    exact hfc.aestronglyMeasurable
  have hdom_ae :
      ∀ᵐ s ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        ‖Real.sqrt (2 * min r (Real.exp (-s)))‖
          ≤ (Set.Ioc (0 : ℝ) L).indicator (fun _ : ℝ => Real.sqrt (2 * r)) s
            + (Set.Ioi L).indicator (fun s : ℝ => Real.sqrt 2 * Real.exp (-s / 2)) s := by
    rw [ae_restrict_iff']
    · exact ae_of_all volume (fun s hs => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
        exact hdom s hs)
    · exact measurableSet_Ioi
  exact Integrable.mono' (hg := IntegrableOn.add h1i h2i) hf_ae hdom_ae

/-- One-dimensional estimate (very loose constant 4096, true value is
`√2·√r·(2 + |log r|)`): for `0 < r ≤ 1`,

`∫ s in (0,∞), √(2 · min r (exp (-s))) ds ≤ 4096 · √r · (2 + |log r|)`.

Hint: split at `L := |Real.log r| = -Real.log r ≥ 0`. On `(0, L]` the min equals
`r` (so the integrand is the constant `√(2r)` and the integral is `√(2r)·L ≤ 2√r·L`),
while on `(L, ∞)` the min equals `exp(-s)`, the integrand is `√2·exp(-s/2)`, and
`∫ on (L,∞) exp(-s/2) = 2·exp(-L/2) = 2·√r` — use `integral_exp_mul_Ioi` with
`a = -1/2` and `c = L`, then `exp(-L/2) = √r` (since `r ≤ 1` makes `L = -log r`).
-/
theorem halfline_sqrtmin_le {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    (∫ s : ℝ in Set.Ioi (0 : ℝ), Real.sqrt (2 * min r (Real.exp (-s))))
      ≤ 4096 * Real.sqrt r * (2 + |Real.log r|) := by
  let L : ℝ := |Real.log r|
  have hL0 : 0 ≤ L := abs_nonneg _
  have hlog : Real.log r ≤ 0 := Real.log_nonpos (le_of_lt hr0) hr1
  have hL_eq : L = -Real.log r := by
    dsimp [L]
    exact abs_of_nonpos hlog
  have hexpL : Real.exp (-L) = r := by
    rw [hL_eq, neg_neg]
    exact Real.exp_log hr0
  have hexpL2 : Real.exp (-L / 2) = Real.sqrt r := by
    rw [Real.exp_half (-L), hexpL]
  let f : ℝ → ℝ := fun s => Real.sqrt (2 * min r (Real.exp (-s)))
  have hfi : IntegrableOn f (Set.Ioi (0 : ℝ)) := by
    simpa [f] using (integrableOn_sqrtmin_Ioi hr0)
  have h1i : IntegrableOn ((Set.Ioc (0 : ℝ) L).indicator (fun _ : ℝ => Real.sqrt (2 * r)))
      (Set.Ioi (0 : ℝ)) := integrableOn_env1_Ioi L (Real.sqrt (2 * r))
  have h2i : IntegrableOn ((Set.Ioi L).indicator
      (fun s : ℝ => Real.sqrt 2 * Real.exp (-s / 2))) (Set.Ioi (0 : ℝ)) :=
    integrableOn_env2_Ioi L (Real.sqrt 2) hL0
  have hdom : ∀ s : ℝ, 0 < s →
      Real.sqrt (2 * min r (Real.exp (-s)))
        ≤ (Set.Ioc (0 : ℝ) L).indicator (fun _ : ℝ => Real.sqrt (2 * r)) s
          + (Set.Ioi L).indicator (fun s : ℝ => Real.sqrt 2 * Real.exp (-s / 2)) s :=
    sqrtmin_le_env r L
  have hmono :
      (∫ s : ℝ in Set.Ioi (0 : ℝ), Real.sqrt (2 * min r (Real.exp (-s))))
        ≤ ∫ s : ℝ in Set.Ioi (0 : ℝ),
            ((Set.Ioc (0 : ℝ) L).indicator (fun _ : ℝ => Real.sqrt (2 * r)) s
              + (Set.Ioi L).indicator (fun s : ℝ => Real.sqrt 2 * Real.exp (-s / 2)) s) := by
    refine MeasureTheory.setIntegral_mono_on hfi (IntegrableOn.add h1i h2i) measurableSet_Ioi ?_
    intro s hs
    exact hdom s hs
  have hsum :
      (∫ s : ℝ in Set.Ioi (0 : ℝ),
          ((Set.Ioc (0 : ℝ) L).indicator (fun _ : ℝ => Real.sqrt (2 * r)) s
            + (Set.Ioi L).indicator (fun s : ℝ => Real.sqrt 2 * Real.exp (-s / 2)) s))
        = (∫ s : ℝ in Set.Ioi (0 : ℝ),
            (Set.Ioc (0 : ℝ) L).indicator (fun _ : ℝ => Real.sqrt (2 * r)) s)
          + (∫ s : ℝ in Set.Ioi (0 : ℝ),
            (Set.Ioi L).indicator (fun s : ℝ => Real.sqrt 2 * Real.exp (-s / 2)) s) := by
    simpa [Pi.add_apply] using
      (integral_add (μ := volume.restrict (Set.Ioi (0 : ℝ))) h1i h2i)
  have hv1 : (∫ s : ℝ in Set.Ioi (0 : ℝ),
        (Set.Ioc (0 : ℝ) L).indicator (fun _ : ℝ => Real.sqrt (2 * r)) s)
      = Real.sqrt (2 * r) * L := integral_env1_Ioi L r hL0
  have hv2 : (∫ s : ℝ in Set.Ioi (0 : ℝ),
        (Set.Ioi L).indicator (fun s : ℝ => Real.sqrt 2 * Real.exp (-s / 2)) s)
      = Real.sqrt 2 * (2 * Real.exp (-L / 2)) := integral_env2_Ioi L hL0
  have hsqrt_le : Real.sqrt (2 * r) ≤ 4096 * Real.sqrt r :=
    sqrt_two_mul_le (le_of_lt hr0)
  have hA1 : Real.sqrt (2 * r) * L ≤ 4096 * Real.sqrt r * L := by
    exact mul_le_mul_of_nonneg_right hsqrt_le hL0
  have hA2 : Real.sqrt 2 * (2 * Real.sqrt r) ≤ 8192 * Real.sqrt r := by
    have h22 : Real.sqrt 2 * 2 ≤ 8192 := by
      have h2le : Real.sqrt 2 ≤ 4096 := sqrt_two_le_4096
      nlinarith
    have : Real.sqrt 2 * (2 * Real.sqrt r) = (Real.sqrt 2 * 2) * Real.sqrt r := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right h22 (Real.sqrt_nonneg r)
  have hfinal :
      (∫ s : ℝ in Set.Ioi (0 : ℝ), Real.sqrt (2 * min r (Real.exp (-s))))
        ≤ 4096 * Real.sqrt r * (2 + L) := by
    calc
      (∫ s : ℝ in Set.Ioi (0 : ℝ), Real.sqrt (2 * min r (Real.exp (-s))))
          ≤ ∫ s : ℝ in Set.Ioi (0 : ℝ),
              ((Set.Ioc (0 : ℝ) L).indicator (fun _ : ℝ => Real.sqrt (2 * r)) s
                + (Set.Ioi L).indicator (fun s : ℝ => Real.sqrt 2 * Real.exp (-s / 2)) s) := hmono
      _ = (∫ s : ℝ in Set.Ioi (0 : ℝ),
            (Set.Ioc (0 : ℝ) L).indicator (fun _ : ℝ => Real.sqrt (2 * r)) s)
          + (∫ s : ℝ in Set.Ioi (0 : ℝ),
            (Set.Ioi L).indicator (fun s : ℝ => Real.sqrt 2 * Real.exp (-s / 2)) s) := hsum
      _ = Real.sqrt (2 * r) * L
          + Real.sqrt 2 * (2 * Real.exp (-L / 2)) := by rw [hv1, hv2]
      _ = Real.sqrt (2 * r) * L + Real.sqrt 2 * (2 * Real.sqrt r) := by rw [hexpL2]
      _ ≤ 4096 * Real.sqrt r * L + 8192 * Real.sqrt r := by
        have hA2' : Real.sqrt 2 * (2 * Real.sqrt r) ≤ 8192 * Real.sqrt r := hA2
        nlinarith
      _ = 4096 * Real.sqrt r * (2 + L) := by ring
  simpa [L] using hfinal

end Submission.HalflineBound
