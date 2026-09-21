import Mathlib
import Submission.Work.OddVolterra.WinData.deriv2_main
import Submission.Work.OddVolterra.Window.krad_deriv2_data
import Submission.Work.OddVolterra.Window.hquot_deriv2_bound

/-!
# Jet data for `KvecM` on the extended box

This file adapts the second-derivative estimates of `Window/krad_deriv2_data` to the extended box
`u ∈ [3/16,1]`, `σ ∈ [1/4,1]`, and proves the Lipschitz-in-`t` and Lipschitz-in-`state` bounds of
the jet curve `KJet` that the jet-curve lemma `JetCurve_box` consumes.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddVolterra.WinData

noncomputable section

open Work.OddVolterra Work.OddVolterra.Window Work.OddVolterra.KernelExt

set_option maxHeartbeats 1600000

/-- `line h σ t + line h a t` and its first two `a`-derivatives are bounded by `6`, on the
extended box. -/
lemma krad2_line_add_iteratedDeriv_bound_ext {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {δ σ t a : ℝ} (hδ1 : δ ≤ 1 / 100)
    (hjet : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ)
    (hσ1 : 1 / 4 ≤ σ) (hσ2 : σ ≤ 1) (ht2 : |t| ≤ 2)
    (ha1 : 3 / 16 ≤ a) (ha2 : a ≤ 1) :
    ∀ k : ℕ, k ≤ 2 → |iteratedDeriv k (fun a' : ℝ => line h σ t + line h a' t) a| ≤ 6 := by
  have h0 : ∀ s : ℝ, |h s| ≤ δ := fun s => by
    have := hjet 0 (by norm_num) s
    rwa [iteratedDeriv_zero] at this
  have h1 : ∀ s : ℝ, |deriv h s| ≤ δ := fun s => by
    have := hjet 1 (by norm_num) s
    rwa [iteratedDeriv_one] at this
  have ha_abs : |a| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hs_abs : |σ| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  have hline : ∀ x : ℝ, |x| ≤ 1 → |line h x t| ≤ 201 / 100 := by
    intro x hx
    simp only [line]
    calc |x * t + h x| ≤ |x * t| + |h x| := abs_add_le _ _
      _ = |x| * |t| + |h x| := by rw [abs_mul]
      _ ≤ 1 * 2 + δ := add_le_add (mul_le_mul hx ht2 (abs_nonneg _) (by norm_num)) (h0 x)
      _ ≤ 201 / 100 := by linarith
  intro k hk
  interval_cases k
  · rw [iteratedDeriv_zero]
    calc |line h σ t + line h a t| ≤ |line h σ t| + |line h a t| := abs_add_le _ _
      _ ≤ 201 / 100 + 201 / 100 := add_le_add (hline σ hs_abs) (hline a ha_abs)
      _ ≤ 6 := by norm_num
  · have he : iteratedDeriv 1 (fun a' : ℝ => line h σ t + line h a' t) a = t + deriv h a := by
      rw [iteratedDeriv_const_add (by norm_num : (0 : ℕ) < 1) (line h σ t)]
      rw [Work.OddExistence.Manifest.AW.iteratedDeriv_line_eq h hh t a 1]
      norm_num
    rw [he]
    calc |t + deriv h a| ≤ |t| + |deriv h a| := abs_add_le _ _
      _ ≤ 2 + δ := add_le_add ht2 (h1 a)
      _ ≤ 6 := by linarith
  · rw [krad2_line_add_iteratedDeriv_two hh σ t a]
    calc |iteratedDeriv 2 h a| ≤ δ := hjet 2 (by norm_num) a
      _ ≤ 6 := by linarith

/-- Bound on the second `a`-derivative of `krad` on the extended box. -/
lemma krad2_abs_deriv_deriv_krad_le_ext {h : ℝ → ℝ} {δ σ t a : ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 100)
    (hjet : ∀ k : ℕ, k ≤ 3 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ)
    (hσ1 : 1 / 4 ≤ σ) (hσ2 : σ ≤ 1) (ht2 : |t| ≤ 2)
    (ha1 : 3 / 16 ≤ a) (ha2 : a ≤ 1)
    (hH2 : |deriv (deriv (fun x : ℝ => hquot h x σ)) a| ≤ δ) :
    |deriv (deriv (fun a' : ℝ => krad h σ t a')) a| ≤ 26 * δ := by
  have h1 : ∀ s : ℝ, |deriv h s| ≤ δ := fun s => by
    have := hjet 1 (by norm_num) s
    rwa [iteratedDeriv_one] at this
  have h2 : ∀ s : ℝ, |iteratedDeriv 2 h s| ≤ δ := fun s => hjet 2 (by norm_num) s
  have hb := Work.OddExistence.Manifest.AW.hquot_deriv_bound hh hδ0 h1 h2 a σ
  have hAc0 : ContDiffAt ℝ (⊤ : ℕ∞) (fun a' : ℝ => hquot h a' σ) a :=
    ((Work.OddVolterra.Existence.hquot_contDiff hh).comp (f := fun a' : ℝ => (a', σ))
      (by fun_prop)).contDiffAt
  have hAc : ContDiffAt ℝ (2 : ℕ∞) (fun a' : ℝ => hquot h a' σ) a :=
    hAc0.of_le (Work.OddExistence.Manifest.AW.natCast_le_top_enat 2)
  have hAcd : ContDiffAt ℝ (2 : ℕ∞) (fun a' : ℝ => t + hquot h a' σ) a :=
    (contDiffAt_const (c := t)).add hAc
  have hl0 : ContDiffAt ℝ (⊤ : ℕ∞) (fun a' : ℝ => line h a' t) a :=
    ((line_contDiff hh).comp (f := fun a' : ℝ => (a', t)) (by fun_prop)).contDiffAt
  have hl : ContDiffAt ℝ (2 : ℕ∞) (fun a' : ℝ => line h a' t) a :=
    hl0.of_le (Work.OddExistence.Manifest.AW.natCast_le_top_enat 2)
  have hBcd : ContDiffAt ℝ (2 : ℕ∞) (fun a' : ℝ => line h σ t + line h a' t) a :=
    (contDiffAt_const (c := line h σ t)).add hl
  have hAf0 : |(fun a' : ℝ => t + hquot h a' σ) a| ≤ 3 := by
    show |t + hquot h a σ| ≤ 3
    calc |t + hquot h a σ| ≤ |t| + |hquot h a σ| := abs_add_le _ _
      _ ≤ 2 + δ := add_le_add ht2 hb.1
      _ ≤ 3 := by linarith
  have hAf1 : |iteratedDeriv 1 (fun a' : ℝ => t + hquot h a' σ) a| ≤ δ := by
    rw [iteratedDeriv_one, deriv_const_add]
    exact hb.2
  have hAf2 : |iteratedDeriv 2 (fun a' : ℝ => t + hquot h a' σ) a| ≤ δ := by
    rw [iteratedDeriv_const_add (by norm_num : (0 : ℕ) < 2) t, krad2_iteratedDeriv_two_eq_deriv_deriv]
    exact hH2
  have hgB := krad2_line_add_iteratedDeriv_bound_ext hh hδ1 (fun k hk => hjet k (by omega))
    hσ1 hσ2 ht2 ha1 ha2
  have hB0 : |iteratedDeriv 0 (fun a' : ℝ => line h σ t + line h a' t) a| ≤ 6 :=
    hgB 0 (by norm_num)
  have hB1 : |iteratedDeriv 1 (fun a' : ℝ => line h σ t + line h a' t) a| ≤ 6 :=
    hgB 1 (by norm_num)
  have hB2 : |iteratedDeriv 2 (fun a' : ℝ => line h σ t + line h a' t) a| ≤ δ := by
    rw [krad2_line_add_iteratedDeriv_two hh σ t a]; exact h2 a
  have hmain : |iteratedDeriv 2
      ((fun a' : ℝ => t + hquot h a' σ) * (fun a' : ℝ => line h σ t + line h a' t)) a|
      ≤ 3 * δ + 2 * δ * 6 + δ * 6 :=
    krad2_iteratedDeriv2_mul_bound hAcd hBcd (by norm_num) hδ0 hδ0
      hAf0 hAf1 hAf2 hB0 hB1 hB2
  have hmul_fun : (fun a' : ℝ => krad h σ t a')
      = (fun a' : ℝ => t + hquot h a' σ) * (fun a' : ℝ => line h σ t + line h a' t) := by
    funext a'; rw [krad_apply]; rfl
  rw [← krad2_iteratedDeriv_two_eq_deriv_deriv (fun a' : ℝ => krad h σ t a'), hmul_fun]
  linarith [hmain, hδ0]

/-- **Second `a`-derivative of `krad` on the extended box**, with explicit constant. -/
theorem krad_deriv2_ext :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (h : ℝ → ℝ) (δ u σ : ℝ),
        ContDiff ℝ (⊤ : ℕ∞) h → 0 < δ → δ ≤ 1 / 100 →
        (∀ k : ℕ, k ≤ 3 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
        u ∈ Set.Icc (3 / 16 : ℝ) 1 → σ ∈ Set.Icc (1 / 4 : ℝ) 1 →
        ∀ t : ℝ, 1 / 5 ≤ |t| → |t| ≤ 2 →
        |deriv (deriv (fun x : ℝ => krad h σ t x)) u| ≤ K * δ ∧
        |deriv (deriv (fun x : ℝ => krad h σ t x)) u -
         deriv (deriv (fun x : ℝ => krad 0 σ t x)) u| ≤ K * δ := by
  refine ⟨26, by norm_num, ?_⟩
  intro h δ u σ hh hδ0 hδ1 hjet hu hσ t _ht1 ht2
  have hH2 : |deriv (deriv (fun x : ℝ => hquot h x σ)) u| ≤ δ := by
    have h3 : ∀ s : ℝ, |iteratedDeriv 3 h s| ≤ δ := fun s => hjet 3 (by norm_num) s
    exact hquot_deriv2_bound hh hδ0.le h3 σ u
  have hmain := krad2_abs_deriv_deriv_krad_le_ext hh hδ0.le hδ1 hjet hσ.1 hσ.2 ht2 hu.1 hu.2 hH2
  have hzero := krad2_krad_zero_deriv2 σ t u
  constructor
  · linarith
  · rw [hzero, sub_zero]; linarith

end

end Work.OddVolterra.WinData
