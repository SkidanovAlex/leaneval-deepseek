import Mathlib
import Submission.Work.Anchor.ThetaM_contDiffOn

/-!
# Smoothness of the manifest odd `Θ`-data on a *wider* slope window

`Work.Anchor.ThetaM_contDiffOn` proves that

`(s, σ, z) ↦ KernelExt.ThetaM n h s σ z`

is `C^∞` on the region

`9/20 < s < 21/20`, `9/20 < σ < 21/20`, `|z 0| > 1/5`, `|z 1| > 1/5`

(`Work.Anchor.Good`), and deduces the statement with the *second* slot constrained to the
narrower window `(481/1000, 97/100)`.  Here we widen that slot to `(481/1000, 102/100)`:
the region `Good` is unchanged, so the additional content is entirely the numeric bound

`profileX σ > 13/20` for `σ ∈ (481/1000, 102/100)`

(`profileX σ = 1/√(1+σ²)` is decreasing, and `1/√(1 + (102/100)²) > 0.7 > 13/20`), which
upgrades `‖z - baseState σ‖ < 9/20` to `|z i| > 1/5` for `i = 0, 1`.

We first restate the `Good`-region smoothness as an exported lemma
(`ThetaM_contDiffOn_Good`, the content of the proof of `ThetaM_contDiffOn`), then specialise
it to the widened region.
-/

namespace Work.Anchor

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

open Work.OddVolterra Work.OddVolterra.KernelExt

/-- Smoothness of the manifest odd `Θ`-data on the open region `Good`.  This is the geometric
content of `Work.Anchor.ThetaM_contDiffOn`, exported on its own. -/
theorem ThetaM_contDiffOn_Good (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ × St => ThetaM n h q.1 q.2.1 q.2.2) Good := by
  have hconv : ∀ {c a₁ a₂ : ℝ}, 0 ≤ c → c ≤ 1 → 9 / 20 < a₁ → 9 / 20 < a₂ →
      9 / 20 < a₁ + c * (a₂ - a₁) := by
    intro c a₁ a₂ hc0 hc1 ha₁ ha₂
    have h3 : 9 / 20 < min a₁ a₂ := lt_min ha₁ ha₂
    have h5 : (1 - c) * min a₁ a₂ + c * min a₁ a₂ ≤ (1 - c) * a₁ + c * a₂ := by
      have h6 : 0 ≤ 1 - c := by linarith
      have h7 := mul_le_mul_of_nonneg_left (min_le_left a₁ a₂) h6
      have h8 := mul_le_mul_of_nonneg_left (min_le_right a₁ a₂) hc0
      linarith
    have h9 : (1 - c) * a₁ + c * a₂ = a₁ + c * (a₂ - a₁) := by ring
    linarith
  -- the `τ`-parametrised manifest kernel is smooth
  have hKτ : ∀ i : Fin 2, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (ℝ × ℝ × St) × ℝ => (KvecM n h (p.1.1 + p.2 * (p.1.2.1 - p.1.1)) p.1.2.1
        (p.1.2.2 0) (p.1.2.2 1) (p.1.2.2 2) (p.1.2.2 3)) i)
      (Good ×ˢ Set.Icc (0 : ℝ) 1) := by
    intro i
    have hK := contDiffOn_KvecM_comp (n := n) (hh := hh) (B := Good ×ˢ Set.Icc (0 : ℝ) 1)
      (s := fun p : (ℝ × ℝ × St) × ℝ => p.1.1 + p.2 * (p.1.2.1 - p.1.1))
      (σ := fun p => p.1.2.1) (x := fun p => p.1.2.2 0) (y := fun p => p.1.2.2 1)
      (x' := fun p => p.1.2.2 2) (y' := fun p => p.1.2.2 3)
      (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
      (fun p hp => by
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp.1
        exact krad_pos_of_add_pos' hsmall
          (by have := hconv hp.2.1 hp.2.2 h1 h3; linarith) (by simpa using h5.le))
      (fun p hp => by
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp.1
        exact krad_pos_of_add_pos' hsmall
          (by have := hconv hp.2.1 hp.2.2 h1 h3; linarith) (by simpa using h6.le))
    exact (contDiffOn_pi.mp hK) i
  -- the `θ`-parametrised manifest kernel is smooth
  have hKθ : ∀ i : Fin 2, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (ℝ × ℝ × St) × ℝ => (KvecM n h (p.1.1 + Real.sin p.2 ^ 2 * (p.1.2.1 - p.1.1))
        p.1.2.1 (p.1.2.2 0) (p.1.2.2 1) (p.1.2.2 2) (p.1.2.2 3)) i)
      (Good ×ˢ Set.univ) := by
    intro i
    have hsin : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : (ℝ × ℝ × St) × ℝ => (p.1, Real.sin p.2 ^ 2))
        (Good ×ˢ Set.univ) :=
      (((contDiff_fst : ContDiff ℝ (⊤ : ℕ∞) (fun p : (ℝ × ℝ × St) × ℝ => p.1)).prodMk
        ((Real.contDiff_sin.pow 2).comp contDiff_snd))).contDiffOn
    have hcomp := (hKτ i).comp hsin (fun p hp => ⟨hp.1, ⟨sq_nonneg _, Real.sin_sq_le_one _⟩⟩)
    simpa only [Function.comp_def] using hcomp
  -- the `θ`-integral is smooth
  have hInt : ∀ i : Fin 2, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ × St => ∫ θ in (0 : ℝ)..(Real.pi / 2),
        2 * (KvecM n h (q.1 + Real.sin θ ^ 2 * (q.2.1 - q.1)) q.2.1
          (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) i) Good := by
    intro i
    refine contDiffOn_intervalIntegral_parametric (hU := isOpen_Good) (a := 0) (b := Real.pi / 2)
      (G := fun (p : (ℝ × ℝ × St) × ℝ) => 2 * (KvecM n h
        (p.1.1 + Real.sin p.2 ^ 2 * (p.1.2.1 - p.1.1)) p.1.2.1
        (p.1.2.2 0) (p.1.2.2 1) (p.1.2.2 2) (p.1.2.2 3)) i) ?_
    exact (contDiffOn_const (c := (2 : ℝ))).mul (by simpa using hKθ i)
  -- `G2M` is smooth on `Good`
  have hG2 : ∀ i : Fin 2, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ × St =>
        (G2M n h q.1 q.2.1 (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) i) Good := by
    intro i
    refine (hInt i).congr (fun q hq => ?_)
    have hcont : ContinuousOn (fun τ : ℝ => (KvecM n h (q.1 + τ * (q.2.1 - q.1)) q.2.1
        (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) i) (Set.Icc (0 : ℝ) 1) := by
      have h := (hKτ i).continuousOn.comp
        (by fun_prop : ContinuousOn (fun τ : ℝ => (q, τ)) (Set.Icc (0 : ℝ) 1))
        (fun τ hτ => ⟨hq, hτ⟩)
      simpa only [Function.comp_def] using h
    have h := AbelWeight_subst (K := fun τ : ℝ => (KvecM n h (q.1 + τ * (q.2.1 - q.1)) q.2.1
        (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) i) hcont
    simpa only [G2M] using h
  -- the derivative rows
  have hderiv : ∀ i : Fin 2, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ × St => deriv (fun u : ℝ =>
        (G2M n h u q.2.1 (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) i) q.1) Good := by
    intro i
    exact contDiffOn_deriv_slice_fst (P := ℝ × St) (U := Good) isOpen_Good (hG2 i)
  -- assembly
  have hcoord : ∀ k : Fin 4, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ × St => q.2.2 k) Good := by
    intro k
    have h : ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ × St => q.2.2) Good := by fun_prop
    exact (contDiffOn_pi.mp h) k
  have hTheta : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : ℝ × ℝ × St => ThetaM n h q.1 q.2.1 q.2.2) Good := by
    rw [contDiffOn_pi]
    intro i
    fin_cases i
    · simpa [ThetaM] using (hcoord 2).neg
    · simpa [ThetaM] using (hcoord 3).neg
    · simpa [ThetaM] using (hderiv 0).neg
    · simpa [ThetaM] using (hderiv 1).neg
  exact hTheta

/-- On the widened slope window `(481/1000, 102/100)` the ball profile is still larger than
`13/20`. -/
lemma profileX_gt_thirteen_twentieths_wide {σ : ℝ} (h1 : 481 / 1000 < σ)
    (h2 : σ < 102 / 100) : 13 / 20 < Commons.Geometry.Ulam.profileX σ := by
  have hσpos : 0 < σ := by linarith
  have hsq : σ ^ 2 < (102 / 100 : ℝ) ^ 2 := by
    rw [sq_lt_sq, abs_of_pos (by norm_num : (0 : ℝ) < 102 / 100)]
    rw [abs_lt]
    exact ⟨by linarith, h2⟩
  have hden : 1 + σ ^ 2 < 5101 / 2500 := by
    rw [show (5101 : ℝ) / 2500 = 1 + (102 / 100) ^ 2 by norm_num]
    linarith
  have h1pos : 0 < 1 + σ ^ 2 := by positivity
  have hA : (13 / 20) ^ 2 < 1 / (1 + σ ^ 2) := by
    rw [lt_div_iff₀ h1pos]
    have : (13 / 20 : ℝ) ^ 2 * (5101 / 2500) < 1 := by norm_num
    nlinarith [hden]
  have hpc : (13 / 20) ^ 2 < Commons.Geometry.Ulam.profileX σ ^ 2 := by
    rw [Commons.Geometry.Ulam.profileX_sq]
    exact hA
  exact (pow_lt_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 13 / 20)
    (le_of_lt (Commons.Geometry.Ulam.profileX_pos σ hσpos))
    (by norm_num : (2 : ℕ) ≠ 0)).mp hpc

/-- The region of the widened statement is contained in `Good`. -/
lemma target_subset_Good_wide {p : ℝ × ℝ × St}
    (hp1 : p.1 ∈ Set.Ioo (481 / 1000 : ℝ) (97 / 100))
    (hp2 : p.2.1 ∈ Set.Ioo (481 / 1000 : ℝ) (102 / 100))
    (hp3 : ‖p.2.2 - baseState p.2.1‖ < 9 / 20) : p ∈ Good := by
  refine ⟨by linarith [hp1.1], by linarith [hp1.2], by linarith [hp2.1], by linarith [hp2.2],
    ?_, ?_⟩
  · have h2 : |p.2.2 0 - Commons.Geometry.Ulam.profileX p.2.1| < 9 / 20 := by
      have h := norm_le_pi_norm (p.2.2 - baseState p.2.1) 0
      rw [Pi.sub_apply, Real.norm_eq_abs] at h
      have hb : baseState p.2.1 0 = Commons.Geometry.Ulam.profileX p.2.1 := rfl
      rw [hb] at h
      exact lt_of_le_of_lt h hp3
    have hprof : 13 / 20 < Commons.Geometry.Ulam.profileX p.2.1 :=
      profileX_gt_thirteen_twentieths_wide hp2.1 hp2.2
    have h4 : (1 : ℝ) / 5 < p.2.2 0 := by
      have h5 : Commons.Geometry.Ulam.profileX p.2.1 - 9 / 20 < p.2.2 0 := by
        have := (abs_lt.mp h2).1
        linarith
      linarith
    exact lt_of_lt_of_le h4 (le_abs_self _)
  · have h2 : |p.2.2 1 - Commons.Geometry.Ulam.profileX p.2.1| < 9 / 20 := by
      have h := norm_le_pi_norm (p.2.2 - baseState p.2.1) 1
      rw [Pi.sub_apply, Real.norm_eq_abs] at h
      have hb : baseState p.2.1 1 = Commons.Geometry.Ulam.profileX p.2.1 := rfl
      rw [hb] at h
      exact lt_of_le_of_lt h hp3
    have hprof : 13 / 20 < Commons.Geometry.Ulam.profileX p.2.1 :=
      profileX_gt_thirteen_twentieths_wide hp2.1 hp2.2
    have h4 : (1 : ℝ) / 5 < p.2.2 1 := by
      have h5 : Commons.Geometry.Ulam.profileX p.2.1 - 9 / 20 < p.2.2 1 := by
        have := (abs_lt.mp h2).1
        linarith
      linarith
    exact lt_of_lt_of_le h4 (le_abs_self _)

/-- **The target.**  Smoothness of the manifest odd `Θ`-data on the widened slope/state
region; this is `Work.Anchor.ThetaM_contDiffOn` with the second slot relaxed from
`(481/1000, 97/100)` to `(481/1000, 102/100)`. -/
theorem ThetaM_contDiffOn_wide (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ × Work.OddVolterra.St =>
        Work.OddVolterra.KernelExt.ThetaM n h p.1 p.2.1 p.2.2)
      {p : ℝ × ℝ × Work.OddVolterra.St | p.1 ∈ Set.Ioo (481 / 1000) (97 / 100) ∧
        p.2.1 ∈ Set.Ioo (481 / 1000) (102 / 100) ∧
        ‖p.2.2 - Work.OddVolterra.baseState p.2.1‖ < 9 / 20} := by
  refine (ThetaM_contDiffOn_Good n hh hsmall).mono (fun p hp => ?_)
  exact target_subset_Good_wide hp.1 hp.2.1 hp.2.2

end

end Work.Anchor
