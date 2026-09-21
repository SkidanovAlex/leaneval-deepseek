import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib
import Submission.Work.OddExistence.Manifest
import Submission.Work.OddBridge.KvecM_contDiffOn_box
import Submission.Work.OddExistence.Manifest.ThetaMBridge
import Submission.Work.OddExistence.Manifest.hasDerivAt_G2M_apply

/-!
# Continuity of the manifest odd `𝚯M`-data on the state region

The manifest kernel `Work.OddExistence.ThetaM n h s σ z` is built from the `τ`-average `G2M` of
`Work.OddBridge.KvecM`; its last two components are (up to sign) the first-slot derivatives of
that average.  This file proves that `(s,σ,z) ↦ 𝚯M n h s σ z` is continuous on the region

`{p | p.1.1 ∈ [a,b] ∧ p.1.2 ∈ [a,b] ∧ p.2 ∈ closedBall (baseState p.1.2) ρ}`

of the target, with `0 < a ≤ b ≤ 1`, `0 < ρ ≤ 1/2` and the hypothesis `KdenPosOn h a b` that the
Abel denominator does not vanish on the square `[a,b]²` for `|t| ≥ 1/5`.

The two analytic ingredients are

* `deriv_G2M_eq_integral_on_RcM` — on the region the first-slot derivative of `G2M` is the
  Abel-weighted integral of the first-slot derivative of `KvecM`, by differentiating under the
  integral sign (the local inputs are `exists_bound_local` and `exists_bound_RcM`);
* `continuousOn_integral_deriv_KvecM` — that integral expression is continuous on the region, by
  dominated convergence, using the joint continuity of the first-slot derivative field of `KvecM`
  on the open set `GoodM h` (`continuousOn_deriv_KvecM_component_GoodM`).
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddExistence.Manifest

open Work.OddVolterra Work.OddBridge

noncomputable section

set_option maxHeartbeats 1000000

/-! ## 1. The first-slot derivative of `G2M` as an Abel integral on the region -/

/-- The moving point `x + τ(σ - x)` with `x` in a neighbourhood of `s` and `τ ∈ [0,1]` either
stays near `s` or lands in the window `[a,b]`. -/
lemma moving_point_mem_union {a b s σ δ x τ : ℝ} (hδ : 0 ≤ δ) (hs : s ∈ Set.Icc a b)
    (hσ : σ ∈ Set.Icc a b) (hx : x ∈ Set.Ioo (s - δ) (s + δ)) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    x + τ * (σ - x) ∈ Set.Icc (s - δ) (s + δ) ∨ x + τ * (σ - x) ∈ Set.Icc a b := by
  obtain ⟨hxs, hxs'⟩ := hx
  by_cases hle : x ≤ σ
  · have hge : x ≤ x + τ * (σ - x) := by
      have : 0 ≤ τ * (σ - x) := mul_nonneg hτ.1 (by linarith)
      linarith
    have hle' : x + τ * (σ - x) ≤ σ := by
      have : 0 ≤ (1 - τ) * (σ - x) := mul_nonneg (by linarith [hτ.2]) (by linarith)
      have hkey : σ - (x + τ * (σ - x)) = (1 - τ) * (σ - x) := by ring
      linarith
    by_cases ha' : a ≤ x + τ * (σ - x)
    · exact Or.inr ⟨ha', le_trans hle' hσ.2⟩
    · have ha'' : x + τ * (σ - x) < a := not_le.mp ha'
      exact Or.inl ⟨by linarith [hxs, hge], by linarith [ha'', hs.1, hxs']⟩
  · have hlt : σ < x := not_le.mp hle
    have hge : σ ≤ x + τ * (σ - x) := by
      have : (1 - τ) * (σ - x) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith [hτ.2]) (by linarith)
      have hkey : x + τ * (σ - x) - σ = -((1 - τ) * (σ - x)) := by ring
      linarith
    have hle' : x + τ * (σ - x) ≤ x := by
      have : τ * (σ - x) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hτ.1 (by linarith)
      linarith
    by_cases hb' : x + τ * (σ - x) ≤ b
    · exact Or.inr ⟨le_trans hσ.1 hge, hb'⟩
    · have hb'' : b < x + τ * (σ - x) := not_le.mp hb'
      exact Or.inl ⟨by linarith [hb'', hs.2], by linarith [hle', hxs']⟩

/-- **The first-slot derivative of `G2M` on the region.**  For every point of the state region
the derivative of `u ↦ (G₂M n h u σ z) j` at `s` is the Abel-weighted integral of the
first-slot derivative of the manifest kernel along the moving chord point. -/
theorem deriv_G2M_eq_integral_on_RcM (n : ℕ) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) {a b ρ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) (hpos : KdenPosOn h a b) (j : Fin 2) :
    ∀ q ∈ RcM a b ρ,
      deriv (fun u : ℝ =>
        (Work.OddBridge.G2M n h u q.2.1 (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) j) q.1 =
        ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ *
          ((1 - τ) * deriv (fun u : ℝ =>
            (Work.OddBridge.KvecM n h u q.2.1 (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) j)
              (q.1 + τ * (q.2.1 - q.1))) := by
  intro q hq
  obtain ⟨hq1, hq2, hq3⟩ := hq
  obtain ⟨hz0, hz1, _⟩ := mem_RcM_facts ha hab hb hρ1 ⟨hq1, hq2, hq3⟩
  have hz0' : (0 : ℝ) < q.2.2 0 := lt_of_lt_of_le (by norm_num) hz0
  have hz1' : (0 : ℝ) < q.2.2 1 := lt_of_lt_of_le (by norm_num) hz1
  obtain ⟨δ, hδpos, hposloc, C, hCpos, hbndloc⟩ :=
    exists_bound_local n hh ha hab hb hρ1 hpos ⟨hq1, hq2, hq3⟩ j
  obtain ⟨CR, hCRpos, hbndR⟩ := exists_bound_RcM n hh ha hab hb hρ0 hρ1 hpos j
  set Cmax : ℝ := max C CR with hCmax
  have hCmaxpos : 0 < Cmax := lt_max_of_lt_left hCpos
  have hbdK : ∀ x ∈ Set.Ioo (q.1 - δ) (q.1 + δ), ∀ τ ∈ Set.Ico (0 : ℝ) 1,
      ‖(Work.OddBridge.KvecM n h (x + τ * (q.2.1 - x)) q.2.1
        (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) j‖ ≤ Cmax := by
    intro x hx τ hτ
    have hτ' : τ ∈ Set.Icc (0 : ℝ) 1 := ⟨hτ.1, le_of_lt hτ.2⟩
    rcases moving_point_mem_union (le_of_lt hδpos) hq1 hq2 hx hτ' with h | h
    · exact le_trans (hbndloc _ h).1 (le_max_left _ _)
    · exact le_trans (hbndR (x + τ * (q.2.1 - x), (q.2.1, q.2.2))
        ⟨h, hq2, hq3⟩).1 (le_max_right _ _)
  have hdiffK : ∀ x ∈ Set.Ioo (q.1 - δ) (q.1 + δ), ∀ τ ∈ Set.Ico (0 : ℝ) 1,
      DifferentiableAt ℝ (fun u : ℝ =>
        (Work.OddBridge.KvecM n h u q.2.1 (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) j)
        (x + τ * (q.2.1 - x)) := by
    intro x hx τ hτ
    have hτ' : τ ∈ Set.Icc (0 : ℝ) 1 := ⟨hτ.1, le_of_lt hτ.2⟩
    rcases moving_point_mem_union (le_of_lt hδpos) hq1 hq2 hx hτ' with h | h
    · exact differentiableAt_KvecM_component n j hh (q.2.2) (hposloc _ h).1 (hposloc _ h).2
    · exact differentiableAt_KvecM_component n j hh (q.2.2)
        (Real.sqrt_pos.mp (hpos (x + τ * (q.2.1 - x)) h q.2.1 hq2 (-(q.2.2 0))
          (by simpa [abs_neg, abs_of_pos hz0'] using hz0)))
        (Real.sqrt_pos.mp (hpos (x + τ * (q.2.1 - x)) h q.2.1 hq2 (q.2.2 1)
          (by simpa [abs_of_pos hz1'] using hz1)))
  have hboundK : ∀ x ∈ Set.Ioo (q.1 - δ) (q.1 + δ), ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ‖(1 - τ) * deriv (fun u : ℝ =>
        (Work.OddBridge.KvecM n h u q.2.1 (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) j)
        (x + τ * (q.2.1 - x))‖ ≤ Cmax := by
    intro x hx τ hτ
    have hτ' : 0 ≤ 1 - τ := by linarith [hτ.2]
    rcases moving_point_mem_union (le_of_lt hδpos) hq1 hq2 hx hτ with h | h
    · have hb := (hbndloc _ h).2
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hτ']
      exact le_trans (le_trans (mul_le_of_le_one_left (norm_nonneg _) (by linarith [hτ.1])) hb)
        (le_max_left _ _)
    · have hb := (hbndR (x + τ * (q.2.1 - x), (q.2.1, q.2.2)) ⟨h, hq2, hq3⟩).2
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hτ']
      exact le_trans (le_trans (mul_le_of_le_one_left (norm_nonneg _) (by linarith [hτ.1])) hb)
        (le_max_right _ _)
  have hmain := hasDerivAt_G2M_apply n hh (q.2.2) j hδpos hbdK hdiffK hboundK
  exact hmain.deriv

/-! ## 2. Continuity of the Abel integral of the first-slot derivative -/

/-- **Continuity of the Abel integral of the first-slot derivative of `KvecM`** on the state
region, by dominated convergence. -/
theorem continuousOn_integral_deriv_KvecM (n : ℕ) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) {a b ρ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) (hpos : KdenPosOn h a b) (j : Fin 2) :
    ContinuousOn (fun q : ℝ × (ℝ × St) =>
      ∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * (1 - τ)))⁻¹ *
        ((1 - τ) * deriv (fun u : ℝ =>
          (Work.OddBridge.KvecM n h u q.2.1 (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) j)
            (q.1 + τ * (q.2.1 - q.1)))) (RcM a b ρ) := by
  obtain ⟨C, hCpos, hbndR⟩ := exists_bound_RcM n hh ha hab hb hρ0 hρ1 hpos j
  set Φ : (ℝ × (ℝ × St)) → ℝ → ℝ := fun q τ => (Real.sqrt (τ * (1 - τ)))⁻¹ *
    ((1 - τ) * deriv (fun u : ℝ =>
      (Work.OddBridge.KvecM n h u q.2.1 (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) j)
        (q.1 + τ * (q.2.1 - q.1))) with hΦ
  intro q₀ hq₀
  refine intervalIntegral.continuousWithinAt_of_dominated_interval
    (μ := volume) (a := (0 : ℝ)) (b := 1) (s := RcM a b ρ) (x₀ := q₀) (F := Φ)
    (bound := fun τ => (Real.sqrt (τ * (1 - τ)))⁻¹ * C) ?_ ?_ ?_ ?_
  · -- measurability in the parameter
    refine Filter.Eventually.of_forall (fun q => ?_)
    refine Measurable.aestronglyMeasurable ?_
    simp only [hΦ]
    refine Measurable.mul ?_ (Measurable.mul ?_ ?_)
    · exact (Real.continuous_sqrt.measurable.comp
        (measurable_id.mul (measurable_const.sub measurable_id))).inv
    · exact measurable_const.sub measurable_id
    · exact (measurable_deriv (𝕜 := ℝ) (fun u : ℝ => (Work.OddBridge.KvecM n h u q.2.1
        (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) j)).comp
        (by fun_prop : Measurable fun τ : ℝ => q.1 + τ * (q.2.1 - q.1))
  · -- domination
    rw [eventually_nhdsWithin_iff]
    refine Filter.Eventually.of_forall (fun q hq => ?_)
    refine Filter.Eventually.of_forall (fun τ hτ => ?_)
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hτ
    rcases eq_or_lt_of_le hτ.2 with h1 | h1
    · subst h1
      simp only [hΦ]
      norm_num
    · obtain ⟨hq1, hq2, hq3⟩ := hq
      have hτIcc : τ ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hτ.1, le_of_lt h1⟩
      have hmem : q.1 + τ * (q.2.1 - q.1) ∈ Set.Icc a b := by
        constructor <;> nlinarith [hq1.1, hq1.2, hq2.1, hq2.2, hτIcc.1, hτIcc.2]
      have hb := (hbndR (q.1 + τ * (q.2.1 - q.1), (q.2.1, q.2.2)) ⟨hmem, hq2, hq3⟩).2
      have hτ' : 0 ≤ 1 - τ := by linarith [hτIcc.1]
      have hw : 0 ≤ (Real.sqrt (τ * (1 - τ)))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
      simp only [hΦ]
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hw, abs_of_nonneg hτ']
      refine mul_le_mul_of_nonneg_left ?_ hw
      exact le_trans (le_trans (mul_le_of_le_one_left (abs_nonneg _) (by linarith [hτIcc.1]))
        hb) (le_refl C)
  · -- integrability of the dominating function
    exact Commons.Geometry.Ulam.intervalIntegrable_abel_weight.mul_const C
  · -- a.e. slice continuity
    refine Filter.Eventually.of_forall (fun τ hτ => ?_)
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hτ
    rcases eq_or_lt_of_le hτ.2 with h1 | h1
    · subst h1
      have hzero : (fun q : ℝ × (ℝ × St) => Φ q 1) = fun _ => (0 : ℝ) := by
        funext q
        simp only [hΦ]
        norm_num
      rw [hzero]
      exact continuousWithinAt_const
    · have hτIcc : τ ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hτ.1, le_of_lt h1⟩
      have hψ : Continuous (fun q : ℝ × (ℝ × St) => (q.1 + τ * (q.2.1 - q.1), (q.2.1, q.2.2))) :=
        (by fun_prop : Continuous fun q : ℝ × (ℝ × St) => q.1 + τ * (q.2.1 - q.1)).prodMk
          (by fun_prop : Continuous fun q : ℝ × (ℝ × St) => (q.2.1, q.2.2))
      have hmaps : Set.MapsTo
          (fun q : ℝ × (ℝ × St) => (q.1 + τ * (q.2.1 - q.1), (q.2.1, q.2.2)))
          (RcM a b ρ) (GoodM h) := by
        intro q hq
        obtain ⟨hq1, hq2, hq3⟩ := hq
        obtain ⟨hz0, hz1, _⟩ := mem_RcM_facts ha hab hb hρ1 ⟨hq1, hq2, hq3⟩
        have hz0' : (0 : ℝ) < q.2.2 0 := lt_of_lt_of_le (by norm_num) hz0
        have hz1' : (0 : ℝ) < q.2.2 1 := lt_of_lt_of_le (by norm_num) hz1
        have hmem : q.1 + τ * (q.2.1 - q.1) ∈ Set.Icc a b := by
          constructor <;> nlinarith [hq1.1, hq1.2, hq2.1, hq2.2, hτIcc.1, hτIcc.2]
        exact ⟨Real.sqrt_pos.mp (hpos (q.1 + τ * (q.2.1 - q.1)) hmem q.2.1 hq2 (-(q.2.2 0))
            (by simpa [abs_neg, abs_of_pos hz0'] using hz0)),
          Real.sqrt_pos.mp (hpos (q.1 + τ * (q.2.1 - q.1)) hmem q.2.1 hq2 (q.2.2 1)
            (by simpa [abs_of_pos hz1'] using hz1))⟩
      have hcont : ContinuousWithinAt (fun q : ℝ × (ℝ × St) =>
          deriv (fun u : ℝ => (Work.OddBridge.KvecM n h u q.2.1
            (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) j)
            (q.1 + τ * (q.2.1 - q.1))) (RcM a b ρ) q₀ := by
        have hcomp := (continuousOn_deriv_KvecM_component_GoodM n j hh).comp hψ.continuousOn hmaps
        exact hcomp.continuousWithinAt hq₀
      simp only [hΦ]
      exact ((hcont.const_mul (1 - τ)).const_mul _)

/-! ## 3. Continuity of `𝚯M` on the region -/

/-- **Continuity of the manifest `𝚯M`-data**, in the curried coordinates
`q = (s, (σ, z))`. -/
theorem continuousOn_thetaM_curried (n : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {a b ρ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2)
    (hpos : KdenPosOn h a b) :
    ContinuousOn (fun q : ℝ × (ℝ × St) => ThetaM n h q.1 q.2.1 q.2.2) (RcM a b ρ) := by
  have hkey : ∀ j : Fin 2, ContinuousOn (fun q : ℝ × (ℝ × St) =>
      deriv (fun u : ℝ =>
        (Work.OddBridge.G2M n h u q.2.1 (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) j) q.1)
      (RcM a b ρ) := by
    intro j
    refine (continuousOn_integral_deriv_KvecM n hh ha hab hb hρ0 hρ1 hpos j).congr ?_
    intro q hq
    exact deriv_G2M_eq_integral_on_RcM n hh ha hab hb hρ0 hρ1 hpos j q hq
  rw [continuousOn_pi]
  intro i
  fin_cases i
  · have hc : ContinuousOn (fun q : ℝ × (ℝ × St) => - q.2.2 2) (RcM a b ρ) :=
      (((continuous_apply (2 : Fin 4)).comp
        (continuous_snd.comp continuous_snd)).neg).continuousOn
    exact hc.congr (fun q _ => by simp [Work.OddExistence.ThetaM])
  · have hc : ContinuousOn (fun q : ℝ × (ℝ × St) => - q.2.2 3) (RcM a b ρ) :=
      (((continuous_apply (3 : Fin 4)).comp
        (continuous_snd.comp continuous_snd)).neg).continuousOn
    exact hc.congr (fun q _ => by simp [Work.OddExistence.ThetaM])
  · have hc : ContinuousOn (fun q : ℝ × (ℝ × St) =>
        - deriv (fun u : ℝ =>
          (Work.OddBridge.G2M n h u q.2.1 (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) 0) q.1)
        (RcM a b ρ) := (hkey 0).neg
    exact hc.congr (fun q _ => by simp [Work.OddExistence.ThetaM])
  · have hc : ContinuousOn (fun q : ℝ × (ℝ × St) =>
        - deriv (fun u : ℝ =>
          (Work.OddBridge.G2M n h u q.2.1 (q.2.2 0) (q.2.2 1) (q.2.2 2) (q.2.2 3)) 1) q.1)
        (RcM a b ρ) := (hkey 1).neg
    exact hc.congr (fun q _ => by simp [Work.OddExistence.ThetaM])

/-! ## 4. The target: continuity of `𝚯M` on the region of the statement -/

theorem thetaM_continuous (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1)
    (hpos : Work.OddExistence.KdenPosOn h a b) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1 / 2) :
    ContinuousOn (fun p : (ℝ × ℝ) × Work.OddVolterra.St =>
        Work.OddExistence.ThetaM n h p.1.1 p.1.2 p.2)
      {p : (ℝ × ℝ) × Work.OddVolterra.St |
        p.1.1 ∈ Set.Icc a b ∧ p.1.2 ∈ Set.Icc a b ∧
        p.2 ∈ Metric.closedBall (Work.OddVolterra.baseState p.1.2) ρ} := by
  have hmain := continuousOn_thetaM_curried n hh ha hab hb hρ0 hρ1 hpos
  have hmap : Continuous (fun p : (ℝ × ℝ) × St => (p.1.1, (p.1.2, p.2))) := by fun_prop
  have hmaps : Set.MapsTo (fun p : (ℝ × ℝ) × St => (p.1.1, (p.1.2, p.2)))
      {p : (ℝ × ℝ) × St | p.1.1 ∈ Set.Icc a b ∧ p.1.2 ∈ Set.Icc a b ∧
        p.2 ∈ Metric.closedBall (Work.OddVolterra.baseState p.1.2) ρ} (RcM a b ρ) :=
    fun p hp => hp
  have := hmain.comp hmap.continuousOn hmaps
  simpa [Function.comp_def, RcM] using this


end

end Work.OddExistence.Manifest
