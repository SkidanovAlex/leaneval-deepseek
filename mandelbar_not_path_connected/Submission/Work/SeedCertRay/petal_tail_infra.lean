/-
# Infrastructure for the petal tail induction (`SeedCertRay`)

This module collects the elementary facts shared by the tail-induction lemmas of the ray-chain
certificate (`Submission/Work/NOTES_LEAD_mandelbar_noncusp.md` §2.4–§2.5):

* the level sequence `ρ` with `1 < ρ (k+1)` and `ρ (k+1) ^ 2 = ρ k` is strictly decreasing with
  `1 < ρ k`, `ρ (k+n) ^ 2^n = ρ k`, and `ρ (k+10) ^ 1024 = ρ k`;
* the holomorphic degree-`1024` map `F c = (T_c)^{10}` maps the ray segment
  `seg hN α₁ r₁ r₂` into the segment of angle `α₁` at the levels raised to the power `1024`
  (using `T^[10] α₁ = α₁` and `rayPt_iterate`);
* a preconnected set in `ℂ` all of whose points map under `F c` into a petal `Petal z₁ A R`
  and such that no point on the sphere `‖z - z₁‖ = ρ₁` maps into the petal, is contained in the
  closed ball of radius `ρ₁` about `z₁` (the intermediate-value step of the tail induction).
-/
import Mathlib
import Submission.Work.SeedCertRay.Basic
import Submission.Work.SeedCertRay.isPreconnected_seg
import Submission.Work.ELRig.rayPt_iterate

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Set Function Filter
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.SeedCertRay

/-! ## The level sequence `ρ` -/

/-- Every level of a sequence with `1 < ρ (k+1)` and `ρ (k+1) ^ 2 = ρ k` is `> 1`. -/
theorem rho_one_lt {ρ : ℕ → ℝ} (hρ : ∀ k, 1 < ρ (k + 1) ∧ ρ (k + 1) ^ 2 = ρ k) :
    ∀ k, 1 < ρ k := by
  intro k
  cases k with
  | zero =>
    have h := hρ 0
    rw [← h.2]
    nlinarith [h.1]
  | succ k => exact (hρ k).1

/-- The level sequence is strictly decreasing. -/
theorem rho_succ_lt {ρ : ℕ → ℝ} (hρ : ∀ k, 1 < ρ (k + 1) ∧ ρ (k + 1) ^ 2 = ρ k) :
    ∀ k, ρ (k + 1) < ρ k := by
  intro k
  have h := hρ k
  rw [← h.2]
  nlinarith [h.1]

/-- The level sequence is antitone. -/
theorem rho_antitone {ρ : ℕ → ℝ} (hρ : ∀ k, 1 < ρ (k + 1) ∧ ρ (k + 1) ^ 2 = ρ k) :
    Antitone ρ := by
  intro k l hkl
  have key : ∀ d, ρ (k + d) ≤ ρ k := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      rw [Nat.add_succ]
      exact le_trans (le_of_lt (rho_succ_lt hρ (k + d))) ih
  obtain ⟨d, hd⟩ : ∃ d, l = k + d := ⟨l - k, by omega⟩
  rw [hd]
  exact key d

/-- `ρ (k + n) ^ 2^n = ρ k`: the `n`-fold square-root relation. -/
theorem rho_pow {ρ : ℕ → ℝ} (hρ : ∀ k, 1 < ρ (k + 1) ∧ ρ (k + 1) ^ 2 = ρ k) :
    ∀ k n : ℕ, ρ (k + n) ^ (2 ^ n) = ρ k := by
  intro k n
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : ρ (k + (n + 1)) ^ (2 ^ (n + 1)) = ρ k := by
      have hsq : ρ (k + (n + 1)) ^ 2 = ρ (k + n) := by
        have h := (hρ (k + n)).2
        rwa [show k + n + 1 = k + (n + 1) from by omega] at h
      rw [show (2 : ℕ) ^ (n + 1) = 2 * 2 ^ n from by ring]
      rw [pow_mul, hsq]
      exact ih
    exact hstep

/-- The level relation in the form used by the ray chain: `ρ (k + 10) ^ 1024 = ρ k`. -/
theorem rho_pow_ten {ρ : ℕ → ℝ} (hρ : ∀ k, 1 < ρ (k + 1) ∧ ρ (k + 1) ^ 2 = ρ k) (k : ℕ) :
    ρ (k + 10) ^ (1024 : ℕ) = ρ k := by
  have h := rho_pow hρ k 10
  norm_num at h
  exact h

/-- **The window lemma for the level sequence `ρ`.**  If `ρ (k+1) ^ 2 = ρ k` and `1 < ρ (k+1)`
for every `k`, then for every real `t > 1` and every `j₀ ≥ 1` with `t < ρ (j₀ + 1)` there is an
index `j ≥ j₀` whose window `[ρ (j+1), ρ j]` contains `t`: the windows tile `(1, ρ 1]`, and `t`
lies below the window of `j₀`. -/
theorem rho_window {ρ : ℕ → ℝ} (hρ : ∀ k, 1 < ρ (k + 1) ∧ ρ (k + 1) ^ 2 = ρ k)
    {t : ℝ} (ht : 1 < t) {j₀ : ℕ} (hj₀ : 1 ≤ j₀) (h0 : t < ρ (j₀ + 1)) :
    ∃ j, j₀ ≤ j ∧ ρ (j + 1) ≤ t ∧ t ≤ ρ j := by
  have hanti : Antitone ρ := rho_antitone hρ
  have hone : 1 < ρ j₀ := rho_one_lt hρ j₀
  -- some level is below `t`
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (ρ j₀) ht
  have h2m : t ^ m ≤ t ^ (2 ^ m) :=
    pow_le_pow_right₀ (le_of_lt ht) (le_of_lt Nat.lt_two_pow_self)
  have hm' : ρ j₀ < t ^ (2 ^ m) := lt_of_lt_of_le hm h2m
  have hpow : ρ (j₀ + m) ^ (2 ^ m) = ρ j₀ := rho_pow hρ j₀ m
  have hlt : ρ (j₀ + m) < t := by
    by_contra hcon
    have hle : t ^ (2 ^ m) ≤ ρ (j₀ + m) ^ (2 ^ m) :=
      pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ t) (not_lt.mp hcon) _
    rw [hpow] at hle
    exact absurd hm' (not_lt.mpr hle)
  have hex : ∃ k : ℕ, ρ (k + 1) < t := by
    refine ⟨j₀ + m - 1, ?_⟩
    have hidx : j₀ + m - 1 + 1 = j₀ + m := by omega
    rw [hidx]
    exact hlt
  obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j := ⟨_, rfl⟩
  have hjP : ρ (j + 1) < t := by rw [← hj]; exact Nat.find_spec hex
  have hjmin : ∀ k, k < j → ¬ (ρ (k + 1) < t) := by
    intro k hk
    rw [← hj] at hk
    exact Nat.find_min hex hk
  have hjge : j₀ ≤ j := by
    by_contra hcon
    have h1 : j + 1 ≤ j₀ := by omega
    have h2 : ρ j₀ ≤ ρ (j + 1) := hanti h1
    have h3 : ρ (j₀ + 1) ≤ ρ j₀ := hanti (by omega)
    linarith
  have hmono := hjmin (j - 1) (by omega)
  have hidx : (j - 1) + 1 = j := by omega
  rw [hidx] at hmono
  exact ⟨j, hjge, le_of_lt hjP, not_lt.mp hmono⟩

/-! ## The petal is contained in the ball of radius `ρ₁` -/

/-- A point of the repelling petal `Petal z₁ A R` is within `ρ₁` of `z₁`, provided
`1 ≤ R * ‖A‖ * ρ₁` (which also forces `R > 0`): the Fatou coordinate `w = -1/(A (z - z₁))` of a
point of the petal satisfies `R < -Re w ≤ |w| = 1/(‖A‖ ‖z - z₁‖)`, so
`‖z - z₁‖ < 1/(R ‖A‖) ≤ ρ₁`. -/
theorem petal_subset_closedBall {z₁ A : ℂ} {R ρ₁ : ℝ} (hA : A ≠ 0) (hρ₁ : 0 < ρ₁)
    (hRQ : 1 ≤ R * ‖A‖ * ρ₁) : Petal z₁ A R ⊆ Metric.closedBall z₁ ρ₁ := by
  intro z hz
  obtain ⟨hzne, hzR⟩ := hz
  have hApos : 0 < ‖A‖ := norm_pos_iff.mpr hA
  have hRpos : 0 < R := by
    by_contra hcon
    have hnn : 0 ≤ ‖A‖ * ρ₁ := mul_nonneg hApos.le hρ₁.le
    have hle : R * (‖A‖ * ρ₁) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hcon) hnn
    nlinarith [hRQ]
  have hd0 : z - z₁ ≠ 0 := sub_ne_zero.mpr hzne
  have hdpos : 0 < ‖z - z₁‖ := norm_pos_iff.mpr hd0
  have hnorm : ‖fatou z₁ A z‖ = (‖A‖ * ‖z - z₁‖)⁻¹ := by
    simp only [fatou, norm_neg, norm_inv, norm_mul]
  have h1 : R < (‖A‖ * ‖z - z₁‖)⁻¹ := by
    calc R < -(fatou z₁ A z).re := by linarith
      _ ≤ |(fatou z₁ A z).re| := neg_le_abs _
      _ ≤ ‖fatou z₁ A z‖ := Complex.abs_re_le_norm _
      _ = (‖A‖ * ‖z - z₁‖)⁻¹ := hnorm
  have h3 : ‖z - z₁‖ < 1 / (R * ‖A‖) := by
    have hlt : ‖A‖ * ‖z - z₁‖ < R⁻¹ :=
      (lt_inv_comm₀ (a := R) (b := ‖A‖ * ‖z - z₁‖) hRpos
        (mul_pos hApos hdpos)).mp h1
    rw [show (1 : ℝ) / (R * ‖A‖) = R⁻¹ / ‖A‖ from by ring]
    rw [lt_div_iff₀ hApos, mul_comm]
    exact hlt
  have h4 : 1 / (R * ‖A‖) ≤ ρ₁ := by
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < R * ‖A‖)]
    linarith
  rw [Metric.mem_closedBall, dist_eq_norm]
  linarith

/-- If `z` lies in the repelling petal of `z₁` (multiplier model `A`) and its Fatou coordinate
`w = -1/(A (z - z₁))` has real part at most `-R - nδ` (with `R > 0`, `δ > 0`), then
`‖z - z₁‖ ≤ 1/(‖A‖ (R + nδ))`. -/
theorem norm_sub_le_of_fatou_bound {z₁ A : ℂ} {R δ : ℝ} (hA : A ≠ 0) (hR : 0 < R)
    (hδ : 0 < δ) (n : ℕ) {z : ℂ} (hz : z ∈ Petal z₁ A R)
    (hW : (fatou z₁ A z).re ≤ -R - n * δ) :
    ‖z - z₁‖ ≤ (‖A‖ * (R + n * δ))⁻¹ := by
  obtain ⟨hzne, -⟩ := hz
  have hApos : 0 < ‖A‖ := norm_pos_iff.mpr hA
  have hd0 : z - z₁ ≠ 0 := sub_ne_zero.mpr hzne
  have hdpos : 0 < ‖z - z₁‖ := norm_pos_iff.mpr hd0
  have hnd : 0 < R + n * δ := by positivity
  have hnorm : ‖fatou z₁ A z‖ = (‖A‖ * ‖z - z₁‖)⁻¹ := by
    simp only [fatou, norm_neg, norm_inv, norm_mul]
  have h1 : R + n * δ ≤ (‖A‖ * ‖z - z₁‖)⁻¹ := by
    calc R + n * δ = -(-R - n * δ) := by ring
      _ ≤ -(fatou z₁ A z).re := by linarith
      _ ≤ |(fatou z₁ A z).re| := neg_le_abs _
      _ ≤ ‖fatou z₁ A z‖ := Complex.abs_re_le_norm _
      _ = (‖A‖ * ‖z - z₁‖)⁻¹ := hnorm
  have h2 : ‖A‖ * ‖z - z₁‖ ≤ (R + n * δ)⁻¹ :=
    (le_inv_comm₀ (a := R + n * δ) (b := ‖A‖ * ‖z - z₁‖) hnd
      (mul_pos hApos hdpos)).mp h1
  rw [show (‖A‖ * (R + n * δ))⁻¹ = (R + n * δ)⁻¹ / ‖A‖ from by
        rw [mul_inv, inv_mul_eq_div]]
  rw [le_div_iff₀ hApos, mul_comm]
  exact h2

/-! ## The `F`-image of a ray segment -/

/-- **`F` maps the segment of the ray `α₁` between the levels `r₁ ≤ r₂` into the segment between
the levels `r₁ ^ 1024` and `r₂ ^ 1024`.**  `F c = (T_c)^{10}` multiplies the angle by `T^[10]`
and raises the level to the power `1024`; the hypothesis `hα` says that `α₁` is fixed by the
angle map, so the image is again a piece of the same ray, at the levels raised to the power
`1024`. -/
theorem F_mem_seg {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hφ : Work.ParamRays.IsDynBottcher c φ)
    (hα : Work.EL.T^[10] Work.EL.alpha1 = Work.EL.alpha1) {r₁ r₂ s₁ s₂ : ℝ}
    (h1 : s₁ = r₁ ^ (1024 : ℕ)) (h2 : s₂ = r₂ ^ (1024 : ℕ)) (hr : 1 < r₁) {t : ℝ}
    (ht : t ∈ Set.Icc r₁ r₂) :
    Work.EL.F c (Work.EL.rayPt hN Work.EL.alpha1 t) ∈
      seg hN Work.EL.alpha1 s₁ s₂ := by
  have ht1 : 1 < t := lt_of_lt_of_le hr ht.1
  refine ⟨t ^ (1024 : ℕ), ⟨?_, ?_⟩, ?_⟩
  · rw [h1]
    exact pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ r₁) ht.1 1024
  · rw [h2]
    exact pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ t) ht.2 1024
  · rw [Work.ELRig.rayPt_iterate hN hφ ht1, hα]

/-! ## Crossing the sphere of radius `ρ₁` -/

/-- **A preconnected set whose `F`-image lies in the petal and which is missed by the injectivity
of `F` on the sphere is contained in the closed ball of radius `ρ₁`.**  If the preconnected set
`S` contains a point of the closed ball and had a point outside it, the continuous function
`z ↦ ‖z - z₁‖` would take the value `ρ₁` on `S`; but the hypothesis `hsphere` says that no point
of `S` on the sphere has its `F`-image in the petal, while `hpetal` says that every point of `S`
has its `F`-image in the petal. -/
theorem preconnected_subset_closedBall {c : ℂ} {z₁ A : ℂ} {R ρ₁ : ℝ} {S : Set ℂ}
    (hS : IsPreconnected S) (ha : ∃ a ∈ S, ‖a - z₁‖ ≤ ρ₁)
    (hsphere : ∀ z ∈ S, ‖z - z₁‖ = ρ₁ → Work.EL.F c z ∉ Petal z₁ A R)
    (hpetal : ∀ z ∈ S, Work.EL.F c z ∈ Petal z₁ A R) :
    S ⊆ Metric.closedBall z₁ ρ₁ := by
  intro x hx
  by_contra hxc
  rw [Metric.mem_closedBall, dist_eq_norm] at hxc
  obtain ⟨a, haS, haρ⟩ := ha
  have hcont : ContinuousOn (fun z : ℂ => ‖z - z₁‖) S :=
    (continuous_norm.comp (continuous_id.sub continuous_const)).continuousOn
  have hxc' : ρ₁ < ‖x - z₁‖ := not_le.mp hxc
  have hmem : ρ₁ ∈ Set.Icc ((fun z : ℂ => ‖z - z₁‖) a) ((fun z : ℂ => ‖z - z₁‖) x) :=
    ⟨haρ, le_of_lt hxc'⟩
  obtain ⟨z, hzS, hzρ⟩ := hS.intermediate_value haS hx hcont hmem
  exact hsphere z hzS hzρ (hpetal z hzS)

end Work.SeedCertRay
