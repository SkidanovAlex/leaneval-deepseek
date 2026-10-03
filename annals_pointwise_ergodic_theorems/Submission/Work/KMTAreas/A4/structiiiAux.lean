/-
# Auxiliary `ℓᵖ` lemmas for the proof of Corollary `struct-iii` (`A4.structiiiWinA`)

The `ℒᵖ` seminorm of a function `f : ℤ → ℂ` against the counting measure on `ℤ` is the
`ℓᵖ`-norm `(∑_x ‖f x‖^p)^{1/p}`, whenever that sum converges:

  `eLpNorm f (ofReal p) count = ofReal ((∑' x, ‖f x‖ ^ p) ^ (1/p))`.

This module also records the level-set (`truncation`) estimate

  `eLpNorm (g · 1_{λ < ‖g‖}) (ofReal p) ≤ ofReal (λ^{1-2/p} a^{2/p})`  (`1 < p < 2`),

for `g` with `eLpNorm g 2 = ofReal a`, which is the interpolation step used in the proof of
Corollary `struct-iii`.
-/
import Mathlib
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Work.KMTAreas.A4

theorem rpow_two_eq (a : ℝ) : a ^ (2 : ℝ) = a ^ 2 := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

theorem pow_two_eq (a : ℝ) : a ^ 2 = a ^ (2 : ℝ) := (rpow_two_eq a).symm

/-- **The `ℒᵖ` seminorm w.r.t. counting measure is the `ℓᵖ`-norm.**  For a function
`f : ℤ → ℂ` whose `p`-th powers are summable,

  `eLpNorm f (ofReal p) count = ofReal ((∑' x, ‖f x‖ ^ p) ^ (1/p))`. -/
theorem eLpNorm_count_eq_ofReal_tsum_rpow (f : ℤ → ℂ) {p : ℝ} (hp : 0 < p)
    (hs : Summable (fun x : ℤ => ‖f x‖ ^ p)) :
    MeasureTheory.eLpNorm f (ENNReal.ofReal p) Measure.count
      = ENNReal.ofReal ((∑' x : ℤ, ‖f x‖ ^ p) ^ (1 / p)) := by
  have hpne : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hp)
  have hptop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have htoReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp.le
  have hnn : ∀ x : ℤ, (0 : ℝ) ≤ ‖f x‖ ^ p := fun x => Real.rpow_nonneg (norm_nonneg _) _
  calc MeasureTheory.eLpNorm f (ENNReal.ofReal p) Measure.count
      = (∫⁻ x : ℤ, ‖f x‖ₑ ^ ((ENNReal.ofReal p).toReal) ∂Measure.count)
          ^ (1 / (ENNReal.ofReal p).toReal) :=
        MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hpne hptop
    _ = (∑' x : ℤ, ‖f x‖ₑ ^ p) ^ (1 / p) := by
        rw [htoReal, MeasureTheory.lintegral_count]
    _ = (∑' x : ℤ, ENNReal.ofReal (‖f x‖ ^ p)) ^ (1 / p) := by
        congr 1
        apply tsum_congr
        intro x
        rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le]
    _ = (ENNReal.ofReal (∑' x : ℤ, ‖f x‖ ^ p)) ^ (1 / p) := by
        rw [ENNReal.ofReal_tsum_of_nonneg hnn hs]
    _ = ENNReal.ofReal ((∑' x : ℤ, ‖f x‖ ^ p) ^ (1 / p)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (tsum_nonneg hnn) (by positivity)]

/-- **The `ℓ²`-sum of a function whose `ℒ²` seminorm is `ofReal a`.**  If
`eLpNorm g 2 count = ofReal a` (`a ≥ 0`) then `∑_x ‖g x‖² = a²` (and in particular the sum
converges). -/
theorem summable_sq_tsum_eq_of_eLpNorm_two {g : ℤ → ℂ} {a : ℝ} (ha : 0 ≤ a)
    (hg : MeasureTheory.eLpNorm g 2 Measure.count = ENNReal.ofReal a) :
    Summable (fun x : ℤ => ‖g x‖ ^ (2 : ℝ))
      ∧ (∑' x : ℤ, ‖g x‖ ^ (2 : ℝ)) = a ^ 2 := by
  have h2ne : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2top : (2 : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top 2
  have hlin := MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (μ := Measure.count)
    (f := g) h2ne h2top
  rw [hg, ENNReal.toReal_ofNat] at hlin
  have hI : (∫⁻ x : ℤ, ‖g x‖ₑ ^ (2 : ℝ) ∂Measure.count) = ENNReal.ofReal (a ^ (2 : ℝ)) := by
    have h1 : (ENNReal.ofReal a) ^ (2 : ℝ)
        = ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2 : ℝ) ∂Measure.count := by
      rw [hlin, ← ENNReal.rpow_mul,
        show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one]
    rw [← h1, ENNReal.ofReal_rpow_of_nonneg ha (by norm_num : (0 : ℝ) ≤ 2)]
  have hbound : ∀ s : Finset ℤ, ∑ x ∈ s, ‖g x‖ ^ (2 : ℝ) ≤ a ^ 2 := by
    intro s
    refine (ENNReal.ofReal_le_ofReal_iff (sq_nonneg a)).mp ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => Real.rpow_nonneg (norm_nonneg _) _)]
    calc ∑ x ∈ s, ENNReal.ofReal (‖g x‖ ^ (2 : ℝ))
        = ∑ x ∈ s, ‖g x‖ₑ ^ (2 : ℝ) := by
          refine Finset.sum_congr rfl (fun x _ => ?_)
          rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _)
            (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ ∑' x : ℤ, ‖g x‖ₑ ^ (2 : ℝ) := ENNReal.sum_le_tsum s
      _ = ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2 : ℝ) ∂Measure.count :=
          (MeasureTheory.lintegral_count _).symm
      _ = ENNReal.ofReal (a ^ (2 : ℝ)) := hI
      _ = ENNReal.ofReal (a ^ 2) := by rw [rpow_two_eq a]
  have hs : Summable (fun x : ℤ => ‖g x‖ ^ (2 : ℝ)) :=
    summable_of_sum_le (fun x => Real.rpow_nonneg (norm_nonneg _) _) hbound
  refine ⟨hs, ?_⟩
  have hkey := eLpNorm_count_eq_ofReal_tsum_rpow g (p := 2) (by norm_num) hs
  have hg' : MeasureTheory.eLpNorm g (ENNReal.ofReal 2) Measure.count = ENNReal.ofReal a := by
    rw [show (ENNReal.ofReal 2 : ℝ≥0∞) = 2 by norm_num]; exact hg
  rw [hg'] at hkey
  have hnn : (0 : ℝ) ≤ (∑' x : ℤ, ‖g x‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (tsum_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) _
  have hsqrt : (∑' x : ℤ, ‖g x‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = a :=
    (ENNReal.ofReal_eq_ofReal_iff hnn ha).mp hkey.symm
  have hnn2 : (0 : ℝ) ≤ ∑' x : ℤ, ‖g x‖ ^ (2 : ℝ) :=
    tsum_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  calc (∑' x : ℤ, ‖g x‖ ^ (2 : ℝ))
      = ((∑' x : ℤ, ‖g x‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
        rw [← Real.rpow_mul hnn2, show (1 / 2 : ℝ) * 2 = 1 by norm_num, Real.rpow_one]
    _ = a ^ 2 := by
        rw [hsqrt, rpow_two_eq a]

/-- **The level-set (truncation) estimate.**  If `eLpNorm g 2 count = ofReal a` then the part of
`g` above the level `lam > 0` satisfies the `ℓ^p` bound
`‖g · 1_{lam < ‖g‖}‖_p ≤ lam^{1-2/p} a^{2/p}` for every `1 < p < 2`. -/
theorem eLpNorm_indicator_lp_le {g : ℤ → ℂ} {p lam a : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hlam : 0 < lam) (ha : 0 ≤ a)
    (hg : MeasureTheory.eLpNorm g 2 Measure.count = ENNReal.ofReal a) :
    MeasureTheory.eLpNorm (fun x : ℤ => if lam < ‖g x‖ then g x else 0)
        (ENNReal.ofReal p) Measure.count
      ≤ ENNReal.ofReal (lam ^ (1 - 2 / p) * a ^ (2 / p)) := by
  obtain ⟨hsum2, htsum2⟩ := summable_sq_tsum_eq_of_eLpNorm_two ha hg
  have hp0 : 0 < p := by linarith
  set G : ℤ → ℂ := fun x => if lam < ‖g x‖ then g x else 0 with hG
  have hpt : ∀ x : ℤ, ‖G x‖ ^ p ≤ lam ^ (p - 2) * ‖g x‖ ^ (2 : ℝ) := by
    intro x
    by_cases hx : lam < ‖g x‖
    · rw [hG]
      simp only [hx, if_true]
      have hgx : 0 < ‖g x‖ := lt_trans hlam hx
      have h1 : ‖g x‖ ^ (p - 2) ≤ lam ^ (p - 2) :=
        Real.rpow_le_rpow_of_nonpos hlam (le_of_lt hx) (by linarith)
      calc ‖g x‖ ^ p = ‖g x‖ ^ (p - 2) * ‖g x‖ ^ (2 : ℝ) := by
            rw [← Real.rpow_add hgx]
            norm_num
        _ ≤ lam ^ (p - 2) * ‖g x‖ ^ (2 : ℝ) :=
            mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (norm_nonneg _) _)
    · rw [hG]
      simp only [hx, if_false, norm_zero, Real.zero_rpow (ne_of_gt hp0)]
      exact mul_nonneg (Real.rpow_nonneg hlam.le _) (Real.rpow_nonneg (norm_nonneg _) _)
  have hsum1 : Summable (fun x : ℤ => ‖G x‖ ^ p) :=
    Summable.of_nonneg_of_le (fun x => Real.rpow_nonneg (norm_nonneg _) _) hpt
      (hsum2.mul_left (lam ^ (p - 2)))
  rw [eLpNorm_count_eq_ofReal_tsum_rpow G hp0 hsum1]
  refine ENNReal.ofReal_le_ofReal ?_
  have hle : (∑' x : ℤ, ‖G x‖ ^ p) ≤ lam ^ (p - 2) * a ^ (2 : ℝ) := by
    have h1 : (∑' x : ℤ, ‖G x‖ ^ p) ≤ ∑' x : ℤ, lam ^ (p - 2) * ‖g x‖ ^ (2 : ℝ) :=
      Summable.tsum_le_tsum hpt hsum1 (hsum2.mul_left _)
    rw [tsum_mul_left, htsum2] at h1
    rwa [pow_two_eq a] at h1
  have hnn : (0 : ℝ) ≤ ∑' x : ℤ, ‖G x‖ ^ p := tsum_nonneg fun x =>
    Real.rpow_nonneg (norm_nonneg _) _
  calc (∑' x : ℤ, ‖G x‖ ^ p) ^ (1 / p)
      ≤ (lam ^ (p - 2) * a ^ (2 : ℝ)) ^ (1 / p) :=
        Real.rpow_le_rpow hnn hle (by positivity)
    _ = lam ^ (1 - 2 / p) * a ^ (2 / p) := by
        have key1 : a ^ ((2 : ℝ) * (1 / p)) = (a ^ (2 : ℝ)) ^ (1 / p) :=
          Real.rpow_mul ha 2 (1 / p)
        have key2 : lam ^ ((p - 2) * (1 / p)) = (lam ^ (p - 2)) ^ (1 / p) :=
          Real.rpow_mul hlam.le (p - 2) (1 / p)
        have hp2' : (p - 2) * (1 / p) = 1 - 2 / p := by field_simp
        have hp3' : (2 : ℝ) * (1 / p) = 2 / p := by ring
        rw [Real.mul_rpow (Real.rpow_nonneg hlam.le _) (Real.rpow_nonneg ha _),
          ← key1, ← key2, hp2', hp3']

end Work.KMTAreas.A4
