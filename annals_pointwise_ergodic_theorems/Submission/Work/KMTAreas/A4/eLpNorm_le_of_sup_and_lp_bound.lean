import Mathlib
import Submission.Work.KMTAreas.A4.structiiiAux
import Submission.Work.Analysis.InverseTheory.Transpose

/-!
# Interpolation of an operator on `ℓ²(ℤ)` between an `ℓ^∞` bound and an `ℓᵖ` bound

Let `T` be an operator on sequences `ℤ → ℂ`, additive on sequences supported in `[-N₀, N₀]`,
which is bounded
* from `ℓ^∞` (restricted to `N₀`-supported sequences) to `ℓ²` with constant `X`, and
* from `ℓ^p` to `ℓ²` with constant `Y` (`1 < p < 2`).

Then for every `N₀`-supported `g`,

  `‖T g‖_{ℓ²} ≤ 2 X^{1-p/2} Y^{p/2} ‖g‖_{ℓ²}`.

This is the standard real-interpolation-with-truncation argument: split `g` at the level `λ` into
its small part `g 1_{‖g‖ ≤ λ}` (bounded by `λ`, hence handled by the `ℓ^∞` bound) and its large
part `g 1_{λ < ‖g‖}` (handled by the `ℓ^p` bound together with the level-set estimate
`Work.KMTAreas.A4.eLpNorm_indicator_lp_le`, `‖g 1_{λ<‖g‖}‖_p ≤ λ^{1-2/p} a^{2/p}` where
`a = ‖g‖₂`).  Optimising in `λ` gives the constant `2 X^{1-p/2} Y^{p/2}`.
-/

set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace Work.KMTAreas.A4

/-- **The optimal truncation level.**  With `λ = (Y/X)^{p/2} a` the two terms of the truncated
estimate balance, and both equal `X^{1-p/2} Y^{p/2} a`:

  `X λ + Y λ^{1-2/p} a^{2/p} = 2 X^{1-p/2} Y^{p/2} a`. -/
private lemma lam_arith {p X Y a : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hX : 0 < X) (hY : 0 < Y)
    (ha : 0 ≤ a) :
    X * ((Y / X) ^ (p / 2) * a) + Y * (((Y / X) ^ (p / 2) * a) ^ (1 - 2 / p) * a ^ (2 / p))
      = 2 * X ^ (1 - p / 2) * Y ^ (p / 2) * a := by
  have hp0 : 0 < p := by linarith
  have he1 : p / 2 * (1 - 2 / p) = p / 2 - 1 := by
    field_simp
    try ring
  have hYX : 0 ≤ Y / X := div_nonneg hY.le hX.le
  have hXsub : X ^ (1 - p / 2) = X / X ^ (p / 2) := by
    rw [Real.rpow_sub hX 1 (p / 2), Real.rpow_one]
  have hXinv : X ^ (1 - p / 2) = 1 / X ^ (p / 2 - 1) := by
    rw [hXsub]
    have hXe : X ^ (p / 2) = X ^ (p / 2 - 1) * X := by
      calc X ^ (p / 2) = X ^ ((p / 2 - 1) + 1) := by rw [show p / 2 - 1 + 1 = p / 2 by ring]
        _ = X ^ (p / 2 - 1) * X ^ (1 : ℝ) := Real.rpow_add hX _ _
        _ = X ^ (p / 2 - 1) * X := by rw [Real.rpow_one]
    rw [hXe]; field_simp
  have hbody : (Y / X) ^ (p / 2) = Y ^ (p / 2) / X ^ (p / 2) :=
    Real.div_rpow hY.le hX.le _
  have hterm1 : X * ((Y / X) ^ (p / 2) * a) = X ^ (1 - p / 2) * Y ^ (p / 2) * a := by
    rw [hbody, hXsub]
    field_simp
    try ring
  rcases eq_or_lt_of_le ha with h0 | hapos
  · rw [← h0]
    have hz1 : (0 : ℝ) ^ (1 - 2 / p) = 0 := by
      apply Real.zero_rpow
      intro h
      have : p = 2 := by field_simp at h; linarith
      linarith
    have hz2 : (0 : ℝ) ^ (2 / p) = 0 := Real.zero_rpow (by positivity)
    simp [hz1, hz2]
  · have hYpow : Y ^ (p / 2) = Y * Y ^ (p / 2 - 1) := by
      calc Y ^ (p / 2) = Y ^ (1 + (p / 2 - 1)) := by rw [show 1 + (p / 2 - 1) = p / 2 by ring]
        _ = Y ^ (1 : ℝ) * Y ^ (p / 2 - 1) := Real.rpow_add hY _ _
        _ = Y * Y ^ (p / 2 - 1) := by rw [Real.rpow_one]
    have hap : a = a ^ (1 - 2 / p) * a ^ (2 / p) := by
      calc a = a ^ (1 : ℝ) := (Real.rpow_one a).symm
        _ = a ^ ((1 - 2 / p) + (2 / p)) := by rw [show 1 - 2 / p + 2 / p = 1 by ring]
        _ = a ^ (1 - 2 / p) * a ^ (2 / p) := Real.rpow_add hapos _ _
    have hpow : ((Y / X) ^ (p / 2) * a) ^ (1 - 2 / p)
        = Y ^ (p / 2 - 1) * X ^ (1 - p / 2) * a ^ (1 - 2 / p) := by
      calc ((Y / X) ^ (p / 2) * a) ^ (1 - 2 / p)
          = ((Y / X) ^ (p / 2)) ^ (1 - 2 / p) * a ^ (1 - 2 / p) :=
            Real.mul_rpow (Real.rpow_nonneg hYX _) ha
        _ = (Y / X) ^ (p / 2 * (1 - 2 / p)) * a ^ (1 - 2 / p) := by
            rw [← Real.rpow_mul hYX (p / 2) (1 - 2 / p)]
        _ = (Y / X) ^ (p / 2 - 1) * a ^ (1 - 2 / p) := by rw [he1]
        _ = (Y ^ (p / 2 - 1) / X ^ (p / 2 - 1)) * a ^ (1 - 2 / p) := by
            rw [Real.div_rpow hY.le hX.le]
        _ = Y ^ (p / 2 - 1) * X ^ (1 - p / 2) * a ^ (1 - 2 / p) := by
            rw [hXinv]; ring
    have hterm2 : Y * (((Y / X) ^ (p / 2) * a) ^ (1 - 2 / p) * a ^ (2 / p))
        = X ^ (1 - p / 2) * Y ^ (p / 2) * a := by
      calc Y * (((Y / X) ^ (p / 2) * a) ^ (1 - 2 / p) * a ^ (2 / p))
          = Y * (Y ^ (p / 2 - 1) * X ^ (1 - p / 2) * a ^ (1 - 2 / p)) * a ^ (2 / p) := by
              rw [hpow]; ring
        _ = (Y * Y ^ (p / 2 - 1)) * X ^ (1 - p / 2)
              * (a ^ (1 - 2 / p) * a ^ (2 / p)) := by ring
        _ = Y ^ (p / 2) * X ^ (1 - p / 2) * a := by rw [← hYpow, ← hap]
        _ = X ^ (1 - p / 2) * Y ^ (p / 2) * a := by ring
    rw [hterm1, hterm2]
    ring

theorem eLpNorm_le_of_sup_and_lp_bound {T : (ℤ → ℂ) → (ℤ → ℂ)} {N₀ : ℕ} (hadd : ∀ u v : ℤ → ℂ, Work.Analysis.InverseTheory.SupportIn u N₀ → Work.Analysis.InverseTheory.SupportIn v N₀ → T (u + v) = T u + T v) {p X Y : ℝ} (hp1 : 1 < p) (hp2 : p < 2) (hX : 0 < X) (hY : 0 < Y) (hsup : ∀ (u : ℤ → ℂ) (M : ℝ), 0 ≤ M → Work.Analysis.InverseTheory.SupportIn u N₀ → (∀ x : ℤ, ‖u x‖ ≤ M) → MeasureTheory.eLpNorm (T u) 2 MeasureTheory.Measure.count ≤ ENNReal.ofReal (X * M)) (hlp : ∀ u : ℤ → ℂ, MeasureTheory.eLpNorm (T u) 2 MeasureTheory.Measure.count ≤ ENNReal.ofReal Y * MeasureTheory.eLpNorm u (ENNReal.ofReal p) MeasureTheory.Measure.count) {g : ℤ → ℂ} (hgs : Work.Analysis.InverseTheory.SupportIn g N₀) {a : ℝ} (ha : 0 ≤ a) (hg2 : MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count = ENNReal.ofReal a) : MeasureTheory.eLpNorm (T g) 2 MeasureTheory.Measure.count ≤ ENNReal.ofReal (2 * X ^ (1 - p / 2) * Y ^ (p / 2)) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  -- the truncation bound, valid for every level `λ > 0`
  have hgen : ∀ lam : ℝ, 0 < lam →
      MeasureTheory.eLpNorm (T g) 2 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (X * lam + Y * (lam ^ (1 - 2 / p) * a ^ (2 / p))) := by
    intro lam hlam
    set g₁ : ℤ → ℂ := fun x => if ‖g x‖ ≤ lam then g x else 0 with hg₁
    set g₂ : ℤ → ℂ := fun x => if lam < ‖g x‖ then g x else 0 with hg₂
    have hg₁s : Work.Analysis.InverseTheory.SupportIn g₁ N₀ := by
      intro x hx
      rw [hg₁]
      have hx0 : g x = 0 := hgs x hx
      simp [hx0, hlam.le]
    have hg₂s : Work.Analysis.InverseTheory.SupportIn g₂ N₀ := by
      intro x hx
      rw [hg₂]
      have hx0 : g x = 0 := hgs x hx
      simp [hx0, show ¬ (lam < (0 : ℝ)) from not_lt.mpr hlam.le]
    have hsum : g₁ + g₂ = g := by
      funext x
      rw [hg₁, hg₂]
      simp only [Pi.add_apply]
      by_cases h : ‖g x‖ ≤ lam
      · rw [if_pos h, if_neg (not_lt.mpr h), add_zero]
      · rw [if_neg h, if_pos (lt_of_not_ge h), zero_add]
    have hT : T g = T g₁ + T g₂ := by
      rw [← hsum]
      exact hadd g₁ g₂ hg₁s hg₂s
    have hA : MeasureTheory.eLpNorm (T g₁) 2 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (X * lam) := by
      refine hsup g₁ lam hlam.le hg₁s ?_
      intro x
      show ‖(if ‖g x‖ ≤ lam then g x else 0 : ℂ)‖ ≤ lam
      by_cases h : ‖g x‖ ≤ lam
      · rw [if_pos h]; exact h
      · rw [if_neg h]; simp only [norm_zero]; exact hlam.le
    have hB : MeasureTheory.eLpNorm (T g₂) 2 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal Y * ENNReal.ofReal (lam ^ (1 - 2 / p) * a ^ (2 / p)) := by
      refine (hlp g₂).trans ?_
      have htr := eLpNorm_indicator_lp_le (g := g) (p := p) (lam := lam) (a := a)
        hp1 hp2 hlam ha hg2
      rw [← hg₂] at htr
      exact mul_le_mul' le_rfl htr
    calc MeasureTheory.eLpNorm (T g) 2 MeasureTheory.Measure.count
        = MeasureTheory.eLpNorm (T g₁ + T g₂) 2 MeasureTheory.Measure.count := by rw [hT]
      _ ≤ MeasureTheory.eLpNorm (T g₁) 2 MeasureTheory.Measure.count
            + MeasureTheory.eLpNorm (T g₂) 2 MeasureTheory.Measure.count :=
          eLpNorm_add_le (by norm_num)
      _ ≤ ENNReal.ofReal (X * lam)
            + ENNReal.ofReal Y * ENNReal.ofReal (lam ^ (1 - 2 / p) * a ^ (2 / p)) :=
          add_le_add hA hB
      _ = ENNReal.ofReal (X * lam + Y * (lam ^ (1 - 2 / p) * a ^ (2 / p))) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_mul (p := Y) (q := lam ^ (1 - 2 / p) * a ^ (2 / p)) hY.le]
  rcases eq_or_lt_of_le ha with h0 | hapos
  · -- `a = 0`: let the truncation level tend to `0`
    rw [← h0] at hgen hg2
    have hzero : MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count = 0 := by
      rw [hg2, ENNReal.ofReal_zero]
    rw [hzero, mul_zero]
    refine ENNReal.le_of_forall_pos_le_add ?_
    intro ε hε _
    have hlam : 0 < (ε : ℝ) / X := div_pos (by exact_mod_cast hε) hX
    have hb := hgen ((ε : ℝ) / X) hlam
    have hz : (0 : ℝ) ^ (2 / p) = 0 := Real.zero_rpow (by positivity)
    have hsimp : X * ((ε : ℝ) / X)
        + Y * (((ε : ℝ) / X) ^ (1 - 2 / p) * (0 : ℝ) ^ (2 / p)) = (ε : ℝ) := by
      rw [hz]
      simp only [mul_zero, add_zero]
      field_simp
    rw [hsimp] at hb
    calc MeasureTheory.eLpNorm (T g) 2 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal ((ε : ℝ)) := hb
      _ = (ε : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
      _ = 0 + (ε : ℝ≥0∞) := (zero_add _).symm
  · -- `a > 0`: the truncation level `λ = (Y/X)^{p/2} a` is positive and optimal
    have hlam : 0 < (Y / X) ^ (p / 2) * a :=
      mul_pos (Real.rpow_pos_of_pos (div_pos hY hX) _) hapos
    have hb := hgen ((Y / X) ^ (p / 2) * a) hlam
    rw [lam_arith hp1 hp2 hX hY ha] at hb
    refine hb.trans_eq ?_
    rw [ENNReal.ofReal_mul (p := 2 * X ^ (1 - p / 2) * Y ^ (p / 2)) (q := a) (by positivity),
      ← hg2]

end Work.KMTAreas.A4
