import Mathlib
import Submission.Work.Interfaces.Fatou
import Submission.Work.FatouCH.Ends.Basic
import Submission.Work.FatouCH.Ends.geometry
import Submission.Work.FatouCH.Ends.derivBound
import Submission.Work.FatouCH.Ends.endsCore

/-!
# `Work.FatouCH.fatouEnds`: the two ends of the Écalle cylinder

`MandelDim.FatouEnds` (interface `Submission/Work/Interfaces/Fatou.lean`) says that if the
near-translation `F` on `Qreg b₁ b₂` is exponentially close to the translation `z ↦ z + ρ` at the
upper (resp. lower) end, then the Fatou coordinate `Φ` satisfies `Φ z = z/ρ + c + o(1)` there,
uniformly on vertical windows of width `4`.

The derivation is `Ends.endsCore`, applied with `σ = 1` (upper end, using the upper tail bound) and
with `σ = -1` (lower end, using the lower one).  `endsCore` runs the chain
`FatouDerivEstimate → endsDerivBound → {integrability of the derivative bound} → limit`, with the
two ends handled simultaneously by keeping the height `T = σ · Im z` as a parameter.

The only auxiliary input is `MandelDim.FatouDerivEstimate` (`hD`); the hypotheses `hE`
(`FatouExists`) and `hU` (`FatouUnique`) are part of the contract's signature but are not needed:
the statement `FatouEnds` concerns *every* Fatou coordinate, so existence/uniqueness play no role.
-/

namespace Work.FatouCH

open Set Metric Complex Filter
open scoped Topology

noncomputable section

/-- `|M| exp (-(7 κ T / 8)) ≤ 1/4` as soon as `T` is large: the threshold is
`8 (log (4|M|) + 1) / (7 κ)`. -/
theorem ends_small_of_large {M κ T : ℝ} (hκ : 0 < κ)
    (hTs : 8 * (Real.log (4 * |M|) + 1) / (7 * κ) ≤ T) :
    |M| * Real.exp (-(7 * κ * T / 8)) ≤ 1 / 4 := by
  rcases eq_or_lt_of_le (abs_nonneg M) with hM0 | hMpos
  · rw [← hM0]; simp
  · have h4 : (0 : ℝ) < 4 * |M| := by linarith
    have hstep : Real.log (4 * |M|) + 1 ≤ 7 * κ * T / 8 := by
      have h7 : (0 : ℝ) < 7 * κ / 8 := by positivity
      have hmul := mul_le_mul_of_nonneg_left hTs (le_of_lt h7)
      have hker : 7 * κ / 8 * (8 * (Real.log (4 * |M|) + 1) / (7 * κ)) =
          Real.log (4 * |M|) + 1 := by
        field_simp
      rw [hker] at hmul
      have heq : T * (7 * κ / 8) = 7 * κ * T / 8 := by ring
      linarith [hmul, heq.le, heq.ge]
    have hexp : Real.exp (-(7 * κ * T / 8)) ≤ 1 / (4 * |M| * Real.exp 1) := by
      have h1 : Real.exp (-(7 * κ * T / 8)) ≤ Real.exp (-(Real.log (4 * |M|) + 1)) :=
        Real.exp_le_exp.mpr (by linarith)
      have h2 : Real.exp (-(Real.log (4 * |M|) + 1)) = 1 / (4 * |M| * Real.exp 1) := by
        rw [show -(Real.log (4 * |M|) + 1) = -Real.log (4 * |M|) + -1 by ring,
          Real.exp_add, Real.exp_neg, Real.exp_log h4, Real.exp_neg]
        ring
      rwa [h2] at h1
    have h3 : |M| * (1 / (4 * |M| * Real.exp 1)) = 1 / (4 * Real.exp 1) := by
      field_simp
    have h4e : (1 : ℝ) ≤ Real.exp 1 := (Real.one_le_exp_iff).mpr (by norm_num)
    have hfin : (1 : ℝ) / (4 * Real.exp 1) ≤ 1 / 4 := by
      have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 4) (by linarith : (4:ℝ) ≤ 4 * Real.exp 1)
      simpa using h
    calc |M| * Real.exp (-(7 * κ * T / 8)) ≤ |M| * (1 / (4 * |M| * Real.exp 1)) :=
          mul_le_mul_of_nonneg_left hexp (abs_nonneg M)
      _ = 1 / (4 * Real.exp 1) := h3
      _ ≤ 1 / 4 := hfin

/-- `‖ρ‖ ≥ 1/2` from `‖ρ - 1‖ ≤ 1/32`. -/
theorem ends_norm_rho {ρ : ℂ} (hρ : ‖ρ - 1‖ ≤ 1 / 32) : 1 / 2 ≤ ‖ρ‖ := by
  have h1 : (1 : ℝ) ≤ ‖ρ‖ + ‖ρ - 1‖ := by
    have h := norm_add_le ρ ((1 : ℂ) - ρ)
    have he : ρ + (1 - ρ) = 1 := by ring
    rw [he, norm_one] at h
    rwa [norm_sub_rev] at h
  linarith

theorem fatouEnds (hE : MandelDim.FatouExists) (hU : MandelDim.FatouUnique)
    (hD : MandelDim.FatouDerivEstimate) : MandelDim.FatouEnds := by
  obtain ⟨R₁, C₁, hR₁, hC₁, hDiff⟩ := Ends.exists_diffEst hD
  intro b₁ b₂ F Φ ρ M κ Y hAdm hNT hΦ hκ hρ
  constructor
  · -- ## the upper end (`σ = 1`)
    intro htail
    have hρ' : 1 / 2 ≤ ‖ρ‖ := ends_norm_rho hρ
    obtain ⟨Tg, hTgpos, hmarg⟩ := Ends.marginsSafe (b₁ := b₁) (b₂ := b₂)
    set Ts : ℝ := max (max 1 Tg) (max (8 * Y / 7) (8 * (Real.log (4 * |M|) + 1) / (7 * κ)))
      with hTsdef
    have hTs1 : 1 ≤ Ts := le_trans (le_max_left _ _) (le_max_left _ _)
    have hTs_Tg : Tg ≤ Ts := le_trans (le_max_right _ _) (le_max_left _ _)
    have hTs_Y : 8 * Y / 7 ≤ Ts := le_trans (le_max_left _ _) (le_max_right _ _)
    have hTs_M : 8 * (Real.log (4 * |M|) + 1) / (7 * κ) ≤ Ts :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    have hsmall : ∀ T : ℝ, Ts ≤ T → |M| * Real.exp (-(7 * κ * T / 8)) ≤ 1 / 4 :=
      fun T hT => ends_small_of_large hκ (le_trans hTs_M hT)
    have htailball : ∀ (T : ℝ) (u : ℂ), Ts ≤ T → u.im = (1 : ℝ) * T → |u.re| ≤ T / 4 →
        ∀ ζ ∈ Metric.ball u (T / 8), ‖F ζ - (ζ + ρ)‖ ≤ |M| * Real.exp (-(7 * κ * T / 8)) := by
      intro T u hT him hre ζ hζ
      have hT1pos : 0 < T := lt_of_lt_of_le (by linarith) hT
      have himT : |u.im| = T := by
        rw [him, one_mul, abs_of_nonneg (by linarith)]
      have hm := hmarg T u (le_trans hTs_Tg hT) himT hre
      have hball := Ends.ballSubsetSafe hT1pos hm.1 hm.2
      have hζQ : ζ ∈ MandelDim.Qreg b₁ b₂ := by
        apply hball
        rw [Metric.mem_ball, dist_eq_norm] at hζ ⊢
        linarith
      have hζim : 7 * T / 8 < ζ.im := by
        have h1 : ‖ζ - u‖ < T / 8 := by
          rw [Metric.mem_ball, dist_eq_norm] at hζ; exact hζ
        have h2 : |ζ.im - u.im| ≤ ‖ζ - u‖ := by
          have h := Complex.abs_im_le_norm (ζ - u)
          rwa [Complex.sub_im] at h
        have h3 : |ζ.im - u.im| < T / 8 := lt_of_le_of_lt h2 h1
        have h4 : ζ.im - u.im > -(T / 8) := (abs_lt.mp h3).1
        rw [him, one_mul] at h4
        linarith
      have hY : Y < ζ.im := by
        have h := le_trans hTs_Y hT
        linarith
      have h3 := htail ζ hζQ hY
      have h4 : Real.exp (-(κ * ζ.im)) ≤ Real.exp (-(7 * κ * T / 8)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hκ, hζim]
      calc ‖F ζ - (ζ + ρ)‖ ≤ M * Real.exp (-(κ * ζ.im)) := h3
        _ ≤ |M| * Real.exp (-(κ * ζ.im)) := by
            have := le_abs_self M
            have h5 : (0 : ℝ) < Real.exp (-(κ * ζ.im)) := Real.exp_pos _
            nlinarith [h5]
        _ ≤ |M| * Real.exp (-(7 * κ * T / 8)) :=
            mul_le_mul_of_nonneg_left h4 (abs_nonneg M)
    obtain ⟨c, hc⟩ := Ends.endsCore (b₁ := b₁) (b₂ := b₂) (F := F) (Φ := Φ) (ρ := ρ) (M := M)
      (κ := κ) (σ := 1) (Ts := Ts) hDiff (le_of_lt hC₁) (Or.inl rfl) hκ hρ' hNT hΦ hTs1 hsmall
      htailball
    refine ⟨c, ?_⟩
    intro x ε hε
    obtain ⟨Y', hY'⟩ := hc x ε hε
    exact ⟨Y', fun z hzQ hz hzre => by
      simpa [Ends.devFn] using hY' z hzQ (by simpa using hz) hzre⟩
  · -- ## the lower end (`σ = -1`)
    intro htail
    have hρ' : 1 / 2 ≤ ‖ρ‖ := ends_norm_rho hρ
    obtain ⟨Tg, hTgpos, hmarg⟩ := Ends.marginsSafe (b₁ := b₁) (b₂ := b₂)
    set Ts : ℝ := max (max 1 Tg) (max (8 * Y / 7) (8 * (Real.log (4 * |M|) + 1) / (7 * κ)))
      with hTsdef
    have hTs1 : 1 ≤ Ts := le_trans (le_max_left _ _) (le_max_left _ _)
    have hTs_Tg : Tg ≤ Ts := le_trans (le_max_right _ _) (le_max_left _ _)
    have hTs_Y : 8 * Y / 7 ≤ Ts := le_trans (le_max_left _ _) (le_max_right _ _)
    have hTs_M : 8 * (Real.log (4 * |M|) + 1) / (7 * κ) ≤ Ts :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    have hsmall : ∀ T : ℝ, Ts ≤ T → |M| * Real.exp (-(7 * κ * T / 8)) ≤ 1 / 4 :=
      fun T hT => ends_small_of_large hκ (le_trans hTs_M hT)
    have htailball : ∀ (T : ℝ) (u : ℂ), Ts ≤ T → u.im = (-1 : ℝ) * T → |u.re| ≤ T / 4 →
        ∀ ζ ∈ Metric.ball u (T / 8), ‖F ζ - (ζ + ρ)‖ ≤ |M| * Real.exp (-(7 * κ * T / 8)) := by
      intro T u hT him hre ζ hζ
      have hT1pos : 0 < T := lt_of_lt_of_le (by linarith) hT
      have himT : |u.im| = T := by
        rw [him, neg_one_mul, abs_neg, abs_of_nonneg (by linarith)]
      have hm := hmarg T u (le_trans hTs_Tg hT) himT hre
      have hball := Ends.ballSubsetSafe hT1pos hm.1 hm.2
      have hζQ : ζ ∈ MandelDim.Qreg b₁ b₂ := by
        apply hball
        rw [Metric.mem_ball, dist_eq_norm] at hζ ⊢
        linarith
      have hζim : ζ.im < -(7 * T / 8) := by
        have h1 : ‖ζ - u‖ < T / 8 := by
          rw [Metric.mem_ball, dist_eq_norm] at hζ; exact hζ
        have h2 : |ζ.im - u.im| ≤ ‖ζ - u‖ := by
          have h := Complex.abs_im_le_norm (ζ - u)
          rwa [Complex.sub_im] at h
        have h3 : |ζ.im - u.im| < T / 8 := lt_of_le_of_lt h2 h1
        have h4 : ζ.im - u.im < T / 8 := (abs_lt.mp h3).2
        rw [him, neg_one_mul] at h4
        linarith
      have hY : ζ.im < -Y := by
        have h := le_trans hTs_Y hT
        linarith
      have h3 := htail ζ hζQ hY
      have h4 : Real.exp (κ * ζ.im) ≤ Real.exp (-(7 * κ * T / 8)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hκ, hζim]
      calc ‖F ζ - (ζ + ρ)‖ ≤ M * Real.exp (κ * ζ.im) := h3
        _ ≤ |M| * Real.exp (κ * ζ.im) := by
            have := le_abs_self M
            have h5 : (0 : ℝ) < Real.exp (κ * ζ.im) := Real.exp_pos _
            nlinarith [h5]
        _ ≤ |M| * Real.exp (-(7 * κ * T / 8)) :=
            mul_le_mul_of_nonneg_left h4 (abs_nonneg M)
    obtain ⟨c, hc⟩ := Ends.endsCore (b₁ := b₁) (b₂ := b₂) (F := F) (Φ := Φ) (ρ := ρ) (M := M)
      (κ := κ) (σ := -1) (Ts := Ts) hDiff (le_of_lt hC₁) (Or.inr rfl) hκ hρ' hNT hΦ hTs1 hsmall
      htailball
    refine ⟨c, ?_⟩
    intro x ε hε
    obtain ⟨Y', hY'⟩ := hc x ε hε
    exact ⟨Y', fun z hzQ hz hzre => by
      simpa [Ends.devFn] using hY' z hzQ (by linarith) hzre⟩

end

end Work.FatouCH
