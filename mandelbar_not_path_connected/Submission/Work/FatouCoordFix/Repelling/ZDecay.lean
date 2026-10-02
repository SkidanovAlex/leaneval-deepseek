/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FatouCoordFix team
-/
import Mathlib
import Submission.Work.FatouCoordFix.Repelling.ZCorrection
import Submission.Work.FatouCoordFix.Repelling.Z_Omega_decay

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The conjugacy `V w = w + c·Λ w + Z w` of the repelling side, with the decay of `Z`

This is the export of the repelling-side construction requested in
`NOTES_LEAD_mandelbar_residuals.md` §A.7 (item "(+ the A.7 Z-decay export)" of the
`FatouCoordFix` contract).

The repelling coordinate of the parabolic germ `f z = z + z^2 h z` is obtained from the corrected
ansatz

  `V w = w + (1 - a) * Λ w + Z w`,   `Λ w = log (-w) + π i`,

where the correction `Z` is the bounded holomorphic fixed point of the contraction
`Petal.Omega f a` of the `FatouCoord` area: `Z = Ω Z`, i.e.

  `Z w = ∑' n, defect f a (w - n - 1) (Z (w - n - 1))`.

The single new mathematical content here (everything else is the delivered construction, copied
into this area so that the *fixed-point form* of `Z` — which is what the decay needs — and the
decay itself are exported together) is:

* `Z w = Petal.Omega f a Z w` on the half-plane (the fixed-point form, §A.7), and
* the **decay** `Z w → 0` at the far left end: quantitatively
  `‖Z w‖ ≤ K / √(1 + Re (-w))`, and consequently

    `∀ ε > 0, ∃ R', ∀ w, Re w < -R' → ‖Z w‖ < ε`.

The decay is what `Implosion`'s exit comparison (B.4) uses: it says that
`V w - w - (1 - a) Λ w` — the error of the corrected ansatz — tends to `0` as `Re w → -∞`.

## Main results

* `Work.FatouCoordFix.Repelling.exists_conjugacy_Z` — `R`, `Z`, `V` with the conjugacy
  `V (w+1) = wMap f (V w)`, the fixed-point form of `Z` and the quantitative decay;
* `Work.FatouCoordFix.Repelling.Z_tendsto_zero` — the ε-form of the decay;
* `Work.FatouCoordFix.Repelling.V_sub_tendsto` — `V w - w - (1 - a) Λ w → 0`.
-/

open scoped Topology
open Set Filter Metric

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Work.FatouCoordFix.Repelling

open Work.FatouCoord
open Work.FatouCoord.Repelling

noncomputable section

variable {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}

/-! ## The main export -/

/-- **The repelling conjugacy with the decay of the correction.**  For the parabolic germ
`f z = z + z^2 h z` there are `R > 1/r`, a correction `Z` and the repelling coordinate
`V = w + (1 - a) Λ w + Z` on the left half-plane `{Re w < -R}`, such that

* `V` solves `V (w + 1) = wMap f (V w)` and is injective, `V w ≈ w` and `V w ≠ 0`;
* `Z` is holomorphic, `‖Z w‖ ≤ 1/2`, solves the difference equation
  `Z (w+1) - Z w = defect f a w (Z w)` and is the fixed point `Z = Ω Z` of the contraction;
* `Z` **decays at the far left end**: `‖Z w‖ ≤ K / √(1 + Re (-w))`, so that for every `ε > 0`
  there is `R'` with `‖Z w‖ < ε` for all `w` of real part `< -R'`. -/
theorem exists_conjugacy_Z (hb : ParabolicBounds f h a r A A') :
    ∃ R : ℝ, 0 < R ∧ 1 / r < R ∧ ∃ Z V : ℂ → ℂ,
      DifferentiableOn ℂ Z (Petal.LeftHalfPlane R) ∧
      (∀ w : ℂ, w ∈ Petal.LeftHalfPlane R → ‖Z w‖ ≤ 1 / 2) ∧
      (∀ w : ℂ, w ∈ Petal.LeftHalfPlane R → Z (w + 1) - Z w = Petal.defect f a w (Z w)) ∧
      (∀ w : ℂ, w ∈ Petal.LeftHalfPlane R → Z w = Petal.Omega f a Z w) ∧
      DifferentiableOn ℂ V (Petal.LeftHalfPlane R) ∧
      (∀ w : ℂ, w ∈ Petal.LeftHalfPlane R → V w = w + (1 - a) * Petal.Lambda w + Z w) ∧
      (∀ w : ℂ, w ∈ Petal.LeftHalfPlane R → V (w + 1) = wMap f (V w)) ∧
      (∀ w : ℂ, w ∈ Petal.LeftHalfPlane R → ‖V w - w‖ ≤ (1 / 2) * ‖w‖) ∧
      (∀ w : ℂ, w ∈ Petal.LeftHalfPlane R → V w ≠ 0) ∧
      Set.InjOn V (Petal.LeftHalfPlane R) ∧
      (∀ w : ℂ, w ∈ Petal.LeftHalfPlane R →
        ‖V w - w‖ ≤ ‖1 - a‖ * (2 * Real.sqrt ‖w‖ + 2 * Real.pi) + 1 / 2) ∧
      (∃ K : ℝ, 0 < K ∧ ∀ w : ℂ, w ∈ Petal.LeftHalfPlane R →
        ‖Z w‖ ≤ K / Real.sqrt (1 + (-w.re))) ∧
      (∀ ε : ℝ, 0 < ε → ∃ R' : ℝ, R ≤ R' ∧ ∀ w : ℂ, w.re < -R' → ‖Z w‖ < ε) := by
  obtain ⟨R₀, hR₀pos, hrR₀, Z, hZdiff, hZbd, hZeq, hZfix₀⟩ := exists_correction_self_fix hb
  obtain ⟨ρ, hρpos, hρinj⟩ := wMap_injOn_large (f := f) (h := h) (a := a) (r := r) hb
  obtain ⟨T₁, hT₁, hthresh⟩ := exists_threshold_sqrt ‖1 - a‖
  set R : ℝ := max (max R₀ (max T₁ 1)) (max (2 * ρ) 2) with hRdef
  have hR₀le : R₀ ≤ R := by
    rw [hRdef]
    exact le_trans (le_max_left R₀ (max T₁ 1)) (le_max_left (max R₀ (max T₁ 1)) (max (2 * ρ) 2))
  have hT₁le : T₁ ≤ R := by
    rw [hRdef]
    exact le_trans (le_trans (le_max_left T₁ 1) (le_max_right R₀ (max T₁ 1)))
      (le_max_left (max R₀ (max T₁ 1)) (max (2 * ρ) 2))
  have h1le : (1 : ℝ) ≤ R := by
    rw [hRdef]
    exact le_trans (le_trans (le_max_right T₁ 1) (le_max_right R₀ (max T₁ 1)))
      (le_max_left (max R₀ (max T₁ 1)) (max (2 * ρ) 2))
  have h2ρle : 2 * ρ ≤ R := by
    rw [hRdef]
    exact le_trans (le_max_left (2 * ρ) 2) (le_max_right (max R₀ (max T₁ 1)) (max (2 * ρ) 2))
  have hRpos : 0 < R := lt_of_lt_of_le one_pos h1le
  have hrR : 1 / r < R := lt_of_lt_of_le hrR₀ hR₀le
  have hsub₀ : Petal.LeftHalfPlane R ⊆ Petal.LeftHalfPlane R₀ := by
    intro w hw
    rw [Petal.mem_LeftHalfPlane] at hw ⊢
    linarith
  have hZdiffR : DifferentiableOn ℂ Z (Petal.LeftHalfPlane R) := hZdiff.mono hsub₀
  have hZbdR : ∀ w : ℂ, w ∈ Petal.LeftHalfPlane R → ‖Z w‖ ≤ 1 / 2 :=
    fun w hw => hZbd w (hsub₀ hw)
  have hZeqR : ∀ w : ℂ, w ∈ Petal.LeftHalfPlane R → Z (w + 1) - Z w = Petal.defect f a w (Z w) :=
    fun w hw => hZeq w (hsub₀ hw)
  set V : ℂ → ℂ := fun u => u + (1 - a) * Petal.Lambda u + Z u with hVdef
  have hnorm_w : ∀ w : ℂ, w ∈ Petal.LeftHalfPlane R → R ≤ ‖w‖ := by
    intro w hw
    rw [Petal.mem_LeftHalfPlane] at hw
    have h := Complex.re_le_norm (-w)
    rw [Complex.neg_re, norm_neg] at h
    linarith
  -- (1) differentiability
  have hVdiff : DifferentiableOn ℂ V (Petal.LeftHalfPlane R) := by
    rw [hVdef]
    exact (differentiableOn_id.add ((differentiableOn_Lambda hRpos.le).const_mul (1 - a))).add hZdiffR
  -- (2) the conjugacy
  have hVconj : ∀ w : ℂ, w ∈ Petal.LeftHalfPlane R → V (w + 1) = wMap f (V w) := by
    intro w hw
    rw [hVdef]
    exact self_conjugacy (f := f) (a := a) hZeqR w hw
  -- (3) the pointwise estimate
  have hVnorm : ∀ w : ℂ, w ∈ Petal.LeftHalfPlane R → ‖V w - w‖ ≤ (1 / 2) * ‖w‖ := by
    intro w hw
    have hwR : R ≤ ‖w‖ := hnorm_w w hw
    have hw1 : (1 : ℝ) ≤ ‖w‖ := le_trans h1le hwR
    have hZ := hZbdR w hw
    have hΛ := norm_Lambda_le w hw1
    have hthr := hthresh ‖w‖ (le_trans hT₁le hwR)
    have hVw : V w - w = (1 - a) * Petal.Lambda w + Z w := by rw [hVdef]; ring
    rw [hVw]
    calc ‖(1 - a) * Petal.Lambda w + Z w‖
        ≤ ‖(1 - a) * Petal.Lambda w‖ + ‖Z w‖ := norm_add_le _ _
      _ = ‖1 - a‖ * ‖Petal.Lambda w‖ + ‖Z w‖ := by rw [norm_mul]
      _ ≤ ‖1 - a‖ * (2 * Real.sqrt ‖w‖ + 2 * Real.pi) + 1 / 2 := by
            have h1 : 0 ≤ ‖1 - a‖ := norm_nonneg _
            nlinarith [hΛ, hZ, h1]
      _ ≤ (1 / 2) * ‖w‖ := by linarith
  -- (4) non-vanishing
  have hVne : ∀ w : ℂ, w ∈ Petal.LeftHalfPlane R → V w ≠ 0 := by
    intro w hw h0
    have hb := hVnorm w hw
    have hwR : R ≤ ‖w‖ := hnorm_w w hw
    have hwpos : 0 < ‖w‖ := lt_of_lt_of_le hRpos hwR
    have h1 : ‖w‖ ≤ ‖V w - w‖ + ‖V w‖ := by
      calc ‖w‖ = ‖(w - V w) + V w‖ := by ring_nf
        _ ≤ ‖w - V w‖ + ‖V w‖ := norm_add_le _ _
        _ = ‖V w - w‖ + ‖V w‖ := by rw [norm_sub_rev]
    have h2 : ‖V w‖ = 0 := by rw [h0, norm_zero]
    rw [h2, add_zero] at h1
    linarith only [h1, hb, hwpos]
  -- (5) injectivity on the half-plane
  have hVinj : Set.InjOn V (Petal.LeftHalfPlane R) := by
    have hnormV : ∀ u : ℂ, u ∈ Petal.LeftHalfPlane R → (1 / 2) * ‖u‖ ≤ ‖V u‖ := by
      intro u hu
      have h1 : ‖u‖ ≤ ‖V u - u‖ + ‖V u‖ := by
        calc ‖u‖ = ‖(u - V u) + V u‖ := by ring_nf
          _ ≤ ‖u - V u‖ + ‖V u‖ := norm_add_le _ _
          _ = ‖V u - u‖ + ‖V u‖ := by rw [norm_sub_rev]
      have h2 := hVnorm u hu
      linarith [norm_nonneg (V u)]
    have hmem : ∀ w : ℂ, w ∈ Petal.LeftHalfPlane R → ∀ n : ℕ,
        w - (n : ℂ) ∈ Petal.LeftHalfPlane R := by
      intro w hw n
      rw [Petal.mem_LeftHalfPlane] at hw ⊢
      simp only [Complex.sub_re, Complex.natCast_re]
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    -- the pointwise values of `V` far to the left are `V u ≈ u`
    have hsn : ∀ w : ℂ, w ∈ Petal.LeftHalfPlane R → ∀ n : ℕ, R ≤ ‖w - (n : ℂ)‖ := by
      intro w hw n
      have h := hnorm_w (w - (n : ℂ)) (hmem w hw n)
      exact h
    intro w₁ hw₁ w₂ hw₂ hVeq
    -- propagation of the equality to the left
    have hprop : ∀ n : ℕ, V (w₁ - (n : ℂ)) = V (w₂ - (n : ℂ)) := by
      intro n
      induction n with
      | zero => simpa using hVeq
      | succ n ih =>
        have h1 : w₁ - ((n + 1 : ℕ) : ℂ) ∈ Petal.LeftHalfPlane R := hmem w₁ hw₁ (n + 1)
        have h2 : w₂ - ((n + 1 : ℕ) : ℂ) ∈ Petal.LeftHalfPlane R := hmem w₂ hw₂ (n + 1)
        have hc1 := hVconj _ h1
        have hc2 := hVconj _ h2
        have e1 : w₁ - ((n + 1 : ℕ) : ℂ) + 1 = w₁ - (n : ℂ) := by push_cast; ring
        have e2 : w₂ - ((n + 1 : ℕ) : ℂ) + 1 = w₂ - (n : ℂ) := by push_cast; ring
        rw [e1] at hc1
        rw [e2] at hc2
        have hkey : wMap f (V (w₁ - ((n + 1 : ℕ) : ℂ)))
            = wMap f (V (w₂ - ((n + 1 : ℕ) : ℂ))) := by rw [← hc1, ← hc2, ih]
        have hb1 : ρ ≤ ‖V (w₁ - ((n + 1 : ℕ) : ℂ))‖ := by
          have h3 := hnormV _ h1
          have h4 : R / 2 ≤ (1 / 2) * ‖w₁ - ((n + 1 : ℕ) : ℂ)‖ := by
            have h5 := hsn w₁ hw₁ (n + 1)
            linarith
          linarith
        have hb2 : ρ ≤ ‖V (w₂ - ((n + 1 : ℕ) : ℂ))‖ := by
          have h3 := hnormV _ h2
          have h4 : R / 2 ≤ (1 / 2) * ‖w₂ - ((n + 1 : ℕ) : ℂ)‖ := by
            have h5 := hsn w₂ hw₂ (n + 1)
            linarith
          linarith
        exact hρinj hb1 hb2 hkey
    -- far to the left the two points have to be compared
    set m : ℝ := max w₁.re w₂.re with hmdef
    obtain ⟨n : ℕ, hn⟩ := exists_nat_gt (m + max (4 * ‖1 - a‖ + 2) (R + 5))
    set T : ℝ := (n : ℝ) - m - 1 with hTdef
    have hT4 : 4 * ‖1 - a‖ + 1 ≤ T := by
      rw [hTdef]
      have := le_max_left (4 * ‖1 - a‖ + 2) (R + 5)
      linarith
    have hTR4 : R + 4 ≤ T := by
      rw [hTdef]
      have := le_max_right (4 * ‖1 - a‖ + 2) (R + 5)
      linarith
    have hTpos : 0 < T := by
      have h1 : (0 : ℝ) ≤ ‖1 - a‖ := norm_nonneg _
      linarith
    have hTR : R < T := by linarith
    have hxT : w₁ - (n : ℂ) ∈ Petal.LeftHalfPlane T := by
      rw [Petal.mem_LeftHalfPlane, Complex.sub_re, Complex.natCast_re, hTdef]
      have hm : w₁.re ≤ m := by rw [hmdef]; exact le_max_left _ _
      linarith
    have hyT : w₂ - (n : ℂ) ∈ Petal.LeftHalfPlane T := by
      rw [Petal.mem_LeftHalfPlane, Complex.sub_re, Complex.natCast_re, hTdef]
      have hm : w₂.re ≤ m := by rw [hmdef]; exact le_max_right _ _
      linarith
    have heq := hprop n
    have hxy : w₁ - (n : ℂ) - (w₂ - (n : ℂ)) = w₁ - w₂ := by ring
    have hid : w₁ - w₂ + (1 - a) * (Petal.Lambda (w₁ - (n : ℂ)) - Petal.Lambda (w₂ - (n : ℂ)))
        + (Z (w₁ - (n : ℂ)) - Z (w₂ - (n : ℂ))) = 0 := by
      have hsub : V (w₁ - (n : ℂ)) - V (w₂ - (n : ℂ)) = 0 := by rw [heq]; ring
      have hstep : (w₁ - (n : ℂ)) - (w₂ - (n : ℂ))
            + (1 - a) * (Petal.Lambda (w₁ - (n : ℂ)) - Petal.Lambda (w₂ - (n : ℂ)))
            + (Z (w₁ - (n : ℂ)) - Z (w₂ - (n : ℂ)))
          = V (w₁ - (n : ℂ)) - V (w₂ - (n : ℂ)) := by rw [hVdef]; ring
      rw [← hxy, hstep]
      exact hsub
    have hL := norm_Lambda_sub_le_aux (x := w₁ - (n : ℂ)) (y := w₂ - (n : ℂ)) hTpos hxT hyT
    rw [hxy] at hL
    have hZb := norm_Z_sub_le hRpos hZdiffR hZbdR hTR hxT hyT
    rw [hxy] at hZb
    have htri : ‖w₁ - w₂‖ ≤ ‖1 - a‖ * ‖Petal.Lambda (w₁ - (n : ℂ)) - Petal.Lambda (w₂ - (n : ℂ))‖
        + ‖Z (w₁ - (n : ℂ)) - Z (w₂ - (n : ℂ))‖ := by
      have h1 : w₁ - w₂ = -((1 - a) * (Petal.Lambda (w₁ - (n : ℂ)) - Petal.Lambda (w₂ - (n : ℂ)))
          + (Z (w₁ - (n : ℂ)) - Z (w₂ - (n : ℂ)))) := by
        rw [eq_neg_iff_add_eq_zero]
        simpa only [add_assoc] using hid
      rw [h1]
      calc ‖-((1 - a) * (Petal.Lambda (w₁ - (n : ℂ)) - Petal.Lambda (w₂ - (n : ℂ)))
            + (Z (w₁ - (n : ℂ)) - Z (w₂ - (n : ℂ))))‖
          = ‖(1 - a) * (Petal.Lambda (w₁ - (n : ℂ)) - Petal.Lambda (w₂ - (n : ℂ)))
            + (Z (w₁ - (n : ℂ)) - Z (w₂ - (n : ℂ)))‖ := norm_neg _
        _ ≤ ‖(1 - a) * (Petal.Lambda (w₁ - (n : ℂ)) - Petal.Lambda (w₂ - (n : ℂ)))‖
            + ‖Z (w₁ - (n : ℂ)) - Z (w₂ - (n : ℂ))‖ := norm_add_le _ _
        _ = ‖1 - a‖ * ‖Petal.Lambda (w₁ - (n : ℂ)) - Petal.Lambda (w₂ - (n : ℂ))‖
            + ‖Z (w₁ - (n : ℂ)) - Z (w₂ - (n : ℂ))‖ := by rw [norm_mul]
    have hsum : ‖1 - a‖ / T + 1 / (T - R) ≤ 1 / 2 := by
      have hTRpos : 0 < T - R := by linarith
      have hterm1 : ‖1 - a‖ / T ≤ 1 / 4 := by
        rw [div_le_iff₀ hTpos]
        nlinarith [norm_nonneg (1 - a)]
      have hterm2 : 1 / (T - R) ≤ 1 / 4 := by
        rw [div_le_iff₀ hTRpos]
        linarith
      linarith
    have hfinal : ‖w₁ - w₂‖ ≤ (1 / 2) * ‖w₁ - w₂‖ := by
      calc ‖w₁ - w₂‖
          ≤ ‖1 - a‖ * (‖w₁ - w₂‖ / T) + (1 / (T - R)) * ‖w₁ - w₂‖ := by
            have := add_le_add (mul_le_mul_of_nonneg_left hL (norm_nonneg (1 - a))) hZb
            linarith
        _ = (‖1 - a‖ / T + 1 / (T - R)) * ‖w₁ - w₂‖ := by ring
        _ ≤ (1 / 2) * ‖w₁ - w₂‖ := mul_le_mul_of_nonneg_right hsum (norm_nonneg _)
    have hzero : ‖w₁ - w₂‖ = 0 := by nlinarith [norm_nonneg (w₁ - w₂)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hzero)
  have hVrefine : ∀ w : ℂ, w ∈ Petal.LeftHalfPlane R →
      ‖V w - w‖ ≤ ‖1 - a‖ * (2 * Real.sqrt ‖w‖ + 2 * Real.pi) + 1 / 2 := by
    intro w hw
    have hwR : R ≤ ‖w‖ := hnorm_w w hw
    have hw1 : (1 : ℝ) ≤ ‖w‖ := le_trans h1le hwR
    have hZ := hZbdR w hw
    have hΛ := norm_Lambda_le w hw1
    have hVw : V w - w = (1 - a) * Petal.Lambda w + Z w := by rw [hVdef]; ring
    rw [hVw]
    calc ‖(1 - a) * Petal.Lambda w + Z w‖
        ≤ ‖(1 - a) * Petal.Lambda w‖ + ‖Z w‖ := norm_add_le _ _
      _ = ‖1 - a‖ * ‖Petal.Lambda w‖ + ‖Z w‖ := by rw [norm_mul]
      _ ≤ ‖1 - a‖ * (2 * Real.sqrt ‖w‖ + 2 * Real.pi) + 1 / 2 := by
            have h1 : 0 ≤ ‖1 - a‖ := norm_nonneg _
            nlinarith [hΛ, hZ, h1]
  have hVdef' : ∀ w : ℂ, w ∈ Petal.LeftHalfPlane R →
      V w = w + (1 - a) * Petal.Lambda w + Z w := by
    intro w hw
    rw [hVdef]
  -- ### the decay of the correction `Z`
  have hfixR : ∀ w : ℂ, w ∈ Petal.LeftHalfPlane R → Z w = Petal.Omega f a Z w :=
    fun w hw => hZfix₀ w (hsub₀ hw)
  have hdec := Work.FatouCoordFix.Repelling.Z_Omega_decay hb (le_of_lt hRpos) Z hZbdR hfixR
  exact ⟨R, hRpos, hrR, Z, V, hZdiffR, hZbdR, hZeqR, hfixR, hVdiff, hVdef', hVconj, hVnorm,
    hVne, hVinj, hVrefine, hdec.1, hdec.2⟩


/-- **The ε-form of the decay of the correction**: at the far repelling end the correction `Z`
is as small as we like.  (Immediate from `exists_conjugacy_Z`.) -/
theorem Z_tendsto_zero (hb : ParabolicBounds f h a r A A') :
    ∃ R : ℝ, 0 < R ∧ ∃ Z : ℂ → ℂ, DifferentiableOn ℂ Z (Petal.LeftHalfPlane R) ∧
      (∀ ε : ℝ, 0 < ε → ∃ R' : ℝ, R ≤ R' ∧ ∀ w : ℂ, w.re < -R' → ‖Z w‖ < ε) := by
  obtain ⟨R, hR, -, Z, V, hZdiff, hZbd, hZeq, hZfix, hVdiff, hVdef, hVconj, hVnorm, hVne,
    hVinj, hVref, hdec, htail⟩ := exists_conjugacy_Z hb
  exact ⟨R, hR, Z, hZdiff, htail⟩

/-- **The error of the corrected ansatz tends to `0` at the far repelling end**: the repelling
coordinate `V` differs from `w + (1 - a) Λ w` by `Z w`, which tends to `0` as `Re w → -∞`.
This is the form in which `Implosion`'s exit comparison (B.4) uses the decay. -/
theorem V_sub_tendsto (hb : ParabolicBounds f h a r A A') :
    ∃ R : ℝ, 0 < R ∧ ∃ Z V : ℂ → ℂ,
      (∀ w : ℂ, w ∈ Petal.LeftHalfPlane R → V w = w + (1 - a) * Petal.Lambda w + Z w) ∧
      (∀ ε : ℝ, 0 < ε → ∃ R' : ℝ, R ≤ R' ∧ ∀ w : ℂ, w.re < -R' →
        ‖V w - w - (1 - a) * Petal.Lambda w‖ < ε) := by
  obtain ⟨R, hR, -, Z, V, hZdiff, hZbd, hZeq, hZfix, hVdiff, hVdef, hVconj, hVnorm, hVne,
    hVinj, hVref, hdec, htail⟩ := exists_conjugacy_Z hb
  refine ⟨R, hR, Z, V, hVdef, fun ε hε => ?_⟩
  obtain ⟨R', hR'R, hR'⟩ := htail ε hε
  refine ⟨R', hR'R, fun w hw => ?_⟩
  have hwR : w ∈ Petal.LeftHalfPlane R := by
    rw [Petal.mem_LeftHalfPlane]
    linarith
  rw [hVdef w hwR]
  have h1 : w + (1 - a) * Petal.Lambda w + Z w - w - (1 - a) * Petal.Lambda w = Z w := by ring
  rw [h1]
  exact hR' w hw

end

end Work.FatouCoordFix.Repelling
