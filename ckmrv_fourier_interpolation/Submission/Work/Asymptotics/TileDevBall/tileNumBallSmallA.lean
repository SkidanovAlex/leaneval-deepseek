/-
# The small-`scale` tile ball bound on the cusp-`0` tile

Bound for the tile numerator

  `N(ζ) = 2 · Sh(τ,ζ) · (Kfun(τ,ζ) − Gfun(τ,ζ))`,   `τ = n +ᵥ w`,  `n = ±1`,

on the small-`scale` part `scale w ≤ 8` of the cusp-`0` tile `E = KEpsilon`, for `ζ` in the ball
`‖ζ − S • w‖ ≤ 29/20`.  This is the piece of the tile analysis in which the hypothesis
`3 ≤ Im ζ` available in the large-`scale` regime is *not* available (`scale w ≤ 8` only gives
`Im w ≥ 1/8` and hence `Im ζ ≥ 11/20`), so neither the `BBdd` calculus of
`TileDevBall/BallShape.lean` nor the half-deviation bounds `bracket8Ball`, `bracket24Ball`,
`kplusDev8Ball`, `kplusDev24Ball` (all of which assume `3 ≤ Im ζ`) can be used.  Instead the two
halves of `N` are bounded separately, each by an *elementary* estimate:

* `scale w ≤ 8` bounds `w` away from the cusp `0` (`1/8 ≤ Im w`, `‖w‖ ≤ 1/2`), and the ball
  keeps `ζ` in the fixed region `11/20 ≤ Im ζ`, `‖ζ‖ ≤ 10`;
* `Sh · Kfun`:  off the coincidence locus `j τ = j ζ` one has the pointwise identity
  `Sh τ ζ · Kfun τ ζ = −KfunClear τ ζ / (Δ τ · Δ ζ^{e-1})` (`e = 1` for `d = 8`, `e = 2` for
  `d = 24`), while at a coincidence `Sh τ ζ = 0`;  so Lean's convention `0⁻¹ = 0` makes the
  identity valid *everywhere* and the two-variable moderate growth `KClear_mg2` of `KfunClear`,
  together with the lower bound `E_bdd_invDelta` for `‖Δ‖` on `E` and the half-plane bound for
  `‖Δ‖` on `Im ≥ 1/2`, bounds this half;
* `Sh · Gfun = −Δ(ζ)·(j τ − j ζ)·Gfun(τ,ζ)`:  the disc bound `jInvariantFunUpperDisc` for `j`,
  the half-plane bounds `DeltaFunBoundsHalf` for `Δ`, and the `τ`-atom bound `Gcusp_tile_bound`
  bound this half.

No cancellation is used: the pointwise identity above is the whole content, and there is no
`j τ = j ζ` distinction left in the final bound.  The conclusion is the existence of a constant
`M` (the explicit value produced by the three input bounds, made uniform over `w ∈ E` with
`scale w ≤ 8` and over `ζ` in the ball).
-/
import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Asymptotics.KClear_mg2
import Submission.Work.Asymptotics.Kaxis_local_coincidence
import Submission.Work.Asymptotics.EtailE.Atoms
import Submission.Work.Asymptotics.SpikeCircle.DeltaFunBoundsHalf
import Submission.Work.Asymptotics.SpikeCircle.jInvariantFunUpperDisc
import Submission.Work.Asymptotics.KMinusFunnelZBounds
import Submission.Work.Asymptotics.Gcusp_tile_bound
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Asymptotics.EtailE.Assembly
import Submission.Work.Asymptotics.Tile.Ncusp_tile_crude

noncomputable section

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane

namespace Work.Asymptotics.TileDevBall

set_option maxHeartbeats 1000000

open Work.Kernels Work.Asymptotics.Compact

/-! ## Region geometry -/

/-- On the small-`scale` part of `E` the imaginary part of `w` is bounded below. -/
lemma im_ge_of_scale_le_eight {w : ℍ} (hsw : scale w ≤ 8) : (1 / 8 : ℝ) ≤ w.im := by
  have h := Work.Kernels.inv_im_le_scale w
  have h1 : (w.im)⁻¹ ≤ 8 := le_trans h hsw
  rw [inv_le_comm₀ w.im_pos (by norm_num : (0 : ℝ) < 8)] at h1
  linarith

/-- `Im (n +ᵥ w) = Im w`. -/
lemma im_vadd (n : ℤ) (w : ℍ) : (((n : ℝ) +ᵥ w : ℍ)).im = w.im :=
  UpperHalfPlane.vadd_im (n : ℝ) w

/-- `‖(n +ᵥ w : ℍ) : ℂ‖ ≤ ‖w‖ + 1` for `n = ±1`. -/
lemma norm_vadd_le (n : ℤ) (hn : n = 1 ∨ n = -1) (w : ℍ) :
    ‖(((n : ℝ) +ᵥ w : ℍ) : ℂ)‖ ≤ ‖(w : ℂ)‖ + 1 := by
  have h : ((((n : ℝ) +ᵥ w : ℍ)) : ℂ) = ((n : ℝ) : ℂ) + (w : ℂ) :=
    UpperHalfPlane.coe_vadd (n : ℝ) w
  rw [h]
  calc ‖((n : ℝ) : ℂ) + (w : ℂ)‖ ≤ ‖((n : ℝ) : ℂ)‖ + ‖(w : ℂ)‖ := norm_add_le _ _
    _ = ‖(w : ℂ)‖ + ‖((n : ℝ) : ℂ)‖ := by ring
    _ ≤ ‖(w : ℂ)‖ + 1 := by
        rcases hn with h | h <;> rw [h] <;> norm_num

/-- The ball gives a lower bound for `Im ζ`. -/
lemma im_ge_of_ball {w ζ : ℍ} (hw : w ∈ Work.Asymptotics.KEpsilon)
    (hball : ‖(ζ : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ)‖ ≤ 29 / 20) :
    (11 / 20 : ℝ) ≤ ζ.im := by
  have h1 : |ζ.im - (ModularGroup.S • w).im| ≤ 29 / 20 := by
    have h := Complex.abs_im_le_norm ((ζ : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ))
    rw [Complex.sub_im, UpperHalfPlane.coe_im, UpperHalfPlane.coe_im] at h
    exact le_trans h hball
  have h2 : 2 ≤ (ModularGroup.S • w).im := hw.2
  linarith [(abs_le.mp h1).1]

/-! ## The identity `Sh · Kfun = -KfunClear / (Δ τ Δ ζ^{e-1})` -/

/-- Dimension `8`: `Sh τ ζ · Kfun τ ζ = - KfunClear τ ζ / Δ τ` off the coincidence locus. -/
lemma Sh_mul_Kfun_eq_eight (ℓ : Work.Kernels.LogLambdaData) (τ ζ : ℍ)
    (h : jInvariantFun τ ≠ jInvariantFun ζ) :
    Sh τ ζ * Kfun ℓ 8 τ ζ = - KfunClear ℓ 8 τ ζ / DeltaFun τ := by
  have h1 := Work.Asymptotics.KL.Kfun_eq_KfunClear_div ℓ 8 (Or.inl rfl) τ ζ h
  have hgp : growthPrefactor 8 τ ζ
      = DeltaFun τ * DeltaFun ζ * (jInvariantFun τ - jInvariantFun ζ) := by
    simp only [Work.Kernels.growthPrefactor, if_true, pow_one]
  have hDτ : DeltaFun τ ≠ 0 := by
    simpa [Work.Kernels.DeltaFun] using ModularForm.discriminant_ne_zero τ
  have hDζ : DeltaFun ζ ≠ 0 := by
    simpa [Work.Kernels.DeltaFun] using ModularForm.discriminant_ne_zero ζ
  have hJ : jInvariantFun τ - jInvariantFun ζ ≠ 0 := sub_ne_zero.mpr h
  have hden : DeltaFun ζ * E4Fun τ ^ 3 - DeltaFun τ * E4Fun ζ ^ 3 ≠ 0 := by
    have hE : DeltaFun ζ * E4Fun τ ^ 3 - DeltaFun τ * E4Fun ζ ^ 3
        = (DeltaFun ζ * DeltaFun τ) * (jInvariantFun τ - jInvariantFun ζ) := by
      rw [← ClassicalFacts.DeltaFun_mul_jInvariantFun τ,
        ← ClassicalFacts.DeltaFun_mul_jInvariantFun ζ]
      ring
    rw [hE]; exact mul_ne_zero (mul_ne_zero hDζ hDτ) hJ
  have hShgp : Sh τ ζ / growthPrefactor 8 τ ζ = -1 / DeltaFun τ := by
    rw [hgp, Sh_eq]
    field_simp
  calc Sh τ ζ * Kfun ℓ 8 τ ζ
      = Sh τ ζ * (KfunClear ℓ 8 τ ζ / growthPrefactor 8 τ ζ) := by rw [h1]
    _ = KfunClear ℓ 8 τ ζ * (Sh τ ζ / growthPrefactor 8 τ ζ) := by ring
    _ = KfunClear ℓ 8 τ ζ * (-1 / DeltaFun τ) := by rw [hShgp]
    _ = - KfunClear ℓ 8 τ ζ / DeltaFun τ := by ring

/-- Dimension `24`: `Sh τ ζ · Kfun τ ζ = - KfunClear τ ζ / (Δ τ · Δ ζ)` off the coincidence
locus. -/
lemma Sh_mul_Kfun_eq_twentyfour (ℓ : Work.Kernels.LogLambdaData) (τ ζ : ℍ)
    (h : jInvariantFun τ ≠ jInvariantFun ζ) :
    Sh τ ζ * Kfun ℓ 24 τ ζ = - KfunClear ℓ 24 τ ζ / (DeltaFun τ * DeltaFun ζ) := by
  have h1 := Work.Asymptotics.KL.Kfun_eq_KfunClear_div ℓ 24 (Or.inr rfl) τ ζ h
  have hgp : growthPrefactor 24 τ ζ
      = DeltaFun τ * DeltaFun ζ ^ 2 * (jInvariantFun τ - jInvariantFun ζ) := by
    simp only [Work.Kernels.growthPrefactor, if_neg (by norm_num : ¬ ((24 : ℕ) = 8))]
  have hDτ : DeltaFun τ ≠ 0 := by
    simpa [Work.Kernels.DeltaFun] using ModularForm.discriminant_ne_zero τ
  have hDζ : DeltaFun ζ ≠ 0 := by
    simpa [Work.Kernels.DeltaFun] using ModularForm.discriminant_ne_zero ζ
  have hJ : jInvariantFun τ - jInvariantFun ζ ≠ 0 := sub_ne_zero.mpr h
  have hden : DeltaFun ζ * E4Fun τ ^ 3 - DeltaFun τ * E4Fun ζ ^ 3 ≠ 0 := by
    have hE : DeltaFun ζ * E4Fun τ ^ 3 - DeltaFun τ * E4Fun ζ ^ 3
        = (DeltaFun ζ * DeltaFun τ) * (jInvariantFun τ - jInvariantFun ζ) := by
      rw [← ClassicalFacts.DeltaFun_mul_jInvariantFun τ,
        ← ClassicalFacts.DeltaFun_mul_jInvariantFun ζ]
      ring
    rw [hE]; exact mul_ne_zero (mul_ne_zero hDζ hDτ) hJ
  have hShgp : Sh τ ζ / growthPrefactor 24 τ ζ = -1 / (DeltaFun τ * DeltaFun ζ) := by
    rw [hgp, Sh_eq]
    field_simp
  calc Sh τ ζ * Kfun ℓ 24 τ ζ
      = Sh τ ζ * (KfunClear ℓ 24 τ ζ / growthPrefactor 24 τ ζ) := by rw [h1]
    _ = KfunClear ℓ 24 τ ζ * (Sh τ ζ / growthPrefactor 24 τ ζ) := by ring
    _ = KfunClear ℓ 24 τ ζ * (-1 / (DeltaFun τ * DeltaFun ζ)) := by rw [hShgp]
    _ = - KfunClear ℓ 24 τ ζ / (DeltaFun τ * DeltaFun ζ) := by ring

/-- Pointwise norm form, valid everywhere. -/
lemma norm_Sh_mul_Kfun_le (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ ζ : ℍ) :
    ‖Sh τ ζ * Kfun ℓ d τ ζ‖
      ≤ ‖KfunClear ℓ d τ ζ‖ / (‖DeltaFun τ‖ * ‖DeltaFun ζ‖ ^ (if d = 8 then 0 else 1)) := by
  by_cases h : jInvariantFun τ = jInvariantFun ζ
  · have hSh : Sh τ ζ = 0 := by rw [Sh_eq, h, sub_self, mul_zero, neg_zero]
    rw [hSh, zero_mul, norm_zero]
    positivity
  · rcases hd with rfl | rfl
    · rw [Sh_mul_Kfun_eq_eight ℓ τ ζ h,
        if_pos (show (8 : ℕ) = 8 from rfl), pow_zero, mul_one]
      apply le_of_eq
      simp only [norm_div, norm_neg, norm_mul, mul_one]
    · rw [Sh_mul_Kfun_eq_twentyfour ℓ τ ζ h,
        if_neg (by norm_num : ¬ ((24 : ℕ) = 8)), pow_one]
      apply le_of_eq
      simp only [norm_div, norm_neg, norm_mul]

/-! ## The main bound -/

/-- Bound for `‖Ept ζ ^ (-2)‖`. -/
lemma norm_Ept_zpow_neg_two (ζ : ℍ) :
    ‖(Work.Residues.Ept ζ) ^ (-2 : ℤ)‖ = Real.exp (2 * Real.pi * ζ.im) := by
  rw [norm_zpow, Work.Residues.norm_Ept]
  rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]
  rw [← Real.exp_nat_mul, ← Real.exp_neg]
  congr 1
  ring

set_option autoImplicit false in
/-- **The small-`scale` tile ball bound** (`Assembly`-branch compatibility copy of
`TileDevBall.tileNumBallSmall`).** -/
theorem tileNumBallSmallA (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ M : ℝ, 0 < M ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → Work.Kernels.scale w ≤ 8 →
        ∀ (n : ℤ), (n = 1 ∨ n = -1) → ∀ ζ : UpperHalfPlane,
          ‖(ζ : ℂ) - (((ModularGroup.S • w : UpperHalfPlane)) : ℂ)‖ ≤ 29 / 20 →
          ‖2 * (Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) ζ
              * (Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
                  - Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) ζ))‖
            ≤ M := by
  obtain ⟨α, Nα, Mα, hα0, hNα, hMα, hmg⟩ := (Work.Asymptotics.KClear_mg2 ℓ d hd).1
  obtain ⟨CinvD, NinvD, hCinvD, hNinvD, hinvD⟩ := Work.Asymptotics.EtailE.E_bdd_invDelta
  obtain ⟨cD, CD, hcD, hCD, hDHalf⟩ := Work.Asymptotics.SpikeCircle.DeltaFunBoundsHalf
  obtain ⟨CJ, hCJ, hJdisc⟩ := Work.Asymptotics.SpikeCircle.jInvariantFunUpperDisc
  obtain ⟨CG, NG, hCG, hNG, hGc⟩ := Work.Asymptotics.Gcusp_tile_bound ℓ d hd
  have hGcg : Work.Asymptotics.Gcusp ℓ d = Work.Asymptotics.Compact.Gcoef d ℓ :=
    Work.Asymptotics.Gcusp_eq_Gcoef ℓ d hd
  refine ⟨2 * (α * 11 ^ Nα * 13 ^ Mα) * (CinvD * 8 ^ NinvD * Real.exp (2 * Real.pi * 8))
        * (1 + cD⁻¹ * Real.exp (2 * Real.pi * 10))
      + 2 * ((CD * (CJ * Real.exp (2 * Real.pi * 8)))
          * ((CG * 8 ^ NG) * 11 * (1 + Real.exp (2 * Real.pi * 10)))) + 1,
    by positivity, ?_⟩
  intro w hw hsw n hn ζ hball
  -- region facts
  have hw8 : (1 / 8 : ℝ) ≤ w.im := im_ge_of_scale_le_eight hsw
  have hσ_im_le : (ModularGroup.S • w).im ≤ scale w := Work.Asymptotics.EtailE.E_im_S_le_scale w
  have hσ_norm_le : ‖((ModularGroup.S • w : ℍ) : ℂ)‖ ≤ scale w :=
    Work.Asymptotics.EtailE.E_norm_S_le_scale w
  have hw_norm : ‖(w : ℂ)‖ ≤ 1 / 2 := Work.Asymptotics.EtailE.E_norm_le_half hw
  have hσF : Work.Asymptotics.Funnel (ModularGroup.S • w) :=
    Work.Asymptotics.EtailE.E_S_mem_Funnel hw
  have hζim : (11 / 20 : ℝ) ≤ ζ.im := im_ge_of_ball hw hball
  have hζhalf : (1 / 2 : ℝ) ≤ ζ.im := by linarith
  have hζnorm : ‖(ζ : ℂ)‖ ≤ 10 := by
    have h1 : ‖(ζ : ℂ)‖ ≤ ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖
        + ‖(ζ : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ)‖ := by
      have h2 := norm_add_le (((ModularGroup.S • w : ℍ) : ℂ))
        ((ζ : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ))
      have h3 : ((ModularGroup.S • w : ℍ) : ℂ) + ((ζ : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ))
          = (ζ : ℂ) := by ring
      rwa [h3] at h2
    linarith
  have hζim_le : ζ.im ≤ 10 := le_trans (Work.Kernels.im_le_coe_norm ζ) hζnorm
  have hscaleζ_le : scale ζ ≤ 13 := by
    rw [Work.Kernels.scale]
    have h1 : (ζ.im)⁻¹ ≤ 20 / 11 := by
      rw [inv_le_comm₀ ζ.im_pos (by norm_num)]
      linarith
    linarith
  have hτim : (1 / 8 : ℝ) ≤ (((n : ℝ) +ᵥ w : ℍ)).im := by rw [im_vadd]; exact hw8
  have hτnorm : ‖((((n : ℝ) +ᵥ w : ℍ)) : ℂ)‖ ≤ 3 / 2 := by
    have h := norm_vadd_le n hn w
    linarith
  have hscaleτ_le : scale ((n : ℝ) +ᵥ w : ℍ) ≤ 11 := by
    rw [Work.Kernels.scale]
    have h1 : ((((n : ℝ) +ᵥ w : ℍ)).im)⁻¹ ≤ 8 := by
      rw [im_vadd]
      rw [inv_le_comm₀ w.im_pos (by norm_num : (0 : ℝ) < 8)]
      simpa only [one_div] using hw8
    linarith
  -- the pieces
  have hA : ‖KfunClear ℓ d ((n : ℝ) +ᵥ w) ζ‖ ≤ α * 11 ^ Nα * 13 ^ Mα := by
    refine le_trans (hmg ((n : ℝ) +ᵥ w) ζ) ?_
    have hs1 : (1 : ℝ) ≤ scale ((n : ℝ) +ᵥ w) := Work.Kernels.one_le_scale _
    have hs2 : (1 : ℝ) ≤ scale ζ := Work.Kernels.one_le_scale ζ
    have h1 : (scale ((n : ℝ) +ᵥ w)) ^ Nα ≤ 11 ^ Nα :=
      Real.rpow_le_rpow (le_trans zero_le_one hs1) hscaleτ_le hNα
    have h2 : (scale ζ) ^ Mα ≤ 13 ^ Mα :=
      Real.rpow_le_rpow (le_trans zero_le_one hs2) hscaleζ_le hMα
    have h3 : (0 : ℝ) ≤ (11 : ℝ) ^ Nα := Real.rpow_nonneg (by norm_num) _
    have h4 : (0 : ℝ) ≤ (scale ζ) ^ Mα := Real.rpow_nonneg (by positivity) _
    calc α * (scale ((n : ℝ) +ᵥ w)) ^ Nα * (scale ζ) ^ Mα
        ≤ α * 11 ^ Nα * (scale ζ) ^ Mα :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hα0) h4
      _ ≤ α * 11 ^ Nα * 13 ^ Mα :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg hα0 (Real.rpow_nonneg (by norm_num) _))
  have hB : (‖DeltaFun ((n : ℝ) +ᵥ w)‖)⁻¹
      ≤ CinvD * 8 ^ NinvD * Real.exp (2 * Real.pi * 8) := by
    have h := hinvD w hw
    have h' : (‖DeltaFun w‖)⁻¹
        ≤ CinvD * (scale w) ^ NinvD * Real.exp (2 * Real.pi * (ModularGroup.S • w).im) := by
      rw [← norm_inv]; exact h
    rw [Work.Asymptotics.Tile.vadd_int_eq_self DeltaFun
      (fun τ => Work.Kernels.KernelFacts.DeltaFun_vadd_one τ) n hn w]
    have h1 : (scale w) ^ NinvD ≤ (8 : ℝ) ^ NinvD :=
      Real.rpow_le_rpow (le_trans zero_le_one (Work.Kernels.one_le_scale w)) hsw hNinvD
    have h2 : Real.exp (2 * Real.pi * (ModularGroup.S • w).im)
        ≤ Real.exp (2 * Real.pi * 8) :=
      Real.exp_le_exp.mpr (by nlinarith [hσ_im_le, Real.pi_pos])
    exact le_trans h' (mul_le_mul (mul_le_mul_of_nonneg_left h1 hCinvD.le) h2
            (Real.exp_pos _).le (by positivity))
  have hC : (‖DeltaFun ζ‖)⁻¹ ≤ cD⁻¹ * Real.exp (2 * Real.pi * 10) := by
    have h := (hDHalf ζ hζhalf).1
    have h1 : Real.exp (-(2 * Real.pi * ζ.im)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, hζim]
    have h2 : Real.exp (2 * Real.pi * ζ.im) ≤ Real.exp (2 * Real.pi * 10) :=
      Real.exp_le_exp.mpr (by nlinarith [hζim_le, Real.pi_pos])
    calc (‖DeltaFun ζ‖)⁻¹ ≤ (cD * Real.exp (-(2 * Real.pi * ζ.im)))⁻¹ :=
          inv_anti₀ (by positivity) h
      _ = cD⁻¹ * Real.exp (2 * Real.pi * ζ.im) := by
          rw [mul_inv, ← Real.exp_neg]; ring_nf
      _ ≤ cD⁻¹ * Real.exp (2 * Real.pi * 10) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
  have hSh : ‖Sh ((n : ℝ) +ᵥ w) ζ‖ ≤ CD * (CJ * Real.exp (2 * Real.pi * 8)) := by
    have hΔζ : ‖DeltaFun ζ‖ ≤ CD := by
      refine le_trans (hDHalf ζ hζhalf).2 ?_
      have h1 : Real.exp (-(2 * Real.pi * ζ.im)) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, hζim]
      nlinarith [hCD.le, h1]
    have hj : ‖jInvariantFun ((n : ℝ) +ᵥ w) - jInvariantFun ζ‖
        ≤ CJ * Real.exp (2 * Real.pi * 8) := by
      have h := hJdisc (ModularGroup.S • w) ζ hσF hball
      rw [Work.Asymptotics.Tile.vadd_int_eq_self jInvariantFun
        (fun τ => Work.Kernels.KernelFacts.jInvariantFun_vadd_one τ) n hn w,
        ← Work.Kernels.KernelFacts.jInvariantFun_S_smul w]
      refine le_trans h ?_
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
        nlinarith [hσ_im_le, Real.pi_pos])) hCJ.le
    rw [Sh_eq, norm_neg, norm_mul]
    exact mul_le_mul hΔζ hj (norm_nonneg _) hCD.le
  have hGcoef : ∀ i j : Fin 2, ‖Gcoef d ℓ i j (((n : ℝ) +ᵥ w : ℍ))‖ ≤ CG * 8 ^ NG := by
    intro i j
    have h := hGc w n hn hw i j
    have h1 : (scale w) ^ NG ≤ (8 : ℝ) ^ NG :=
      Real.rpow_le_rpow (le_trans zero_le_one (Work.Kernels.one_le_scale w)) hsw hNG
    have h2 : ‖Gcoef d ℓ i j (((n : ℝ) +ᵥ w : ℍ))‖
        = ‖Work.Asymptotics.Gcusp ℓ d i j (((n : ℝ) +ᵥ w : ℍ))‖ := by rw [hGcg]
    rw [h2]
    exact le_trans h (mul_le_mul_of_nonneg_left h1 hCG.le)
  have hG : ‖Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) ζ‖
      ≤ (CG * 8 ^ NG) * 11 * (1 + Real.exp (2 * Real.pi * 10)) := by
    have hEpt2 : ‖(Work.Residues.Ept ζ) ^ (-2 : ℤ)‖ ≤ Real.exp (2 * Real.pi * 10) := by
      rw [norm_Ept_zpow_neg_two]
      exact Real.exp_le_exp.mpr (by nlinarith [hζim_le, Real.pi_pos])
    have b1 := hGcoef 0 0
    have b2 := hGcoef 0 1
    have b3 := hGcoef 1 0
    have b4 := hGcoef 1 1
    rw [Work.Asymptotics.Compact.Gfun]
    have hs : (0 : ℝ) ≤ CG * 8 ^ NG := by positivity
    have e1 : ‖Gcoef d ℓ 0 0 (((n : ℝ) +ᵥ w : ℍ))‖ ≤ CG * 8 ^ NG := b1
    have e2 : ‖(ζ : ℂ) * Gcoef d ℓ 0 1 (((n : ℝ) +ᵥ w : ℍ))‖ ≤ 10 * (CG * 8 ^ NG) := by
      rw [norm_mul]
      exact mul_le_mul hζnorm b2 (norm_nonneg _) (by norm_num)
    have e3 : ‖(Work.Residues.Ept ζ) ^ (-2 : ℤ)
          * (Gcoef d ℓ 1 0 (((n : ℝ) +ᵥ w : ℍ))
              + (ζ : ℂ) * Gcoef d ℓ 1 1 (((n : ℝ) +ᵥ w : ℍ)))‖
        ≤ Real.exp (2 * Real.pi * 10) * (11 * (CG * 8 ^ NG)) := by
      rw [norm_mul]
      refine mul_le_mul hEpt2 ?_ (norm_nonneg _) (Real.exp_pos _).le
      have e4 : ‖(ζ : ℂ) * Gcoef d ℓ 1 1 (((n : ℝ) +ᵥ w : ℍ))‖ ≤ 10 * (CG * 8 ^ NG) := by
        rw [norm_mul]
        exact mul_le_mul hζnorm b4 (norm_nonneg _) (by norm_num)
      calc ‖Gcoef d ℓ 1 0 (((n : ℝ) +ᵥ w : ℍ))
            + (ζ : ℂ) * Gcoef d ℓ 1 1 (((n : ℝ) +ᵥ w : ℍ))‖
          ≤ ‖Gcoef d ℓ 1 0 (((n : ℝ) +ᵥ w : ℍ))‖
            + ‖(ζ : ℂ) * Gcoef d ℓ 1 1 (((n : ℝ) +ᵥ w : ℍ))‖ := norm_add_le _ _
        _ ≤ CG * 8 ^ NG + 10 * (CG * 8 ^ NG) := add_le_add b3 e4
        _ ≤ 11 * (CG * 8 ^ NG) := by nlinarith [hs]
    calc ‖Gcoef d ℓ 0 0 (((n : ℝ) +ᵥ w : ℍ))
          + (ζ : ℂ) * Gcoef d ℓ 0 1 (((n : ℝ) +ᵥ w : ℍ))
          + (Work.Residues.Ept ζ) ^ (-2 : ℤ)
            * (Gcoef d ℓ 1 0 (((n : ℝ) +ᵥ w : ℍ))
                + (ζ : ℂ) * Gcoef d ℓ 1 1 (((n : ℝ) +ᵥ w : ℍ)))‖
        ≤ ‖Gcoef d ℓ 0 0 (((n : ℝ) +ᵥ w : ℍ))
              + (ζ : ℂ) * Gcoef d ℓ 0 1 (((n : ℝ) +ᵥ w : ℍ))‖
            + ‖(Work.Residues.Ept ζ) ^ (-2 : ℤ)
              * (Gcoef d ℓ 1 0 (((n : ℝ) +ᵥ w : ℍ))
                  + (ζ : ℂ) * Gcoef d ℓ 1 1 (((n : ℝ) +ᵥ w : ℍ)))‖ := norm_add_le _ _
      _ ≤ (CG * 8 ^ NG + 10 * (CG * 8 ^ NG))
            + Real.exp (2 * Real.pi * 10) * (11 * (CG * 8 ^ NG)) := by
          refine add_le_add ?_ e3
          calc ‖Gcoef d ℓ 0 0 (((n : ℝ) +ᵥ w : ℍ))
                + (ζ : ℂ) * Gcoef d ℓ 0 1 (((n : ℝ) +ᵥ w : ℍ))‖
              ≤ ‖Gcoef d ℓ 0 0 (((n : ℝ) +ᵥ w : ℍ))‖
                + ‖(ζ : ℂ) * Gcoef d ℓ 0 1 (((n : ℝ) +ᵥ w : ℍ))‖ := norm_add_le _ _
            _ ≤ CG * 8 ^ NG + 10 * (CG * 8 ^ NG) := add_le_add e1 e2
      _ ≤ (CG * 8 ^ NG) * 11 * (1 + Real.exp (2 * Real.pi * 10)) := by
          have hE : 0 < Real.exp (2 * Real.pi * 10) := Real.exp_pos _
          nlinarith [hs, hE]
  -- products
  have hKC : ‖Sh ((n : ℝ) +ᵥ w) ζ * Kfun ℓ d ((n : ℝ) +ᵥ w) ζ‖
      ≤ (α * 11 ^ Nα * 13 ^ Mα) * (CinvD * 8 ^ NinvD * Real.exp (2 * Real.pi * 8))
        * (1 + cD⁻¹ * Real.exp (2 * Real.pi * 10)) := by
    have hA0 : (0 : ℝ) ≤ α * 11 ^ Nα * 13 ^ Mα := by positivity
    have hB0 : (0 : ℝ) ≤ CinvD * 8 ^ NinvD * Real.exp (2 * Real.pi * 8) := by positivity
    have hC0 : (0 : ℝ) ≤ cD⁻¹ * Real.exp (2 * Real.pi * 10) := by positivity
    rcases hd with rfl | rfl
    · have hnorm := norm_Sh_mul_Kfun_le ℓ 8 (Or.inl rfl) ((n : ℝ) +ᵥ w) ζ
      rw [if_pos (show (8 : ℕ) = 8 from rfl), pow_zero, mul_one] at hnorm
      refine le_trans hnorm ?_
      refine le_trans (div_le_div_of_nonneg_right hA (by positivity)) ?_
      rw [div_eq_mul_inv]
      refine le_trans (mul_le_mul_of_nonneg_left hB hA0) ?_
      nlinarith [mul_nonneg hA0 hB0, hC0]
    · have hnorm := norm_Sh_mul_Kfun_le ℓ 24 (Or.inr rfl) ((n : ℝ) +ᵥ w) ζ
      rw [if_neg (by norm_num : ¬ ((24 : ℕ) = 8)), pow_one] at hnorm
      refine le_trans hnorm ?_
      refine le_trans (div_le_div_of_nonneg_right hA (by positivity)) ?_
      rw [div_eq_mul_inv, mul_inv]
      refine le_trans (mul_le_mul_of_nonneg_left
        (mul_le_mul hB hC (by positivity) hB0) hA0) ?_
      nlinarith [mul_nonneg hA0 hB0, hC0]
  have hSG : ‖Sh ((n : ℝ) +ᵥ w) ζ * Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) ζ‖
      ≤ (CD * (CJ * Real.exp (2 * Real.pi * 8)))
        * ((CG * 8 ^ NG) * 11 * (1 + Real.exp (2 * Real.pi * 10))) := by
    rw [norm_mul]
    exact mul_le_mul hSh hG (norm_nonneg _) (by positivity)
  -- assemble
  have hfin : ‖2 * (Sh ((n : ℝ) +ᵥ w) ζ
        * (Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
            - Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) ζ))‖
      ≤ 2 * ((α * 11 ^ Nα * 13 ^ Mα) * (CinvD * 8 ^ NinvD * Real.exp (2 * Real.pi * 8))
            * (1 + cD⁻¹ * Real.exp (2 * Real.pi * 10)))
          + 2 * ((CD * (CJ * Real.exp (2 * Real.pi * 8)))
              * ((CG * 8 ^ NG) * 11 * (1 + Real.exp (2 * Real.pi * 10)))) := by
    have h2 : ‖Sh ((n : ℝ) +ᵥ w) ζ
          * (Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
              - Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) ζ)‖
        ≤ ‖Sh ((n : ℝ) +ᵥ w) ζ * Kfun ℓ d ((n : ℝ) +ᵥ w) ζ‖
          + ‖Sh ((n : ℝ) +ᵥ w) ζ
              * Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) ζ‖ := by
      rw [mul_sub]; exact norm_sub_le _ _
    have h1 : ‖2 * (Sh ((n : ℝ) +ᵥ w) ζ
          * (Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
              - Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) ζ))‖
        = 2 * ‖Sh ((n : ℝ) +ᵥ w) ζ
          * (Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
              - Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) ζ)‖ := by
      rw [norm_mul, show ‖(2 : ℂ)‖ = 2 from by norm_num]
    rw [h1]
    calc 2 * ‖Sh ((n : ℝ) +ᵥ w) ζ
          * (Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
              - Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) ζ)‖
        ≤ 2 * (‖Sh ((n : ℝ) +ᵥ w) ζ * Kfun ℓ d ((n : ℝ) +ᵥ w) ζ‖
            + ‖Sh ((n : ℝ) +ᵥ w) ζ
                * Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) ζ‖) :=
          mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = 2 * ‖Sh ((n : ℝ) +ᵥ w) ζ * Kfun ℓ d ((n : ℝ) +ᵥ w) ζ‖
            + 2 * ‖Sh ((n : ℝ) +ᵥ w) ζ
                * Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) ζ‖ := by ring
      _ ≤ 2 * ((α * 11 ^ Nα * 13 ^ Mα) * (CinvD * 8 ^ NinvD * Real.exp (2 * Real.pi * 8))
            * (1 + cD⁻¹ * Real.exp (2 * Real.pi * 10)))
          + 2 * ((CD * (CJ * Real.exp (2 * Real.pi * 8)))
              * ((CG * 8 ^ NG) * 11 * (1 + Real.exp (2 * Real.pi * 10)))) := by
          linarith [mul_le_mul_of_nonneg_left hKC (by norm_num : (0:ℝ) ≤ 2),
            mul_le_mul_of_nonneg_left hSG (by norm_num : (0:ℝ) ≤ 2)]
  linarith [hfin]


end Work.Asymptotics.TileDevBall

end
