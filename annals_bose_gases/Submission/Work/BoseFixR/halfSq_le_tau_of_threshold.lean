import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseFixR.TauSmGeQuarter
import Submission.Work.BoseGateFS.TauRows
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.halfSq_le_tau_of_threshold`

At FS's parameter point the smoothed kinetic symbol `τ̃ = tauSm eT s d ℓ` dominates half
of the momentum square, as soon as the momentum is *above* the first kink scale
`(sℓ)^{-1}` — the condition `(sℓ)^{-1} ≤ ‖k‖/8` of the `P_H` region.

## The mathematics

`tauSm eT s d ℓ q = (1-eT)·c²·τ̃(‖q‖/c) + eT·c'²·τ̃(‖q‖/c')` with `c = (2sℓ)⁻¹` and
`c' = (2dsℓ)⁻¹`, and the profile satisfies `(max 0 (r-2))² ≤ τ̃ r`
(`BoseBoxFock.exists_tauProf`).  So, since `eT ∈ [0,1]` and the second term is
nonnegative,

  `tauSm ≥ (1-eT)·(‖q‖ - 2c)²`.

The threshold `‖q‖ ≥ 8/(sℓ) = 16c` gives `2c ≤ ‖q‖/8`, hence
`(‖q‖ - 2c)² ≥ (7‖q‖/8)² = (49/64)‖q‖²`, and `eT ≤ 9/49` gives `1 - eT ≥ 40/49`.
Therefore

  `tauSm ≥ (40/49)·(49/64)·‖q‖² = (5/8)‖q‖² ≥ ‖q‖²/2`.

The constant `9/49` is exactly the threshold that makes the last step work: `5/8 > 1/2`
(cf. `TauSmGeQuarter`, which is the same computation with the cruder threshold `4c`
and the weaker constant `(1-eT)/4`).
-/

noncomputable section

namespace Work.BoseFixR

open Work.BoseBox

/-- **The kinetic symbol dominates `‖q‖²/2` above the threshold** `‖q‖ ≥ 16·(2sℓ)⁻¹`.

Unfolding `tauSm`, the first term is `(1-eT)·c²·τ̃(‖q‖/c)` with `c = (2sℓ)⁻¹`, and
`τ̃ = tauProf` satisfies `(max 0 (r-2))² ≤ τ̃ r`.  The threshold `‖q‖ ≥ 16c` forces
`‖q‖/c ≥ 2`, so that term is at least `(1-eT)·(‖q‖ - 2c)² ≥ (1-eT)·(49/64)‖q‖² ≥
(5/8)‖q‖² ≥ ‖q‖²/2`; the `eT`-weighted second term is nonnegative and is discarded. -/
theorem tauSm_ge_half_sq {eT s d ℓ : ℝ} (heT0 : 0 ≤ eT) (heT : eT ≤ 9 / 49)
    (hs : 0 < s) (hℓ : 0 < ℓ) (q : EuclideanSpace ℝ (Fin 3))
    (hq : 16 * (2 * s * ℓ)⁻¹ ≤ ‖q‖) :
    ‖q‖ ^ 2 / 2 ≤ Work.BoseBoxFock.tauSm eT s d ℓ q := by
  have hc : (0 : ℝ) < (2 * s * ℓ)⁻¹ := by positivity
  have h1eT : 0 ≤ 1 - eT := by linarith
  have hprof : ∀ r : ℝ, (max 0 (r - 2)) ^ 2 ≤ Work.BoseBoxFock.tauProf r :=
    fun r => Work.BoseBoxFock.tauProf_spec.2.2.1 r
  have hnn_prof : ∀ r : ℝ, 0 ≤ Work.BoseBoxFock.tauProf r :=
    fun r => le_trans (sq_nonneg _) (hprof r)
  -- the kink bound at `c = (2sℓ)⁻¹`
  have hkink : (‖q‖ - 2 * (2 * s * ℓ)⁻¹) ^ 2
      ≤ ((2 * s * ℓ)⁻¹) ^ 2 * Work.BoseBoxFock.tauProf (‖q‖ / (2 * s * ℓ)⁻¹) := by
    have hr2 : (2 : ℝ) ≤ ‖q‖ / (2 * s * ℓ)⁻¹ := by
      rw [le_div_iff₀ hc]; linarith
    have hm : max 0 (‖q‖ / (2 * s * ℓ)⁻¹ - 2) = ‖q‖ / (2 * s * ℓ)⁻¹ - 2 :=
      max_eq_right (by linarith)
    have h1 : (‖q‖ / (2 * s * ℓ)⁻¹ - 2) ^ 2
        ≤ Work.BoseBoxFock.tauProf (‖q‖ / (2 * s * ℓ)⁻¹) := by
      have h := hprof (‖q‖ / (2 * s * ℓ)⁻¹)
      rwa [hm] at h
    have h2 : ((2 * s * ℓ)⁻¹) ^ 2 * (‖q‖ / (2 * s * ℓ)⁻¹ - 2) ^ 2
        = (‖q‖ - 2 * (2 * s * ℓ)⁻¹) ^ 2 := by
      field_simp
    calc (‖q‖ - 2 * (2 * s * ℓ)⁻¹) ^ 2
        = ((2 * s * ℓ)⁻¹) ^ 2 * (‖q‖ / (2 * s * ℓ)⁻¹ - 2) ^ 2 := h2.symm
      _ ≤ ((2 * s * ℓ)⁻¹) ^ 2 * Work.BoseBoxFock.tauProf (‖q‖ / (2 * s * ℓ)⁻¹) :=
          mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  -- the threshold upgrades the kink to `(49/64)·‖q‖²`
  have hregion : (49 / 64) * ‖q‖ ^ 2 ≤ (‖q‖ - 2 * (2 * s * ℓ)⁻¹) ^ 2 := by
    have h8 : 2 * (2 * s * ℓ)⁻¹ ≤ ‖q‖ / 8 := by linarith
    have hge : 7 * ‖q‖ / 8 ≤ ‖q‖ - 2 * (2 * s * ℓ)⁻¹ := by linarith [abs_nonneg ‖q‖]
    have h0 : (0 : ℝ) ≤ 7 * ‖q‖ / 8 := by positivity
    have h := pow_le_pow_left₀ h0 hge 2
    have he : (7 * ‖q‖ / 8) ^ 2 = (49 / 64) * ‖q‖ ^ 2 := by ring
    linarith [h, he.le, he.symm.le]
  -- combine with `eT ≤ 9/49`
  have hfirst : ‖q‖ ^ 2 / 2
      ≤ (1 - eT) * (((2 * s * ℓ)⁻¹) ^ 2 * Work.BoseBoxFock.tauProf (‖q‖ / (2 * s * ℓ)⁻¹)) := by
    have hstep : (1 - eT) * ((49 / 64) * ‖q‖ ^ 2)
        ≤ (1 - eT) * (((2 * s * ℓ)⁻¹) ^ 2
            * Work.BoseBoxFock.tauProf (‖q‖ / (2 * s * ℓ)⁻¹)) :=
      mul_le_mul_of_nonneg_left (le_trans hregion hkink) h1eT
    have h49 : (40 / 49 : ℝ) ≤ 1 - eT := by linarith
    have hnon : (0 : ℝ) ≤ (49 / 64) * ‖q‖ ^ 2 := by positivity
    have hcoef := mul_le_mul_of_nonneg_right h49 hnon
    have he : (40 / 49) * ((49 / 64) * ‖q‖ ^ 2) = (5 / 8) * ‖q‖ ^ 2 := by ring
    have hhalf : ‖q‖ ^ 2 / 2 ≤ (5 / 8) * ‖q‖ ^ 2 := by nlinarith [sq_nonneg ‖q‖]
    linarith [hstep, hcoef, he.le, he.symm.le, hhalf]
  -- the second (smoothed) term is nonnegative
  have hsecond : 0 ≤ eT * ((2 * d * s * ℓ)⁻¹) ^ 2
      * Work.BoseBoxFock.tauProf (‖q‖ / (2 * d * s * ℓ)⁻¹) :=
    mul_nonneg (mul_nonneg heT0 (sq_nonneg _)) (hnn_prof _)
  have hassoc : (1 - eT) * ((2 * s * ℓ)⁻¹) ^ 2 * Work.BoseBoxFock.tauProf (‖q‖ / (2 * s * ℓ)⁻¹)
      = (1 - eT) * (((2 * s * ℓ)⁻¹) ^ 2 * Work.BoseBoxFock.tauProf (‖q‖ / (2 * s * ℓ)⁻¹)) := by
    ring
  rw [Work.BoseBoxFock.tauSm]
  have hfirstL : ‖q‖ ^ 2 / 2
      ≤ (1 - eT) * ((2 * s * ℓ)⁻¹) ^ 2
        * Work.BoseBoxFock.tauProf (‖q‖ / (2 * s * ℓ)⁻¹) := by
    rw [hassoc]; exact hfirst
  linarith [hfirstL, hsecond]

/-- At FS's parameter point (`FSParamsView E`, so `s = X`, `d = X⁶`, `ℓ = K_ℓ(μa)^{-1/2}`)
the kinetic symbol `τ = tauSm` dominates `‖k‖²/2` above the threshold
`(sℓ)^{-1} ≤ ‖k‖/8` of the `P_H` region. -/
theorem halfSq_le_tau_of_threshold {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode]
    {F : Work.BoseB7.FockData Mode} {E : Work.BoseB7.Q3Env Mode}
    (htau : ∀ k : Mode, E.tau k = Work.BoseBoxFock.tauSm E.eT E.s E.d E.ell (F.kmom k))
    (hv : Work.BoseB7.FSParamsView E)
    (heT : E.eT ≤ 9 / 49)
    (k : Mode) (hx : (E.s * E.ell)⁻¹ ≤ ‖F.kmom k‖ / 8) :
    ‖F.kmom k‖ ^ 2 / 2 ≤ E.tau k := by
  rw [htau k]
  have ht0 : 0 < hv.t := hv.t_pos
  have hs : 0 < E.s := by rw [hv.s_eq]; exact Work.BoseBox.fsXp_pos ht0
  have hℓ : 0 < E.ell := Work.BoseB7.ell_pos E hv
  have heT0 : 0 ≤ E.eT := by rw [hv.eT_eq]; exact (Work.BoseBox.fsXp_pos ht0).le
  refine tauSm_ge_half_sq heT0 heT hs hℓ _ ?_
  have hq : 16 * (2 * E.s * E.ell)⁻¹ = 8 * (E.s * E.ell)⁻¹ := by
    rw [show (2 * E.s * E.ell) = 2 * (E.s * E.ell) by ring, mul_inv, inv_eq_one_div]
    ring
  rw [hq]
  linarith

end Work.BoseFixR
