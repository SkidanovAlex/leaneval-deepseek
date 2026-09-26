/-
# Assembly of the tile ball bound for the numerator
`N(ζ) = 2 · Sh(τ,ζ) · (Kfun(τ,ζ) − Gfun(τ,ζ))`, `τ = n +ᵥ w`

This module reduces the target `Work.Asymptotics.TileNumBallTS` (the bound
`‖N(ζ)‖ ≤ C (scale w)^N` on the ball `‖ζ − S • w‖ ≤ 29/20`) to three pieces:

* the *large-`scale`* bound `8 < scale w`, which uses the two cleared half-deviations
  `Sh·(K_± − 𝒢_±)` (the `K₊` half by the algebraic decomposition, the `K₋` half by
  `Compact.tail_identity` together with the bracket bound);
* the *small-`scale`* bound `scale w ≤ 8` (a compactness statement).

The separation is available because on `E = KEpsilon` one has `scale w ≤ Im (S • w) + 2`
(`scale_le_im_S_add_two`), so `8 < scale w` forces `3 ≤ ζ.im` for every `ζ` in the ball
(`three_le_im_of_scale_gt`) — the hypothesis under which the half-deviation bounds are stated.
-/
import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Asymptotics.Compact.gfun_eq
import Submission.Work.Asymptotics.EtailE.Basic

noncomputable section

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane

namespace Work.Asymptotics.TileNumBallTS

open Work.Kernels
open Work.Asymptotics.Compact (Sh brMinus br0)

/-! ## The geometry of `E` -/

/-- **`scale w ≤ Im (S • w) + 2` on `E`.**  Writing `σ = S • w` one has `w = S • σ`,
`w.im = σ.im / ‖σ‖²` and `‖w‖ = ‖σ‖⁻¹`; hence

`scale w = 1 + ‖σ‖²/σ.im + ‖σ‖⁻¹ = 1 + σ.re²/σ.im + σ.im + ‖σ‖⁻¹`,

and `σ.re² < 1`, `σ.im ≥ 2` (since `σ ∈ 𝒟` has `|σ.re| < 1` and `Im σ ≥ 2`) give
`σ.re²/σ.im < 1/2` and `‖σ‖⁻¹ ≤ 1/σ.im ≤ 1/2`. -/
lemma scale_le_im_S_add_two {w : ℍ} (hw : w ∈ Work.Asymptotics.KEpsilon) :
    scale w ≤ (ModularGroup.S • w).im + 2 := by
  set σ : ℍ := ModularGroup.S • w with hσdef
  have hswap : w = ModularGroup.S • σ := by rw [hσdef, Work.Asymptotics.S_smul_S_smul]
  have hσim : 0 < σ.im := σ.im_pos
  have hσnorm : 0 < ‖(σ : ℂ)‖ := norm_pos_iff.mpr σ.ne_zero
  have him : w.im = σ.im / ‖(σ : ℂ)‖ ^ 2 := by
    rw [hswap, Work.Asymptotics.EtailE.E_im_S]
  have hnorm : ‖(w : ℂ)‖ = (‖(σ : ℂ)‖)⁻¹ := by
    rw [hswap, Work.Asymptotics.EtailE.E_norm_S]
  have hσD : σ ∈ Work.Asymptotics.DomainD := by
    rw [hσdef]; exact Work.Asymptotics.S_smul_mem_DomainD hw.1
  have hσim2 : 2 ≤ σ.im := by rw [hσdef]; exact hw.2
  have hre : σ.re ^ 2 < 1 := by
    have h1 : |σ.re| < 1 := by
      have h2 := hσD
      rw [Work.Asymptotics.mem_DomainD] at h2
      exact abs_lt.mpr ⟨h2.1, h2.2.1⟩
    have h3 : σ.re ^ 2 = |σ.re| ^ 2 := (sq_abs σ.re).symm
    rw [h3]
    nlinarith [h1, abs_nonneg σ.re]
  have hsq : ‖(σ : ℂ)‖ ^ 2 = σ.re ^ 2 + σ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  have hA : σ.re ^ 2 / σ.im < 1 / 2 := by
    rw [div_lt_iff₀ hσim]; nlinarith [hre, hσim2]
  have hB : (‖(σ : ℂ)‖)⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ hσnorm (by norm_num)]
    have h : σ.im ≤ ‖(σ : ℂ)‖ := Work.Kernels.im_le_coe_norm σ
    linarith
  have hsplit : ‖(σ : ℂ)‖ ^ 2 / σ.im = σ.re ^ 2 / σ.im + σ.im := by
    rw [hsq]; field_simp
  have hgoal : scale w = 1 + (σ.re ^ 2 / σ.im + σ.im) + (‖(σ : ℂ)‖)⁻¹ := by
    simp only [Work.Kernels.scale, him, hnorm]
    rw [show (σ.im / ‖(σ : ℂ)‖ ^ 2)⁻¹ = ‖(σ : ℂ)‖ ^ 2 / σ.im from inv_div _ _]
    rw [hsplit]
  rw [hgoal]
  linarith [hA, hB]

/-- **`8 < scale w` forces `3 ≤ ζ.im` on the ball.** -/
lemma three_le_im_of_scale_gt {w ζ : ℍ} (hw : w ∈ Work.Asymptotics.KEpsilon)
    (hball : ‖(ζ : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ)‖ ≤ 29 / 20) (hsc : 8 < scale w) :
    3 ≤ ζ.im := by
  have h1 : |ζ.im - (ModularGroup.S • w).im| ≤ 29 / 20 := by
    have h := Complex.abs_im_le_norm ((ζ : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ))
    rw [Complex.sub_im, UpperHalfPlane.coe_im, UpperHalfPlane.coe_im] at h
    exact le_trans h hball
  have h2 : ζ.im ≥ (ModularGroup.S • w).im - 29 / 20 := by
    linarith [(abs_le.mp h1).1]
  have h3 : (ModularGroup.S • w).im > 6 := by
    have := scale_le_im_S_add_two hw
    linarith
  linarith

/-! ## The two halves of the target -/

/-- **The large-`scale` part.**  Assumes the ball bounds for the two half-deviations
`Sh·(K₊ − 𝒢₊)` and for the bracket `brMinus + Sh·br0 = 3456π·Sh·(K₋ − 𝒢₋)`; produces the
bound on `N = 2·Sh·(Kfun − Gfun)`. -/
lemma big_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hKp : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : ℍ), w ∈ Work.Asymptotics.KEpsilon → ∀ (n : ℤ), (n = 1 ∨ n = -1) → ∀ ζ : ℍ,
        ‖(ζ : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ)‖ ≤ 29 / 20 → 3 ≤ ζ.im →
        ‖Sh ((n : ℝ) +ᵥ w) ζ
          * (Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) ζ
              - Work.Asymptotics.Compact.Gplus d ((n : ℝ) +ᵥ w) ζ)‖
        ≤ C * (scale w) ^ N)
    (hbm : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : ℍ), w ∈ Work.Asymptotics.KEpsilon → ∀ (n : ℤ), (n = 1 ∨ n = -1) → ∀ ζ : ℍ,
        ‖(ζ : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ)‖ ≤ 29 / 20 → 3 ≤ ζ.im →
        ‖brMinus ℓ d ((n : ℝ) +ᵥ w) ζ
          + Sh ((n : ℝ) +ᵥ w) ζ * br0 d ℓ ((n : ℝ) +ᵥ w) ζ‖
        ≤ C * (scale w) ^ N) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : ℍ), w ∈ Work.Asymptotics.KEpsilon → 8 < scale w →
        ∀ (n : ℤ), (n = 1 ∨ n = -1) → ∀ ζ : ℍ,
        ‖(ζ : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ)‖ ≤ 29 / 20 →
        ‖2 * (Sh ((n : ℝ) +ᵥ w) ζ
            * (Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
                - Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) ζ))‖
        ≤ C * (scale w) ^ N := by
  obtain ⟨Ck, Nk, hCk, hNk, hk⟩ := hKp
  obtain ⟨Cb, Nb, hCb, hNb, hb⟩ := hbm
  have hpi : (0 : ℝ) < 3456 * Real.pi := by positivity
  refine ⟨Ck + Cb / (3456 * Real.pi) + 1, max Nk Nb, by positivity, le_max_of_le_left hNk, ?_⟩
  intro w hw hsc n hn ζ hball
  have him : 3 ≤ ζ.im := three_le_im_of_scale_gt hw hball hsc
  have hs1 : (1 : ℝ) ≤ scale w := Work.Kernels.one_le_scale w
  have hs0 : (0 : ℝ) < scale w := Work.Kernels.scale_pos w
  have hA : ((3456 : ℂ) * (Real.pi : ℂ)) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
    exact_mod_cast Real.pi_ne_zero
  have hG : Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) ζ
      = (Work.Asymptotics.Compact.Gplus d ((n : ℝ) +ᵥ w) ζ
          + Work.Asymptotics.Compact.Gminus d ℓ ((n : ℝ) +ᵥ w) ζ) / 2 := by
    have h := Work.Asymptotics.Compact.gfun_eq ℓ d hd ((n : ℝ) +ᵥ w) ζ
    rw [eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)]
    rw [mul_comm]
    exact h.symm
  have hsplit : 2 * (Sh ((n : ℝ) +ᵥ w) ζ
        * (Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
            - Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) ζ))
      = Sh ((n : ℝ) +ᵥ w) ζ
          * (Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) ζ
              - Work.Asymptotics.Compact.Gplus d ((n : ℝ) +ᵥ w) ζ)
        + Sh ((n : ℝ) +ᵥ w) ζ
          * (Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) ζ
              - Work.Asymptotics.Compact.Gminus d ℓ ((n : ℝ) +ᵥ w) ζ) := by
    rw [hG]
    simp only [Work.Kernels.Kfun]
    ring
  by_cases hSh : Sh ((n : ℝ) +ᵥ w) ζ = 0
  · rw [hsplit, hSh, zero_mul, zero_mul, add_zero, norm_zero]
    positivity
  · have hKm : Sh ((n : ℝ) +ᵥ w) ζ
        * (Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) ζ
            - Work.Asymptotics.Compact.Gminus d ℓ ((n : ℝ) +ᵥ w) ζ)
        = -((brMinus ℓ d ((n : ℝ) +ᵥ w) ζ
              + Sh ((n : ℝ) +ᵥ w) ζ * br0 d ℓ ((n : ℝ) +ᵥ w) ζ)
            / ((3456 : ℂ) * (Real.pi : ℂ))) := by
      have htail := Work.Asymptotics.Compact.tail_identity ℓ d hd ((n : ℝ) +ᵥ w) ζ hSh
      have h1 : Sh ((n : ℝ) +ᵥ w) ζ
            * (((3456 : ℂ) * (Real.pi : ℂ))
                * (Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) ζ
                    - Work.Asymptotics.Compact.Gminus d ℓ ((n : ℝ) +ᵥ w) ζ))
          = -(brMinus ℓ d ((n : ℝ) +ᵥ w) ζ
                + Sh ((n : ℝ) +ᵥ w) ζ * br0 d ℓ ((n : ℝ) +ᵥ w) ζ) := by
        rw [htail]
        field_simp
      rw [← neg_div, eq_div_iff hA]
      calc Sh ((n : ℝ) +ᵥ w) ζ
              * (Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) ζ
                  - Work.Asymptotics.Compact.Gminus d ℓ ((n : ℝ) +ᵥ w) ζ)
              * ((3456 : ℂ) * (Real.pi : ℂ))
          = Sh ((n : ℝ) +ᵥ w) ζ
              * (((3456 : ℂ) * (Real.pi : ℂ))
                  * (Work.Kernels.KMinus ℓ d ((n : ℝ) +ᵥ w) ζ
                      - Work.Asymptotics.Compact.Gminus d ℓ ((n : ℝ) +ᵥ w) ζ)) := by ring
        _ = -(brMinus ℓ d ((n : ℝ) +ᵥ w) ζ
                + Sh ((n : ℝ) +ᵥ w) ζ * br0 d ℓ ((n : ℝ) +ᵥ w) ζ) := h1
    rw [hsplit, hKm]
    have h1 : ‖Sh ((n : ℝ) +ᵥ w) ζ
          * (Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) ζ
              - Work.Asymptotics.Compact.Gplus d ((n : ℝ) +ᵥ w) ζ)‖
        ≤ Ck * (scale w) ^ Nk := hk w hw n hn ζ hball him
    have h2 : ‖brMinus ℓ d ((n : ℝ) +ᵥ w) ζ
          + Sh ((n : ℝ) +ᵥ w) ζ * br0 d ℓ ((n : ℝ) +ᵥ w) ζ‖
        ≤ Cb * (scale w) ^ Nb := hb w hw n hn ζ hball him
    have hnormA : ‖((3456 : ℂ) * (Real.pi : ℂ))‖ = 3456 * Real.pi := by
      have hp : ‖(Real.pi : ℂ)‖ = Real.pi := by
        have h1 : ‖(Real.pi : ℂ)‖ ^ 2 = Real.pi ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
        nlinarith [norm_nonneg (Real.pi : ℂ), Real.pi_pos, h1]
      rw [norm_mul, Complex.norm_ofNat, hp]
    have h2' : ‖(brMinus ℓ d ((n : ℝ) +ᵥ w) ζ
            + Sh ((n : ℝ) +ᵥ w) ζ * br0 d ℓ ((n : ℝ) +ᵥ w) ζ)
          / ((3456 : ℂ) * (Real.pi : ℂ))‖ ≤ Cb * (scale w) ^ Nb / (3456 * Real.pi) := by
      rw [norm_div, hnormA]
      exact div_le_div_of_nonneg_right h2 hpi.le
    have hNk' : (scale w) ^ Nk ≤ (scale w) ^ (max Nk Nb) :=
      Real.rpow_le_rpow_of_exponent_le hs1 (le_max_left _ _)
    have hNb' : (scale w) ^ Nb ≤ (scale w) ^ (max Nk Nb) :=
      Real.rpow_le_rpow_of_exponent_le hs1 (le_max_right _ _)
    have hpos : (0 : ℝ) ≤ (scale w) ^ (max Nk Nb) := Real.rpow_nonneg hs0.le _
    have hge1 : (1 : ℝ) ≤ (scale w) ^ (max Nk Nb) :=
      Real.one_le_rpow hs1 (le_max_of_le_left hNk)
    have e1 : Ck * (scale w) ^ Nk ≤ Ck * (scale w) ^ (max Nk Nb) :=
      mul_le_mul_of_nonneg_left hNk' hCk.le
    have e2 : Cb * (scale w) ^ Nb / (3456 * Real.pi)
        ≤ (Cb / (3456 * Real.pi)) * (scale w) ^ (max Nk Nb) := by
      rw [show Cb * (scale w) ^ Nb / (3456 * Real.pi)
            = (Cb / (3456 * Real.pi)) * (scale w) ^ Nb from by ring]
      exact mul_le_mul_of_nonneg_left hNb' (by positivity)
    calc ‖Sh ((n : ℝ) +ᵥ w) ζ
            * (Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) ζ
                - Work.Asymptotics.Compact.Gplus d ((n : ℝ) +ᵥ w) ζ)
          + -((brMinus ℓ d ((n : ℝ) +ᵥ w) ζ
              + Sh ((n : ℝ) +ᵥ w) ζ * br0 d ℓ ((n : ℝ) +ᵥ w) ζ)
              / ((3456 : ℂ) * (Real.pi : ℂ)))‖
        ≤ ‖Sh ((n : ℝ) +ᵥ w) ζ
              * (Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) ζ
                  - Work.Asymptotics.Compact.Gplus d ((n : ℝ) +ᵥ w) ζ)‖
            + ‖-((brMinus ℓ d ((n : ℝ) +ᵥ w) ζ
                + Sh ((n : ℝ) +ᵥ w) ζ * br0 d ℓ ((n : ℝ) +ᵥ w) ζ)
                / ((3456 : ℂ) * (Real.pi : ℂ)))‖ := norm_add_le _ _
      _ = ‖Sh ((n : ℝ) +ᵥ w) ζ
              * (Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) ζ
                  - Work.Asymptotics.Compact.Gplus d ((n : ℝ) +ᵥ w) ζ)‖
            + ‖(brMinus ℓ d ((n : ℝ) +ᵥ w) ζ
                + Sh ((n : ℝ) +ᵥ w) ζ * br0 d ℓ ((n : ℝ) +ᵥ w) ζ)
                / ((3456 : ℂ) * (Real.pi : ℂ))‖ := by rw [norm_neg]
      _ ≤ Ck * (scale w) ^ Nk + Cb * (scale w) ^ Nb / (3456 * Real.pi) :=
          add_le_add h1 h2'
      _ ≤ (Ck + Cb / (3456 * Real.pi) + 1) * (scale w) ^ (max Nk Nb) := by
          nlinarith [e1, e2, hge1, hpos, mul_nonneg hCk.le hpos,
            mul_nonneg (by positivity : (0:ℝ) ≤ Cb / (3456 * Real.pi)) hpos]

/-- **The small-`scale` part.**  A uniform bound `M` on `scale w ≤ 8` gives a polynomial bound
with exponent `0`. -/
lemma small_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hsm : ∃ M : ℝ, 0 < M ∧
      ∀ (w : ℍ), w ∈ Work.Asymptotics.KEpsilon → scale w ≤ 8 →
        ∀ (n : ℤ), (n = 1 ∨ n = -1) → ∀ ζ : ℍ,
        ‖(ζ : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ)‖ ≤ 29 / 20 →
        ‖2 * (Sh ((n : ℝ) +ᵥ w) ζ
            * (Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
                - Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) ζ))‖
        ≤ M) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : ℍ), w ∈ Work.Asymptotics.KEpsilon → scale w ≤ 8 →
        ∀ (n : ℤ), (n = 1 ∨ n = -1) → ∀ ζ : ℍ,
        ‖(ζ : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ)‖ ≤ 29 / 20 →
        ‖2 * (Sh ((n : ℝ) +ᵥ w) ζ
            * (Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
                - Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) ζ))‖
        ≤ C * (scale w) ^ N := by
  obtain ⟨M, hM, hMb⟩ := hsm
  refine ⟨M + 1, 0, by positivity, le_rfl, ?_⟩
  intro w hw hsw n hn ζ hball
  have hpos : (0 : ℝ) ≤ (scale w) ^ (0 : ℝ) := Real.rpow_nonneg (Work.Kernels.scale_pos w).le 0
  calc ‖2 * (Sh ((n : ℝ) +ᵥ w) ζ
        * (Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
            - Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) ζ))‖
      ≤ M := hMb w hw hsw n hn ζ hball
    _ ≤ (M + 1) * (scale w) ^ (0 : ℝ) := by
        rw [Real.rpow_zero, mul_one]; linarith

/-- **The assembly.**  From the large- and small-`scale` bounds one obtains the unconditional
tile ball bound. -/
theorem of_pieces (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hKp : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : ℍ), w ∈ Work.Asymptotics.KEpsilon → ∀ (n : ℤ), (n = 1 ∨ n = -1) → ∀ ζ : ℍ,
        ‖(ζ : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ)‖ ≤ 29 / 20 → 3 ≤ ζ.im →
        ‖Sh ((n : ℝ) +ᵥ w) ζ
          * (Work.Kernels.KPlus d ((n : ℝ) +ᵥ w) ζ
              - Work.Asymptotics.Compact.Gplus d ((n : ℝ) +ᵥ w) ζ)‖
        ≤ C * (scale w) ^ N)
    (hbm : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : ℍ), w ∈ Work.Asymptotics.KEpsilon → ∀ (n : ℤ), (n = 1 ∨ n = -1) → ∀ ζ : ℍ,
        ‖(ζ : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ)‖ ≤ 29 / 20 → 3 ≤ ζ.im →
        ‖brMinus ℓ d ((n : ℝ) +ᵥ w) ζ
          + Sh ((n : ℝ) +ᵥ w) ζ * br0 d ℓ ((n : ℝ) +ᵥ w) ζ‖
        ≤ C * (scale w) ^ N)
    (hsm : ∃ M : ℝ, 0 < M ∧
      ∀ (w : ℍ), w ∈ Work.Asymptotics.KEpsilon → scale w ≤ 8 →
        ∀ (n : ℤ), (n = 1 ∨ n = -1) → ∀ ζ : ℍ,
        ‖(ζ : ℂ) - ((ModularGroup.S • w : ℍ) : ℂ)‖ ≤ 29 / 20 →
        ‖2 * (Sh ((n : ℝ) +ᵥ w) ζ
            * (Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
                - Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) ζ))‖
        ≤ M) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → ∀ n : ℤ, (n = 1 ∨ n = -1) →
        ∀ ζ : UpperHalfPlane,
          ‖(ζ : ℂ) - ((ModularGroup.S • w : UpperHalfPlane) : ℂ)‖ ≤ 29 / 20 →
          ‖2 * (Sh ((n : ℝ) +ᵥ w) ζ
              * (Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) ζ
                  - Work.Asymptotics.Compact.Gfun d ℓ ((n : ℝ) +ᵥ w) ζ))‖
          ≤ C * (scale w) ^ N := by
  obtain ⟨C1, N1, hC1, hN1, h1⟩ := big_bound ℓ d hd hKp hbm
  obtain ⟨C2, N2, hC2, hN2, h2⟩ := small_bound ℓ d hsm
  refine ⟨max C1 C2 + 1, max N1 N2, by positivity, le_max_of_le_left hN1, ?_⟩
  intro w hw n hn ζ hball
  have hs1 : (1 : ℝ) ≤ scale w := Work.Kernels.one_le_scale w
  have hs0 : (0 : ℝ) < scale w := Work.Kernels.scale_pos w
  have hN1' : (scale w) ^ N1 ≤ (scale w) ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_max_left _ _)
  have hN2' : (scale w) ^ N2 ≤ (scale w) ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hs1 (le_max_right _ _)
  have hpos : (0 : ℝ) ≤ (scale w) ^ (max N1 N2) := Real.rpow_nonneg hs0.le _
  by_cases hsc : scale w ≤ 8
  · refine le_trans (h2 w hw hsc n hn ζ hball) ?_
    calc C2 * (scale w) ^ N2 ≤ C2 * (scale w) ^ (max N1 N2) :=
          mul_le_mul_of_nonneg_left hN2' hC2.le
      _ ≤ (max C1 C2 + 1) * (scale w) ^ (max N1 N2) := by
          apply mul_le_mul_of_nonneg_right _ hpos
          linarith [le_max_right C1 C2]
  · have hsc' : 8 < scale w := lt_of_not_ge hsc
    refine le_trans (h1 w hw hsc' n hn ζ hball) ?_
    calc C1 * (scale w) ^ N1 ≤ C1 * (scale w) ^ (max N1 N2) :=
          mul_le_mul_of_nonneg_left hN1' hC1.le
      _ ≤ (max C1 C2 + 1) * (scale w) ^ (max N1 N2) := by
          apply mul_le_mul_of_nonneg_right _ hpos
          linarith [le_max_left C1 C2]

end Work.Asymptotics.TileNumBallTS

end
