import Mathlib
import Submission.Work.Asymptotics.KhatE1Core.Bracket24TailCore
import Submission.Work.Asymptotics.KhatE1Core.Bracket24E2PrimeDefs
import Submission.Work.Asymptotics.KhatE1Core.Bracket24E2Prime_bound
import Submission.Work.Asymptotics.KhatE1Core.Bracket24B35Core
import Submission.Work.Asymptotics.KhatE1Core.Bracket24P24Bound
import Submission.Work.Asymptotics.KhatE1.ShBracketAux
import Submission.Work.Asymptotics.KMFDDefs
import Submission.Work.Asymptotics.KhatE1Core.B24XMData
import Submission.Work.Asymptotics.KhatE1Core.B24XMBounds
import Submission.Work.Asymptotics.KhatE1Core.Bracket24B4Bound_proof
import Submission.Work.Asymptotics.KhatE1Core.KPlus24GroupT_tail
import Submission.Work.Asymptotics.KhatE1Core.KMinus24Group_tail

/-!
# `Bracket24ExpansionHold`: the `d = 24` double-cusp expansion remainder

`X = KPlus24Group + KMinus24Group = Sh τ z·Bracket24 ℓ τ z` and `Xtrunc2X` is the explicit
truncation of `X` with every `z`-atom replaced by its cusp truncation (`B24XMData`), for which

  `Xtrunc2X - B₂E² - B₃E³ - B₄E⁴ - B₅E⁵ = E⁴·XR4X + E⁶·XWX`

(`B24XMData.Xtrunc2X_decomp`), with `XR4X` and `XWX` bounded in `B24XMBounds`
(`‖XR4X‖ = O((scale τ)^N(1+t)^M)`, `‖XWX‖ = O(‖q(τ)‖⁻¹(scale τ)^N(1+t)^M)`).

The remaining input is the *truncation tail* `X - Xtrunc2X`, split into its two halves
(`KPlus24GroupT_tail`, `KMinus24Group_tail`), and the `E(z)⁴`-coefficient `B₄` whose bound
`Bracket24B4Bound_proof` is already available.  This file assembles them.
-/

namespace Work.Asymptotics.KhatE1Core

open UpperHalfPlane
open Work.Residues (Ept)

noncomputable section

/-! ## The `E(z)³`- and `E(z)⁵`-coefficients agree with the workspace's `B₃`, `B₅` -/

lemma Bracket24E3_eq_B3 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    Work.Asymptotics.KhatE1.Bracket24E3 ℓ τ z = Work.Asymptotics.KhatE1.Bracket24B3 ℓ τ := by
  rw [Work.Asymptotics.KhatE1.Bracket24E3, Work.Asymptotics.KhatE1.Bracket24B3]
  ring

lemma Bracket24E5_eq_B5 (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ) :
    Work.Asymptotics.KhatE1.Bracket24E5 ℓ τ z = Work.Asymptotics.KhatE1.Bracket24B5 ℓ τ := by
  rw [Work.Asymptotics.KhatE1.Bracket24E5, Work.Asymptotics.KhatE1.Bracket24B5]
  ring

/-! ## Shape monotonicity -/

lemma shape_monoX (A s u X N M N' M' : ℝ) (hA : 0 ≤ A) (hs : 1 ≤ s) (hu : 1 ≤ u) (hX : 0 ≤ X)
    (hN : N ≤ N') (hM : M ≤ M') :
    A * s ^ N * u ^ M * X ≤ A * s ^ N' * u ^ M' * X := by
  have hs0 : (0 : ℝ) ≤ s := le_trans zero_le_one hs
  have hu0 : (0 : ℝ) ≤ u := le_trans zero_le_one hu
  have h1 : s ^ N ≤ s ^ N' := Real.rpow_le_rpow_of_exponent_le hs hN
  have h2 : u ^ M ≤ u ^ M' := Real.rpow_le_rpow_of_exponent_le hu hM
  calc A * s ^ N * u ^ M * X = A * (s ^ N * u ^ M) * X := by ring
    _ ≤ A * (s ^ N' * u ^ M') * X := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hA) hX
        exact mul_le_mul h1 h2 (Real.rpow_nonneg hu0 _) (Real.rpow_nonneg hs0 _)
    _ = A * s ^ N' * u ^ M' * X := by ring

/-! ## The truncation tail -/

/-- **`Xtrunc2X_tail`** from the two half-tails. -/
theorem Xtrunc2X_tail (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖KPlus24Group ℓ τ z + KMinus24Group ℓ τ z - Xtrunc2X ℓ τ z‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4) := by
  obtain ⟨C1, N1, M1, hC1, hN1, hM1, hb1⟩ := KPlus24GroupT_tail ℓ
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, hb2⟩ := KMinus24Group_tail ℓ
  refine ⟨2 * (C1 + C2) + 1, max N1 N2, max M1 M2, by positivity,
    le_trans hN1 (le_max_left _ _), le_trans hM1 (le_max_left _ _), ?_⟩
  intro τ z t hF ht hz0 hz1 hzim
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hu1 : (1 : ℝ) ≤ 1 + t := by have := hF.2; linarith
  have hsp0 : (0 : ℝ) ≤ Work.Kernels.scale τ := le_trans zero_le_one hs1
  have hup0 : (0 : ℝ) ≤ 1 + t := le_trans zero_le_one hu1
  have hYN : (0 : ℝ) ≤ (‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4 :=
    add_nonneg (mul_nonneg (inv_nonneg.mpr (norm_nonneg (Work.Kernels.qParamFun τ)))
      (by positivity)) (by positivity)
  have hA1 := hb1 τ z t hF ht hz0 hz1 hzim
  have hA2 := hb2 τ z t hF ht hz0 hz1 hzim
  have hE4 : ‖Ept z‖ ^ 4 ≤ (‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4 := by
    have h6 : (0 : ℝ) ≤ ‖Ept z‖ ^ 6 := by positivity
    linarith [mul_nonneg (inv_nonneg.mpr (norm_nonneg (Work.Kernels.qParamFun τ))) h6]
  have hdec : KPlus24Group ℓ τ z + KMinus24Group ℓ τ z - Xtrunc2X ℓ τ z
      = (KPlus24Group ℓ τ z - KPlus24GroupT τ z)
        + (KMinus24Group ℓ τ z - XMinusT ℓ τ z) := by
    rw [Xtrunc2X_eq]
    ring
  rw [hdec]
  have mono : ∀ C' : ℝ, 0 ≤ C' → ∀ N M : ℝ, N ≤ max N1 N2 → M ≤ max M1 M2 →
      C' * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M * ‖Ept z‖ ^ 4
        ≤ C' * (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)
          * ‖Ept z‖ ^ 4 := by
    intro C' hC' N M hN hM
    exact shape_monoX C' (Work.Kernels.scale τ) (1 + t) (‖Ept z‖ ^ 4) N M (max N1 N2)
      (max M1 M2) hC' hs1 hu1 (by positivity) hN hM
  have hA1' : ‖KPlus24Group ℓ τ z - KPlus24GroupT τ z‖
      ≤ C1 * (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)
          * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4) := by
    refine le_trans (le_trans hA1 (mono C1 hC1.le N1 M1 (le_max_left _ _) (le_max_left _ _))) ?_
    exact mul_le_mul_of_nonneg_left hE4
      (mul_nonneg (mul_nonneg hC1.le (Real.rpow_nonneg hsp0 _)) (Real.rpow_nonneg hup0 _))
  have hA2' : ‖KMinus24Group ℓ τ z - XMinusT ℓ τ z‖
      ≤ C2 * (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)
          * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4) := by
    refine le_trans (le_trans hA2 (mono C2 hC2.le N2 M2 (le_max_right _ _) (le_max_right _ _))) ?_
    exact mul_le_mul_of_nonneg_left hE4
      (mul_nonneg (mul_nonneg hC2.le (Real.rpow_nonneg hsp0 _)) (Real.rpow_nonneg hup0 _))
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add hA1' hA2') ?_
  rw [show C1 * (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)
        * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4)
      + C2 * (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)
        * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4)
      = (C1 + C2) * ((Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)
        * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4)) by ring]
  have hcc : C1 + C2 ≤ 2 * (C1 + C2) + 1 := by linarith
  have hY0 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)
      * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hsp0 _) (Real.rpow_nonneg hup0 _)) hYN
  calc (C1 + C2) * ((Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)
        * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4))
      ≤ (2 * (C1 + C2) + 1) * ((Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)
        * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4)) :=
        mul_le_mul_of_nonneg_right hcc hY0
    _ = (2 * (C1 + C2) + 1) * (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)
        * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4) := by ring

/-! ## The target from the tail -/

theorem Bracket24ExpansionHold_of_tail (ℓ : Work.Kernels.LogLambdaData)
    (hTail : ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖KPlus24Group ℓ τ z + KMinus24Group ℓ τ z - Xtrunc2X ℓ τ z‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4)) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖Work.Asymptotics.KhatE1Core.KPlus24Group ℓ τ z
            + Work.Asymptotics.KhatE1Core.KMinus24Group ℓ τ z
            - Work.Asymptotics.KhatE1Core.Bracket24E2' ℓ τ z * (Work.Residues.Ept z) ^ 2
            - Work.Asymptotics.KhatE1.Bracket24B3 ℓ τ * (Work.Residues.Ept z) ^ 3
            - Work.Asymptotics.KhatE1.Bracket24B5 ℓ τ * (Work.Residues.Ept z) ^ 5‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Work.Residues.Ept z‖ ^ 6
                  + ‖Work.Residues.Ept z‖ ^ 4) := by
  obtain ⟨C1, N1, M1, hC1, hN1, hM1, h1⟩ := XWX_bound ℓ
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, h2⟩ := XR4X_bound ℓ
  obtain ⟨C3, N3, M3, hC3, hN3, hM3, h3⟩ := Bracket24B4Bound_proof ℓ
  obtain ⟨C4, N4, M4, hC4, hN4, hM4, h4⟩ := hTail
  refine ⟨2 * (C1 + C2 + C3 + C4) + 1, max (max (max N1 N2) N3) N4,
    max (max (max M1 M2) M3) M4, by positivity,
    le_trans hN4 (le_max_right (max (max N1 N2) N3) N4),
    le_trans hM4 (le_max_right (max (max M1 M2) M3) M4), ?_⟩
  intro τ z t hF ht hz0 hz1 hzim
  have hs1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hu1 : (1 : ℝ) ≤ 1 + t := by have := hF.2; linarith
  have hsp0 : (0 : ℝ) ≤ Work.Kernels.scale τ := le_trans zero_le_one hs1
  have hup0 : (0 : ℝ) ≤ 1 + t := le_trans zero_le_one hu1
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have hYN : (0 : ℝ) ≤ (‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4 :=
    add_nonneg (mul_nonneg (inv_nonneg.mpr hq0) (by positivity)) (by positivity)
  have hE4 : ‖Ept z‖ ^ 4 ≤ (‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4 := by
    have h6 : (0 : ℝ) ≤ ‖Ept z‖ ^ 6 := by positivity
    linarith [mul_nonneg (inv_nonneg.mpr hq0) h6]
  have hdec : Work.Asymptotics.KhatE1Core.KPlus24Group ℓ τ z
          + Work.Asymptotics.KhatE1Core.KMinus24Group ℓ τ z
          - Work.Asymptotics.KhatE1Core.Bracket24E2' ℓ τ z * (Ept z) ^ 2
          - Work.Asymptotics.KhatE1.Bracket24B3 ℓ τ * (Ept z) ^ 3
          - Work.Asymptotics.KhatE1.Bracket24B5 ℓ τ * (Ept z) ^ 5
      = (KPlus24Group ℓ τ z + KMinus24Group ℓ τ z - Xtrunc2X ℓ τ z)
        + ((Ept z) ^ 4 * XR4X ℓ τ z + (Ept z) ^ 6 * XWX ℓ τ z)
        + Bracket24B4 ℓ τ z * (Ept z) ^ 4 := by
    rw [← Xtrunc2X_decomp ℓ τ z, Bracket24E3_eq_B3 ℓ τ z, Bracket24E5_eq_B5 ℓ τ z]
    ring
  rw [hdec]
  have mono : ∀ (C' X : ℝ), 0 ≤ C' → 0 ≤ X → ∀ N M : ℝ,
      N ≤ max (max (max N1 N2) N3) N4 → M ≤ max (max (max M1 M2) M3) M4 →
      C' * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M * X
        ≤ C' * (Work.Kernels.scale τ) ^ (max (max (max N1 N2) N3) N4)
          * (1 + t) ^ (max (max (max M1 M2) M3) M4) * X := by
    intro C' X hC' hX N M hN hM
    exact shape_monoX C' (Work.Kernels.scale τ) (1 + t) X N M
      (max (max (max N1 N2) N3) N4) (max (max (max M1 M2) M3) M4) hC' hs1 hu1 hX hN hM
  have htail' : ‖KPlus24Group ℓ τ z + KMinus24Group ℓ τ z - Xtrunc2X ℓ τ z‖
      ≤ C4 * (Work.Kernels.scale τ) ^ (max (max (max N1 N2) N3) N4)
        * (1 + t) ^ (max (max (max M1 M2) M3) M4)
        * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4) :=
    le_trans (h4 τ z t hF ht hz0 hz1 hzim)
      (mono C4 ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4) hC4.le hYN
        N4 M4 (le_max_right (max (max N1 N2) N3) N4) (le_max_right (max (max M1 M2) M3) M4))
  have hb1 : ‖(Ept z) ^ 4 * XR4X ℓ τ z‖
      ≤ C2 * (Work.Kernels.scale τ) ^ (max (max (max N1 N2) N3) N4)
        * (1 + t) ^ (max (max (max M1 M2) M3) M4)
        * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4) := by
    have h2' := h2 τ z t hF ht hz0 hz1 hzim
    have hnorm : ‖(Ept z) ^ 4 * XR4X ℓ τ z‖
        ≤ C2 * (Work.Kernels.scale τ) ^ N2 * (1 + t) ^ M2 * ‖Ept z‖ ^ 4 := by
      rw [norm_mul, norm_pow]
      calc ‖(Ept z)‖ ^ 4 * ‖XR4X ℓ τ z‖
          ≤ ‖(Ept z)‖ ^ 4 * (C2 * (Work.Kernels.scale τ) ^ N2 * (1 + t) ^ M2) :=
            mul_le_mul_of_nonneg_left h2' (by positivity)
        _ = C2 * (Work.Kernels.scale τ) ^ N2 * (1 + t) ^ M2 * ‖Ept z‖ ^ 4 := by ring
    refine le_trans hnorm ?_
    refine le_trans (mono C2 (‖Ept z‖ ^ 4) hC2.le (by positivity) N2 M2
      (le_trans (le_max_right N1 N2) (le_trans (le_max_left (max N1 N2) N3) (le_max_left (max (max N1 N2) N3) N4)))
      (le_trans (le_max_right M1 M2) (le_trans (le_max_left (max M1 M2) M3) (le_max_left (max (max M1 M2) M3) M4)))) ?_
    exact mul_le_mul_of_nonneg_left hE4
      (mul_nonneg (mul_nonneg hC2.le
        (Real.rpow_nonneg hsp0 _)) (Real.rpow_nonneg hup0 _))
  have hb2 : ‖(Ept z) ^ 6 * XWX ℓ τ z‖
      ≤ C1 * (Work.Kernels.scale τ) ^ (max (max (max N1 N2) N3) N4)
        * (1 + t) ^ (max (max (max M1 M2) M3) M4)
        * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4) := by
    have h1' := h1 τ z t hF ht hz0 hz1 hzim
    have hnorm : ‖(Ept z) ^ 6 * XWX ℓ τ z‖
        ≤ C1 * (Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1
          * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6) := by
      rw [norm_mul, norm_pow]
      calc ‖(Ept z)‖ ^ 6 * ‖XWX ℓ τ z‖
          ≤ ‖(Ept z)‖ ^ 6 * (C1 * (‖Work.Kernels.qParamFun τ‖)⁻¹
              * (Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1) :=
            mul_le_mul_of_nonneg_left h1' (by positivity)
        _ = C1 * (Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1
            * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6) := by ring
    refine le_trans hnorm ?_
    refine le_trans (mono C1 ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6)
      hC1.le (by positivity) N1 M1
      (le_trans (le_max_left N1 N2) (le_trans (le_max_left (max N1 N2) N3) (le_max_left (max (max N1 N2) N3) N4)))
      (le_trans (le_max_left M1 M2) (le_trans (le_max_left (max M1 M2) M3) (le_max_left (max (max M1 M2) M3) M4)))) ?_
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (mul_nonneg hC1.le
      (Real.rpow_nonneg hsp0 _)) (Real.rpow_nonneg hup0 _))
    have h6 : (0 : ℝ) ≤ ‖Ept z‖ ^ 6 := by positivity
    have h4 : (0 : ℝ) ≤ ‖Ept z‖ ^ 4 := by positivity
    linarith [mul_nonneg (inv_nonneg.mpr hq0) h6, h4]
  have hb3 : ‖Bracket24B4 ℓ τ z * (Ept z) ^ 4‖
      ≤ C3 * (Work.Kernels.scale τ) ^ (max (max (max N1 N2) N3) N4)
        * (1 + t) ^ (max (max (max M1 M2) M3) M4)
        * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4) := by
    have h3' := h3 τ z t hF ht hz0 hz1 hzim
    have hnorm : ‖Bracket24B4 ℓ τ z * (Ept z) ^ 4‖
        ≤ C3 * (Work.Kernels.scale τ) ^ N3 * (1 + t) ^ M3 * ‖Ept z‖ ^ 4 := by
      rw [norm_mul, norm_pow]
      calc ‖Bracket24B4 ℓ τ z‖ * ‖(Ept z)‖ ^ 4
          ≤ (C3 * (Work.Kernels.scale τ) ^ N3 * (1 + t) ^ M3) * ‖(Ept z)‖ ^ 4 :=
            mul_le_mul_of_nonneg_right h3' (by positivity)
        _ = C3 * (Work.Kernels.scale τ) ^ N3 * (1 + t) ^ M3 * ‖Ept z‖ ^ 4 := by ring
    refine le_trans hnorm ?_
    refine le_trans (mono C3 (‖Ept z‖ ^ 4) hC3.le (by positivity) N3 M3
      (le_trans (le_max_right (max N1 N2) N3) (le_max_left (max (max N1 N2) N3) N4))
      (le_trans (le_max_right (max M1 M2) M3) (le_max_left (max (max M1 M2) M3) M4))) ?_
    exact mul_le_mul_of_nonneg_left hE4
      (mul_nonneg (mul_nonneg hC3.le
        (Real.rpow_nonneg hsp0 _)) (Real.rpow_nonneg hup0 _))
  have htri : ‖(KPlus24Group ℓ τ z + KMinus24Group ℓ τ z - Xtrunc2X ℓ τ z)
        + ((Ept z) ^ 4 * XR4X ℓ τ z + (Ept z) ^ 6 * XWX ℓ τ z)
        + Bracket24B4 ℓ τ z * (Ept z) ^ 4‖
      ≤ C1 * (Work.Kernels.scale τ) ^ (max (max (max N1 N2) N3) N4)
          * (1 + t) ^ (max (max (max M1 M2) M3) M4)
          * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4)
        + C2 * (Work.Kernels.scale τ) ^ (max (max (max N1 N2) N3) N4)
          * (1 + t) ^ (max (max (max M1 M2) M3) M4)
          * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4)
        + C3 * (Work.Kernels.scale τ) ^ (max (max (max N1 N2) N3) N4)
          * (1 + t) ^ (max (max (max M1 M2) M3) M4)
          * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4)
        + C4 * (Work.Kernels.scale τ) ^ (max (max (max N1 N2) N3) N4)
          * (1 + t) ^ (max (max (max M1 M2) M3) M4)
          * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4) := by
    have h5 := norm_add_le ((KPlus24Group ℓ τ z + KMinus24Group ℓ τ z - Xtrunc2X ℓ τ z)
        + ((Ept z) ^ 4 * XR4X ℓ τ z + (Ept z) ^ 6 * XWX ℓ τ z))
      (Bracket24B4 ℓ τ z * (Ept z) ^ 4)
    have h6 := norm_add_le (KPlus24Group ℓ τ z + KMinus24Group ℓ τ z - Xtrunc2X ℓ τ z)
      ((Ept z) ^ 4 * XR4X ℓ τ z + (Ept z) ^ 6 * XWX ℓ τ z)
    have h7 := norm_add_le ((Ept z) ^ 4 * XR4X ℓ τ z) ((Ept z) ^ 6 * XWX ℓ τ z)
    linarith [h5, h6, h7, htail', hb1, hb2, hb3]
  refine le_trans htri ?_
  rw [show C1 * (Work.Kernels.scale τ) ^ (max (max (max N1 N2) N3) N4)
          * (1 + t) ^ (max (max (max M1 M2) M3) M4)
          * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4)
        + C2 * (Work.Kernels.scale τ) ^ (max (max (max N1 N2) N3) N4)
          * (1 + t) ^ (max (max (max M1 M2) M3) M4)
          * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4)
        + C3 * (Work.Kernels.scale τ) ^ (max (max (max N1 N2) N3) N4)
          * (1 + t) ^ (max (max (max M1 M2) M3) M4)
          * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4)
        + C4 * (Work.Kernels.scale τ) ^ (max (max (max N1 N2) N3) N4)
          * (1 + t) ^ (max (max (max M1 M2) M3) M4)
          * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4)
      = (C1 + C2 + C3 + C4) * ((Work.Kernels.scale τ) ^ (max (max (max N1 N2) N3) N4)
          * (1 + t) ^ (max (max (max M1 M2) M3) M4)
          * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4)) by ring]
  have hcc : C1 + C2 + C3 + C4 ≤ 2 * (C1 + C2 + C3 + C4) + 1 := by linarith
  have hY0 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ (max (max (max N1 N2) N3) N4)
      * (1 + t) ^ (max (max (max M1 M2) M3) M4)
      * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hsp0 _) (Real.rpow_nonneg hup0 _)) hYN
  calc (C1 + C2 + C3 + C4) * ((Work.Kernels.scale τ) ^ (max (max (max N1 N2) N3) N4)
        * (1 + t) ^ (max (max (max M1 M2) M3) M4)
        * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4))
      ≤ (2 * (C1 + C2 + C3 + C4) + 1)
        * ((Work.Kernels.scale τ) ^ (max (max (max N1 N2) N3) N4)
          * (1 + t) ^ (max (max (max M1 M2) M3) M4)
          * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4)) :=
        mul_le_mul_of_nonneg_right hcc hY0
    _ = (2 * (C1 + C2 + C3 + C4) + 1) * (Work.Kernels.scale τ)
          ^ (max (max (max N1 N2) N3) N4) * (1 + t) ^ (max (max (max M1 M2) M3) M4)
          * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Ept z‖ ^ 6 + ‖Ept z‖ ^ 4) := by ring

theorem Bracket24ExpansionHold_proof (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖Work.Asymptotics.KhatE1Core.KPlus24Group ℓ τ z
            + Work.Asymptotics.KhatE1Core.KMinus24Group ℓ τ z
            - Work.Asymptotics.KhatE1Core.Bracket24E2' ℓ τ z * (Work.Residues.Ept z) ^ 2
            - Work.Asymptotics.KhatE1.Bracket24B3 ℓ τ * (Work.Residues.Ept z) ^ 3
            - Work.Asymptotics.KhatE1.Bracket24B5 ℓ τ * (Work.Residues.Ept z) ^ 5‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * ((‖Work.Kernels.qParamFun τ‖)⁻¹ * ‖Work.Residues.Ept z‖ ^ 6
                  + ‖Work.Residues.Ept z‖ ^ 4) :=
  Bracket24ExpansionHold_of_tail ℓ (Xtrunc2X_tail ℓ)

end

end Work.Asymptotics.KhatE1Core
