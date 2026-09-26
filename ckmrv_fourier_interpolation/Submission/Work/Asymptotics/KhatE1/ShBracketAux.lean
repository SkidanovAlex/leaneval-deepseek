import Mathlib
import Submission.Work.Asymptotics.KhatE1.Bracket24Defs
import Submission.Work.Asymptotics.KhatE1.KPlus24SharpStrip
import Submission.Work.Asymptotics.Compact.kminus_tail_core

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

noncomputable section

/-!
# `Sh`-cleared helpers for the `d = 24` funnel bracket

This module collects the `Sh`-cleared formulation of the sharp `d = 24` bracket bound
(`Bracket24SharpCleared`), the decomposition identities for the `Sh`-cleared bracket, and the
reduction of the target `Kdev24BracketSharp` to the `Sh`-cleared bound.  It is separated from
`KhatE1/Kdev24BracketSharp.lean` so that the (large) `Sh`-cleared chain proving the bound is
*below* the target's file in the import graph.
-/

/-! ## The `Sh`-cleared decomposition of the bracket

`Sh`-clearing is the natural formulation of the sharp bound: it removes the division by
`j(τ)-j(z)`.  The two identities below record the resulting expression. -/

/-- **The `Sh`-cleared `K₊`-decomposition** (`K24F.KPlus24_diff` + `Compact.Sh_eq`):
`Sh τ z·(K₊^{(24)} - 𝒢₊^{(24)}) = -c z²(Sm1+…+Sm5)`. -/
theorem Sh_mul_KPlus24_sub_Gplus24 (τ z : UpperHalfPlane) (hE4 : Work.Kernels.E4Fun z ≠ 0)
    (hSh : Work.Asymptotics.Compact.Sh τ z ≠ 0) :
    Work.Asymptotics.Compact.Sh τ z
        * (Work.Kernels.KPlus 24 τ z - Work.Asymptotics.Compact.Gplus 24 τ z)
      = -(Work.Asymptotics.K24F.c * (z : ℂ) ^ 2
          * (Work.Asymptotics.K24F.Sm1 τ z + Work.Asymptotics.K24F.Sm2 τ z
              + Work.Asymptotics.K24F.Sm3 τ z + Work.Asymptotics.K24F.Sm4 τ z
              + Work.Asymptotics.K24F.Sm5 τ z)) := by
  have hJ : Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z ≠ 0 := by
    intro h0
    exact hSh (by rw [Work.Asymptotics.Compact.Sh_eq τ z, h0, mul_zero, neg_zero])
  have h := Work.Asymptotics.K24F.KPlus24_diff τ z hJ hE4
  rw [Work.Asymptotics.Compact.Sh_eq τ z]
  rw [show -(Work.Kernels.DeltaFun z
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z))
        * (Work.Kernels.KPlus 24 τ z - Work.Asymptotics.Compact.Gplus 24 τ z)
      = -(Work.Kernels.DeltaFun z
          * (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z)
        * (Work.Kernels.KPlus 24 τ z - Work.Asymptotics.Compact.Gplus 24 τ z)) from by ring]
  rw [h]

/-- **The `Sh`-cleared bracket.** -/
theorem Sh_mul_Bracket24 (ℓ : Work.Kernels.LogLambdaData) (τ z : UpperHalfPlane)
    (hE4 : Work.Kernels.E4Fun z ≠ 0) (hSh : Work.Asymptotics.Compact.Sh τ z ≠ 0) :
    Work.Asymptotics.Compact.Sh τ z * Bracket24 ℓ τ z
      = -(Work.Asymptotics.K24F.c * (z : ℂ) ^ 2
            * (Work.Asymptotics.K24F.Sm1 τ z + Work.Asymptotics.K24F.Sm2 τ z
                + Work.Asymptotics.K24F.Sm3 τ z + Work.Asymptotics.K24F.Sm4 τ z
                + Work.Asymptotics.K24F.Sm5 τ z))
        + Work.Asymptotics.Compact.Sh τ z
            * (((3456 : ℂ) * (Real.pi : ℂ))⁻¹
                * (Work.Residues.Ept z * (Work.Asymptotics.Compact.R24 ℓ τ z
                    - Work.Asymptotics.Compact.R24_p0 ℓ τ)
                  + Work.Asymptotics.Compact.Dev24Sum ℓ τ z
                  - Am24 ℓ τ * Work.Residues.Ept z)) := by
  rw [Bracket24, mul_add, Sh_mul_KPlus24_sub_Gplus24 τ z hE4 hSh]

/-- **The `Sh`-cleared form of the sharp `d = 24` bracket bound.** -/
def Bracket24SharpCleared (ℓ : Work.Kernels.LogLambdaData) : Prop :=
  ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
    ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
      0 ≤ z.re → z.re ≤ 1 → z.im = t →
      ‖Work.Asymptotics.Compact.Sh τ z * Bracket24 ℓ τ z‖
        ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
            * Real.exp (-(2 * Real.pi * t))

/-- `Sh τ z` is bounded below by `1/16` on the strip `τ ∈ 𝔽`, `Im τ + 1 ≤ Im z`. -/
theorem Sh_norm_lower_strip (τ z : UpperHalfPlane) (hτ : Work.Asymptotics.Funnel τ)
    (htz : τ.im + 1 ≤ z.im) : (1 / 16 : ℝ) ≤ ‖Work.Asymptotics.Compact.Sh τ z‖ := by
  rw [Work.Asymptotics.Compact.Sh_eq τ z, norm_neg]
  exact KPlus24Strip.divisor_lower_strip τ z hτ htz

/-- `Sh τ z ≠ 0` on the strip `τ ∈ 𝔽`, `Im τ + 1 ≤ Im z`. -/
theorem Sh_ne_zero_strip (τ z : UpperHalfPlane) (hτ : Work.Asymptotics.Funnel τ)
    (htz : τ.im + 1 ≤ z.im) : Work.Asymptotics.Compact.Sh τ z ≠ 0 := by
  intro h0
  have h1 := Sh_norm_lower_strip τ z hτ htz
  rw [h0, norm_zero] at h1
  exact absurd h1 (by norm_num)

/-- **The target follows from the `Sh`-cleared bound**, since `‖Sh τ z‖ ≥ 1/16` on the strip. -/
theorem Kdev24BracketSharp_of_cleared (ℓ : Work.Kernels.LogLambdaData)
    (h : Bracket24SharpCleared ℓ) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        0 ≤ z.re → z.re ≤ 1 → z.im = t →
        ‖Bracket24 ℓ τ z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * t)) := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  refine ⟨16 * C, N, M, by linarith [hC], hN, hM, ?_⟩
  intro τ z t hF ht hz0 hz1 hzt
  have htz : τ.im + 1 ≤ z.im := by rw [hzt]; exact ht
  have hSh := Sh_norm_lower_strip τ z hF htz
  have hShpos : (0 : ℝ) < ‖Work.Asymptotics.Compact.Sh τ z‖ :=
    lt_of_lt_of_le (by norm_num) hSh
  have h16 : (‖Work.Asymptotics.Compact.Sh τ z‖)⁻¹ ≤ 16 := by
    rw [inv_le_comm₀ hShpos (by norm_num : (0 : ℝ) < 16)]
    have h : ((16 : ℝ))⁻¹ = 1 / 16 := by norm_num
    rw [h]
    exact hSh
  have hb' := hb τ z t hF ht hz0 hz1 hzt
  have hnorm : ‖Bracket24 ℓ τ z‖
      = ‖Work.Asymptotics.Compact.Sh τ z * Bracket24 ℓ τ z‖
          * (‖Work.Asymptotics.Compact.Sh τ z‖)⁻¹ := by
    rw [norm_mul]
    field_simp
  rw [hnorm]
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have hs0 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N :=
    Real.rpow_nonneg (Work.Kernels.scale_pos τ).le N
  have ht1 : (0 : ℝ) < 1 + t := by have := hF.2; linarith
  have ht0 : (0 : ℝ) ≤ (1 + t) ^ M := Real.rpow_nonneg ht1.le M
  have he0 : (0 : ℝ) ≤ Real.exp (-(2 * Real.pi * t)) := (Real.exp_pos _).le
  have hB0 : (0 : ℝ) ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N
      * (1 + t) ^ M * Real.exp (-(2 * Real.pi * t)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC.le hq0) hs0) ht0) he0
  have hstep : ‖Work.Asymptotics.Compact.Sh τ z * Bracket24 ℓ τ z‖
        * (‖Work.Asymptotics.Compact.Sh τ z‖)⁻¹
      ≤ (16 * C) * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
            * Real.exp (-(2 * Real.pi * t)) := by
    calc ‖Work.Asymptotics.Compact.Sh τ z * Bracket24 ℓ τ z‖
          * (‖Work.Asymptotics.Compact.Sh τ z‖)⁻¹
        ≤ (C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * t))) * 16 :=
          mul_le_mul hb' h16 (inv_nonneg.mpr hShpos.le) hB0
      _ = (16 * C) * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(2 * Real.pi * t)) := by ring
  exact hstep


end

end Work.Asymptotics.KhatE1
