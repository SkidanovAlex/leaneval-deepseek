import Mathlib
import Submission.Work.PARIMPL.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.PARIMPL2.Direct

open Complex

/-- Real arithmetic behind `4 (‖ζ‖ + λ) ≤ 1`: with `λR² ≤ 1` and `R ≥ 128` one has
`4 (4/R + λ) ≤ 16/R + 4/R² ≤ 1/8 + 1/8 ≤ 1`. -/
private lemma four_mul_four_div_add_le_one {R lam : ℝ} (hR : 128 ≤ R)
    (hlamR : lam * R ^ 2 ≤ 1) : 4 * (4 / R + lam) ≤ 1 := by
  have hRpos : 0 < R := by linarith
  have hR2 : 0 < R ^ 2 := by positivity
  have hl : lam ≤ 1 / R ^ 2 := by
    rw [le_div_iff₀ hR2]; linarith
  have h16 : 16 / R ≤ 1 / 8 := by
    rw [div_le_iff₀ hRpos]; linarith
  have h4l : 4 * lam ≤ 1 / 8 := by
    have h1 : 4 * lam ≤ 4 * (1 / R ^ 2) := mul_le_mul_of_nonneg_left hl (by norm_num)
    have h2 : 4 * (1 / R ^ 2) ≤ 1 / 8 := by
      rw [show (4 : ℝ) * (1 / R ^ 2) = 4 / R ^ 2 by ring, div_le_iff₀ hR2]
      nlinarith [hR]
    linarith
  have h : 4 * (4 / R + lam) = 16 / R + 4 * lam := by ring
  rw [h]; linarith

/-- `Work.PARIMPL.GoodTransitRot a h τ lam (R/4) u` follows from the strip facts `R/4+2 ≤ Re u ≤ π/λ - R/4`, `‖ecalPt a u‖ ≤ 4/R < r` and the slit condition at `u`, assuming `ParBounds h τ h1 A r`, `‖h1‖ ≤ B`, `‖τ-1‖ ≤ 1/8`, `4B/R + 16A/R² ≤ 3/8`, `λR² ≤ 1`, `R ≥ 128`.  (`‖h ζ - τ‖ ≤ A‖ζ‖² + B‖ζ‖ ≤ 16A/R² + 4B/R ≤ 3/8` and `‖h ζ - 1‖ ≤ 3/8 + 1/8 = 1/2`.) -/
theorem goodTransitRotOfStrip (lam R A B r : ℝ) (hlam : 0 < lam) (hR : 128 ≤ R)
    (hlamR : lam * R ^ 2 ≤ 1) (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (h : ℂ → ℂ) (τ h1 : ℂ) (hb : Work.PARIMPL.ParBounds h τ h1 A r)
    (hh1 : ‖h1‖ ≤ B) (hτ1 : ‖τ - 1‖ ≤ 1 / 8) (hAr : 4 * B / R + 16 * A / R ^ 2 ≤ 3 / 8)
    (u : ℂ) (hx1 : R / 4 + 2 ≤ u.re) (hx2 : u.re ≤ Real.pi / lam - R / 4)
    (hz : ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ ≤ 4 / R)
    (hzr : ‖Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u‖ < r)
    (hslit : Complex.sinh (((lam : ℂ) * Complex.I) * u) / ((lam : ℂ) * Complex.I)
      ∈ Complex.slitPlane) :
    Work.PARIMPL.GoodTransitRot ((lam : ℂ) * Complex.I) h τ lam (R / 4) u := by
  unfold Work.PARIMPL.GoodTransitRot
  set ζ := Work.Implosion.ecalPt ((lam : ℂ) * Complex.I) u with hζdef
  have hζn : ‖ζ‖ ≤ 4 / R := by rw [hζdef]; exact hz
  have hζr : ‖ζ‖ < r := by rw [hζdef]; exact hzr
  -- `‖h ζ - τ‖ ≤ A‖ζ‖² + B‖ζ‖ ≤ 3/8`
  have hτ' : ‖h ζ - τ‖ ≤ 3 / 8 := by
    have hpar := hb.2.2.1 ζ hζr
    have h1 : ‖h ζ - τ‖ ≤ A * ‖ζ‖ ^ 2 + B * ‖ζ‖ := by
      calc ‖h ζ - τ‖ = ‖(h ζ - τ - h1 * ζ) + h1 * ζ‖ := by congr 1; ring
        _ ≤ ‖h ζ - τ - h1 * ζ‖ + ‖h1 * ζ‖ := norm_add_le _ _
        _ ≤ A * ‖ζ‖ ^ 2 + B * ‖ζ‖ := by
            have h2 : ‖h1 * ζ‖ ≤ B * ‖ζ‖ := by
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_right hh1 (norm_nonneg ζ)
            linarith
    have hA : A * ‖ζ‖ ^ 2 ≤ 16 * A / R ^ 2 := by
      have h2 : ‖ζ‖ ^ 2 ≤ (4 / R) ^ 2 := pow_le_pow_left₀ (norm_nonneg ζ) hζn 2
      have h3 : A * ‖ζ‖ ^ 2 ≤ A * (4 / R) ^ 2 := mul_le_mul_of_nonneg_left h2 hA0
      have h4 : A * (4 / R) ^ 2 = 16 * A / R ^ 2 := by ring
      rwa [h4] at h3
    have hB : B * ‖ζ‖ ≤ 4 * B / R := by
      have h3 : B * ‖ζ‖ ≤ B * (4 / R) := mul_le_mul_of_nonneg_left hζn hB0
      have h4 : B * (4 / R) = 4 * B / R := by ring
      rwa [h4] at h3
    linarith
  -- `‖h ζ - 1‖ ≤ ‖h ζ - τ‖ + ‖τ - 1‖ ≤ 3/8 + 1/8 = 1/2`
  have h1' : ‖h ζ - 1‖ ≤ 1 / 2 := by
    calc ‖h ζ - 1‖ = ‖(h ζ - τ) + (τ - 1)‖ := by congr 1; ring
      _ ≤ ‖h ζ - τ‖ + ‖τ - 1‖ := norm_add_le _ _
      _ ≤ 1 / 2 := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, hb.2.2.2.1 ζ hζr, hslit⟩
  · exact (Work.Implosion.mem_transitStrip_iff lam (R / 4) u).mpr ⟨by linarith, hx2⟩
  · linarith
  · have h4 : 4 * (‖ζ‖ + lam) = 4 * ‖ζ‖ + 4 * lam := by ring
    have h5 : 4 * ‖ζ‖ ≤ 16 / R := by
      have h := mul_le_mul_of_nonneg_left hζn (by norm_num : (0 : ℝ) ≤ 4)
      have he : 4 * (4 / R) = 16 / R := by ring
      rwa [he] at h
    have h6 : 4 * (4 / R + lam) = 16 / R + 4 * lam := by ring
    have h7 := four_mul_four_div_add_le_one hR hlamR
    linarith [h4, h5, h6, h7]
  · linarith
  · linarith

end Work.PARIMPL2.Direct
