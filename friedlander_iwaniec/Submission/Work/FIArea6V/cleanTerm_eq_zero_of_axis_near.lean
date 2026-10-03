import Mathlib
import Submission.Work.FIArea6V.CleanVDefs

namespace Work.FIArea6V

/-- In a "bad" angular range (the sector meets `±π`), every non-zero clean summand vanishes
under the axis-free hypothesis that `Work.FIArea6V.S16CleanCoreTwoA` carries on its polar box.

Clean-support analogue of the proved `Work.FIArea6Road.s16Term_eq_zero_of_axis_near` (same proof,
with the support hypothesis weakened from `SuppTau` to `IsPrimary`, which is all the pinned proof
uses): a nonzero summand forces `InPolarBox Pa φ z` (because `q` is supported on `[0,2πθ]`, `p` on
`(N,(1+θ)N]`, and `q 0 = 0`), hence `IsAxisFree` by `hax`; but the sector is within `2πθ` of a real
axis, so `|Im z| = √|z|²·|sin(arg z)| ≤ 2π√2θ√N ≤ ϑ√N`, contradicting axis-freeness. -/
lemma cleanTerm_eq_zero_of_axis_near (Pa : Work.FITop.Params) (φ : ℝ) (j : ℤ)
    (chi : GaussianInt → ℂ) (q p : ℝ → ℝ)
    (hax : ∀ z : GaussianInt, Work.FITop4.InPolarBox Pa φ z → Work.FITop4.IsAxisFree Pa z)
    (hqC : ContDiff ℝ 2 q)
    (hqsupp : ∀ α, q α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * Pa.θ)
    (hpsupp : ∀ u : ℝ, p u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N)
    (hsep : 2 * Real.pi * Real.sqrt 2 * Pa.θ ≤ Pa.ϑ) (hθ1 : Pa.θ ≤ 1)
    {z : GaussianInt} (hz : Work.FIPlan.IsPrimary z)
    (hsin : |Real.sin (Complex.arg z.toComplex)| ≤ 2 * Real.pi * Pa.θ) :
    Work.FIArea6Road.s16Term Pa φ j chi q p z = 0 := by
  by_cases hq : q (Complex.arg z.toComplex - φ) = 0
  · rw [Work.FIArea6Road.s16Term]; simp [hq]
  · by_cases hp : p (Work.FIPlan.gnorm z) = 0
    · rw [Work.FIArea6Road.s16Term]; simp [hp]
    · exfalso
      have hβ := hqsupp _ hq
      have hn := hpsupp _ hp
      have hq0 : q 0 = 0 := Work.FIArea6Hecke.mollQ_zero hqC hqsupp
      have hstrict : φ < (Complex.arg z.toComplex : ℝ) := by
        rcases lt_or_eq_of_le hβ.1 with h | h
        · linarith
        · exact absurd (h.symm ▸ hq0) hq
      have haxis := hax z ⟨hz, hn.1, hn.2, hstrict, by linarith [hβ.2]⟩
      have hgn : (Work.FIPlan.gnorm z : ℝ) ≤ (1 + Pa.θ) * Pa.N := hn.2
      have hs2 : (0 : ℝ) ≤ 1 + Pa.θ := by linarith [Pa.hθ0]
      have hsqrt_gn : Real.sqrt (Work.FIPlan.gnorm z : ℝ)
          ≤ Real.sqrt (1 + Pa.θ) * Real.sqrt Pa.N := by
        rw [← Real.sqrt_mul hs2]
        exact Real.sqrt_le_sqrt hgn
      have hsqrtθ : Real.sqrt (1 + Pa.θ) ≤ Real.sqrt 2 :=
        Real.sqrt_le_sqrt (by linarith)
      have him := Work.FIArea6Road.abs_im_toComplex_eq z
      have hbound : |((z.im : ℝ))| ≤ 2 * Real.pi * Real.sqrt 2 * Pa.θ * Real.sqrt Pa.N := by
        rw [him]
        calc Real.sqrt (Work.FIPlan.gnorm z : ℝ) * |Real.sin (Complex.arg z.toComplex)|
            ≤ (Real.sqrt (1 + Pa.θ) * Real.sqrt Pa.N) * (2 * Real.pi * Pa.θ) :=
              mul_le_mul hsqrt_gn hsin (abs_nonneg _) (by positivity)
          _ ≤ (Real.sqrt 2 * Real.sqrt Pa.N) * (2 * Real.pi * Pa.θ) := by
              refine mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hsqrtθ (Real.sqrt_nonneg _)) ?_
              have hπ : (0 : ℝ) ≤ 2 * Real.pi := by positivity
              exact mul_nonneg hπ (le_of_lt Pa.hθ0)
          _ = 2 * Real.pi * Real.sqrt 2 * Pa.θ * Real.sqrt Pa.N := by ring
      have hfin : |((z.im : ℝ))| ≤ Pa.ϑ * Real.sqrt Pa.N := by
        refine le_trans hbound ?_
        rw [show 2 * Real.pi * Real.sqrt 2 * Pa.θ * Real.sqrt Pa.N
            = (2 * Real.pi * Real.sqrt 2 * Pa.θ) * Real.sqrt Pa.N from by ring]
        exact mul_le_mul_of_nonneg_right hsep (Real.sqrt_nonneg _)
      exact absurd haxis.2 (not_lt.mpr hfin)

end Work.FIArea6V
