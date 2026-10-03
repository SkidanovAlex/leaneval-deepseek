import Mathlib
import Submission.Work.FIArea6V.CleanVDefs

set_option autoImplicit false

namespace Work.FIArea6V

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The clean §16 Fourier–Hecke identity in the "good" angular range.

This is the clean-support analogue of the proved `Work.FIArea6Road.boxTermSum_eq_freqSum`
(same proof, with `tsumTau` replaced by the unrestricted `Work.FIArea6Hecke.Tsum`,
`SuppTau` by `Work.FIArea6V.SuppClean`, and the axis clause dropped from the support):
for `-π ≤ φ ≤ π - 2πθ` the whole sector `[φ, φ+2πθ]` lies inside the principal range
`(-2π+2πθ, 2π]` of `β_z = arg z - φ`, so the mollifier `q` equals its Fourier series there
(`Work.FIArea6Road.TauHeartFserEqQ`), and regrouping the box sum by the norm
(`Work.FIArea6.TauPieces.CleanSumEqTsum` = `Work.FIArea6.S16CleanSum_eq_Tsum` together with
`Work.FIArea6Road.s16Core_mul_exp_eq`) gives
`Σ_z [SuppClean z] q(β_z)·g(z) = Σ'_ℓ q̂(ℓ)·e^{-iℓφ}·Tsum Pa χ (j+ℓ) p`. -/
theorem cleanBoxTermSum_eq_freqSum (Pa : Work.FITop.Params) (φ : ℝ) (j : ℤ)
    (chi : GaussianInt → ℂ) (q p : ℝ → ℝ)
    (hqC : ContDiff ℝ 2 q) (hq0 : ∀ α, 0 ≤ q α) (hq1 : ∀ α, q α ≤ 1)
    (hqsupp : ∀ α, q α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * Pa.θ)
    (hd2 : ∀ α, |iteratedDeriv 2 q α| ≤ 1048576 / Pa.θ ^ 2)
    (hpsupp : ∀ u : ℝ, p u ≠ 0 → Pa.N < u ∧ u ≤ (1 + Pa.θ) * Pa.N)
    (hθlt : Pa.θ < 1) (hφlo : -Real.pi ≤ φ) (hφhi : φ ≤ Real.pi - 2 * Real.pi * Pa.θ) :
    Work.FIArea6V.boxTermSumClean Pa φ j chi q p
      = ∑' ℓ : ℤ, Work.FIArea5.S16.fcoef q ℓ *
          Complex.exp (-((ℓ : ℂ) * Complex.I * (φ : ℂ)))
          * Work.FIArea6Hecke.Tsum Pa chi (j + ℓ) p := by
  classical
  -- Step 1: split off the angular factor `q(arg z − φ)` from the summand.
  have hstep1 : Work.FIArea6V.boxTermSumClean Pa φ j chi q p
      = ∑ z ∈ Work.FITop.boxN Pa,
          (if SuppClean Pa z then
            ((q (Complex.arg z.toComplex - φ) : ℝ) : ℂ)
              * Work.FIArea6Road.s16Core Pa j chi p z
            else 0) := by
    unfold Work.FIArea6V.boxTermSumClean
    refine Finset.sum_congr rfl (fun z _ => ?_)
    by_cases h : SuppClean Pa z
    · rw [if_pos h, if_pos h, Work.FIArea6Road.s16Term_eq]
    · rw [if_neg h, if_neg h]
  rw [hstep1, ← Finset.sum_filter]
  set s : Finset GaussianInt := (Work.FITop.boxN Pa).filter (fun z => SuppClean Pa z) with hsdef
  -- Step 2: on the clean support, `q` equals its Fourier series in the angle `arg z − φ`.
  have hser : ∀ z : GaussianInt, SuppClean Pa z →
      Work.FIArea6Road.fser q (Complex.arg z.toComplex - φ)
        = (q (Complex.arg z.toComplex - φ) : ℂ) := by
    intro z _
    refine Work.FIArea6Road.TauHeartFserEqQ q Pa.hθ0 hθlt hqC hq0 hq1 hqsupp hd2 ⟨?_, ?_⟩
    · have h1 : (-Real.pi : ℝ) < (Complex.arg z.toComplex : ℝ) := Complex.neg_pi_lt_arg _
      have h2 : φ - 2 * Real.pi + 2 * Real.pi * Pa.θ ≤ -Real.pi := by linarith
      linarith
    · have h1 : (Complex.arg z.toComplex : ℝ) ≤ Real.pi := Complex.arg_le_pi _
      linarith
  -- Step 3: each summand is the sum of its (absolutely convergent) Fourier series.
  have hsumm : ∀ z : GaussianInt, Summable (fun ℓ : ℤ =>
      (Work.FIArea5.S16.fcoef q ℓ * Complex.exp ((ℓ : ℂ) * Complex.I
        * (((Complex.arg z.toComplex - φ) : ℝ) : ℂ)))
        * Work.FIArea6Road.s16Core Pa j chi p z) := by
    intro z
    refine Summable.mul_right _ (Summable.of_norm_bounded
      (g := fun ℓ : ℤ => ‖Work.FIArea5.S16.fcoef q ℓ‖)
      (Work.FIArea6Road.summable_norm_fcoef q Pa.hθ0 (le_of_lt hθlt) hqC hq0 hq1 hqsupp hd2)
      (fun ℓ => ?_))
    rw [norm_mul, Work.FIArea6Road.norm_exp_int_mul_I, mul_one]
  have htsum : ∀ z ∈ s, ((q (Complex.arg z.toComplex - φ) : ℝ) : ℂ)
        * Work.FIArea6Road.s16Core Pa j chi p z
      = ∑' ℓ : ℤ, (Work.FIArea5.S16.fcoef q ℓ * Complex.exp ((ℓ : ℂ) * Complex.I
          * (((Complex.arg z.toComplex - φ) : ℝ) : ℂ)))
            * Work.FIArea6Road.s16Core Pa j chi p z := by
    intro z hz
    rw [Finset.mem_filter] at hz
    rw [← hser z hz.2, Work.FIArea6Road.fser, tsum_mul_right]
  set F : GaussianInt → ℤ → ℂ := fun z ℓ => (Work.FIArea5.S16.fcoef q ℓ
      * Complex.exp ((ℓ : ℂ) * Complex.I
        * (((Complex.arg z.toComplex - φ) : ℝ) : ℂ)))
          * Work.FIArea6Road.s16Core Pa j chi p z with hFdef
  rw [Finset.sum_congr rfl htsum]
  rw [(Work.FIArea6Road.tsum_finset_sum s (fun z => ∑' ℓ : ℤ, F z ℓ) F
      (fun z _ => (hsumm z).hasSum)).symm]
  -- Step 4: evaluate the inner (over the box) sum — this is the clean `Tsum`.
  refine tsum_congr (fun ℓ => ?_)
  have hinner : (∑ z ∈ s, Complex.exp ((ℓ : ℂ) * Complex.I
        * (((Complex.arg z.toComplex : ℝ)) : ℂ))
          * Work.FIArea6Road.s16Core Pa j chi p z)
      = Work.FIArea6Hecke.Tsum Pa chi (j + ℓ) p := by
    rw [← Work.FIArea6.S16CleanSum_eq_Tsum Pa chi (j + ℓ) p hpsupp]
    rw [Finset.sum_congr rfl (fun z _ =>
      (SuppClean_summand_eq Pa chi (j + ℓ) p z).symm)]
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun z hz => ?_)
    · exact hsdef
    · rw [Finset.mem_filter] at hz
      exact SuppClean_exp_mul_s16Core Pa j ℓ chi p hz.2
  have hexp : ∀ z : GaussianInt,
      Complex.exp ((ℓ : ℂ) * Complex.I * (((Complex.arg z.toComplex - φ) : ℝ) : ℂ))
        = Complex.exp (-((ℓ : ℂ) * Complex.I * (φ : ℂ)))
          * Complex.exp ((ℓ : ℂ) * Complex.I * ((Complex.arg z.toComplex : ℝ) : ℂ)) := by
    intro z
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hfac : ∀ z : GaussianInt,
      (Work.FIArea5.S16.fcoef q ℓ * Complex.exp ((ℓ : ℂ) * Complex.I
          * (((Complex.arg z.toComplex - φ) : ℝ) : ℂ)))
            * Work.FIArea6Road.s16Core Pa j chi p z
        = Work.FIArea5.S16.fcoef q ℓ * Complex.exp (-((ℓ : ℂ) * Complex.I * (φ : ℂ)))
          * (Complex.exp ((ℓ : ℂ) * Complex.I * ((Complex.arg z.toComplex : ℝ) : ℂ))
            * Work.FIArea6Road.s16Core Pa j chi p z) := by
    intro z
    rw [hexp z]
    ring
  rw [Finset.sum_congr rfl (fun z _ => hfac z), ← Finset.mul_sum, hinner]

end

end Work.FIArea6V
