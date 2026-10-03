import Mathlib
import Submission.Work.KMTAreas.A7.fiberOpTex_eq_fiberOp_self_bdd

namespace Work.KMTAreas.A7Hi

open MeasureTheory

/-- **The fibre at the residue `0` of the packet `φ` is the exact-height projection itself.**
By definition `fiberOp ρ l φ 0` is the convolution with the kernel
`j ↦ (∑_{α ∈ (ℚ/ℤ)_l} e(-j α)) · cw φ j`, which is precisely the kernel `iwKernel` of the
Ionescu--Wainger symbol `iwSymbolSet (ℚ/ℤ)_l (periodize φ)`, and `Tex ρ l φ` is the IW
convolution with that symbol; the identification is
`Work.KMTAreas.A7.fiberOp_zero_eq_iwConv` plus the definition of `Tex`. -/
theorem fiberOp_zero_eq_Tex (ρ : ℝ) (l : ℕ) (φ : ℝ → ℂ) (hφ : MeasureTheory.Integrable φ)
    (f : ℤ → ℂ) :
    Work.KMTAreas.A7.fiberOp ρ l φ 0 f = Work.KMTAreas.A7.Tex ρ l φ f :=
  Work.KMTAreas.A7.fiberOp_zero_eq_iwConv ρ l φ hφ f

/-- **The narrow-band cut fixes the exact-height projection.**  With the §6 cutoff
`m_* = mStarF U = η_{≤ -2U}`, which is `1` on `[-2^{-2U-1}, 2^{-2U-1}]` and supported in
`[-2^{-2U}, 2^{-2U}]`, and with `φ` supported in `[-2^{-2U-1}, 2^{-2U-1}]` and the exact-height
arithmetic frequency set `(ℚ/ℤ)_l = iwArithFreqsNew ρ l` non-aliasing at the scale `-2U`, the
fiber of the twisted projection at the residue `0`

  `fiberOp ρ l (mStarF U) 0 u x = ∑'_j (∑_{α ∈ (ℚ/ℤ)_l} e(-jα)) · cw (mStarF U) j · u (x-j)`

leaves `Tex ρ l φ f` unchanged.  The plateau factor `m_*` disappears from the product of the
symbols by the aliasing/plateau collapse of §6 (`form-1`), and the resulting operator is the
exact-height projection itself (`fiberOp_zero_eq_Tex`).

This is the specialization to `n₀ = 0` and `B = C` of
`Work.KMTAreas.A7.fiberOpTex_eq_fiberOp_self_bdd` (`A7/fiberOpTex_eq_fiberOp_self_bdd.lean`),
which carries the whole aliasing/plateau computation. -/
theorem FiberOpTexFixNarrow (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l U : ℕ) (hU : 1 ≤ U)
    (hna : Work.Analysis.IonescuWainger.NonAliasing (-(2 * (U : ℤ)))
      (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l))
    (φ : ℝ → ℂ) (hφ : MeasureTheory.Integrable φ)
    (hφsum : Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw φ j‖))
    (hφsupp : ∀ ξ : ℝ, φ ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1))
    (f : ℤ → ℂ) (hf : ∃ C : ℝ, ∀ x : ℤ, ‖f x‖ ≤ C) :
    Work.KMTAreas.A7.fiberOp ρ l (Work.KMTAreas.A7.mStarF U) 0
      (Work.KMTAreas.A7.Tex ρ l φ f) = Work.KMTAreas.A7.Tex ρ l φ f := by
  obtain ⟨C, hC⟩ := hf
  rw [Work.KMTAreas.A7.fiberOpTex_eq_fiberOp_self_bdd ρ hρ hρ1 l U hU hna φ hφ hφsum hφsupp
    f C hC 0]
  exact fiberOp_zero_eq_Tex ρ l φ hφ f

end Work.KMTAreas.A7Hi
