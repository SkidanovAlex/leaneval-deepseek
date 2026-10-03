import Mathlib
import Submission.Work.KMTAreas.A7.randSymb_schwartz
import Submission.Work.KMTAreas.A7.cw_etaCut_decay
import Submission.Work.KMTAreas.A7.LacDevBasics

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped FourierTransform

/-
The Fourier coefficient sequence of the modulated Schwartz bump `φ_{N,t} = φ_N · e(Nt·)`
(`varphiNt`, a compactly supported smooth function times a modulation) is absolutely summable:
`cw (varphiNt N k t) j = ∫ θ, varphiNt N k t θ * ee (-(j*θ))`, which is the Fourier transform of
the Schwartz function `varphiNtSch N k t` evaluated at `j`.
Prove it via the workspace's `varphiNtSch` (`Submission/Work/KMTAreas/A7/randSymb_schwartz.lean`,
with `varphiNtSch_apply`) and the Schwartz decay of its Fourier transform
(`Commons.Analysis.Fourier.schwartzMap_real_decay`, in the `Submission/Commons/Analysis/Fourier/`
directory), *without* importing `Submission.Work.KMTAreas.A7.SmallKernMassBasics` (that module is
reported broken) and without importing anything under `Submission/Work/KMTAreas/A7c/`.
-/

/-- **`cw (varphiNt N k t) j` is the Fourier transform of the Schwartz function
`varphiNtSch N k t` at the integer frequency `j`.**

The modulated bump is `C^∞` with compact support, so it is realised by the Schwartz map
`varphiNtSch N k t` (`varphiNtSch_coe`); the bridge `cw_eq_fourierTransform` identifies `cw m j`
with the Fourier transform `𝓕 m (j:ℝ)` of `m`, and `SchwartzMap.fourier_coe` transports that to
the Schwartz-map Fourier transform. -/
lemma cw_varphiNt_eq_fourierSch (N k : ℕ) (t : ℝ) (j : ℤ) :
    cw (varphiNt N k t) j
      = ((𝓕 (varphiNtSch N k t) : SchwartzMap ℝ ℂ) : ℝ → ℂ) (j : ℝ) := by
  rw [cw_eq_fourierTransform, ← varphiNtSch_coe, SchwartzMap.fourier_coe]

/-- The Schwartz decay of the Fourier transform of `varphiNtSch N k t` (order `2`) makes the
Fourier-coefficient sequence absolutely summable: `(1 + |j|)^{-2}` is summable on `ℤ`
(`summable_int_one_add_abs_neg_two`). -/
theorem cw_varphiNt_summable (N k : ℕ) (t : ℝ) :
    Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.varphiNt N k t) j‖) := by
  obtain ⟨B, _hBpos, hBdec⟩ :=
    Commons.Analysis.Fourier.schwartzMap_real_decay (𝓕 (varphiNtSch N k t)) 2
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    ((summable_int_one_add_abs_neg_two).mul_left B)
  rw [cw_varphiNt_eq_fourierSch]
  simpa using hBdec (j : ℝ)

end Work.KMTAreas.A7
