import Mathlib
import Submission.Work.KMTAreas.A7LoLin.fareyModDiffK
import Submission.Work.KMTAreas.A7LoLin.fareyModKC
import Submission.Work.KMTAreas.A7LoLin.lepingle
import Submission.Work.KMTAreas.A7LoLin.main

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar

noncomputable section

/-- **The linear lacunary variational estimate at arithmetic height `0`, in the main regime**
— the paper's `(lin-1)` in the discrete setting, for the level-`0` modulated piece.

For `0 < ρ ≤ 1`, `1 < p < ∞`, `r > 2` and `Λ > 1` there is a constant `C` such that for every
`Λ`-lacunary scale sequence `a` with `a n ≥ 1`, every continuous scale `k` **with
`2^k ≤ ⌊a n⌋` for all `n`** (the paper's main regime, a necessary hypothesis: without it the
individual pieces have norm `≍ 2^k/⌊a n⌋`, so no uniform bound can hold — see the counterexample
recorded for the first version of this statement), every `t ∈ [1/2,1]` and every `f : ℤ → ℂ`,

  `‖ V^r (n ↦ T^0_{φ_{⌊a n⌋,t}} f) ‖_{ℓ^p(ℤ)} ≤ C ⟨k⟩² ‖f‖_{ℓ^p(ℤ)}`,

where `T^0_φ = Work.KMTAreas.A7.Tle ρ 0 φ` is the arithmetic-height-`0` Ionescu--Wainger
multiplier (the multiplier with symbol `periodize φ`, since `iwArithFreqs ρ 0 = {0}`) and
`φ_{N,t} = Work.KMTAreas.A7.varphiNt N k t = φ_N · e(N t ·)` is the paper's modulated piece.
The bound is uniform in `t ∈ [1/2,1]`, in `k` up to the polynomial factor `⟨k⟩²`, and in the
lacunary sequence; the multiplier family is the lacunary family of modulated band-pieces of `f`
(bump averages at the scales `2^{logN ⌊a n⌋ - k}` translated by `N t`).

This is the crux of `Work.KMTAreas.A7.LoModelLargeScale` (§8 of Krause--Mirek--Tao), where it is
combined with the variational product rule and Hölder's inequality, and where the main-regime
hypothesis is supplied by the guard.  Available tools: the shifted Calderón--Zygmund
square-function estimate `Work.Analysis.CzShift.cz_shift_square_function_of_symbol` (with
`λ_N = N t`, `A = 2^{-k}`, `K = O(k)`) and the KMSZ sampling principle
`Work.BourgainPlan.Thm52.decimatedKernel_lp.sampling_principle_variation_decimated_lp` /
`exists_thm52`; for the unmodulated part one may use Lépingle-type estimates for lacunary bump
convolutions (`Work.KMTAreas.A7.lacunaryBumpDilationVar`, for the bottom piece `k = 0`), split off
by `varphiNt N k t - varphiN N k` (which vanishes at the frequency origin). -/
theorem LoLinVar (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hpt : p < ⊤)
    (r : NNReal) (hr : 2 < r) (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ C : NNReal, ∀ (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a)
      (ha1 : ∀ n, 1 ≤ a n) (k : ℕ) (hkN : ∀ n, 2 ^ k ≤ Nat.floor (a n))
      (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1) (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ =>
            Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k t) f x))
        p MeasureTheory.Measure.count
        ≤ (C : ENNReal) * ENNReal.ofReal ((1 + (k : ℝ)) ^ 2)
          * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  exact Work.KMTAreas.A7LoLin.LoLinVar_of_pieces ρ hρ hρ1 p hp hpt r hr Λ hΛ
    (Work.KMTAreas.A7LoLin.lowpass0 ρ hρ hρ1 p hp hpt r hr Λ hΛ)
    (Work.KMTAreas.A7LoLin.fareyModKC ρ hρ hρ1 p hp hpt r hr Λ hΛ)
    (Work.KMTAreas.A7LoLin.fareyModDiffK ρ hρ hρ1 p hp hpt r hr Λ hΛ)
    (Work.KMTAreas.A7.Tle_varphiNt_single_scale ρ hρ 0 p hp hpt)


end

end Work.KMTAreas.A7
