import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.KPlus_funnel_tail_eight
import Submission.Work.Asymptotics.KMinus_funnel_tail_eight
import Submission.Work.Asymptotics.KPlus_funnel_tail_twentyfour
import Submission.Work.Asymptotics.KMinus_funnel_tail_twentyfour
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Asymptotics.Compact.kplus8_tail_core
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.KernelFacts.psi2_T2
import Submission.Work.Kernels.KernelFacts.psi4_T2
import Submission.Work.Kernels.KernelFacts.KMinus_T2
import Submission.Work.Kernels.KernelFacts.KPlus_T2
import Submission.Work.Asymptotics.KhatE1Defs
import Submission.Work.Asymptotics.KhatE1.Kdev_strip_sharp

namespace Work.Asymptotics

open UpperHalfPlane

/-!
## The sharp funnel tail of `K̂`, from the sharp strip bound

Write `E := K̂ - Ĝ = (K₊ - 𝒢₊)/2 - (K₋ - 𝒢₋)/2` (`Work.Asymptotics.Kdev`).  With the two exact
algebraic decompositions

* `K₊^{(8)}(τ,z) - 𝒢₊^{(8)}(τ,z) = tailC⁻¹(Φ₁+Φ₂+Φ₃)` (`Compact.KPlus8_sub_Gplus8_decomp`);
* `3456π·(K₋^{(d)}(τ,z) - 𝒢₋^{(d)}(τ,z)) = -(Sh τ z)⁻¹ (br + Sh·br0)` (`Compact.tail_identity`),

(`Khat8_sub_Ghat8_eq` below) the deviation is exactly the explicit bracket expression in which
the cusp expansion is analysed.

The sharp bound

  `‖Kdev τ z‖ ≤ C ‖q(τ)‖ (scale τ)^N (1+t)^M e^{-πt}`

is proved on the whole vertical strip `0 ≤ Re z ≤ 1`, `Im z = t` with `t ≥ Im τ + 1` in
`Work.Asymptotics.KhatE1.Kdev_strip_sharp` (via the `S`-transport to the cusp-`0` tile `E` and
the sharp bound `Kdev_cusp0_strip_sharp` there).  The target's contour `z = i t` is the
boundary line `Re z = 0` of that strip, so the target follows immediately.
-/

/-- **Reduction of the target to the explicit bracket expressions** (dimension 8).  For
`j τ ≠ j z` and `Sh τ z ≠ 0` the deviation `K̂ - Ĝ` equals
`(tailC⁻¹(Φ₁+Φ₂+Φ₃) + (3456π)⁻¹Sh⁻¹(br + Sh·br0))/2`, exactly the form in which the cusp
expansion is analysed in `KMinus_funnel_tail_eight` / `KPlus_funnel_tail_eight`. -/
theorem Khat8_sub_Ghat8_eq (ℓ : Work.Kernels.LogLambdaData) (τ z : ℍ)
    (hJ : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z)
    (hSh : Work.Asymptotics.Compact.Sh τ z ≠ 0) :
    Work.Kernels.Khat ℓ 8 τ z
        - (Work.Asymptotics.Compact.Gplus 8 τ z
            - Work.Asymptotics.Compact.Gminus 8 ℓ τ z) / 2
      = (Work.Asymptotics.Compact.tailC⁻¹ *
            (Work.Asymptotics.Compact.PhiMain τ z + Work.Asymptotics.Compact.PhiDiv τ z
              + Work.Asymptotics.Compact.PhiCorr τ z)
          + (3456 * (Real.pi : ℂ))⁻¹ * (Work.Asymptotics.Compact.Sh τ z)⁻¹ *
              (Work.Asymptotics.Compact.brMinus ℓ 8 τ z
                + Work.Asymptotics.Compact.Sh τ z * Work.Asymptotics.Compact.br0 8 ℓ τ z))
          / 2 := by
  have h1 := Work.Asymptotics.Compact.KPlus8_sub_Gplus8_decomp τ z hJ
  have h2 := Work.Asymptotics.Compact.tail_identity ℓ 8 (Or.inl rfl) τ z hSh
  have h3 : Work.Asymptotics.Compact.Gplus 8 τ z = Work.Asymptotics.Compact.Gplus8 τ z := by
    rw [Work.Asymptotics.Compact.Gplus]; simp
  have h4 : Work.Asymptotics.Compact.Gminus 8 ℓ τ z
      = Work.Asymptotics.Compact.Gminus8 ℓ τ z := by
    rw [Work.Asymptotics.Compact.Gminus]; simp
  rw [h3, h4]
  have hp : ((3456 : ℂ) * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero (by norm_num) Work.Asymptotics.Compact.pi_ne_zero_complex
  have h5' : Work.Kernels.KMinus ℓ 8 τ z - Work.Asymptotics.Compact.Gminus 8 ℓ τ z
      = -((3456 * (Real.pi : ℂ))⁻¹) * (Work.Asymptotics.Compact.Sh τ z)⁻¹ *
          (Work.Asymptotics.Compact.brMinus ℓ 8 τ z
            + Work.Asymptotics.Compact.Sh τ z * Work.Asymptotics.Compact.br0 8 ℓ τ z) := by
    refine mul_left_cancel₀ hp ?_
    rw [h2]
    field_simp
  have h5 : Work.Kernels.KMinus ℓ 8 τ z - Work.Asymptotics.Compact.Gminus8 ℓ τ z
      = -((3456 * (Real.pi : ℂ))⁻¹) * (Work.Asymptotics.Compact.Sh τ z)⁻¹ *
          (Work.Asymptotics.Compact.brMinus ℓ 8 τ z
            + Work.Asymptotics.Compact.Sh τ z * Work.Asymptotics.Compact.br0 8 ℓ τ z) := by
    rw [← h4]; exact h5'
  rw [Work.Kernels.Khat]
  have hkey : (Work.Kernels.KPlus 8 τ z - Work.Kernels.KMinus ℓ 8 τ z) / 2
        - (Work.Asymptotics.Compact.Gplus8 τ z - Work.Asymptotics.Compact.Gminus8 ℓ τ z) / 2
      = ((Work.Kernels.KPlus 8 τ z - Work.Asymptotics.Compact.Gplus8 τ z)
          - (Work.Kernels.KMinus ℓ 8 τ z - Work.Asymptotics.Compact.Gminus8 ℓ τ z)) / 2 := by
    ring
  rw [hkey, h1, h5]
  ring

/-- **Sharp funnel tail of `K̂ = (K₊ - K₋)/2` with one extra power of the cusp parameter
`q(τ) = e^{2πiτ}`.**

For `τ ∈ 𝔽 = {τ ∈ 𝒟 : 2 ≤ Im τ}` and `z = i t` with `t ≥ Im τ + 1`, the deviation of `K̂` from
its cusp model `Ĝ = (𝒢₊ - 𝒢₋)/2` is `O(‖q(τ)‖ (scale τ)^N (1+t)^M e^{-πt})`.  This is one power
of `‖q(τ)‖ = e^{-2π Im τ}` stronger than the sharp individual estimates
(`Work.Asymptotics.KPlus8_funnel_tail_sharp` gives `D₊ = O(poly · e^{-2π(t-Im τ)})`, which only
reaches the `e^{-πt}` rate in the band `t ≥ 2 Im τ`).

*Reduction.*  `K̂(τ,z) = -τ^{-d/2} K(S•τ,z)` and `Ĝ(τ,z) = -τ^{-d/2} 𝒢(S•τ,z)`
(`Work.Kernels.Khat_eq_neg_slash`, `Work.Asymptotics.Kfun_S_smul`), so this says that the *sum*
`K - 𝒢 = (D₊ + D₋)/2` on the cusp-`0` tile `E = S(𝔽)` satisfies
`‖(K - 𝒢)(u, i t)‖ ≤ C poly(scale u) ‖q(S•u)‖ (1+t)^M e^{-πt}` for `u ∈ E`, `t ≥ Im(S•u) + 1`.
Equivalently, `K̂ - Ĝ` decays one `q(τ)`-power faster than either deviation `D₊`, `D₋`.

The bound is proved on the whole strip `0 ≤ Re z ≤ 1`, `Im z = t` in
`Work.Asymptotics.KhatE1.Kdev_strip_sharp`; the contour `z = i t` is its boundary line
`Re z = 0`. -/
theorem Khat_funnel_tail_sharp_core (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        (z : ℂ) = (t : ℂ) * Complex.I →
        ‖Work.Kernels.Khat ℓ d τ z
            - (Work.Asymptotics.Compact.Gplus d τ z
                - Work.Asymptotics.Compact.Gminus d ℓ τ z) / 2‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
              * Real.exp (-(Real.pi * t)) := by
  obtain ⟨C, N, M, hC, hN, hM, hh⟩ :=
    Work.Asymptotics.KhatE1.Kdev_strip_sharp ℓ d hd
  refine ⟨C, N, M, hC, hN, hM, ?_⟩
  intro τ z t hτ ht hz
  have hzre : z.re = 0 := by
    have h := congrArg Complex.re hz
    simpa using h
  have hzim : z.im = t := by
    have h := congrArg Complex.im hz
    simpa using h
  have hstrip := hh τ z t hτ ht (le_of_eq hzre.symm) (by rw [hzre]; norm_num) hzim
  simpa only [Kdev] using hstrip

end Work.Asymptotics
