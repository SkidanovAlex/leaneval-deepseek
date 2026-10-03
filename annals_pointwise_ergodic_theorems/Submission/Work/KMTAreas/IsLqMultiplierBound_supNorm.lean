/-
# The symbol of a bounded `Lᵖ` Fourier multiplier is bounded by the multiplier norm

For `1 ≤ p < ∞`, a continuous `φ : ℝ → ℂ` whose Fourier multiplier `T_φ = 𝓕⁻ ∘ (φ · 𝓕)`
satisfies `‖T_φ f‖_{Lᵖ} ≤ M ‖f‖_{Lᵖ}` on Schwartz functions (the predicate
`Work.Analysis.IWMultiplier.IsLqMultiplierBound p φ M`) is bounded pointwise by `M`:
`‖φ x‖ ≤ M` for every `x`.

## The argument

Fix `x₀` and a normalised bump `ρ` of compact support.  The *mollified symbol*

`θ_n(ξ) = ∫ b, ρ_n(b) · φ(ξ + b)`   (`ρ_n` the family of `SupNorm.exists_mollifier_family`)

satisfies the same multiplier bound as `φ`, with the same constant, because `T_{φ(·+b)}` has the
same `Lᵖ` bound for every `b` (`SupNorm.IsLqMultiplierBound_comp_add`) and `T` is linear in the
symbol, so `T_{θ_n}` is an average of translates (`SupNorm.isLqMultiplierBound_mollify_continuous`, a Fubini
argument on the compact support of `ρ_n`).  Being `C²` with compactly supported data, `θ_n` can be
tested on the wave packet `f_δ = 𝓕⁻(η((· - x₀)/δ))`: the splitting
`T_{θ_n} f_δ = θ_n(x₀)·f_δ + 𝓕⁻((θ_n - θ_n(x₀))·η_{x₀,δ})` and the decay estimate for the second
term give `‖θ_n x₀‖ ≤ M` (`SupNorm.supNorm_smooth`).  Finally `θ_n x₀ → φ x₀` by the
approximate-identity property of `ρ_n` (`SupNorm.mollify_tendsto`), and passing to the limit gives
`‖φ x₀‖ ≤ M`.  Since `x₀` was arbitrary, this is the claim.
-/
import Mathlib
import Submission.Work.KMTAreas.SupNorm.eLpNorm_wavePacket_and_kernel
import Submission.Work.KMTAreas.SupNorm.contDiff_two_mollify
import Submission.Work.KMTAreas.SupNorm.mollify_tendsto
import Submission.Work.KMTAreas.SupNorm.exists_mollifier_family
import Submission.Work.KMTAreas.SupNorm.isLqMultiplierBound_mollify_continuous
import Submission.Work.KMTAreas.SupNorm.norm_fourierInv_error_le
import Submission.Work.KMTAreas.SupNorm.eLpNorm_error_le
import Submission.Work.KMTAreas.SupNorm.supNorm_smooth

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped ENNReal NNReal FourierTransform
open MeasureTheory Filter

namespace Work.KMTAreas

open Work.KMTAreas.SupNorm

theorem IsLqMultiplierBound_supNorm {p : ENNReal} (hp1 : 1 ≤ p) (hp2 : p < ⊤)
    {φ : ℝ → ℂ} (hφc : Continuous φ) {M : NNReal}
    (h : Work.Analysis.IWMultiplier.IsLqMultiplierBound p φ M) :
    ∀ x : ℝ, ‖φ x‖ ≤ (M : ℝ) := by
  intro x₀
  -- the two analytic facts about the wave packet and its normalising constant
  have hpk := eLpNorm_wavePacket_and_kernel (p := p) hp1 hp2
  obtain ⟨c₀, hc₀, hker⟩ := hpk.1

  -- a normalised bump family of shrinking compact support
  obtain ⟨ρ, hρc, hρs, hρnn, hρ1, hρsupp⟩ := exists_mollifier_family
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := M.coe_nonneg
  -- for every `n` the mollified symbol is bounded by `M` at `x₀`
  have hbd : ∀ n : ℕ,
      ‖(fun ξ : ℝ => ∫ b, ((ρ n b : ℝ) : ℂ) * φ (ξ + b)) x₀‖ ≤ (M : ℝ) := by
    intro n
    let θ : ℝ → ℂ := fun ξ => ∫ b, ((ρ n b : ℝ) : ℂ) * φ (ξ + b)
    have hθ : ContDiff ℝ 2 θ := contDiff_two_mollify hφc (hρc n) (hρs n)
    exact supNorm_smooth (p := p) (x₀ := x₀) (M := (M : ℝ)) hp1 hp2 hθ hMnn hc₀ hker hpk.2
      (fun {E : ℝ → ℂ} {A B ν δ Kb : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hKb : 0 ≤ Kb)
          (hν : 0 ≤ ν) (hν1 : ν ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
          (hE : ∀ x : ℝ, x ≠ 0 → ‖E x‖ ≤ min A (B / x ^ 2))
          (hAb : A ≤ ν * δ * etaI0) (hBb : B ≤ Kb * (ν / δ + 1))
          (hEm : AEStronglyMeasurable E volume) =>
        eLpNorm_error_le (p := p) hp1 hp2 hA hB hKb hν hν1 hδ hδ1 hE hAb hBb hEm)
      (fun {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ν C₁ C₂ : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1)
          (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂)
          (hν : ∀ y ∈ Metric.closedBall x₀ δ, ‖θ y - θ x₀‖ ≤ ν)
          (hC₁ : ∀ y ∈ Metric.closedBall x₀ δ, ‖deriv θ y‖ ≤ C₁)
          (hC₂ : ∀ y ∈ Metric.closedBall x₀ δ, ‖iteratedDeriv 2 θ y‖ ≤ C₂) =>
        norm_fourierInv_error_le hθ hδ hδ1 hν0 hν1 hC₁0 hC₂0 hν hC₁ hC₂)
      (fun δ hδ hδ1 =>
        isLqMultiplierBound_mollify_continuous (p := p) hp1 hp2 hφc h (hρc n).continuous (hρs n) (hρnn n) (hρ1 n)
          (f := wavePacket x₀ δ hδ)
          (HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x₀ δ)
            (wavePacket_fourier_support hδ)))
  -- the mollified values converge to `φ x₀`
  exact le_of_tendsto
    ((continuous_norm.tendsto (φ x₀)).comp (mollify_tendsto hφc x₀ ρ hρ1 hρnn hρsupp))
    (Filter.Eventually.of_forall hbd)

end Work.KMTAreas
