/-
# The repaired §6 model kernels of Area A7 (`ModelApproxHiRep`)

Vocabulary for the proof of `Work.KMTAreas.A7.ModelApproxHiRep`, the §6 model approximation of
Krause--Mirek--Tao at the *repaired* window `uRep ρ l₁ l₂ k₁ k₂ = max (uScale ρ L) (max l₁ l₂ + 3)`
(`L = max (max l₁ l₂) (max k₁ k₂)`), i.e. the same model as `Large.Defs.modelTupleRep` but at the
level of the *kernels*.

* `hiKmodNU ρ P U N l₁ l₂ k₁ k₂` — the kernel of the §6 model operator with an *arbitrary* window
  parameter `U` (the `t`-integral of the composed kernel);
* `hiFibreKer ρ P U N l₁ l₂ k₁ k₂` — the *fibre form* of that kernel, the double sum over the
  arithmetic fibres `(ℚ/ℤ)_{l₁} × (ℚ/ℤ)_{l₂}` of the corresponding Fourier coefficients;
* `hiKmodNRep`, `hiKmodRep` — the same at the repaired window `uRep`;
* `hiM0Ker ρ P N l₁ l₂ k₁ k₂` — the fibre form of the *difference* `hiKconcN - hiKmodNRep` (the
  fibres carry the §6 symbol difference `M0 = weylAvg - m_Ẑ m̃_{N,ℝ}`).

The three mathematical inputs are then

* `hiKmodNU_fibre` (`RepFibre.lean`): the model kernel with window `U` *equals* its fibre form,
  under the non-aliasing and support hypotheses of §6;
* the difference identity (`RepDiff.lean`): on the band the difference of the two kernels is
  `hiM0Ker`;
* the mass bound (`RepMass.lean`): `∑_p ‖hiM0Ker p‖ ≲ 2^{A 2^{ρL}} N⁻¹`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.ModelApproxHiKernels

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.EndVar Work.Analysis.IWMultiplier

/-- **The kernel of the §6 model operator with an arbitrary window parameter `U`**: the
`t`-integral over `(1/2,1]` of the composition of the twisted kernel `hiTwKernel` (with the band
cutoffs `m_*`, `m̃_*` at the window `U`) with the two exact-height kernels of the modulated bumps.

At `U = uScale ρ L` this is `hiKmodN`; at `U = uRep ρ l₁ l₂ k₁ k₂` it is `hiKmodNRep`. -/
noncomputable def hiKmodNU (ρ : ℝ) (P : ℤ[X]) (U N : ℕ) (l₁ l₂ k₁ k₂ : ℕ) : ℤ → ℤ → ℂ :=
  fun j₁ j₂ => ∫ t in (1/2 : ℝ)..1,
    kernComp (hiTwKernel ρ P l₁ l₂ (mStarF U) (mStargF P.natDegree U))
      (hiKer ρ l₁ (varphiNt N k₁ t))
      (hiKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) j₁ j₂

/-- **The fibre form of the §6 model kernel**: the double sum over the arithmetic fibres
`(ℚ/ℤ)_{l₁} × (ℚ/ℤ)_{l₂}` of `e(-j₁α)e(-j₂β) m_Ẑ(α,β)` times the `θ`-integral of
`m_*(θ₁)m̃_*(θ₂)φ_N(θ₁)φ̃_N(θ₂)m̃_{N,ℝ}(θ₁,θ₂)e(-j₁θ₁-j₂θ₂)`. -/
noncomputable def hiFibreKer (ρ : ℝ) (P : ℤ[X]) (U N : ℕ) (l₁ l₂ k₁ k₂ : ℕ) : ℤ → ℤ → ℂ :=
  fun j₁ j₂ =>
    ∑ p ∈ (diffFreqs ρ l₁).product (diffFreqs ρ l₂),
      fourier (T := 1) (-j₁) p.1 * fourier (T := 1) (-j₂) p.2
        * mZ P (arithQ ρ (max l₁ l₂)) p.1 p.2
        * (∫ θ₁ : ℝ, ∫ θ₂ : ℝ,
            mStarF U θ₁ * mStargF P.natDegree U θ₂
            * varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
            * mTilde P N θ₁ θ₂
            * ee (-((j₁ : ℝ) * θ₁ + (j₂ : ℝ) * θ₂)))

/-- **The kernel of the §6 model operator at the repaired window** `uRep ρ l₁ l₂ k₁ k₂`. -/
noncomputable def hiKmodNRep (ρ : ℝ) (P : ℤ[X]) (N : ℕ) (l₁ l₂ k₁ k₂ : ℕ) : ℤ → ℤ → ℂ :=
  hiKmodNU ρ P (uRep ρ l₁ l₂ k₁ k₂) N l₁ l₂ k₁ k₂

/-- The repaired model kernel at the scale `N = ⌊a n⌋`. -/
noncomputable def hiKmodRep (ρ : ℝ) (P : ℤ[X]) (a : ℕ → NNReal)
    (l₁ l₂ k₁ k₂ n : ℕ) : ℤ → ℤ → ℂ :=
  hiKmodNRep ρ P (Nat.floor (a n)) l₁ l₂ k₁ k₂

/-- **The fibre form of the kernel difference `hiKconcN − hiKmodNRep`**: the same double fibre sum
but with the arithmetic symbol `m_Ẑ m̃_{N,ℝ}` replaced by the §6 symbol difference
`M0 = weylAvg − m_Ẑ m̃_{N,ℝ}`. -/
noncomputable def hiM0Ker (ρ : ℝ) (P : ℤ[X]) (N : ℕ) (l₁ l₂ k₁ k₂ : ℕ) : ℤ → ℤ → ℂ :=
  fun j₁ j₂ =>
    ∑ p ∈ (diffFreqs ρ l₁).product (diffFreqs ρ l₂),
      fourier (T := 1) (-j₁) p.1 * fourier (T := 1) (-j₂) p.2
        * (∫ θ₁ : ℝ, ∫ θ₂ : ℝ,
            varphiN N k₁ θ₁ * varphitildeN P.natDegree N k₂ θ₂
            * M0 P N (arithQ ρ (max l₁ l₂)) p.1 p.2 θ₁ θ₂
            * ee (-((j₁ : ℝ) * θ₁ + (j₂ : ℝ) * θ₂)))

end

end Work.KMTAreas.A7
