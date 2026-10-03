/-
# The shared vocabulary of the mixed range (`l₁ = 0`, `l₂ ≥ 1`) of the §8 model estimate

This is the **base module** of `Work.KMTAreas.A7.LoMixedModel` and of the `g`-side cluster
`A7/MixedGSideAux.lean`, `A7/MixedGSideHolds.lean`, `A7MixedG/*`, `A7G/*`, `A7LV/*`.

It exists to break an **import cycle**: `A7/MixedGSideAux.lean` (hence the whole `g`-side cluster)
needs `MixedGSideEstimate` and `loMixedGKer`, and the target file `A7/LoMixedModel.lean` needs the
cluster to close its last factor estimate.  Hence the shared definitions live here, and both
`A7/LoMixedModel.lean` and `A7/MixedGSideAux.lean` import *this* module.

Contents (all proved, axiom-clean): the arithmetic kernel of the mixed twisted bilinear multiplier
and its independence of the first index (`smallArithKernel_zero_left`), `form-1`
(`loMixedGKer_eq_fiberAvg`), the exact factorisation of the mixed multiplier
(`btwistZero_factor`), the plain convolution shape of the first fibre
(`fibreOpSet_singleton_zero_eq_convOp`), and the two factor estimates as `Prop`s
(`MixedFSideEstimate`, `MixedGSideEstimate`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LoMixedDefs
import Submission.Work.KMTAreas.A7.variationalNorm_intervalIntegral_eLpNorm_le
import Submission.Work.KMTAreas.A7.LoMixedAux
import Submission.Work.KMTAreas.A7.iwConv_varphiNt_bounded_measurable
import Submission.Work.KMTAreas.A7.measurable_iwKernel_varphitildeNt
import Submission.Work.KMTAreas.A7.ExcAux2
import Submission.Commons.MeasureTheory.Function.eLpNorm_mul_le_eLpNorm_mul_eLpNorm
import Submission.Work.KMTAreas.A7.LoLinVar
import Submission.Work.KMTAreas.A7.variationalNorm_tsum_conv
import Submission.Work.KMTAreas.A7Hi.variationalNorm_tsum_le
import Submission.Work.KMTPlan.A6.vpc_exists_cw_mStarF_tsum_le

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier Work.KMTContract Work.Analysis.EndVar

local notation "Circ" => Work.Analysis.IonescuWainger.Circle/-! ## The characters and the arithmetic kernel at `l₁ = 0` -/

/-- `e(n · 0) = 1` on the circle. -/
theorem fourier_int_zero (n : ℤ) : fourier (T := 1) n (0 : Circ) = 1 := by
  rw [fourier_apply]; simp

/-- The arithmetic character sum of the singleton `{0}` is `1`. -/
theorem arithCharSet_singleton_zero (y : ℤ) : arithCharSet ({0} : Finset Circ) y = 1 := by
  rw [arithCharSet, Finset.sum_singleton, fourier_int_zero]

/-- **The arithmetic kernel of the mixed range is independent of the first index.**  At `l₁ = 0`
the arithmetic frequency set is the singleton `{0}`, so the first arithmetic Fourier factor is `1`
and the kernel is the Fourier transform of the arithmetic symbol `m_Ẑ(0,·)` at `-j₂`. -/
theorem smallArithKernel_zero_left (ρ : ℝ) (P : ℤ[X]) (q l₂ : ℕ) (j₁ j₂ : ℤ) :
    smallArithKernel ρ P q 0 l₂ j₁ j₂
      = ∑ α₂ ∈ diffFreqs ρ l₂, mZ P q 0 α₂ * fourier (T := 1) (-j₂) α₂ := by
  rw [smallArithKernel, show diffFreqs ρ 0 = ({0} : Finset Circ) from by
        rw [diffFreqs, if_pos rfl, iwArithFreqs_zero]]
  rw [Finset.sum_singleton]
  refine Finset.sum_congr rfl (fun α₂ _ => ?_)
  rw [fourier_int_zero, mul_one]

/-- The kernel `κ` of the second (arithmetic) factor of the mixed twisted multiplier: the
convolution kernel `j ↦ (∑_{α₂ ∈ (ℚ/ℤ)_{l₂}} m_Ẑ(0,α₂) e(-jα₂)) · (𝓕⁻m₂)(j)`. -/
noncomputable def loMixedGKer (ρ : ℝ) (P : ℤ[X]) (l₂ : ℕ) (m₂ : ℝ → ℂ) (j : ℤ) : ℂ :=
  (∑ α₂ ∈ diffFreqs ρ l₂, mZ P (arithQ ρ l₂) 0 α₂ * fourier (T := 1) (-j) α₂) * cw m₂ j

/-- **`form-1` for the mixed range**: the kernel `κ` of the arithmetic factor is the average over
the residues `n₀ < arithQ ρ l₂` of the arithmetic characters `∑_{α₂} e(α₂(P(n₀) - j))`, i.e. the
discrete form of the paper's `∫_{Ẑ}` over the adelic integers. -/
theorem loMixedGKer_eq_fiberAvg (ρ : ℝ) (P : ℤ[X]) (l₂ : ℕ) (m₂ : ℝ → ℂ) (j : ℤ) :
    loMixedGKer ρ P l₂ m₂ j
      = ((arithQ ρ l₂ : ℂ)⁻¹ * ∑ n₀ ∈ Finset.range (arithQ ρ l₂),
          arithCharSet (diffFreqs ρ l₂) (P.eval (n₀ : ℤ) - j)) * cw m₂ j := by
  rw [loMixedGKer]
  congr 1
  have h1 : ∀ α₂ ∈ diffFreqs ρ l₂,
      mZ P (arithQ ρ l₂) 0 α₂ * fourier (T := 1) (-j) α₂
        = (arithQ ρ l₂ : ℂ)⁻¹ * ∑ n₀ ∈ Finset.range (arithQ ρ l₂),
            fourier (T := 1) (P.eval (n₀ : ℤ) - j) α₂ := by
    intro α₂ _
    rw [mZ, mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl (fun n₀ _ => ?_)
    rw [fourier_int_zero, one_mul]
    rw [show P.eval (n₀ : ℤ) - j = P.eval (n₀ : ℤ) + (-j) by ring, fourier_add]
  rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, Finset.sum_comm]
  rfl

/-! ## The factorisation of the mixed twisted bilinear multiplier -/

/-- **`form-1` at `l₁ = 0`: the mixed twisted bilinear multiplier factorises as the product of the
two one-variable convolutions.**  The first factor is the convolution of `h` with the kernel
`cw m₁` (a *fixed* bounded operator), the second is the convolution of `k` with `loMixedGKer`, i.e.
the arithmetic average over the residues of the fibres of the second variable. -/
theorem btwistZero_factor (ρ : ℝ) (P : ℤ[X]) (l₂ : ℕ) (m₁ m₂ : ℝ → ℂ) (h k : ℤ → ℂ) (x : ℤ) :
    smallBtwist ρ P 0 l₂ m₁ m₂ h k x
      = (∑' j : ℤ, cw m₁ j * h (x - j))
        * (∑' j : ℤ, loMixedGKer ρ P l₂ m₂ j * k (x - j)) := by
  unfold smallBtwist
  have hker : ∀ j₁ j₂ : ℤ, smallArithKernel ρ P (arithQ ρ (max 0 l₂)) 0 l₂ j₁ j₂
      = ∑ α₂ ∈ diffFreqs ρ l₂, mZ P (arithQ ρ l₂) 0 α₂ * fourier (T := 1) (-j₂) α₂ := by
    intro j₁ j₂
    rw [show arithQ ρ (max 0 l₂) = arithQ ρ l₂ from by rw [Nat.max_eq_right (Nat.zero_le _)]]
    exact smallArithKernel_zero_left ρ P (arithQ ρ l₂) l₂ j₁ j₂
  simp only [hker, loMixedGKer]
  have hinner : ∀ j₁ : ℤ,
      (∑' j₂ : ℤ,
        (∑ α₂ ∈ diffFreqs ρ l₂, mZ P (arithQ ρ l₂) 0 α₂ * fourier (T := 1) (-j₂) α₂)
          * cw m₁ j₁ * cw m₂ j₂ * h (x - j₁) * k (x - j₂))
        = (cw m₁ j₁ * h (x - j₁)) * (∑' j₂ : ℤ,
          ((∑ α₂ ∈ diffFreqs ρ l₂, mZ P (arithQ ρ l₂) 0 α₂ * fourier (T := 1) (-j₂) α₂)
            * cw m₂ j₂) * k (x - j₂)) := by
    intro j₁
    have hcongr : (fun j₂ : ℤ =>
          (∑ α₂ ∈ diffFreqs ρ l₂, mZ P (arithQ ρ l₂) 0 α₂ * fourier (T := 1) (-j₂) α₂)
            * cw m₁ j₁ * cw m₂ j₂ * h (x - j₁) * k (x - j₂))
        = fun j₂ : ℤ => (cw m₁ j₁ * h (x - j₁)) *
          (((∑ α₂ ∈ diffFreqs ρ l₂, mZ P (arithQ ρ l₂) 0 α₂ * fourier (T := 1) (-j₂) α₂)
            * cw m₂ j₂) * k (x - j₂)) := by
      funext j₂; ring
    rw [hcongr, tsum_mul_left]
  rw [tsum_congr hinner, tsum_mul_right]

/-- The fibre of the twisted projection at the singleton frequency set `{0}` is the plain
convolution with the kernel `cw m`: in the mixed range the first arithmetic factor is trivial. -/
theorem fiberOpSet_singleton_zero_eq_convOp (m : ℝ → ℂ) (n₀ : ℤ) (u : ℤ → ℂ) :
    fiberOpSet ({0} : Finset Circ) m n₀ u = convOp (cw m) u := by
  funext x
  rw [fiberOpSet, convOp]
  exact tsum_congr (fun j => by rw [arithCharSet_singleton_zero, one_mul])

/-! ## The two analytic inputs of the mixed range -/

/-- **The `f`-side input of the mixed range**: the variational estimate for the *first factor*
`convOp (cw m₁) (T^0_{φ_{N_n,t}} f)` of the mixed model operator (`m₁ = η_{≤-2u}` with the repaired
window `u = loMixedU ρ P.natDegree l₂ k₁ k₂` of `Work.KMTAreas.A7.LoMixedDefs`), clipped to the
guard `loGuard ρ C₀ a 0 l₂ k₁ k₂`, with the loss `lossWeight c ρ 0 l₂ k₁ k₂`.

The operator is the paper's `(lin-1)` at arithmetic height `0` (`T^0_φ = Tle ρ 0 φ = Tm ρ 0 φ` is
the plain modulated multiplier, since `(ℚ/ℤ)_0 = diffFreqs ρ 0 = {0}`), multiplied by the fixed
bounded convolution with the kernel `cw (η_{≤-2u})`.  Both the height-`0` linear lacunary
variational estimate (`Work.KMTAreas.A7.LoLinVar`) and the kernel-mass transfer
(`Work.KMTAreas.A7.CwTsumLe`, uniform in the window) are available in the workspace. -/
def MixedFSideEstimate (P : ℤ[X]) (p₁ : ENNReal) : Prop :=
  ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r →
    ∃ c : ℝ, 0 ≤ c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → 1 ≤ l₂ →
          t ∈ Set.Icc (1/2 : ℝ) 1 →
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ =>
                if loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
                  convOp (cw (mStarF (loMixedU ρ P.natDegree l₂ k₁ k₂)))
                    (Tm ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f) x else 0))
            p₁ MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) * ENNReal.ofReal (lossWeight c ρ 0 l₂ k₁ k₂) *
              MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count

/-- **The `g`-side input of the mixed range**: the variational estimate for the *second factor*
`convOp (loMixedGKer ρ P l₂ m₂) (T^{l₂}_{φ̃_{N_n,t}} g)` (`m₂ = η_{≤-2du}`, `u = loMixedU ρ
P.natDegree l₂ k₁ k₂`), clipped to the guard, with the loss `lossWeight c ρ 0 l₂ k₁ k₂`.

The kernel `loMixedGKer` is the arithmetic average over the residues `n₀ < arithQ ρ l₂` of the
fibres of the second variable (`loMixedGKer_eq_fiberAvg`), so this is the frame in which the
paper's `(lin-2)`/sampling estimate of §8 applies: with the *repaired* window the exact-height
fibres `diffFreqs ρ l₂` are separated (`Work.KMTAreas.A7.ltwo_add_three_le_two_mul_loMixedU`), so
`convOp (loMixedGKer) u = q⁻¹ ∑_{n₀} fiberOpP n₀ u` is within the reach of the workspace's fibre
estimate `Work.KMTAreas.A7.fiberVarSamplingG` (together with the linear estimate
`lacunaryBumpVarEstimateG` for the unweighted family). -/
def MixedGSideEstimate (P : ℤ[X]) (p₂ : ENNReal) : Prop :=
  ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r →
    ∃ c : ℝ, 0 ≤ c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → 1 ≤ l₂ →
          t ∈ Set.Icc (1/2 : ℝ) 1 →
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ =>
                if loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
                  convOp (loMixedGKer ρ P l₂ (mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂)))
                    (Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x else 0))
            p₂ MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) * ENNReal.ofReal (lossWeight c ρ 0 l₂ k₁ k₂) *
              MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count

end

end Work.KMTAreas.A7
