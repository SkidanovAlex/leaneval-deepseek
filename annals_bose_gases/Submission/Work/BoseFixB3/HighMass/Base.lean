import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Commons.Analysis.Fourier.integral_mul_eq_integral_fourier_mul
import Submission.Work.BoseFixB3.Defs
import Submission.Work.BoseKinLoc.Momentum.kinFT_l1l2_plancherel
import Submission.Work.BoseKinLoc.Sector.kinForm_fibre_sum
import Submission.Work.hlocWire.boxPInd_smul
import Submission.Work.hlocWire.boxQInd_smul
import Submission.Work.hlocWire.tBdiagFormInd_smul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.HighMass` — FS `eq:QLs_giveNplusH`

Auxiliary lemmas for the domination `highMass ≤ nPlusHB` (FS §7, `eq:QLs_giveNplusH`),
`Σᵢ Q̄_{L,i}(Q̄_{L,i})^* ≤ n_+^H`, in the chapter's form

  `Σᵢ ∫_{Λ} (Q̄_{L,i}Q_iΦ)² ≤ ℓ⁻³ Σᵢ ∫_{Λ} 1_{Λ}(xᵢ)·⟨Q_iΦ, 1_{(d⁻²ℓ⁻¹,∞)}(√−Δ) Q_iΦ⟩`.

Contents:

* `kMult` — the `lowMult` multiplier formula with a general symbol;
* `one_sub_sq_le_momProj` — the pointwise symbol bound `(1 − f(‖p‖/κ))² ≤ 1_{‖p‖ > (d²ℓ)⁻¹}`;
* `fibre_aQ_eq_bsQ`, `highSlot_aQ_eq`, `momForm_eq_indicator` — the fibre identifications;
* `lowMult_pairing` — the weak (Fubini) identity for the cut-off multiplier;
* `parseval_kinFT` — Parseval for `L¹ ∩ L²` in the `p`-convention;
* `oneBody_box_le` — the one-body weighted Plancherel bound for the box (the crux);
* `oneBody_le_momForm` — the same with the `momForm` cut-off, both for `κ > 0` and `κ = 0`;
* the slot peel and the assembly.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseFixB3.HighMass

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseKinLoc
open Work.BoseBoxFix Work.BSKinetic

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## 1. The general symbol multiplier -/

/-- `lowMult` with a general real symbol `g` (the `LowCut` field is replaced by `g`). -/
def kMult (ℓ : ℝ) (g : ℝ³ → ℝ) (Ψ : ℝ³ → ℝ) (x : ℝ³) : ℝ :=
  ((((2 * π) ^ 3)⁻¹ : ℝ) * ∫ p : ℝ³, Complex.exp (Complex.I * (inner ℝ p x : ℂ)) *
      ((g p : ℝ) : ℂ) *
        kinFT (fun z : ℝ³ => (((acube ℓ).indicator Ψ z : ℝ) : ℂ)) p).re

/-- `lowMult` is `kMult` at the cut-off symbol `p ↦ fc.f (‖p‖/κ)`. -/
lemma lowMult_eq_kMult {fc : LowCut} {κ ℓ : ℝ} (Ψ : ℝ³ → ℝ) (x : ℝ³) :
    lowMult fc κ ℓ Ψ x = kMult ℓ (fun p : ℝ³ => fc.f (‖p‖ / κ)) Ψ x := rfl

/-! ## 2. The cut-off `LowCut` facts -/

lemma lowcut_nonneg (fc : LowCut) (s : ℝ) : 0 ≤ fc.f s := by
  by_cases h : s ≤ 2
  · have h2 : fc.f 2 = 0 := fc.zero 2 le_rfl
    have := fc.anti h
    linarith
  · rw [fc.zero s (not_le.mp h).le]

lemma lowcut_le_one (fc : LowCut) (s : ℝ) : fc.f s ≤ 1 := by
  by_cases h : s ≤ 1
  · rw [fc.one s h]
  · have h1 : 1 ≤ s := (not_le.mp h).le
    have := fc.anti h1
    rwa [fc.one 1 le_rfl] at this

lemma lowcut_abs_le_one (fc : LowCut) (s : ℝ) : |fc.f s| ≤ 1 :=
  abs_le.mpr ⟨by linarith [lowcut_nonneg fc s], lowcut_le_one fc s⟩

/-- For `κ > 0` the cut-off symbol vanishes outside the ball of radius `2κ`. -/
lemma lowcut_symbol_hasCompactSupport {fc : LowCut} {κ : ℝ} (hκ : 0 < κ) :
    HasCompactSupport (fun p : ℝ³ => fc.f (‖p‖ / κ)) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ³) (2 * κ)) fun p hp => ?_
  have hp' : 2 * κ < ‖p‖ := by
    have h1 : ¬ (dist p 0 ≤ 2 * κ) := by simpa [Metric.mem_closedBall] using hp
    rw [dist_zero_right] at h1
    exact not_le.mp h1
  rw [fc.zero _ (by rw [le_div_iff₀ hκ]; linarith)]

/-- The pointwise symbol bound: the square of the complementary cut-off is dominated by
the high-momentum indicator of `momProj`, at the FS relation `κ = (d²ℓ)⁻¹`. -/
lemma one_sub_sq_le_momProj {fc : LowCut} {κ d ℓ : ℝ}
    (hκ : κ = (d ^ 2 * ℓ)⁻¹) (hℓ : 0 < ℓ) (p : ℝ³) :
    (1 - fc.f (‖p‖ / κ)) ^ 2 ≤ momProj ℓ d p := by
  have hκnn : 0 ≤ κ := hκ ▸ inv_nonneg.mpr (mul_nonneg (sq_nonneg d) hℓ.le)
  by_cases h0 : κ = 0
  · -- `κ = 0`
    have h1 : fc.f (‖p‖ / κ) = 1 := by
      rw [h0, div_zero]
      exact fc.one 0 (by norm_num)
    rw [h1, sub_self]
    rw [momProj]
    split <;> norm_num
  · have hκpos : 0 < κ := lt_of_le_of_ne hκnn (Ne.symm h0)
    by_cases hle : ‖p‖ ≤ κ
    · have hle' : ‖p‖ / κ ≤ 1 := (div_le_one hκpos).mpr hle
      have : fc.f (‖p‖ / κ) = 1 := fc.one _ hle'
      rw [this, sub_self]
      rw [momProj]
      split <;> norm_num
    · have h : κ < ‖p‖ := not_le.mp hle
      have h1 : (1 - fc.f (‖p‖ / κ)) ^ 2 ≤ 1 := by
        have h0' := lowcut_nonneg fc (‖p‖ / κ)
        have h1' := lowcut_le_one fc (‖p‖ / κ)
        nlinarith
      have hmom : momProj ℓ d p = 1 := by
        rw [momProj, ← hκ]
        exact if_pos h
      rw [hmom]
      exact h1

/-! ## 3. The fibre identifications -/

/-- The slot-`i` fibre of `Q_iΦ` is the mean-free slot-`i` fibre of `Φ`:
`(fun z => Q_iΦ (x_{i←z})) = Q_0 (z ↦ Φ (x_{i←z}))`. -/
lemma fibre_aQ_eq_bsQ {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin n)
    {Φ : X n → ℝ} (hΦc : Continuous Φ) (x : X n) :
    (fun z : ℝ³ => aQ ℓ i Φ (Function.update x i z)) = bsQ ℓ 0 (fibre n i Φ x) := by
  funext z
  have hP : aP ℓ i Φ (Function.update x i z) = aP ℓ i Φ x := aP_const_in_coord hℓ i hΦc x z
  have hU : ∀ y : ℝ³, Function.update (Function.update x i z) i y = Function.update x i y := by
    intro y
    ext k
    by_cases hk : k = i <;> simp [Function.update, hk]
  simp only [aQ, aP, bsQ, bsMean, fibre, hP, hU, smul_zero, zero_add]
  rw [one_div]

/-- The `highSlot` of `Q_iΦ` is the complementary cut-off of the mean-free fibre. -/
lemma highSlot_aQ_eq {fc : LowCut} {κ ℓ : ℝ} {n : ℕ} (hℓ : 0 < ℓ) (i : Fin n)
    {Φ : X n → ℝ} (hΦc : Continuous Φ) (x : X n) :
    highSlot fc κ ℓ i (aQ ℓ i Φ) x
      = highMult fc κ ℓ (bsQ ℓ 0 (fibre n i Φ x)) (x i) := by
  have hfun := fibre_aQ_eq_bsQ (ℓ := ℓ) hℓ i hΦc x
  have hx : aQ ℓ i Φ x = bsQ ℓ 0 (fibre n i Φ x) (x i) := by
    have h := congrFun hfun (x i)
    rwa [Function.update_eq_self] at h
  simp only [highSlot, highMult, lowSlot, hfun, hx]

/-- `momForm` of a fibre only sees its mean-free box restriction. -/
lemma momForm_eq_indicator {ℓ d : ℝ} (ψ : ℝ³ → ℝ) :
    momForm ℓ d 0 ψ
      = ((2 * π) ^ 3)⁻¹ * ∫ p : ℝ³, momProj ℓ d p *
          ‖kinFT (fun z : ℝ³ => (((acube ℓ).indicator (bsQ ℓ 0 ψ) z : ℝ) : ℂ)) p‖ ^ 2 := by
  have hfun : (fun z : ℝ³ => ((indU ℓ 0 z : ℝ) : ℂ) * ((Qfree ℓ 0 ψ z : ℝ) : ℂ))
      = fun z : ℝ³ => (((acube ℓ).indicator (bsQ ℓ 0 ψ) z : ℝ) : ℂ) := by
    funext z
    by_cases hz : z ∈ acube ℓ
    · rw [Work.BoseKinLoc.Sector.indU_zero]
      simp [Set.indicator_of_mem hz, Qfree]
    · rw [Work.BoseKinLoc.Sector.indU_zero_of_notMem hz]
      simp [Set.indicator_of_notMem hz]
  rw [momForm, hfun]

/-- The `momForm` of a fibre does not depend on the value of the slot-`i` coordinate. -/
lemma momForm_fibre_update {ℓ d : ℝ} {m : ℕ} (i : Fin (m + 1)) (Φ : X (m + 1) → ℝ)
    (x : X (m + 1)) (z : ℝ³) :
    momForm ℓ d 0 (fibre (m + 1) i Φ (Function.update x i z))
      = momForm ℓ d 0 (fibre (m + 1) i Φ x) := by
  have hf : fibre (m + 1) i Φ (Function.update x i z) = fibre (m + 1) i Φ x := by
    funext w
    rw [fibre, fibre, Function.update_idem]
  rw [hf]

end Work.BoseFixB3.HighMass
