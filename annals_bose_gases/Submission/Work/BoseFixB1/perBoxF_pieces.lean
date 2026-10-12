import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.AprioriPieces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## 1. The pointwise bounds on FS's weight `F` -/

/-- **`F(t) ≤ μ (t + μ)`**: FS's weight `F(t) = (t−μ)²/(1+tμ⁻¹) = μ(t−μ)²/(t+μ)` is
bounded by `μ(t+μ)` on the physical range `t ≥ 0` (indeed `(t−μ)² ≤ (t+μ)²` for `t ≥ 0`). -/
lemma psiWeight_le_mu_mul_add {μ t : ℝ} (hμ : 0 < μ) (ht : 0 ≤ t) :
    Work.SmallBoxSliding.psiWeight 1 μ t ≤ μ * (t + μ) := by
  rw [Work.SmallBoxSliding.psiWeight]
  have hden : 0 < 1 + t * μ⁻¹ := by
    have : 0 ≤ t * μ⁻¹ := mul_nonneg ht (le_of_lt (inv_pos.mpr hμ))
    linarith
  rw [div_le_iff₀ hden]
  have h1 : 1 + t * μ⁻¹ = (t + μ) / μ := by
    field_simp
    ring
  rw [h1]
  have h2 : μ * (t + μ) * ((t + μ) / μ) = (t + μ) ^ 2 := by
    field_simp
  rw [h2]
  nlinarith [sq_nonneg (t - μ), hμ, ht]

/-- **The `F`-weight is dominated by the `A₀` square** at `c₁ ≤ ¼`:
`c₁·F(t) ≤ ¼(t−μ)²` for all `t ≥ 0`.  This is the shape FS's potential-side `A₀`-estimate
produces, so the `F`-term of `PerBoxF` is paid by the mean-field square at that
coefficient (the sharp/Bogoliubov content of `thm:smallbox` is then not needed). -/
lemma perBoxF_F_weight_le {c₁ μ t : ℝ} (hc0 : 0 < c₁) (hc : c₁ ≤ 1 / 4) (hμ : 0 < μ)
    (ht : 0 ≤ t) :
    c₁ * Work.SmallBoxSliding.psiWeight 1 μ t ≤ (1 / 4) * (t - μ) ^ 2 := by
  rw [Work.SmallBoxSliding.psiWeight]
  have hden : 0 < 1 + t * μ⁻¹ := by
    have : 0 ≤ t * μ⁻¹ := mul_nonneg ht (le_of_lt (inv_pos.mpr hμ))
    linarith
  rw [← mul_div_assoc, div_le_iff₀ hden]
  have h1 : 1 + t * μ⁻¹ = (t + μ) / μ := by
    field_simp
    ring
  rw [h1]
  have hsq : 0 ≤ (t - μ) ^ 2 := sq_nonneg _
  have hratio : (1 : ℝ) ≤ (t + μ) / μ := by
    rw [le_div_iff₀ hμ]; linarith
  have h4 : c₁ ≤ (1 / 4 : ℝ) := hc
  nlinarith [mul_le_mul_of_nonneg_right h4 hsq, mul_le_mul_of_nonneg_left hratio hsq,
    mul_nonneg (by norm_num : (0:ℝ) ≤ 1/4) hsq]

/-! ## 2. The excited-count payment for the FS-faithful word `tBwordBInd` -/

/-- **The gap part of the FS-faithful word**: `tBwordInd` is *defined* as the gap term plus
the spectral term, hence dominates the gap term `tbGapCoeff s ε · n₊(B)`. -/
lemma tBwordInd_ge_gapPart {a s ε c volA : ℝ} {A : Set ℝ³} {χ : ℝ³ → ℝ} {N : ℕ}
    (hker : 0 ≤ Work.UBBInputs8.tBwordKinInd a A volA χ c (fun x : X N => (1 : ℝ))) :
    Work.SmallBoxTBWord.tbGapCoeff s ε * Work.UBBInputs8.cnPlusBoxInd a A volA
        (fun x : X N => (1 : ℝ))
      ≤ Work.UBBInputs8.tBwordInd a A volA χ s ε c (fun x : X N => (1 : ℝ)) := by
  rw [Work.UBBInputs8.tBwordInd]
  linarith

/-- **The gap part of `sbKin`** (FS `eq:appTB`'s first term): the frozen `sbKin` dominates
`tbGapCoeff (dℓ) ε_T · n₊(B)`, provided the spectral half is nonnegative (it is, being a
sum of `‖·‖²`-integrals against a nonnegative symbol). -/
lemma sbKin_ge_gapPart {v : ℝ³ → ℝ} {μ : ℝ} {M : ℕ} {u : ℝ³} {n : ℕ} (Φ : X n → ℝ)
    (hker : 0 ≤ Work.UBBInputs8.tBwordKinInd (sideAt μ (a v)) (dlBox (sideAt μ (a v))
        (paramsAt μ (a v)).d u) (boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u)
        (chiB (sideAt μ (a v)) (paramsAt μ (a v)).d u) (sbCut μ (a v)) Φ) :
    Work.SmallBoxTBWord.tbGapCoeff ((paramsAt μ (a v)).d * sideAt μ (a v))
        (paramsAt μ (a v)).eT
      * Work.UBBInputs8.cnPlusBoxInd (sideAt μ (a v))
          (dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u)
          (boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u) Φ
      ≤ sbKin (v := v) μ M u Φ := by
  rw [sbKin, Work.UBBInputs8.tBwordBInd, Work.UBBInputs8.tBwordInd]
  simp only [Work.UBBInputs8.tBwordInd, mul_comm (sideAt μ (a v)) (paramsAt μ (a v)).d]
  linarith

/-- **FS `eq:appgapestimate` in the frozen vocabulary**: in the regime
`ε_T ≥ 2(1+π⁻²)(dℓ C'√(μ(a v)))²`, the excited count `n₊(B)` of the sliding box is paid
by `sbKin` at the coefficient `C'²μ(a v)`. -/
lemma sbKin_ge_mu_av_cnPlus {v : ℝ³ → ℝ} {μ c' : ℝ} {M : ℕ} {u : ℝ³} {n : ℕ} (Φ : X n → ℝ)
    (hav : 0 ≤ a v) (hμ : 0 ≤ μ) (hC' : 0 ≤ c') (hs : 0 < (paramsAt μ (a v)).d * sideAt μ (a v))
    (hε : 0 < (paramsAt μ (a v)).eT)
    (hreg : 2 * (1 + (Real.pi ^ 2)⁻¹)
        * ((paramsAt μ (a v)).d * sideAt μ (a v) * c' * Real.sqrt (μ * (a v))) ^ 2
        ≤ (paramsAt μ (a v)).eT)
    (hker : 0 ≤ Work.UBBInputs8.tBwordKinInd (sideAt μ (a v)) (dlBox (sideAt μ (a v))
        (paramsAt μ (a v)).d u) (boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u)
        (chiB (sideAt μ (a v)) (paramsAt μ (a v)).d u) (sbCut μ (a v)) Φ) :
    c' ^ 2 * μ * (a v)
      * Work.UBBInputs8.cnPlusBoxInd (sideAt μ (a v))
          (dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u)
          (boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u) Φ
      ≤ sbKin (v := v) μ M u Φ := by
  have hgap : c' ^ 2 * μ * (a v) ≤ Work.SmallBoxTBWord.tbGapCoeff
      ((paramsAt μ (a v)).d * sideAt μ (a v)) (paramsAt μ (a v)).eT :=
    Work.SmallBoxTBWord.gapCoeff_absorbs hav hμ hC' hε hs hreg
  have hnn : 0 ≤ Work.UBBInputs8.cnPlusBoxInd (sideAt μ (a v))
      (dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u)
      (boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u) Φ := by
    rw [Work.UBBInputs8.cnPlusBoxInd]
    exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _
  calc c' ^ 2 * μ * (a v)
        * Work.UBBInputs8.cnPlusBoxInd (sideAt μ (a v))
            (dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u)
            (boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u) Φ
      ≤ Work.SmallBoxTBWord.tbGapCoeff ((paramsAt μ (a v)).d * sideAt μ (a v))
          (paramsAt μ (a v)).eT
        * Work.UBBInputs8.cnPlusBoxInd (sideAt μ (a v))
            (dlBox (sideAt μ (a v)) (paramsAt μ (a v)).d u)
            (boxMass (sideAt μ (a v)) (paramsAt μ (a v)).d u) Φ :=
        mul_le_mul_of_nonneg_right hgap hnn
    _ ≤ sbKin (v := v) μ M u Φ := sbKin_ge_gapPart Φ hker

end Work.BoseFixB1
