import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs8.A.chiB_eq_zero_of_volume_dlBox_eq_zero
import Submission.Work.UBBInputs8.A.tube_indicator_integral_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs8.A

/-! Round 8, strand A — the FS-faithful repair of the kinetic input, verified at the very state
that breaks the corpus's rendering.

`Work.UBBInputs8.tBwordBInd` is the corpus's box word built from
`Work.UBBInputs8.boxQInd volA A i Φ = 1_A(x_i)·Φ − P_{B,i}Φ` — FS's own mean-free projection
`Q_B = 1_B − P_B` (`final_v2.tex` §5: "`Q_{B(u)}φ = 1_{B(u)}φ − P_{B(u)}φ`", with
`P_{B}φ = |B|⁻¹⟨1_B,φ⟩1_B`), whose two terms *both* carry the box indicator.  At the constant
state the word vanishes identically in `u` — unlike the corpus's `tBwordB`
(`Work.UBBInputs8.A.not_integrable_tBwordB_const`).  Route, in the two cases:
for a box of positive measure (`boxMass ℓ d u ≠ 0`) the two terms of `boxQInd` cancel
pointwise; for a null box (`boxMass ℓ d u = 0` with `dlBox ℓ d u` a degenerate face, which
does occur) `boxQInd` reduces to the indicator `1_A(x_i)`, whose contribution to
`cnPlusBoxInd` has zero integral (the tube `{x | x i ∈ A}` is null) and whose contribution to
`tBdiagFormInd` vanishes because the window `chiB ℓ d u` is supported in the *interior* of
`dlBox ℓ d u`, which is empty in the degenerate case. -/

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
open MeasureTheory
open scoped Topology Real BigOperators ENNReal
open Submission.BoseGases

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace TBAux

/-- At the constant state `Φ ≡ 1` the FS-faithful box projection evaluates to
`1_A(x_i)·(1 − |A|⁻¹∫_A 1)`: the two terms of `boxQInd` share the indicator factor `1_A(x_i)`. -/
theorem boxQInd_const_eq (volA : ℝ) (A : Set ℝ³) {N : ℕ} (i : Fin N) :
    Work.UBBInputs8.boxQInd volA A i (fun _ : X N => (1 : ℝ))
      = fun x : X N => A.indicator (fun _ => (1 : ℝ)) (x i)
          * (1 - volA⁻¹ * ∫ z in A, (1 : ℝ)) := by
  funext x
  simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
  ring

/-- If the `Q_{B,i}` all vanish pointwise, the excited count vanishes. -/
theorem cnPlusBoxInd_eq_zero_of_boxQ_eq_zero {a volA : ℝ} {A : Set ℝ³} {N : ℕ} {Ψ : X N → ℝ}
    (h : ∀ i : Fin N, Work.UBBInputs8.boxQInd volA A i Ψ = 0) :
    Work.UBBInputs8.cnPlusBoxInd a A volA Ψ = 0 := by
  simp only [Work.UBBInputs8.cnPlusBoxInd]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [h i]
  simp

/-- If the `Q_{B,i}` all vanish pointwise, the `p`-diagonal kinetic form vanishes. -/
theorem tBdiagFormInd_eq_zero_of_boxQ_eq_zero {a volA : ℝ} {A : Set ℝ³} (χ : ℝ³ → ℝ)
    (F : ℝ → ℝ) {N : ℕ} {Ψ : X N → ℝ}
    (h : ∀ i : Fin N, Work.UBBInputs8.boxQInd volA A i Ψ = 0) :
    Work.UBBInputs8.tBdiagFormInd a A volA χ F Ψ = 0 := by
  simp only [Work.UBBInputs8.tBdiagFormInd]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  simp only [h i]
  simp [Work.SmallBoxTBWord.tBamp]

/-- A vanishing window kills the `p`-diagonal kinetic form. -/
theorem tBdiagFormInd_eq_zero_of_chi_zero {a volA : ℝ} {A : Set ℝ³} (F : ℝ → ℝ) {N : ℕ}
    (Ψ : X N → ℝ) :
    Work.UBBInputs8.tBdiagFormInd a A volA (0 : ℝ³ → ℝ) F Ψ = 0 := by
  simp only [Work.UBBInputs8.tBdiagFormInd]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  simp [Work.SmallBoxTBWord.tBamp]

/-- If the `Q_{B,i}` reduce to the box indicator `1_A(x_i)` and the box is null (while sitting
inside `acube a`), the excited count has zero integral: the tube `{x | x i ∈ A}` is null. -/
theorem cnPlusBoxInd_eq_zero_of_boxQ_indicator {a volA : ℝ} {A : Set ℝ³} {N : ℕ} {Ψ : X N → ℝ}
    (h : ∀ i : Fin N, Work.UBBInputs8.boxQInd volA A i Ψ
        = fun x => A.indicator (fun _ => (1 : ℝ)) (x i))
    (hA : A ⊆ Submission.BoseGases.acube a) (hvol : (volume : Measure ℝ³) A = 0) :
    Work.UBBInputs8.cnPlusBoxInd a A volA Ψ = 0 := by
  simp only [Work.UBBInputs8.cnPlusBoxInd]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [h i]
  exact tube_indicator_integral_zero i hA hvol

end TBAux

theorem tBwordBInd_const_zero {N : ℕ} {ℓ d ε c : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) :
    Work.UBBInputs8.tBwordBInd N ℓ d ε c u
      (fun _ : Submission.BoseGases.X N => (1 : ℝ)) = 0 := by
  by_cases hvolA : Work.SmallBoxSliding.boxMass ℓ d u = 0
  · -- Null box (a degenerate face): `boxQInd` is the box indicator; `χ_B = 0` kills the
    -- spectral half and the tube is null for the gap half.
    have hvol : (volume : Measure ℝ³) (Submission.BoseGases.dlBox ℓ d u) = 0 := by
      have hreal : (volume : Measure ℝ³).real (Submission.BoseGases.dlBox ℓ d u) = 0 := by
        rw [← Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u, hvolA]
      rw [Measure.real] at hreal
      rcases (ENNReal.toReal_eq_zero_iff _).mp hreal with h0 | htop
      · exact h0
      · exact absurd htop (ne_of_lt (Work.SmallBoxSliding.volume_dlBox_lt_top hℓ d u))
    have hχ0 : Submission.BoseGases.chiB ℓ d u = 0 :=
      chiB_eq_zero_of_volume_dlBox_eq_zero hℓ hd u hvol
    have hQ : ∀ i : Fin N, Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) i (fun _ : X N => (1 : ℝ))
        = fun x => (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) (x i) := by
      intro i
      rw [TBAux.boxQInd_const_eq]
      have h1 : (1 : ℝ) - (Work.SmallBoxSliding.boxMass ℓ d u)⁻¹
          * (∫ z in Submission.BoseGases.dlBox ℓ d u, (1 : ℝ)) = 1 := by
        rw [hvolA]; simp
      rw [h1]; simp
    have hdiag : Work.UBBInputs8.tBdiagFormInd ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiB ℓ d u)
        (Submission.BoseGases.fsKinCoeff c) (fun _ : X N => (1 : ℝ)) = 0 := by
      rw [hχ0]
      exact TBAux.tBdiagFormInd_eq_zero_of_chi_zero _ _
    simp only [Work.UBBInputs8.tBwordBInd, Work.UBBInputs8.tBwordInd,
      Work.UBBInputs8.tBwordKinInd]
    rw [TBAux.cnPlusBoxInd_eq_zero_of_boxQ_indicator hQ
        (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u) hvol, hdiag]
    ring
  · -- Positive-measure box: `|A|⁻¹∫_A 1 = 1` and the two terms of `boxQInd` cancel pointwise.
    have hint : (∫ z in Submission.BoseGases.dlBox ℓ d u, (1 : ℝ))
        = Work.SmallBoxSliding.boxMass ℓ d u := by
      rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.setIntegral_const]
      simp
    have hQ : ∀ i : Fin N, Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) i (fun _ : X N => (1 : ℝ)) = 0 := by
      intro i
      rw [TBAux.boxQInd_const_eq]
      have h1 : (1 : ℝ) - (Work.SmallBoxSliding.boxMass ℓ d u)⁻¹
          * (∫ z in Submission.BoseGases.dlBox ℓ d u, (1 : ℝ)) = 0 := by
        rw [hint, inv_mul_cancel₀ hvolA]; ring
      rw [h1]
      funext x; simp
    simp only [Work.UBBInputs8.tBwordBInd, Work.UBBInputs8.tBwordInd,
      Work.UBBInputs8.tBwordKinInd]
    rw [TBAux.cnPlusBoxInd_eq_zero_of_boxQ_eq_zero hQ,
      TBAux.tBdiagFormInd_eq_zero_of_boxQ_eq_zero _ _ hQ]
    ring

end Work.UBBInputs8.A
