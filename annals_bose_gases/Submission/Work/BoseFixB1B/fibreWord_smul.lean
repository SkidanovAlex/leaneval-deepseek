import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.sectorCountDefs
import Submission.Work.SlotWord.Defs
import Submission.Work.hlocWire.boxQInd_smul
import Submission.Work.hlocWire.tBdiagFormInd_smul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.fibreWord_smul` — the sliding word is a quadratic form

`Work.SlotWord.fibreWord h M K L d ε c μ u Ψ = tBwordBInd K L d ε c u Ψ + qLHSwordB h M L d μ u Ψ`
is the sliding (fibre) word of the a-priori chapter (`Submission/Work/SlotWord/Defs.lean`).  Both
summands are **quadratic** in the state:

* the kinetic half `tBwordBInd = tbGapCoeff·cnPlusBoxInd + tBdiagFormInd` is a sum of *squares* of
  objects that are linear in the state — the FS box projection `boxQInd` and the windowed
  `p`-amplitude `tBamp` (`Work.hlocWire.boxQInd_smul`, `Work.hlocWire.tBdiagFormInd_smul`);
* the potential half `qLHSwordB = ∫_{abox}(Φ x)²·(potential profile)` is an integral whose
  integrand is the state factor `(Φ x)²` times a state-independent profile, so only
  `MeasureTheory.integral_const_mul` is needed.

Hence `fibreWord … (fun x => a * Ψ x) = a² · fibreWord … Ψ`.  This is the homogeneity step used by
the count ↔ fibre reduction (`Work.BoseFixB1B.SectorCountSmallbox`): normalising the fibre of a
sector piece rescales the word by the reciprocal of the fibre mass squared.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1B

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

variable {N : ℕ}

/-! ## 1. Linearity of the FS box projection -/

/-- `Work.UBBInputs8.boxQInd` is linear in the state, restated in the `fun x => a * Ψ x` form used
throughout the corpus (it is `Work.hlocWire.boxQInd_smul` with the scalar written as a pointwise
product). -/
lemma boxQInd_const_mul (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3))) (i : Fin N)
    (Ψ : Submission.BoseGases.X N → ℝ) (a : ℝ) :
    Work.UBBInputs8.boxQInd volA A i (fun x => a * Ψ x)
      = fun x => a * Work.UBBInputs8.boxQInd volA A i Ψ x := by
  rw [show (fun x : Submission.BoseGases.X N => a * Ψ x) = a • Ψ from by funext x; rfl]
  rw [Work.hlocWire.boxQInd_smul]
  funext x
  rfl

/-! ## 2. The kinetic half -/

/-- The FS-faithful excited count `cnPlusBoxInd = Σᵢ∫_{abox}(Q_{B,i}Ψ)²` is `2`-homogeneous in the
state: `boxQInd` is linear and the square is quadratic. -/
lemma cnPlusBoxInd_const_mul (a : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3))) (volA : ℝ)
    (Ψ : Submission.BoseGases.X N → ℝ) (t : ℝ) :
    Work.UBBInputs8.cnPlusBoxInd a A volA (fun x => t * Ψ x)
      = t ^ 2 * Work.UBBInputs8.cnPlusBoxInd a A volA Ψ := by
  unfold Work.UBBInputs8.cnPlusBoxInd
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [boxQInd_const_mul volA A i Ψ t]
  rw [show (fun x : Submission.BoseGases.X N =>
        (t * Work.UBBInputs8.boxQInd volA A i Ψ x) ^ 2)
      = (fun x => t ^ 2 * (Work.UBBInputs8.boxQInd volA A i Ψ x) ^ 2) from by
    funext x; ring]
  exact MeasureTheory.integral_const_mul (t ^ 2) _

/-- The FS-faithful `p`-diagonal box form `tBdiagFormInd` is `2`-homogeneous in the state
(`Work.hlocWire.tBdiagFormInd_smul`, restated in the pointwise-product form). -/
lemma tBdiagFormInd_const_mul (a : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3))) (volA : ℝ)
    (χ : EuclideanSpace ℝ (Fin 3) → ℝ) (F : ℝ → ℝ)
    (Ψ : Submission.BoseGases.X N → ℝ) (t : ℝ) :
    Work.UBBInputs8.tBdiagFormInd a A volA χ F (fun x => t * Ψ x)
      = t ^ 2 * Work.UBBInputs8.tBdiagFormInd a A volA χ F Ψ := by
  rw [show (fun x : Submission.BoseGases.X N => t * Ψ x) = t • Ψ from by funext x; rfl]
  exact Work.hlocWire.tBdiagFormInd_smul a A volA χ F Ψ t

/-- `𝒯_B = tbGapCoeff·cnPlusBoxInd + tBwordKinInd` is `2`-homogeneous in the state. -/
lemma tBwordInd_const_mul (a : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3))) (volA : ℝ)
    (χ : EuclideanSpace ℝ (Fin 3) → ℝ) (s ε c : ℝ)
    (Ψ : Submission.BoseGases.X N → ℝ) (t : ℝ) :
    Work.UBBInputs8.tBwordInd a A volA χ s ε c (fun x => t * Ψ x)
      = t ^ 2 * Work.UBBInputs8.tBwordInd a A volA χ s ε c Ψ := by
  unfold Work.UBBInputs8.tBwordInd Work.UBBInputs8.tBwordKinInd
  rw [cnPlusBoxInd_const_mul a A volA Ψ t, tBdiagFormInd_const_mul a A volA χ _ Ψ t]
  ring

/-- The sliding kinetic word `tBwordBInd = 𝒯_{B(u)}` is `2`-homogeneous in the state. -/
lemma tBwordBInd_const_mul (N : ℕ) (L d ε c : ℝ) (u : EuclideanSpace ℝ (Fin 3))
    (Ψ : Submission.BoseGases.X N → ℝ) (t : ℝ) :
    Work.UBBInputs8.tBwordBInd N L d ε c u (fun x => t * Ψ x)
      = t ^ 2 * Work.UBBInputs8.tBwordBInd N L d ε c u Ψ := by
  unfold Work.UBBInputs8.tBwordBInd
  exact tBwordInd_const_mul L (Submission.BoseGases.dlBox L d u)
    (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) (L * d) ε c Ψ t

/-! ## 3. The potential half -/

/-- The potential word `qLHSword = ∫_{abox}(Φ x)²·(profile)` is `2`-homogeneous in the state: the
profile does not depend on the state, so the integrand of `t·Φ` is pointwise `t²` times that of `Φ`
and `MeasureTheory.integral_const_mul` pulls the constant out of the box integral. -/
lemma qLHSword_const_mul (ℓ μ : ℝ)
    (w w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (Φ : Submission.BoseGases.X N → ℝ) (t : ℝ) :
    Submission.BoseGases.qLHSword ℓ μ w w1 (fun x => t * Φ x)
      = t ^ 2 * Submission.BoseGases.qLHSword ℓ μ w w1 Φ := by
  unfold Submission.BoseGases.qLHSword
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  ring

/-- The localised potential word `qLHSwordB` is `2`-homogeneous in the state. -/
lemma qLHSwordB_const_mul {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (M : ℕ)
    (L d μ : ℝ) (u : EuclideanSpace ℝ (Fin 3))
    (Ψ : Submission.BoseGases.X N → ℝ) (t : ℝ) :
    Work.SmallBoxSliding.qLHSwordB h M L d μ u (fun x => t * Ψ x)
      = t ^ 2 * Work.SmallBoxSliding.qLHSwordB h M L d μ u Ψ := by
  unfold Work.SmallBoxSliding.qLHSwordB
  exact qLHSword_const_mul L μ _ _ Ψ t

/-! ## 4. The sliding word -/

theorem fibreWord_smul {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (M : ℕ)
    (n : ℕ) (L d ε c μ : ℝ) (u : EuclideanSpace ℝ (Fin 3)) (a : ℝ)
    (Ψ : Submission.BoseGases.X n → ℝ) :
    Work.SlotWord.fibreWord h M n L d ε c μ u (fun x => a * Ψ x)
      = a ^ 2 * Work.SlotWord.fibreWord h M n L d ε c μ u Ψ := by
  unfold Work.SlotWord.fibreWord
  rw [tBwordBInd_const_mul n L d ε c u Ψ a, qLHSwordB_const_mul h M L d μ u Ψ a]
  ring

end Work.BoseFixB1B
