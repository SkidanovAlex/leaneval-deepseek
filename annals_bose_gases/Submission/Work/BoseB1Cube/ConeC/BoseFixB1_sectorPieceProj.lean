import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1S_boxPotsplitExpect
import Submission.Work.BoseFixB1.BoxQ0Value
import Submission.Work.BoseFixB1.CrossWordsDefs
import Submission.Work.BoseFixB1.KernelFacts
import Submission.Work.BoseFixB1.boxPInd_adjoint_int
import Submission.Work.BoseFixB1.bqPotsplit
import Submission.Work.BoseFixB1.fsRegimeAt
import Submission.Work.BoseFixB1.integrableOn_wSmallPair_cube_fixed
import Submission.Work.BoseFixB1.oneValueAnyB1
import Submission.Work.BoseFixB1B.boxFlat_add_boxQ_eq_card
import Submission.Work.BoseFixB1S.boxFlatSqJensen
import Submission.Work.BoseFixB1S.boxPairValue
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
open Work.SmallBoxSliding Work.FockBridge

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The sector indicator is slot-independent on the box

The whole point of the sector decomposition: replacing a slot of a configuration by a point of
the box `A` does not change the *occupancy* of the configuration in `A`, provided the replaced
slot already lies in `A`.  Consequently the sector indicator `1_{n_A = k}` — like every function
of the off-`i` coordinates — is invariant under that replacement, which is exactly what makes the
box projection `P_{B,i}` commute with multiplication by the sector indicator. -/

/-- Replacing slot `i` of `x` by `y ∈ A` does not change the `A`-occupancy when `x i ∈ A`. -/
theorem boxOccupancy_update_of_mem {N : ℕ} {A : Set ℝ³} {i : Fin N}
    {x : Submission.BoseGases.X N} {y : ℝ³} (hxi : x i ∈ A) (hy : y ∈ A) :
    Work.FockBridge.boxOccupancy A (Function.update x i y) = Work.FockBridge.boxOccupancy A x := by
  classical
  rw [Work.FockBridge.boxOccupancy, Work.FockBridge.boxOccupancy]
  congr 1
  refine Finset.filter_congr (fun j _ => ?_)
  rw [Function.update_apply]
  by_cases hji : j = i
  · subst hji
    simp only [if_true]
    exact ⟨fun _ => hxi, fun _ => hy⟩
  · simp only [hji, ↓reduceIte]

/-- The sector membership is unchanged by replacing slot `i` by a point of `A` when `x i ∈ A`. -/
theorem sectorSet_update_mem_iff {N : ℕ} {A : Set ℝ³} {i : Fin N}
    {x : Submission.BoseGases.X N} {y : ℝ³} {k : ℕ} (hxi : x i ∈ A) (hy : y ∈ A) :
    (Function.update x i y ∈ Work.FockBridge.sectorSet A k)
      ↔ (x ∈ Work.FockBridge.sectorSet A k) := by
  rw [Work.FockBridge.mem_sectorSet_iff, Work.FockBridge.mem_sectorSet_iff,
    boxOccupancy_update_of_mem hxi hy]

/-- The sector indicator is invariant under replacing slot `i` by a point of `A` (when `x i ∈ A`):
it only depends on the off-`i` coordinates (up to what happens off `A`). -/
theorem sectorSet_indicator_slotIndep {N : ℕ} {A : Set ℝ³} (i : Fin N) (k : ℕ) :
    ∀ (x : Submission.BoseGases.X N) (y : ℝ³), x i ∈ A → y ∈ A →
      (Work.FockBridge.sectorSet A k).indicator (fun _ => (1 : ℝ)) (Function.update x i y)
        = (Work.FockBridge.sectorSet A k).indicator (fun _ => (1 : ℝ)) x := by
  intro x y hxi hy
  by_cases hmem : x ∈ Work.FockBridge.sectorSet A k
  · rw [Set.indicator_of_mem hmem,
      Set.indicator_of_mem ((sectorSet_update_mem_iff hxi hy).mpr hmem)]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem]
    intro hc
    exact hmem ((sectorSet_update_mem_iff hxi hy).mp hc)

/-- `sectorPiece A k Φ = 1_{n_A = k}·Φ` as a product. -/
theorem sectorPiece_eq_indicator_mul {N : ℕ} (A : Set ℝ³) (k : ℕ)
    (Φ : Submission.BoseGases.X N → ℝ) :
    Work.FockBridge.sectorPiece A k Φ
      = fun x => (Work.FockBridge.sectorSet A k).indicator (fun _ => (1 : ℝ)) x * Φ x := by
  funext x
  rw [Work.FockBridge.sectorPiece]
  by_cases hx : x ∈ Work.FockBridge.sectorSet A k
  · simp only [Set.indicator_of_mem hx, one_mul]
  · simp only [Set.indicator_of_notMem hx, zero_mul]

/-! ## 2. The box projections commute with a slot-independent multiplier -/

/-- **The box projection commutes with multiplication by a slot-`i`-independent factor.**  If
`g` is unchanged by replacing the `i`-th coordinate by any point of `A` (whenever `x i ∈ A`), then
`P_{B,i}(g·Ψ) = g·P_{B,i}Ψ`.  No measurability of `g` or `Ψ` is needed (the slot integral is
linear in the constant `g x`). -/
theorem boxPInd_smul_slotIndep {N : ℕ} (volA : ℝ) {A : Set ℝ³} (hA : MeasurableSet A)
    (i : Fin N) (g : Submission.BoseGases.X N → ℝ)
    (hg : ∀ (x : Submission.BoseGases.X N) (y : ℝ³), x i ∈ A → y ∈ A →
      g (Function.update x i y) = g x)
    (Ψ : Submission.BoseGases.X N → ℝ) :
    Work.UBBInputs8.boxPInd volA A i (fun x => g x * Ψ x)
      = fun x => g x * Work.UBBInputs8.boxPInd volA A i Ψ x := by
  funext x
  rw [Work.UBBInputs8.boxPInd, Work.UBBInputs8.boxPInd]
  by_cases hx : x i ∈ A
  · simp only [Set.indicator_of_mem hx]
    have hfun : (fun z : ℝ³ => g (Function.update x i z) * Ψ (Function.update x i z))
        =ᵐ[MeasureTheory.volume.restrict A]
        (fun z : ℝ³ => g x * Ψ (Function.update x i z)) := by
      filter_upwards [MeasureTheory.self_mem_ae_restrict hA] with z hz
      rw [hg x z hx hz]
    rw [MeasureTheory.integral_congr_ae hfun, MeasureTheory.integral_const_mul]
    ring
  · simp only [Set.indicator_of_notMem hx]
    ring

/-- The same for the mean-free box projection `Q_{B,i} = 1_A(·i) − P_{B,i}`. -/
theorem boxQInd_smul_slotIndep {N : ℕ} (volA : ℝ) {A : Set ℝ³} (hA : MeasurableSet A)
    (i : Fin N) (g : Submission.BoseGases.X N → ℝ)
    (hg : ∀ (x : Submission.BoseGases.X N) (y : ℝ³), x i ∈ A → y ∈ A →
      g (Function.update x i y) = g x)
    (Ψ : Submission.BoseGases.X N → ℝ) :
    Work.UBBInputs8.boxQInd volA A i (fun x => g x * Ψ x)
      = fun x => g x * Work.UBBInputs8.boxQInd volA A i Ψ x := by
  funext x
  rw [Work.BoseFixB1S.boxQInd_eq, Work.BoseFixB1S.boxQInd_eq,
    congrFun (boxPInd_smul_slotIndep volA hA i g hg Ψ) x]
  ring

/-- **The box projection of a sector piece is the sector indicator times the projection.**
This is the *decisive* structural fact of the sector decomposition: the pair/`μ` words of
`boxQSum` at the sector piece are the `1_{n_A = k}`-weighted words of the undiscretised state, so
the *pointwise* identities proved in the corpus for continuous states (e.g.
`Work.BoseFixB1S.boxPairPointwise`) transfer verbatim to the sector piece. -/
theorem boxPInd_sectorPiece {N : ℕ} (volA : ℝ) {A : Set ℝ³} (hA : MeasurableSet A)
    (i : Fin N) (k : ℕ) (Φ : Submission.BoseGases.X N → ℝ) :
    Work.UBBInputs8.boxPInd volA A i (Work.FockBridge.sectorPiece A k Φ)
      = fun x => (Work.FockBridge.sectorSet A k).indicator (fun _ => (1 : ℝ)) x
          * Work.UBBInputs8.boxPInd volA A i Φ x := by
  rw [sectorPiece_eq_indicator_mul]
  exact boxPInd_smul_slotIndep volA hA i _ (sectorSet_indicator_slotIndep i k) Φ

/-- The mean-free analogue of `boxPInd_sectorPiece`. -/
theorem boxQInd_sectorPiece {N : ℕ} (volA : ℝ) {A : Set ℝ³} (hA : MeasurableSet A)
    (i : Fin N) (k : ℕ) (Φ : Submission.BoseGases.X N → ℝ) :
    Work.UBBInputs8.boxQInd volA A i (Work.FockBridge.sectorPiece A k Φ)
      = fun x => (Work.FockBridge.sectorSet A k).indicator (fun _ => (1 : ℝ)) x
          * Work.UBBInputs8.boxQInd volA A i Φ x := by
  rw [sectorPiece_eq_indicator_mul]
  exact boxQInd_smul_slotIndep volA hA i _ (sectorSet_indicator_slotIndep i k) Φ

end Work.BoseFixB1
