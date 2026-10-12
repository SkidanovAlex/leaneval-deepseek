import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixGlue.Sector.FibreBound
import Submission.Work.BoseKinLoc.Sector.fibState_permInvariant
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixGlue.Sector.fibreSumBound_of_LHYBoxB` — the fibre sum bound from the box theorem

FS `thm:CompareBoxEnergy` needs the fibre/box bound `hfib`, whose `C3` node is the sector (fibre)
sum bound `Work.BoseFixGlue.FibreSumBound`.  This module closes the glue: **the box theorem
`Work.BoseBoxFix.LHYBoxB` implies `FibreSumBound` for some diluteness threshold**.

The two ingredients are

* `Work.BoseFixGlue.hEo_hEi_of_LHYBoxB` (proved in `EΛBound`), which extracts from `LHYBoxB` the two
  bounded-below inputs of the per-fibre argument at every admissible `μ`;
* the **summed per-fibre bound** `minMulNorm_le_fibreSumA_aux` below: for a smooth symmetric state
  supported in a translated box `c + abox N L`, the fibre sum dominates `min 0 EΛ · ∫Ψ²`.  Its
  proof is the per-fibre bound `per_fibre_bound` applied to every fibre (smooth by
  `contDiff_fibState`, symmetric by `fibState_permInvariant`), integrated over the outside
  configurations with the junk-compatible monotone integration step, and summed using the norm
  bookkeeping `fibreNormA_eq` (which identifies `∑_S ∫_y sqNormB |S| ℓ (fibState S Ψ y)` with
  `∫ Ψ²`).

`minMulNorm_le_fibreSumA_aux` is textually the assembly proved inside
`Work.BoseKinLoc.Sector.min_mul_norm_le_fibreSumA`; it is reproduced here because that module
(`Submission/Work/BoseKinLoc/Sector/fibre_bound_v3.lean`) is a *SKELETON* whose main declaration is
still open, and this file belongs to the complete (no open goals) import cone of the theorem.
-/

noncomputable section

open scoped Real Topology BigOperators ENNReal
open MeasureTheory Filter Metric

namespace Work.BoseFixGlue.Sector

open _root_.BoseGases Submission.BoseGases Work.UBB Work.UBBInputs3 Work.BoseBox Work.BoseKinLoc
open Work.BoseBoxFix

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The junk-compatible monotone integration step -/

/-- **Monotone integration, junk-compatible.**  If `g ≤ f` pointwise, `g` is integrable and `g` is
pointwise nonpositive, then `∫ g ≤ ∫ f`.  No integrability of `f` is needed: if `f` is integrable
this is `integral_mono`, and otherwise `∫ f` is the junk value `0`, which dominates `∫ g ≤ 0`.
This is the form in which the per-fibre bound is integrated: the potential integrands of the fibre
forms need not be integrable, and the inequality is the direction in which the junk convention is
harmless. -/
lemma integral_le_of_le_of_nonpos_fibre {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (h : ∀ y, g y ≤ f y) (hg : Integrable g μ) (hgnp : ∀ y, g y ≤ 0) :
    ∫ y, g y ∂μ ≤ ∫ y, f y ∂μ := by
  by_cases hf : Integrable f μ
  · exact integral_mono hg hf h
  · rw [integral_undef hf]
    exact integral_nonpos fun y => hgnp y

/-! ## 2. The per-fibre bound, summed over the slot sets -/

/-- **The per-fibre bound, integrated over the outside configurations.**  For a smooth symmetric
state `Ψ` supported in the translated box `c + abox N L`, the fibre sum dominates `min 0 EΛ` times
the total squared norm: the per-fibre bound `per_fibre_bound` is applied to each fibre (smooth by
`contDiff_fibState`, symmetric by `fibState_permInvariant`) and integrated, the fibre box mass being
integrable (`integrable_sqNormB_fibStateA`) and the integration of the pointwise inequality being
junk-compatible (`integral_le_of_le_of_nonpos_fibre`), with the norm bookkeeping `fibreNormA_eq`. -/
theorem minMulNorm_le_fibreSumA_aux {N : ℕ} {v g : ℝ³ → ℝ} {ℓ μ d s εT b : ℝ} (hℓ : 0 < ℓ)
    (hEo : BddBelow (Set.range (fun m : ℕ => EΛn m v g ℓ μ d s εT b)))
    (hEi : ∀ m : ℕ, BddBelow (Set.range (fun Φ : BoxState m ℓ =>
      boxFormB m v g ℓ μ d s εT b Φ / sqNormB m ℓ Φ)))
    {c : ℝ³} {L : ℝ} {Ψ : X N → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ)
    (hsym : PermInvariant N Ψ)
    (hsupp : tsupport Ψ ⊆ (fun x : X N => fun i : Fin N => c + x i) '' abox N L) :
    min 0 (EΛ v g ℓ μ d s εT b) * (∫ z : X N, (Ψ z) ^ 2)
      ≤ Work.BoseKinLoc.Sector.fibreSumA v g ℓ μ d s εT b
          ((fun z : ℝ³ => c + z) '' acube (max L ℓ)) Ψ := by
  rw [← Work.BoseKinLoc.Sector.fibreNormA_eq (ℓ := ℓ) hℓ (c := c) (L := L) hΨ hsupp]
  rw [Work.BoseKinLoc.Sector.fibreSumA, Work.BoseKinLoc.Sector.fibreNormA, Finset.mul_sum]
  refine Finset.sum_le_sum fun S _ => ?_
  refine le_trans (le_of_eq (integral_const_mul _ _).symm) ?_
  exact integral_le_of_le_of_nonpos_fibre
    (μ := volume.restrict (Work.PerSector.slotBox (ι := Work.PerSector.SlotOut N S)
      (((fun z : ℝ³ => c + z) '' acube (max L ℓ)) ∩ (acube ℓ)ᶜ)))
    (g := fun y : Work.PerSector.SlotOut N S → ℝ³ =>
      min 0 (EΛ v g ℓ μ d s εT b) * sqNormB S.card ℓ (Work.BoseKinLoc.Sector.fibState S Ψ y))
    (f := fun y : Work.PerSector.SlotOut N S → ℝ³ =>
      boxFormB S.card v g ℓ μ d s εT b (Work.BoseKinLoc.Sector.fibState S Ψ y))
    (fun y => Work.BoseKinLoc.Sector.per_fibre_bound hℓ hEo hEi
      (Work.BoseKinLoc.Sector.contDiff_fibState S hΨ y)
      (Work.BoseKinLoc.Sector.fibState_permInvariant hsym y))
    ((Work.BoseKinLoc.Sector.integrable_sqNormB_fibStateA hℓ S hΨ hsupp).const_mul _)
    (fun y => mul_nonpos_of_nonpos_of_nonneg (min_le_left _ _)
      (integral_nonneg fun z => sq_nonneg _))

/-! ## 3. `FibreSumBound` from `LHYBoxB` -/

/-- **`LHYBoxB` implies the fibre sum bound.**  With the diluteness threshold `ε₀` supplied by the box
theorem (`hEo_hEi_of_LHYBoxB`), every admissible `μ` carries the two bounded-below hypotheses needed
by the summed per-fibre bound `minMulNorm_le_fibreSumA_aux` at `ℓ = ℓB v μ`; the box side
`ℓB v μ = sideAt μ (a v)` is positive by `sideB_pos`.  This is exactly `FibreSumBound v h ε₀`. -/
theorem fibreSumBound_of_LHYBoxB {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {η₀ C : ℝ} (hav : 0 < BoseGases.a v) (hC : 0 ≤ C)
    (hL : Work.BoseBoxFix.LHYBoxB v h η₀ C) :
    ∃ ε : ℝ, 0 < ε ∧ Work.BoseFixGlue.FibreSumBound v h ε := by
  obtain ⟨ε₀, hε₀, hEoEi⟩ := hEo_hEi_of_LHYBoxB hav hC hL
  refine ⟨ε₀, hε₀, fun μ hμ N L c Ψ hΨ hsym hsupp => ?_⟩
  obtain ⟨hEo, hEi⟩ := hEoEi μ hμ
  exact minMulNorm_le_fibreSumA_aux (ℓ := ℓB v μ) (sideB_pos hμ.1 hav) hEo hEi hΨ hsym hsupp

end Work.BoseFixGlue.Sector
