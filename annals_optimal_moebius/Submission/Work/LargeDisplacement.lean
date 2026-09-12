import Submission.Work.FoliationInterface
import Submission.Work.BendArcFacts

open OptimalMoebius Topology ContDiff
open scoped BigOperators Matrix Topology Metric
set_option autoImplicit false
set_option maxHeartbeats 800000
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-!
# The large-displacement reduction of Lemma G

For the `f`-relative band foliation `F : BandFoliation a f hf` the free
relation (3) of Lemma G (`BendArcFacts.chord_length_le_sub_abs_delta`) is
available at every leaf:

    √(1 + Δ(y)²) ≤ a − |Δ(y)|           (relation (3), FREE)

Since `x ↦ x + √(1+x²)` is strictly increasing with
`1/√3 + √(4/3) = √3`, relation (3) at a single leaf already gives the
theorem whenever that leaf has `|Δ| > 1/√3`
(`BandFoliation.aspect_gt_of_large_delta`).  So Lemma G is only needed in
the regime `sup_y |Δ(y)| ≤ 1/√3`; there relation (4) (`√(5+t²) < a+t`,
the Figure-2 apex/trapezoid content) carries the whole load.

Also recorded: the Pythagoras identity for a perpendicular pair of leaves,
`‖leafVec y' − leafVec y‖² = ‖leafVec y'‖² + ‖leafVec y‖²`, which is the
exact vector content of the T-pattern's perpendicularity.

Build: `lake build Submission.Work.LargeDisplacement` (rc=0 target).
-/

noncomputable section
namespace Submission

open Submission.PaperBand

/-! ## 1. The pure algebra of relation (3) at a large displacement -/

/-- **`x ↦ x + √(1+x²)` is strictly increasing on `[0,∞)`.** -/
lemma add_sqrt_one_add_sq_lt {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    x + Real.sqrt (1 + x ^ 2) < y + Real.sqrt (1 + y ^ 2) := by
  have hy : 0 ≤ y := le_of_lt (lt_of_le_of_lt hx hxy)
  have hx2 : x ^ 2 < y ^ 2 := by nlinarith
  have hsq : Real.sqrt (1 + x ^ 2) < Real.sqrt (1 + y ^ 2) :=
    Real.sqrt_lt_sqrt (by positivity) (by linarith)
  linarith

/-- **The extremal value**: `1/√3 + √(1 + 1/3) = √3`. -/
lemma inv_sqrt_three_add :
    Real.sqrt (3 : ℝ)⁻¹ + Real.sqrt (1 + (Real.sqrt (3 : ℝ)⁻¹) ^ 2) = Real.sqrt 3 := by
  have hsq : (Real.sqrt (3 : ℝ)⁻¹) ^ 2 = (3 : ℝ)⁻¹ := Real.sq_sqrt (by positivity)
  have hroot : Real.sqrt (1 + (Real.sqrt (3 : ℝ)⁻¹) ^ 2) = 2 * Real.sqrt (3 : ℝ)⁻¹ := by
    rw [hsq]
    have hone : (1 : ℝ) + (3 : ℝ)⁻¹ = 4 * (3 : ℝ)⁻¹ := by norm_num
    rw [hone]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  rw [hroot, Real.sqrt_inv]
  have h3 : Real.sqrt 3 * Real.sqrt 3 = (3 : ℝ) := by
    rw [← sq, Real.sq_sqrt (by norm_num)]
  have hne : Real.sqrt 3 ≠ 0 := by positivity
  field_simp
  linarith [h3]

/-- **Relation (3) at a large displacement gives the theorem**: if a leaf's
chord displacement `t` satisfies `√(1+t²) ≤ a − |t|` (relation (3)) and
`1/√3 < |t|`, then `√3 < a`. -/
theorem aspect_gt_of_chord_bound {a t : ℝ} (ha : 0 < a)
    (ht : Real.sqrt (3 : ℝ)⁻¹ < |t|)
    (h3 : Real.sqrt (1 + t ^ 2) ≤ a - |t|) : Real.sqrt 3 < a := by
  have ht0 : 0 ≤ |t| := abs_nonneg t
  have hstep := add_sqrt_one_add_sq_lt (Real.sqrt_nonneg (3:ℝ)⁻¹) ht
  rw [inv_sqrt_three_add] at hstep
  have htsq : Real.sqrt (1 + t ^ 2) = Real.sqrt (1 + |t| ^ 2) := by rw [sq_abs]
  rw [htsq] at h3
  have hsum : |t| + Real.sqrt (1 + |t| ^ 2) ≤ a := by linarith
  linarith

/-! ## 2. Instantiation for the band foliation -/

namespace BandFoliation

variable {a : ℝ} {f : ℝ² → ℝ³} {hf : IsMoebiusEmbedding a f}

/-- **A leaf with large displacement already proves the theorem.** -/
theorem aspect_gt_of_large_delta (F : BandFoliation a f hf) (ha : 0 < a) {y : ℝ}
    (hbig : Real.sqrt (3 : ℝ)⁻¹ < |Δ F y|) : Real.sqrt 3 < a := by
  have hA : A F y = !₂[0, (A F y) 1] := leftEdge_eq_vec (A_left_coord F y)
  have hB : B F y = !₂[1, (B F y) 1] := rightEdge_eq_vec (B_right_coord F y)
  have himg : ‖f !₂[1, (B F y) 1] - f !₂[0, (A F y) 1]‖
      = ‖(!₂[1, (B F y) 1] : ℝ²) - !₂[0, (A F y) 1]‖ := by
    have hp := F.preBend y
    have e1 : f !₂[1, (B F y) 1] = f (B F y) := congrArg f hB.symm
    have e2 : f !₂[0, (A F y) 1] = f (A F y) := congrArg f hA.symm
    have e3 : (!₂[1, (B F y) 1] : ℝ²) = B F y := hB.symm
    have e4 : (!₂[0, (A F y) 1] : ℝ²) = A F y := hA.symm
    rw [e1, e2, e3, e4]
    exact hp
  have h3 := chord_length_le_sub_abs_delta hf ha ((A F y) 1) ((B F y) 1) himg
  have hΔ : ((B F y) 1) - ((A F y) 1) = Δ F y := by
    unfold Δ BendData.slope; simp [A, B]
  rw [hΔ] at h3
  exact aspect_gt_of_chord_bound ha hbig h3

/-! ## 3. The Pythagoras identity for perpendicular pairs of leaves -/

/-- The leaf vector as a `‖·‖⁻¹ •` multiple of the unit image direction. -/
lemma leafVec_eq_norm_smul' (F : BandFoliation a f hf) (y : ℝ) :
    leafVec F y = ‖leafVec F y‖ • imageDir F y := by
  have hne : (‖leafVec F y‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr (imageChord_ne_zero F y)
  have hs : (‖leafVec F y‖ : ℝ) • ((‖leafVec F y‖ : ℝ)⁻¹ • leafVec F y) = leafVec F y := by
    rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
  rw [imageDir]
  exact hs.symm

/-- **Pythagoras for a perpendicular pair of leaves**: if the leaf vectors
at `y` and `y'` are perpendicular then
`‖leafVec y' − leafVec y‖² = ‖leafVec y'‖² + ‖leafVec y‖²`, purely because
`leafVec y' − leafVec y = (fB(y')−fB(y)) − (fA(y')−fA(y))`. -/
theorem leafVec_perp_sq_identity (F : BandFoliation a f hf) {y y' : ℝ}
    (hperp : inner ℝ (leafVec F y) (leafVec F y') = 0) :
    ‖(f (B F y') - f (B F y)) - (f (A F y') - f (A F y))‖ ^ 2
      = ‖leafVec F y'‖ ^ 2 + ‖leafVec F y‖ ^ 2 := by
  have hdecomp : (f (B F y') - f (B F y)) - (f (A F y') - f (A F y))
      = leafVec F y' - leafVec F y := by
    unfold leafVec; abel
  have hcomm : inner ℝ (leafVec F y') (leafVec F y) = 0 := by
    rw [real_inner_comm]; exact hperp
  rw [hdecomp]
  simpa only [sq] using norm_sub_sq_eq_norm_sq_add_norm_sq_real hcomm

end BandFoliation

end Submission
