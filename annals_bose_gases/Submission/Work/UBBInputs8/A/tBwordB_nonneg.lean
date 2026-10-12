import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs8.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs8.A.tBwordB_nonneg`

The per-`u` spectral word `𝒯_B` of the sliding chapter,
`tBwordB N L d ε c u Φ = tbGapCoeff (L*d) ε · cnPlusBoxB + tBwordKinB`, is
**nonnegative** for `0 ≤ ε`, for *every* `L` (in particular with no side
hypothesis `0 ≤ L`).

Both summands are of the form "nonnegative coefficient × integral of a
nonnegative pointwise quantity".  The one point that needs care is the
spectral half, `tBwordKin`, whose `p`-integrand carries the slot-volume
normalisation `(a³)⁻¹ = (L³)⁻¹`: this factor *is* negative when `L < 0`, but
in that regime the centred box is empty — `acube L = ∅` for `L < 0`, hence
`abox N L = ∅` as soon as `N` is nonempty, and the `i`-summand that carries
the factor is indexed by an `i : Fin N` — so the whole factor is `0`
(`inv_cube_mul_abox_integral_sq_nonneg`).  Thus `tBdiagForm` is nonnegative
for an arbitrary nonnegative symbol with no sign condition on the box side
(`tBdiagForm_nonneg_of_nonneg`), which is exactly what the requested
statement needs at the sliding parameters.
-/

noncomputable section

open MeasureTheory

namespace Work.UBBInputs8.A

open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1  The degenerate centred box -/

/-- The centred cube of negative side contains no point: `a < 0 → y ∉ acube a`. -/
private lemma not_mem_acube_of_neg {a : ℝ} (ha : a < 0) (y : ℝ³) : y ∉ acube a := by
  intro hy
  have h0 : y 0 ∈ Set.Icc (-a / 2) (a / 2) := hy 0
  rw [Set.mem_Icc] at h0
  linarith [h0.1, h0.2]

/-- The `N`-particle centred box of negative side is empty, for any occupied
slot `i : Fin N` (so in particular at every `N ≥ 1`). -/
private lemma abox_eq_empty_of_neg {N : ℕ} {a : ℝ} (ha : a < 0) (i : Fin N) :
    abox N a = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  exact not_mem_acube_of_neg ha (x i) ((mem_abox_iff N a x).mp hx i)

/-! ## 2  Nonnegativity of the normalised slot content -/

/-- **The slot-volume normalisation is harmless.**  For any real `a`, any
occupied slot `i : Fin N` and any `g`, the normalised slot content
`(a³)⁻¹·∫_{abox N a}g²` is nonnegative: for `a ≥ 0` both factors of the product
are nonnegative, and for `a < 0` the box `abox N a` is empty by
`abox_eq_empty_of_neg` (which is available because the summand is indexed by
`i : Fin N`). -/
private lemma inv_cube_mul_abox_integral_sq_nonneg (a : ℝ) {N : ℕ} (i : Fin N)
    (g : X N → ℝ) : 0 ≤ (a ^ 3)⁻¹ * ∫ x in abox N a, g x ^ 2 := by
  rcases le_or_gt 0 a with ha | ha
  · exact mul_nonneg (inv_nonneg.mpr (pow_nonneg ha 3))
      (integral_nonneg fun x => sq_nonneg (g x))
  · rw [abox_eq_empty_of_neg ha i]
    simp

/-! ## 3  The `p`-diagonal form and the spectral half, with no sign condition on the box -/

/-- `tBdiagForm` is nonnegative for a nonnegative symbol, for **every** real
box side `a` (no `0 ≤ a` hypothesis: see `inv_cube_mul_abox_integral_sq_nonneg`). -/
private lemma tBdiagForm_nonneg_of_nonneg {a : ℝ} {A : Set ℝ³} {volA : ℝ}
    {χ : ℝ³ → ℝ} {F : ℝ → ℝ} {N : ℕ} {Ψ : X N → ℝ} (hF : ∀ r, 0 ≤ F r) :
    0 ≤ Work.SmallBoxTBWord.tBdiagForm a A volA χ F Ψ := by
  unfold Work.SmallBoxTBWord.tBdiagForm
  refine Finset.sum_nonneg fun i _ => ?_
  refine mul_nonneg (le_of_lt Work.SmallBoxTBWord.twoPiInv3_pos) ?_
  refine integral_nonneg fun p => mul_nonneg (hF ‖p‖) ?_
  exact inv_cube_mul_abox_integral_sq_nonneg a i
    (fun x => ‖Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ volA A i Ψ) i x‖)

/-! ## 4  The target -/

theorem tBwordB_nonneg {N : ℕ} (L d ε c : ℝ) (hε : 0 ≤ ε)
    (u : EuclideanSpace ℝ (Fin 3)) (Φ : Submission.BoseGases.X N → ℝ) :
    0 ≤ Work.SmallBoxTBWord.tBwordB N L d ε c u Φ := by
  unfold Work.SmallBoxTBWord.tBwordB Work.SmallBoxTBWord.tBword
  refine add_nonneg (mul_nonneg ?_ ?_) ?_
  · exact Work.SmallBoxTBWord.tbGapCoeff_nonneg hε
  · exact Work.SmallBoxTBWord.cnPlusBox_nonneg _ _ _ _
  · unfold Work.SmallBoxTBWord.tBwordKin
    exact tBdiagForm_nonneg_of_nonneg fun r => fsKinCoeff_nonneg c r

end Work.UBBInputs8.A
