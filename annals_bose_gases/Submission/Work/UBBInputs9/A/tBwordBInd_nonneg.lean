import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs9.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs9.A.tBwordBInd_nonneg`

The FS-faithful box word `𝒯_{B(u)}` of the sliding chapter,
`tBwordBInd N ℓ d ε c u Φ = tbGapCoeff (ℓ d) ε · cnPlusBoxInd + tBwordKinInd`,
is **nonnegative** for `0 ≤ ε`, for every `u` and every state `Φ`.

The shape is the same as the corpus's `Work.UBBInputs8.A.tBwordB_nonneg`, but
here the projections are FS's own `boxQInd volA A i Φ = 1_A(x_i)Φ − P_{B,i}Φ`
(with the box indicator, `Work.UBBInputs8/Defs.lean`).  Both summands are
"nonnegative coefficient × integral of a nonnegative pointwise quantity":

* the gap half `tbGapCoeff s ε · cnPlusBoxInd` — the coefficient is
  `½ε_T(1+π⁻²)⁻¹s⁻² ≥ 0` for `0 ≤ ε` (`tbGapCoeff_nonneg`) and the count is a
  sum of integrals of squares;
* the spectral half `tBwordKinInd = tBdiagFormInd a A volA χ (fsKinCoeff c)` —
  the symbol `fsKinCoeff c r = [r−c]₊² ≥ 0` and the `p`-integrand is a
  nonnegative symbol times `(a³)⁻¹·∫_{abox N a}‖·‖²`.

The one point needing care is the slot-volume normalisation `(a³)⁻¹` of
`tBdiagFormInd`: it *is* negative when `a < 0`, but in that regime the centred
box is empty — `acube a = ∅` for `a < 0`, hence `abox N a = ∅` as soon as a slot
`i : Fin N` exists, and the `i`-summand that carries the factor is indexed by an
`i : Fin N` — so the whole factor is `0`.  This is why the statement needs no
sign hypothesis on the box side `ℓ` (the hypothesis `0 < ℓ` is not even used).
-/

noncomputable section

open MeasureTheory

namespace Work.UBBInputs9.A

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
slot `i : Fin N`. -/
private lemma abox_eq_empty_of_neg {N : ℕ} {a : ℝ} (ha : a < 0) (i : Fin N) :
    abox N a = ∅ := by
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hx
  exact not_mem_acube_of_neg ha (x i) ((mem_abox_iff N a x).mp hx i)

/-! ## 2  Nonnegativity of the normalised slot content -/

/-- **The slot-volume normalisation is harmless.**  For any real `a`, any
occupied slot `i : Fin N` and any `g`, the normalised slot content
`(a³)⁻¹·∫_{abox N a}g²` is nonnegative. -/
private lemma inv_cube_mul_abox_integral_sq_nonneg (a : ℝ) {N : ℕ} (i : Fin N)
    (g : X N → ℝ) : 0 ≤ (a ^ 3)⁻¹ * ∫ x in abox N a, g x ^ 2 := by
  rcases le_or_gt 0 a with ha | ha
  · exact mul_nonneg (inv_nonneg.mpr (pow_nonneg ha 3))
      (integral_nonneg fun x => sq_nonneg (g x))
  · rw [abox_eq_empty_of_neg ha i]
    simp

/-! ## 3  The FS-faithful count and the `p`-diagonal form -/

/-- The FS-faithful excited count is a sum of integrals of squares. -/
private lemma cnPlusBoxInd_nonneg (a : ℝ) (A : Set ℝ³) (volA : ℝ) {N : ℕ}
    (Ψ : X N → ℝ) : 0 ≤ Work.UBBInputs8.cnPlusBoxInd a A volA Ψ := by
  unfold Work.UBBInputs8.cnPlusBoxInd
  exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun x => sq_nonneg _))

/-- `tBdiagFormInd` is nonnegative for a nonnegative symbol, for **every** real
box side `a` (no `0 ≤ a` hypothesis: see
`inv_cube_mul_abox_integral_sq_nonneg`). -/
private lemma tBdiagFormInd_nonneg_of_nonneg {a : ℝ} {A : Set ℝ³} {volA : ℝ}
    {χ : ℝ³ → ℝ} {F : ℝ → ℝ} {N : ℕ} {Ψ : X N → ℝ} (hF : ∀ r, 0 ≤ F r) :
    0 ≤ Work.UBBInputs8.tBdiagFormInd a A volA χ F Ψ := by
  unfold Work.UBBInputs8.tBdiagFormInd
  refine Finset.sum_nonneg fun i _ => ?_
  refine mul_nonneg (le_of_lt Work.SmallBoxTBWord.twoPiInv3_pos) ?_
  refine integral_nonneg fun p => mul_nonneg (hF ‖p‖) ?_
  exact inv_cube_mul_abox_integral_sq_nonneg a i
    (fun x => ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA A i Ψ) i x‖)

/-! ## 4  The target -/

theorem tBwordBInd_nonneg {N : ℕ} {ℓ d ε c : ℝ} (hℓ : 0 < ℓ) (hε : 0 ≤ ε)
    (u : EuclideanSpace ℝ (Fin 3)) (Φ : Submission.BoseGases.X N → ℝ) :
    0 ≤ Work.UBBInputs8.tBwordBInd N ℓ d ε c u Φ := by
  unfold Work.UBBInputs8.tBwordBInd Work.UBBInputs8.tBwordInd
  refine add_nonneg (mul_nonneg ?_ ?_) ?_
  · exact Work.SmallBoxTBWord.tbGapCoeff_nonneg hε
  · exact cnPlusBoxInd_nonneg _ _ _ _
  · unfold Work.UBBInputs8.tBwordKinInd
    exact tBdiagFormInd_nonneg_of_nonneg fun r => fsKinCoeff_nonneg c r

end Work.UBBInputs9.A
