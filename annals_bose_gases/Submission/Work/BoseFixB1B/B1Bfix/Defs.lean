import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.sectorCountBoxAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.B1Bfix.Defs`

Vocabulary for the target `Work.BoseFixB1B.tendsto_tBdiagFormInd_cut`.

The target is the convergence, as `δ → 0⁺`, of the `p`-diagonal kinetic form
`Work.UBBInputs8.tBdiagFormInd L (dlBox L d u) (boxMass L d u) (chiB L d u) (fsKinCoeff c)`
evaluated at the smooth approximants `Ψ_δ = cutProd (γ δ) ψ` of the sharp box state
`sharpBoxState (dlBox L d u) ψ`.

By `Work.UBBInputs9.A.tBdiagFormInd_eq_tBdiagForm` (the window `chiB L d u` is supported in
`dlBox L d u`) the FS-faithful form with the box indicator coincides with the corpus form
`Work.SmallBoxTBWord.tBdiagForm` with the indicator-free projection; and that form is, by
definition, the sum over the slots `i : Fin (n+1)` of the quantities defined here:

* `slotAmpF` — the windowed slot-`i` amplitude `tBamp χ p (Q_{B,i}v) i x` (the `p`-mode
  amplitude of the mean-free, windowed slot fibre);
* `slotY a A volA χ i v p` — the `x`-energy of that amplitude at the frequency `p`,
  `(a³)⁻¹∫_{abox} ‖slotAmpF‖²`;
* `slotFormL a A volA χ F i v` — the slot contribution to the form, `(2π)⁻³∫_p F‖p‖·slotY`;
* `fibreDirI a A volA χ i v` — the *position-space* Dirichlet energy of the windowed
  mean-free slot fibre `y ↦ χ y · Q_{B,i}v(kcInsN n i (y,r))`, integrated over the outside
  configuration `r`;
* `fibreMassI a A volA χ i v` — the `L²`-mass of the same fibre.

The two latter quantities are the ones that dominate `slotFormL` for the symbols `‖·‖²` and `1`
(`slotFormL ... (·)² ≤ fibreDirI`, `slotFormL ... 1 ≤ fibreMassI`), and they converge to `0`
along the difference `Ψ_δ − sharpBoxState` (the `H¹`-convergence of the sharp-fibre extension).
-/

noncomputable section

open MeasureTheory
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-- The windowed slot-`i` amplitude of the state `v`, at frequency `p` and configuration `x`. -/
noncomputable def slotAmpF {n : ℕ} (a : ℝ) (A : Set E3) (volA : ℝ) (χ : E3 → ℝ) (i : Fin (n + 1))
    (v : Submission.BoseGases.X (n + 1) → ℝ) (p : E3)
    (x : Submission.BoseGases.X (n + 1)) : ℂ :=
  Work.SmallBoxTBWord.tBamp χ p (Work.SmallBoxTBWord.boxQ volA A i v) i x

/-- The difference of the windowed slot amplitudes of two states. -/
noncomputable def slotAmpDiff {n : ℕ} (a : ℝ) (A : Set E3) (volA : ℝ) (χ : E3 → ℝ)
    (i : Fin (n + 1)) (v w : Submission.BoseGases.X (n + 1) → ℝ) (p : E3)
    (x : Submission.BoseGases.X (n + 1)) : ℂ :=
  slotAmpF a A volA χ i v p x - slotAmpF a A volA χ i w p x

/-- The `x`-energy of the *difference* of two slot amplitudes. -/
noncomputable def slotYDiff {n : ℕ} (a : ℝ) (A : Set E3) (volA : ℝ) (χ : E3 → ℝ)
    (i : Fin (n + 1)) (v w : Submission.BoseGases.X (n + 1) → ℝ) (p : E3) : ℝ :=
  (a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n + 1) a,
    ‖slotAmpDiff a A volA χ i v w p x‖ ^ 2

/-- The slot contribution to the `p`-diagonal form of the *difference* of two slot amplitudes. -/
noncomputable def slotFormDiff {n : ℕ} (a : ℝ) (A : Set E3) (volA : ℝ) (χ : E3 → ℝ)
    (F : ℝ → ℝ) (i : Fin (n + 1)) (v w : Submission.BoseGases.X (n + 1) → ℝ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, F ‖p‖ * slotYDiff a A volA χ i v w p

/-- The `x`-energy of the slot-`i` amplitude at the frequency `p`. -/
noncomputable def slotY {n : ℕ} (a : ℝ) (A : Set E3) (volA : ℝ) (χ : E3 → ℝ) (i : Fin (n + 1))
    (v : Submission.BoseGases.X (n + 1) → ℝ) (p : E3) : ℝ :=
  (a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n + 1) a,
    ‖slotAmpF a A volA χ i v p x‖ ^ 2

/-- The slot-`i` contribution to the `p`-diagonal form with the symbol `F`. -/
noncomputable def slotFormL {n : ℕ} (a : ℝ) (A : Set E3) (volA : ℝ) (χ : E3 → ℝ) (F : ℝ → ℝ)
    (i : Fin (n + 1)) (v : Submission.BoseGases.X (n + 1) → ℝ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, F ‖p‖ * slotY a A volA χ i v p

/-- The fibre Dirichlet energy of the windowed mean-free slot-`i` fibre. -/
noncomputable def fibreDirI {n : ℕ} (a : ℝ) (A : Set E3) (volA : ℝ) (χ : E3 → ℝ)
    (i : Fin (n + 1)) (v : Submission.BoseGases.X (n + 1) → ℝ) : ℝ :=
  ∫ r in Submission.BoseGases.abox n a, ∫ y in Submission.BoseGases.acube a,
    ∑ k : Fin 3, (fderiv ℝ (fun z : E3 => χ z * Work.SmallBoxTBWord.boxQ volA A i v
      (Submission.BoseGases.kcInsN n i (z, r))) y (Submission.BoseGases.kcStdBasis k)) ^ 2

/-- The `L²`-mass of the windowed mean-free slot-`i` fibre. -/
noncomputable def fibreMassI {n : ℕ} (a : ℝ) (A : Set E3) (volA : ℝ) (χ : E3 → ℝ)
    (i : Fin (n + 1)) (v : Submission.BoseGases.X (n + 1) → ℝ) : ℝ :=
  ∫ r in Submission.BoseGases.abox n a, ∫ y in Submission.BoseGases.acube a,
    (χ y * Work.SmallBoxTBWord.boxQ volA A i v (Submission.BoseGases.kcInsN n i (y, r))) ^ 2

/-- The windowed mean-free slot fibre of slot `i` of the state `v`, as a function of the slot
position `y` (the outside configuration `r` is a parameter). -/
noncomputable def slotFibreFun {n : ℕ} (A : Set E3) (volA : ℝ) (χ : E3 → ℝ) (i : Fin (n + 1))
    (v : Submission.BoseGases.X (n + 1) → ℝ) (r : Submission.BoseGases.X n) : E3 → ℝ :=
  fun y : E3 => χ y * Work.SmallBoxTBWord.boxQ volA A i v (Submission.BoseGases.kcInsN n i (y, r))

@[simp] theorem slotAmpF_apply {n : ℕ} (a : ℝ) (A : Set E3) (volA : ℝ) (χ : E3 → ℝ)
    (i : Fin (n + 1)) (v : Submission.BoseGases.X (n + 1) → ℝ) (p : E3)
    (x : Submission.BoseGases.X (n + 1)) :
    slotAmpF a A volA χ i v p x = Work.SmallBoxTBWord.tBamp χ p
      (Work.SmallBoxTBWord.boxQ volA A i v) i x := rfl

@[simp] theorem slotFibreFun_apply {n : ℕ} (A : Set E3) (volA : ℝ) (χ : E3 → ℝ)
    (i : Fin (n + 1)) (v : Submission.BoseGases.X (n + 1) → ℝ) (r : Submission.BoseGases.X n)
    (y : E3) :
    slotFibreFun A volA χ i v r y
      = χ y * Work.SmallBoxTBWord.boxQ volA A i v (Submission.BoseGases.kcInsN n i (y, r)) :=
  rfl

/-- `fibreDirI` is the `r`-integral of the Dirichlet energy of the slot fibre. -/
theorem fibreDirI_eq {n : ℕ} (a : ℝ) (A : Set E3) (volA : ℝ) (χ : E3 → ℝ) (i : Fin (n + 1))
    (v : Submission.BoseGases.X (n + 1) → ℝ) :
    fibreDirI a A volA χ i v
      = ∫ r in Submission.BoseGases.abox n a, ∫ y in Submission.BoseGases.acube a,
          ∑ k : Fin 3, (fderiv ℝ (slotFibreFun A volA χ i v r) y
            (Submission.BoseGases.kcStdBasis k)) ^ 2 := rfl

/-- The slot decomposition of `Work.SmallBoxTBWord.tBdiagForm`. -/
theorem tBdiagForm_eq_sum_slotFormL {n : ℕ} (a : ℝ) (A : Set E3) (volA : ℝ) (χ : E3 → ℝ)
    (F : ℝ → ℝ) (v : Submission.BoseGases.X (n + 1) → ℝ) :
    Work.SmallBoxTBWord.tBdiagForm a A volA χ F v
      = ∑ i : Fin (n + 1), slotFormL a A volA χ F i v := by
  unfold Work.SmallBoxTBWord.tBdiagForm slotFormL slotY slotAmpF
  rfl

/-- `[r−c]₊² ≤ 2r² + 2c²` for all real `r, c`. -/
theorem fsKinCoeff_le_two_mul_sq_add {c r : ℝ} :
    Submission.BoseGases.fsKinCoeff c r ≤ 2 * r ^ 2 + 2 * c ^ 2 := by
  have h1 : Submission.BoseGases.fsKinCoeff c r = (max (r - c) 0) ^ 2 := rfl
  have h2 : max (r - c) 0 ≤ |r - c| := max_le (le_abs_self _) (abs_nonneg _)
  have h3 : (max (r - c) 0) ^ 2 ≤ (r - c) ^ 2 := by
    have h0 : 0 ≤ max (r - c) 0 := le_max_right _ _
    nlinarith [abs_nonneg (r - c), sq_abs (r - c), h2, h0]
  nlinarith [h3, sq_nonneg (r - c), sq_nonneg r, sq_nonneg c, sq_nonneg (r + c),
    sq_nonneg (r - c)]

end Work.BoseFixB1B
