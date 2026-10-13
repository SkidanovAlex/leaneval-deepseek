/-
# `E4R3/NRow2_honest_Aux` — helpers for the honest row 2

Two ingredients of the honest (open-quadrant) port of `Work.FTS.NonlinRows.NRow2`:

* `smoothOpen_differentiableAt_slice_mixed` — the open-quadrant analogue of
  `Work.FTS.LocData.SmoothQuad.differentiableAt_slice_mixed` (the `z`-slices of the mixed
  derivatives of a `SmoothOpen` function are differentiable on `(0,∞)`);
* `radial_leibniz_open` — `Work.FTS.Nonlinear.Pieces.radial_leibniz` with the interior class
  `SmoothQuad h` weakened to `SmoothOpen h`;
* `slot_sum_sq_le` — the binomial-slot Cauchy–Schwarz of `NRow2` (verbatim).
-/
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.NonlinRows.NRow2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-- **The `z`-slices of the mixed derivatives of a `SmoothOpen` function are differentiable
on the open half-line.**  This is the open-quadrant analogue of
`Work.FTS.LocData.SmoothQuad.differentiableAt_slice_mixed`. -/
theorem smoothOpen_differentiableAt_slice_mixed {G : ℝ → ℝ → ℝ}
    (hG : Work.FTS.EllipticEst.SmoothOpen G) (b i : ℕ)
    {z : ℝ} (hz : 0 < z) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    DifferentiableAt ℝ (fun z' => Work.Spaces.mixed b i G z' θ) z :=
  (((hG.mixed b i).curry_z hθ).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
    (isOpen_Ioi.mem_nhds hz)

/-- **The pointwise Leibniz rule for a radial factor, in the open-quadrant class.**  For
`j ≤ 4`, `z > 0`, `θ ∈ (0,π/2)`, if the iterates `D_z^b r`, `b ≤ 3`, of the radial function `r`
are differentiable on the open half-line and `h` is `C^∞` on the open quadrant, then

  `mixed j i (r·h) z θ = Σ_{b≤j} C(j,b)·(D_z^b r z)·(mixed (j-b) i h z θ)`.

This is `Work.FTS.Nonlinear.Pieces.radial_leibniz` with the interior class
`Work.FTS.LocData.SmoothQuad h` weakened to `SmoothOpen h`. -/
theorem radial_leibniz_open (r : ℝ → ℝ) (h : ℝ → ℝ → ℝ) (j i : ℕ) (hj : j ≤ 4) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2))
    (hsm : Work.FTS.EllipticEst.SmoothOpen h)
    (hr : ∀ b : ℕ, b ≤ 3 → ∀ z' ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b r) z') :
    Work.Spaces.mixed j i (fun z θ => r z * h z θ) z θ
      = ∑ b ∈ Finset.range (j + 1), (j.choose b : ℝ)
          * (Work.Elliptic.DzdIter b r z * Work.Spaces.mixed (j - b) i h z θ) := by
  have hθrule : Work.Spaces.DthIter i (fun z θ => r z * h z θ)
      = fun z θ => r z * Work.Spaces.DthIter i h z θ :=
    Work.FTS.Nonlinear.Pieces.dthIter_mul_radial r h i
  have hmix : Work.Spaces.mixed j i (fun z θ => r z * h z θ) z θ
      = Work.Elliptic.DzdIter j
          (fun z' => r z' * Work.Spaces.DthIter i h z' θ) z := by
    rw [Work.Spaces.mixed, hθrule]
    exact Work.FTS.Nonlinear.Pieces.DzIter_slice
      (fun z θ' => r z * Work.Spaces.DthIter i h z θ') j z θ
  rw [hmix]
  -- the `h`-side is differentiable on the open half-line
  have hdiff : ∀ b : ℕ, b < j → ∀ z' ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b
        (fun z' => Work.Spaces.DthIter i h z' θ)) z' := by
    intro b hb z' hz'
    have h1 : DifferentiableAt ℝ (fun u => Work.Spaces.mixed b i h u θ) z' :=
      smoothOpen_differentiableAt_slice_mixed hsm b i (by rw [Set.mem_Ioi] at hz'; exact hz') hθ
    have h2 : (fun u => Work.Spaces.mixed b i h u θ)
        = fun u => Work.Elliptic.DzdIter b (fun z' => Work.Spaces.DthIter i h z' θ) u := by
      funext u
      exact Work.FTS.Nonlinear.Pieces.DzIter_slice (Work.Spaces.DthIter i h) b u θ
    rwa [h2] at h1
  have hr' : ∀ b : ℕ, b < j → ∀ z' ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (Work.Elliptic.DzdIter b r) z' :=
    fun b hb z' hz' => hr b (by omega) z' hz'
  rw [Work.FTS.Nonlinear.Pieces.dzdIter_mul_leibniz j r
    (fun z' => Work.Spaces.DthIter i h z' θ) hr' hdiff z hz]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [show Work.Elliptic.DzdIter (j - b) (fun z' => Work.Spaces.DthIter i h z' θ) z
      = Work.Spaces.mixed (j - b) i h z θ from
    (Work.FTS.Nonlinear.Pieces.DzIter_slice (Work.Spaces.DthIter i h) (j - b) z θ).symm]

/-- Cauchy–Schwarz for a binomial slot sum: `(∑ c_b(x_by_b))² ≤ 256·card·Kc·∑ y_b²` when the
coefficients `c_b` are bounded by `16` and the first factors satisfy `x_b² ≤ Kc`. -/
theorem slot_sum_sq_le {ι : Type*} (s : Finset ι) (c x y : ι → ℝ) {Kc : ℝ} (hK : 0 ≤ Kc)
    (hc : ∀ b ∈ s, |c b| ≤ 16) (hx : ∀ b ∈ s, (x b) ^ 2 ≤ Kc) :
    (∑ b ∈ s, c b * (x b * y b)) ^ 2 ≤ 256 * (s.card : ℝ) * Kc * ∑ b ∈ s, (y b) ^ 2 := by
  have h1 : (∑ b ∈ s, c b * (x b * y b)) ^ 2
      ≤ (s.card : ℝ) * ∑ b ∈ s, (c b * (x b * y b)) ^ 2 :=
    _root_.sq_sum_le_card_mul_sum_sq
  have h2 : ∑ b ∈ s, (c b * (x b * y b)) ^ 2 ≤ ∑ b ∈ s, 256 * (Kc * (y b) ^ 2) := by
    refine Finset.sum_le_sum fun b hb => ?_
    have hc2 : (c b) ^ 2 ≤ 256 := by
      have h := hc b hb
      nlinarith [sq_nonneg (c b), sq_abs (c b), abs_nonneg (c b)]
    have hx2 := hx b hb
    have hy2 : 0 ≤ (y b) ^ 2 := sq_nonneg _
    have hxy : (x b) ^ 2 * (y b) ^ 2 ≤ Kc * (y b) ^ 2 :=
      mul_le_mul_of_nonneg_right hx2 hy2
    have hcx : (c b) ^ 2 * ((x b) ^ 2 * (y b) ^ 2) ≤ 256 * (Kc * (y b) ^ 2) := by
      have h1 : (c b) ^ 2 * ((x b) ^ 2 * (y b) ^ 2) ≤ 256 * ((x b) ^ 2 * (y b) ^ 2) :=
        mul_le_mul_of_nonneg_right hc2 (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      calc (c b) ^ 2 * ((x b) ^ 2 * (y b) ^ 2) ≤ 256 * ((x b) ^ 2 * (y b) ^ 2) := h1
        _ ≤ 256 * (Kc * (y b) ^ 2) := mul_le_mul_of_nonneg_left hxy (by norm_num)
    calc (c b * (x b * y b)) ^ 2 = (c b) ^ 2 * ((x b) ^ 2 * (y b) ^ 2) := by ring
      _ ≤ 256 * (Kc * (y b) ^ 2) := hcx
  have h3 : ∑ b ∈ s, 256 * (Kc * (y b) ^ 2) = 256 * Kc * ∑ b ∈ s, (y b) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  calc (∑ b ∈ s, c b * (x b * y b)) ^ 2
      ≤ (s.card : ℝ) * ∑ b ∈ s, (c b * (x b * y b)) ^ 2 := h1
    _ ≤ (s.card : ℝ) * (256 * Kc * ∑ b ∈ s, (y b) ^ 2) :=
        mul_le_mul_of_nonneg_left (h2.trans (le_of_eq h3)) (Nat.cast_nonneg _)
    _ = 256 * (s.card : ℝ) * Kc * ∑ b ∈ s, (y b) ^ 2 := by ring

end Work.FTS.StrongEps.E4R3
