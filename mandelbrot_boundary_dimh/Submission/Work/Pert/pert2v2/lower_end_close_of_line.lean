import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.pert2v2.exists_strict_line_bound
import Submission.Work.Pert.pert2v2.norm_le_of_bounded_on_right_halfplane
import Submission.Work.Pert.pert2v2.rot_halfplane

/-! # The lower-end closeness bound from the boundary line

**Statement.** `h(w) := R w + a - E w` where `R` and `E` are holomorphic on the closed half-plane
`{w | w.im ≤ -y₁}`, `1`-periodic there (`R (w+1) = R w + 1`, `E (w+1) = E w + 1`) and with
`R - E` bounded there.  If `‖h‖ < δ` on the boundary line `{w | w.im = -y₁}`, then `‖h‖ < δ` on the
whole half-plane.

**Proof.**  `h := fun w => R w + a - E w` is holomorphic on the closed half-plane, `1`-periodic
there, and bounded there (`‖R - E‖ + ‖a‖`).

1. `Work.Pert.pert2v2.exists_strict_line_bound` upgrades the pointwise strict bound on the boundary
   line to a *uniform* strict bound `δ' < δ`: the function `t ↦ h (t - i y₁)` is continuous and
   `1`-periodic, hence its supremum is its maximum on the compact set `[0,1]`.
2. `Work.Pert.pert2v2.rot_halfplane` rotates the half-plane onto the right half-plane
   (`z ↦ -I (z + y₁)`), producing a function `F` holomorphic and bounded on the closed right
   half-plane with `F (i x) = h (x - i y₁)`.
3. `Work.Pert.pert2v2.norm_le_of_bounded_on_right_halfplane` (Phragmén–Lindelöf, via Mathlib's
   `PhragmenLindelof.right_half_plane_of_bounded_on_real`) bounds `‖F‖ ≤ δ'` on the right
   half-plane.
4. Every `w` with `w.im ≤ -y₁` is `F z` for some `z` with `z.re ≥ 0`, so `‖h w‖ ≤ δ' < δ`.
-/

namespace Work.Pert.pert2v2

open Set Metric Filter Topology

theorem lower_end_close_of_line {R E : ℂ → ℂ} {a : ℂ} {y₁ δ : ℝ}
    (hRd : ∀ w : ℂ, w.im ≤ -y₁ → DifferentiableAt ℂ R w)
    (hEd : ∀ w : ℂ, w.im ≤ -y₁ → DifferentiableAt ℂ E w)
    (hRper : ∀ w : ℂ, w.im ≤ -y₁ → R (w + 1) = R w + 1)
    (hEper : ∀ w : ℂ, w.im ≤ -y₁ → E (w + 1) = E w + 1)
    (hbdd : ∃ C : ℝ, ∀ w : ℂ, w.im ≤ -y₁ → ‖R w - E w‖ ≤ C)
    (hline : ∀ w : ℂ, w.im = -y₁ → ‖R w + a - E w‖ < δ) :
    ∀ w : ℂ, w.im ≤ -y₁ → ‖R w + a - E w‖ < δ := by
  obtain ⟨C, hC⟩ := hbdd
  set M : ℝ := |C| + ‖a‖ + 1 with hMdef
  have hMpos : 0 < M := by rw [hMdef]; positivity
  -- `h := fun w => R w + a - E w` is holomorphic on the closed half-plane
  have hhd : ∀ w : ℂ, w.im ≤ -y₁ → DifferentiableAt ℂ (fun w => R w + a - E w) w := by
    intro w hw
    exact ((hRd w hw).add_const a).sub (hEd w hw)
  -- ... and `1`-periodic there
  have hhper : ∀ w : ℂ, w.im ≤ -y₁ →
      (fun w => R w + a - E w) (w + 1) = (fun w => R w + a - E w) w := by
    intro w hw
    have h1 := hRper w hw
    have h2 := hEper w hw
    show R (w + 1) + a - E (w + 1) = R w + a - E w
    rw [h1, h2]; ring
  -- ... and bounded there
  have hhbdd : ∀ w : ℂ, w.im ≤ -y₁ → ‖(fun w => R w + a - E w) w‖ ≤ M := by
    intro w hw
    have h1 : ‖R w + a - E w‖ ≤ ‖R w - E w‖ + ‖a‖ := by
      have he : R w + a - E w = (R w - E w) + a := by ring
      rw [he]; exact norm_add_le _ _
    have h2 : ‖R w - E w‖ ≤ C := hC w hw
    have h3 : C ≤ |C| := le_abs_self C
    rw [hMdef]; linarith
  -- Step 1: a uniform strict bound `δ' < δ` on the boundary line
  obtain ⟨δ', hδ'lt, hδ'le⟩ := exists_strict_line_bound hhd hhper hline
  -- Step 2: rotate the half-plane onto the right half-plane
  obtain ⟨F, hdF, hFbdd, hFhim, hFlift⟩ := rot_halfplane hhd hhbdd
  have him : ∀ x : ℝ, ‖F ((x : ℂ) * Complex.I)‖ ≤ δ' := by
    intro x
    rw [hFhim x]
    exact hδ'le _ (by simp)
  -- Step 3: Phragmén–Lindelöf
  have hPL : ∀ z : ℂ, 0 ≤ z.re → ‖F z‖ ≤ δ' :=
    norm_le_of_bounded_on_right_halfplane hMpos hdF hFbdd him
  -- Step 4: transport back to the half-plane
  intro w hw
  obtain ⟨z, hzre, hzF⟩ := hFlift w hw
  have hz := hPL z hzre
  rw [hzF] at hz
  exact lt_of_le_of_lt hz hδ'lt

end Work.Pert.pert2v2
