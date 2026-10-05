import Mathlib
import Submission.Work.RPCore.Port.Whitney.exists_retraction_succ
import Submission.Work.RPB1a.Caratheodory.Brouwer.RetractDefs
import Submission.Work.RPB1a.Caratheodory.Brouwer.rayT_norm
import Submission.Work.RPB1a.Caratheodory.Brouwer.rayT_eq_one
import Submission.Work.RPB1a.Caratheodory.Brouwer.continuous_rayT_comp

/-!
# A fixed-point-free self-map of the closed ball yields a retraction onto the sphere

`Work.RPB1a.Caratheodory.Brouwer.exists_retraction_of_fixedPointFree`: if a continuous self-map `g`
of `EuclideanSpace ℝ (Fin N)` maps the closed unit ball into itself and has no fixed point in the
closed ball, then the ball admits a continuous retraction onto its boundary sphere.

This is the classical "ray" construction, which is the direction of the Brouwer fixed point theorem
used to derive the latter from the no-retraction theorem: for `x` in the ball, start at `g x`, move
along the ray through `x`, and continue until the boundary sphere is reached.

## Proof

The hypotheses only constrain `g` on the closed ball, whereas the retraction `F` has to be defined
and continuous on all of `EuclideanSpace ℝ (Fin N)`.  We therefore first push `g` inside the ball by
composing with the radial clamp `clamp x = (max 1 ‖x‖)⁻¹ • x`, and put `H = g ∘ clamp`.  Then `H` is
continuous, satisfies `‖H x‖ ≤ 1` for *every* `x`, and — crucially — `H x ≠ x` for every `x`:
for `‖x‖ ≤ 1` this is the absence of fixed points of `g`, while for `‖x‖ > 1` we have
`‖H x‖ ≤ 1 < ‖x‖`.

The retraction is then

  `F x = H x + rayT (H x) (x - H x) • (x - H x)`,

where `rayT p d` (see `RetractDefs`) is the outer root of `‖p + t • d‖ = 1`.  Since `x - H x ≠ 0`
and `‖H x‖ ≤ 1`, the point `F x` always lies on the unit sphere (`rayT_norm`); when `‖x‖ = 1` the
parameter `1` is already a root, so `rayT (H x) (x - H x) = 1` and `F x = H x + (x - H x) = x`
(`rayT_eq_one`); and `F` is continuous because the denominator `‖x - H x‖²` of the closed form for
`rayT` never vanishes (`continuous_rayT_comp`).
-/

namespace Work.RPB1a.Caratheodory.Brouwer

open scoped Topology

/-- The radial projection of `EuclideanSpace ℝ (Fin N)` onto its closed unit ball. -/
noncomputable def clamp {N : ℕ} (x : EuclideanSpace ℝ (Fin N)) : EuclideanSpace ℝ (Fin N) :=
  (max 1 ‖x‖)⁻¹ • x

lemma continuous_clamp {N : ℕ} : Continuous (clamp (N := N)) := by
  unfold clamp
  refine ((continuous_const.max continuous_norm).inv₀ ?_).smul continuous_id
  intro x
  exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))

lemma clamp_eq_self_of_le_one {N : ℕ} {x : EuclideanSpace ℝ (Fin N)} (hx : ‖x‖ ≤ 1) :
    clamp x = x := by
  rw [clamp, max_eq_left hx, inv_one, one_smul]

lemma norm_clamp_le_one {N : ℕ} (x : EuclideanSpace ℝ (Fin N)) : ‖clamp x‖ ≤ 1 := by
  have hpos : 0 < max 1 ‖x‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have h1 : ‖clamp x‖ = (max 1 ‖x‖)⁻¹ * ‖x‖ := by
    rw [clamp, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos]
  rw [h1]
  calc (max 1 ‖x‖)⁻¹ * ‖x‖ ≤ (max 1 ‖x‖)⁻¹ * (max 1 ‖x‖) :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (inv_nonneg.mpr hpos.le)
    _ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)

/-- If a continuous self-map of the closed unit ball of `EuclideanSpace ℝ (Fin N)` has no fixed point in
the closed unit ball, then the ball admits a continuous retraction onto its boundary sphere. -/
lemma exists_retraction_of_fixedPointFree {N : ℕ}
    (g : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N)) (hg : Continuous g)
    (hmaps : ∀ x, ‖x‖ ≤ 1 → ‖g x‖ ≤ 1) (hfix : ∀ x, ‖x‖ ≤ 1 → g x ≠ x) :
    ∃ F : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N),
      Continuous F ∧ (∀ x, ‖x‖ = 1 → F x = x) ∧ (∀ x, ‖x‖ ≤ 1 → ‖F x‖ = 1) := by
  -- push `g` into the ball so that it is defined and fixed-point-free on all of the space
  let H : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) := fun x => g (clamp x)
  have hHc : Continuous H := hg.comp continuous_clamp
  have hHle : ∀ x, ‖H x‖ ≤ 1 := fun x => hmaps (clamp x) (norm_clamp_le_one x)
  have hHne : ∀ x, H x ≠ x := by
    intro x
    by_cases hx : ‖x‖ ≤ 1
    · have h1 : H x = g x := by
        show g (clamp x) = g x
        rw [clamp_eq_self_of_le_one hx]
      rw [h1]; exact hfix x hx
    · intro hcon
      have hlt : ‖H x‖ ≤ 1 := hHle x
      rw [hcon] at hlt
      exact hx hlt
  refine ⟨fun x => H x + rayT (H x) (x - H x) • (x - H x), ?_, ?_, ?_⟩
  · -- continuity: the ray parameter is a continuous function of `x`
    exact hHc.add ((continuous_rayT_comp H hHc hHne).smul (continuous_id.sub hHc))
  · -- the sphere is fixed pointwise: the parameter is `1` there
    intro x hx
    have hd : x - H x ≠ 0 := sub_ne_zero.mpr (Ne.symm (hHne x))
    have hp : ‖H x‖ ≤ 1 := hHle x
    have hpd : H x + (x - H x) = x := by abel
    have hx' : ‖H x + (x - H x)‖ = 1 := by rw [hpd, hx]
    have hrt := rayT_eq_one (H x) (x - H x) hd hp hx'
    show H x + rayT (H x) (x - H x) • (x - H x) = x
    rw [hrt, one_smul, hpd]
  · -- the ball is mapped onto the sphere: `rayT` is a root of the ray equation
    intro x _
    exact rayT_norm (H x) (x - H x) (sub_ne_zero.mpr (Ne.symm (hHne x))) (hHle x)

end Work.RPB1a.Caratheodory.Brouwer
