import Mathlib
import Submission.Work.Drive.CappingSpace

/-!
# The cap disk of the capping: a curve of degree `0` in the first coordinate bounds a cone

This is input B of the capping (see `Submission/Work/Drive/CAPPING_ANALYSIS.md`, §2).  The boundary
curve of the configuration Möbius strip, transported by the gluing `glueTorus` of
`Submission.Work.Drive.CappingDefs` to the boundary torus `S¹ × ∂D²` of the cap solid torus `S¹ × D²`,
has

* second coordinate the position angle of the curve, whose *degree* is the winding number of the
  curve about the origin (`position_angle_lift`), and
* first coordinate `θ = η - 2ψ`, the doubled tangent direction minus twice the position angle, whose
  degree is `±2 - 2·(winding)`; this vanishes exactly when the winding is `±1`
  (`does not need the full Jordan result: the weak form "some off-curve point has non-zero winding"
  suffices`, `Work.Drive.exists_winding_ne_zero`).

A closed curve in the boundary torus whose *first* coordinate has degree `0` bounds a disk in the solid
torus, explicitly the cone

> `D (ρ, t) = ( θ₀ + ρ (Θ t - θ₀),  ρ · circleOf (Φ t) )`,

where `θ₀ := Θ 0`: at `ρ = 1` it is the curve (first coordinate `Θ t`, second coordinate the angle
`Φ t`), at `ρ = 0` it is the single point `(θ₀, 0)` (so that boundary component contributes nothing to
the chain boundary), and it is periodic in `t` as soon as `Θ` is (`Φ` only needs to be periodic modulo
one).  This is the disk that caps the configuration Möbius strip to a projective plane.

The hypothesis `hΦper` says that `t ↦ circleOf (Φ t)` is periodic: it is automatically satisfied when
`Φ` is a lift of the position angle of a closed curve (there `Φ (t+1) - Φ t ∈ ℤ`, by
`position_angle_lift`). -/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

/-- **The cone filling of a closed curve in the solid torus `S¹ × D²` whose first coordinate has
degree `0`.**  Continuity, the two boundary values, the periodicity and the fact that the cone lies in
the unit disk of the second coordinate. -/
theorem exists_disk_filling_of_meridian_class
    (Θ Φ : ℝ → ℝ) (hΘ : Continuous Θ) (hΦ : Continuous Φ)
    (hΘper : ∀ t, Θ (t + 1) = Θ t) (hΦper : ∀ t, circleOf (Φ (t + 1)) = circleOf (Φ t)) :
    ∃ D : ℝ × ℝ → UnitAddCircle × ℂ,
      Continuous D ∧
      (∀ t, D (1, t) = (((Θ t : ℝ) : UnitAddCircle), circleOf (Φ t))) ∧
      (∀ t, D (0, t) = (((Θ 0 : ℝ) : UnitAddCircle), 0)) ∧
      (∀ t, D (0, t) = D (0, 0)) ∧
      (∀ ρ t, D (ρ, t + 1) = D (ρ, t)) ∧
      (∀ ρ t, ρ ∈ Set.Icc (0 : ℝ) 1 → ‖(D (ρ, t)).2‖ ≤ 1) := by
  refine ⟨fun p => (((Θ 0 + p.1 * (Θ p.2 - Θ 0) : ℝ) : UnitAddCircle),
      (p.1 : ℂ) * circleOf (Φ p.2)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- continuity of the cone
    refine Continuous.prodMk ?_ ?_
    · exact QuotientAddGroup.continuous_mk.comp
        (continuous_const.add (continuous_fst.mul ((hΘ.comp continuous_snd).sub continuous_const)))
    · refine (Complex.continuous_ofReal.comp continuous_fst).mul ?_
      refine (continuous_subtype_val.comp
        (AddCircle.homeomorphCircle (T := 1) one_ne_zero).continuous).comp ?_
      exact QuotientAddGroup.continuous_mk.comp (hΦ.comp continuous_snd)
  · intro t; simp
  · intro t; simp
  · intro t; simp
  · -- periodicity in `t`
    intro ρ t
    simp only [Prod.mk.injEq]
    exact ⟨by rw [hΘper t], by rw [hΦper t]⟩
  · -- the cone lies in the unit disk for parameters in `[0,1]`
    intro ρ t hρ
    have hρ' : |ρ| ≤ 1 := by rw [abs_of_nonneg hρ.1]; exact hρ.2
    have : ‖((ρ : ℝ) : ℂ)‖ ≤ 1 := by simpa using hρ'
    calc ‖(ρ : ℂ) * circleOf (Φ t)‖ = ‖((ρ : ℝ) : ℂ)‖ * ‖circleOf (Φ t)‖ := norm_mul _ _
      _ = ‖((ρ : ℝ) : ℂ)‖ * 1 := by rw [norm_circleOf]
      _ ≤ 1 := by rw [mul_one]; exact this

end Work.Drive
