import Mathlib
import Submission.Work.Smooth.Jordan.Defs

/-!
# Filling a loop with a disc map

If a continuous map `e` of the model disc `𝔻` maps the boundary circle to a loop `c`, then `c` is
null-homotopic through a homotopy with image in `Set.range e`: the convex combination
`(s,t) ↦ (1-s) • circlePoint (2 * Real.pi * t) + s • 1` stays in the convex disc.  This is the
*easy* half of the simple case of Borsuk's theorem — producing `e` itself is the
Jordan–Schoenflies input.

The file is split out of `push_loop_to_interior.lean` so that the simple case (`(F)`) and the
cutting step can import it without importing the target file itself (which will in turn import
them).
-/

noncomputable section

namespace Work.Smooth.JordanSeparation

/-- The boundary circle of the model disc is continuous. -/
theorem continuous_circlePoint : Continuous (fun θ : ℝ => (Work.Smooth.Jordan.circlePoint θ : Work.Smooth.Jordan.Disc)) := by
  apply Continuous.subtype_mk
  show Continuous fun θ : ℝ => Complex.exp (θ * Complex.I)
  exact Complex.continuous_exp.comp (by fun_prop)

/-- The basepoint `1` of the model disc is `circlePoint 0`. -/
theorem one_eq_circlePoint_zero : (1 : Work.Smooth.Jordan.Disc) = Work.Smooth.Jordan.circlePoint 0 := by
  apply Subtype.ext
  rw [show ((1 : Work.Smooth.Jordan.Disc) : ℂ) = 1 from rfl, Work.Smooth.Jordan.circlePoint_coe]
  norm_num

/-- **A loop that is the boundary of a disc map is null-homotopic.**

If a continuous map `e` of the closed disc `𝔻` maps the boundary circle to the loop `c`, then `c`
is null-homotopic through a homotopy with image in `Set.range e`: the convex combination
`(s,t) ↦ (1-s) • circlePoint (2 * Real.pi * t) + s • 1` stays in the convex disc, and gives
`c` at `s = 0`, the constant loop at `e 1 = e (circlePoint 0) = c 0` at `s = 1`, and is stationary
at `t ∈ {0,1}`.

(This is the *easy* half of the simple case of Borsuk's theorem: producing `e` itself is the
Jordan–Schoenflies input, see `Work.Smooth.JordanSeparation.exists_spanningDisc_of_jordan_in_closedK`.) -/
theorem exists_homotopy_refl_of_disc_extension {X : Type*} [TopologicalSpace X] {x : X} {c : Path x x}
    (e : C(Work.Smooth.Jordan.Disc, X))
    (hbd : ∀ t : unitInterval, e (Work.Smooth.Jordan.circlePoint (2 * Real.pi * t)) = c t) :
    ∃ F : Path.Homotopy c (Path.refl x), Set.range F ⊆ Set.range e := by
  have hc0 : e (Work.Smooth.Jordan.circlePoint 0) = x := by
    have h := hbd 0
    simpa using h
  have hone_eq := one_eq_circlePoint_zero
  have hball : Convex ℝ (Metric.closedBall (0:ℂ) 1) := convex_closedBall (0:ℂ) (1:ℝ)
  have hcp : Continuous fun p : unitInterval × unitInterval =>
      ((Work.Smooth.Jordan.circlePoint (2 * Real.pi * (p.2:ℝ)) : Work.Smooth.Jordan.Disc) : ℂ) :=
    continuous_subtype_val.comp (continuous_circlePoint.comp (by fun_prop))
  set φ : C(unitInterval × unitInterval, Work.Smooth.Jordan.Disc) :=
    ⟨fun p => ⟨(1 - (p.1:ℝ)) • ((Work.Smooth.Jordan.circlePoint (2 * Real.pi * (p.2:ℝ)) : Work.Smooth.Jordan.Disc) : ℂ)
        + (p.1:ℝ) • ((1 : Work.Smooth.Jordan.Disc) : ℂ),
        hball (Work.Smooth.Jordan.circlePoint (2 * Real.pi * (p.2:ℝ))).2 (1 : Work.Smooth.Jordan.Disc).2
          (sub_nonneg.mpr p.1.2.2) p.1.2.1 (by ring)⟩,
      Continuous.subtype_mk (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul hcp).add
        ((continuous_subtype_val.comp continuous_fst).smul continuous_const)) _⟩ with hφ
  have hφ_apply : ∀ p : unitInterval × unitInterval,
      (φ p : ℂ) = (1 - (p.1:ℝ)) • ((Work.Smooth.Jordan.circlePoint (2 * Real.pi * (p.2:ℝ)) : Work.Smooth.Jordan.Disc) : ℂ)
        + (p.1:ℝ) • ((1 : Work.Smooth.Jordan.Disc) : ℂ) := fun p => rfl
  have hφ_boundary : ∀ t : unitInterval, φ (0, t) = Work.Smooth.Jordan.circlePoint (2 * Real.pi * t) := by
    intro t
    apply Subtype.ext
    rw [hφ_apply, show ((0:unitInterval):ℝ) = 0 from rfl]
    simp
  have hφ_one : ∀ t : unitInterval, φ (1, t) = 1 := by
    intro t
    apply Subtype.ext
    rw [hφ_apply, show ((1:unitInterval):ℝ) = 1 from rfl]
    simp
  have hφ_seam_zero : ∀ s : unitInterval, φ (s, 0) = 1 := by
    intro s
    apply Subtype.ext
    rw [hφ_apply]
    have hc : ((Work.Smooth.Jordan.circlePoint (2 * Real.pi * ((0:unitInterval):ℝ)) : Work.Smooth.Jordan.Disc) : ℂ) = 1 := by
      rw [show (2 * Real.pi * ((0:unitInterval):ℝ)) = 0 from by norm_num, Work.Smooth.Jordan.circlePoint_coe]
      norm_num
    rw [hc]
    simp
  have hφ_seam_one : ∀ s : unitInterval, φ (s, 1) = 1 := by
    intro s
    apply Subtype.ext
    rw [hφ_apply]
    have hc : ((Work.Smooth.Jordan.circlePoint (2 * Real.pi * ((1:unitInterval):ℝ)) : Work.Smooth.Jordan.Disc) : ℂ) = 1 := by
      rw [show (2 * Real.pi * ((1:unitInterval):ℝ)) = 2 * Real.pi from by norm_num, Work.Smooth.Jordan.circlePoint_coe]
      rw [show (2 * Real.pi : ℝ) * Complex.I = 2 * (Real.pi : ℂ) * Complex.I from by push_cast; ring]
      exact Complex.exp_two_pi_mul_I
    rw [hc]
    simp
  refine ⟨{ toContinuousMap := e.comp φ
            map_zero_left := ?_
            map_one_left := ?_
            prop' := ?_ }, ?_⟩
  · intro t
    show e (φ (0, t)) = c t
    rw [hφ_boundary]
    exact hbd t
  · intro t
    show e (φ (1, t)) = (Path.refl x) t
    rw [hφ_one, hone_eq, hc0]
    rfl
  · intro s t ht
    rcases ht with ht | ht
    · subst ht
      show e (φ (s, 0)) = c 0
      rw [hφ_seam_zero, hone_eq, hc0, c.source]
    · subst ht
      show e (φ (s, 1)) = c 1
      rw [hφ_seam_one, hone_eq, hc0, c.target]
  · rintro y ⟨p, rfl⟩
    exact ⟨φ p, rfl⟩

/-- **The simple (Jordan) case of the target, from a spanning disc in `K`.** -/
theorem exists_homotopy_refl_of_spanningDisc_in_K {K : Set (OnePoint ℂ)} {x : OnePoint ℂ}
    {c : Path x x} (e : C(Work.Smooth.Jordan.Disc, OnePoint ℂ)) (heK : Set.range e ⊆ K)
    (hbd : ∀ t : unitInterval, e (Work.Smooth.Jordan.circlePoint (2 * Real.pi * t)) = c t) :
    ∃ F : Path.Homotopy c (Path.refl x), Set.range F ⊆ K := by
  obtain ⟨F, hF⟩ := exists_homotopy_refl_of_disc_extension e hbd
  exact ⟨F, fun y hy => heK (hF hy)⟩

end Work.Smooth.JordanSeparation
