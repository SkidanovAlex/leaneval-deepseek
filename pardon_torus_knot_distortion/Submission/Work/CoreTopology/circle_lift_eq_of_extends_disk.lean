import Mathlib
import Submission.Work.CoreTopology.Disk

/-!
# The winding number of a loop in the circle that extends over the disc

The covering map `Circle.exp : ℝ → Circle` (the universal cover of the unit
circle) turns the study of the *degree* of a loop `g : Circle → Circle` into the
study of the *endpoint* of its lift `Λ : I → ℝ`: the loop `g` is null-homotopic
if and only if the lift is a loop, i.e. `Λ (2π) = Λ 0`.

In this file we prove exactly that, in the setting needed for Pardon's
distortion bound: a continuous closed loop `g : ℝ → Circle` which extends
continuously over the closed unit disc (a map `G` on `𝔻 ⊂ ℂ` restricting to `g`
on the boundary circle) has *every* continuous lift `Λ : ℝ → ℝ` satisfying
`Circle.exp (Λ t) = g t` a loop.

The proof is the standard monodromy argument.  The extension over the disc
exhibits the based loop `t ↦ g (2πt)` as homotopic, relative to its endpoints,
to the constant loop at `g 0` (one radially contracts the disc to its centre).
Lifting two paths that are homotopic relative to `{0,1}` from the same point of
the total space of a covering map ends at the same point
(`IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel`).  The lift of the based
loop `t ↦ g (2π t)` starting at `Λ 0` is `t ↦ Λ (2π t)` (by uniqueness of lifts
through the covering map `Circle.exp`, `IsCoveringMap.eq_liftPath_iff'`), while
the lift of the constant loop is the constant path at `Λ 0`; comparing endpoints
gives `Λ (2π) = Λ 0`.
-/

open scoped unitInterval

namespace Work.CoreTopology

noncomputable section

/-- The point `θ ↦ exp (i θ)` of the unit circle is a continuous function of `θ`. -/
theorem continuous_circlePoint : Continuous circlePoint :=
  Continuous.subtype_mk (by fun_prop) _

/-- The parametrisation of the boundary circle is `2π`-periodic. -/
theorem circlePoint_add_two_pi (θ : ℝ) :
    circlePoint (θ + 2 * Real.pi) = circlePoint θ := by
  apply Subtype.ext
  rw [circlePoint_coe, circlePoint_coe]
  show (Circle.exp (θ + 2 * Real.pi) : ℂ) = (Circle.exp θ : ℂ)
  rw [Circle.exp_add_two_pi]

/-- `circlePoint (2π) = circlePoint 0`: the parametrisation of the boundary of the
disc is a loop. -/
theorem circlePoint_two_pi : circlePoint (2 * Real.pi) = circlePoint 0 := by
  simpa using circlePoint_add_two_pi 0

/-- If a continuous closed loop `g : ℝ → Circle` in the unit circle extends continuously over the closed unit disc, then it is null-homotopic and every continuous lift `Λ : ℝ → ℝ` (with `Circle.exp (Λ t) = g t` for all `t`) is a loop: `Λ (2π) = Λ 0`. Equivalently, the winding number (degree) of a null-homotopic loop in the circle is zero. Proof route: the disc is contractible, so `G` lifts to a continuous `L : 𝔻 → ℝ` along the covering map `Circle.exp`; then `L ∘ circlePoint` and `Λ` are two lifts of `g` from the connected space `ℝ`, hence differ by a constant in `2πℤ`; evaluating at `0` and `2π`, and using `circlePoint (2π) = circlePoint 0`, gives `Λ (2π) = Λ 0`. -/
theorem circle_lift_eq_of_extends_disk (g : ℝ → Circle) (hg : Continuous g)
    (hper : ∀ t : ℝ, g (t + 2 * Real.pi) = g t)
    (G : C(Metric.closedBall (0 : ℂ) 1, Circle)) (hG : ∀ θ : ℝ, G (circlePoint θ) = g θ)
    (Λ : ℝ → ℝ) (hΛ : Continuous Λ) (hlift : ∀ t : ℝ, Circle.exp (Λ t) = g t) :
    Λ (2 * Real.pi) = Λ 0 := by
  -- The point `1 ∈ ℂ` lies in the closed unit disc.
  have hmem1 : (1 : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right]; norm_num
  -- The based loop `t ↦ g (2π t)` and the constant loop at `g 0`.
  let γ₀ : C(I, Circle) := ⟨fun s : I => g (2 * Real.pi * (s : ℝ)), hg.comp (by fun_prop)⟩
  let γ₁ : C(I, Circle) := ⟨fun _ : I => g 0, continuous_const⟩
  have hγ₀_apply : ∀ s : I, γ₀ s = g (2 * Real.pi * (s : ℝ)) := fun s => rfl
  have hγ₁_apply : ∀ s : I, γ₁ s = g 0 := fun s => rfl
  -- Radial contraction of the disc, as a path in the disc from `circlePoint (2π s)`
  -- to the centre `1`.  It stays in the (convex) closed unit disc.
  have hz : ∀ p : I × I,
      (1 - (p.1 : ℝ)) • ((circlePoint (2 * Real.pi * (p.2 : ℝ))) : ℂ) + (p.1 : ℝ) • (1 : ℂ)
        ∈ Metric.closedBall (0 : ℂ) 1 := by
    intro p
    have hconv : Convex ℝ (Metric.closedBall (0 : ℂ) 1) := convex_closedBall 0 1
    exact hconv (circlePoint _).2 (by simp [Metric.mem_closedBall])
      (by linarith [p.1.2.2]) p.1.2.1 (by ring)
  have hzc : Continuous fun p : I × I =>
      (1 - (p.1 : ℝ)) • ((circlePoint (2 * Real.pi * (p.2 : ℝ))) : ℂ) + (p.1 : ℝ) • (1 : ℂ) := by
    have h1 : Continuous fun p : I × I => (1 - (p.1 : ℝ)) := by fun_prop
    have h2 : Continuous fun p : I × I => ((circlePoint (2 * Real.pi * (p.2 : ℝ))) : ℂ) :=
      (continuous_subtype_val.comp continuous_circlePoint).comp (by fun_prop)
    have h3 : Continuous fun p : I × I => (p.1 : ℝ) := by fun_prop
    exact (h1.smul h2).add (h3.smul continuous_const)
  -- The homotopy of loops in the circle, obtained by applying `G` to the contraction.
  let H : C(I × I, Circle) :=
    ⟨fun p => G ⟨_, hz p⟩, G.continuous.comp (Continuous.subtype_mk hzc hz)⟩
  have H_apply : ∀ p : I × I, H p = G ⟨(1 - (p.1 : ℝ)) •
      ((circlePoint (2 * Real.pi * (p.2 : ℝ))) : ℂ) + (p.1 : ℝ) • (1 : ℂ), hz p⟩ := fun p => rfl
  -- Boundary conditions: the homotopy starts at `γ₀`, ends at `γ₁`, and fixes the base point.
  have htest : ∀ s : I, H (0, s) = γ₀ s := by
    intro s
    rw [H_apply, hγ₀_apply]
    have harg : (⟨(1 - ((0 : I) : ℝ)) •
        ((circlePoint (2 * Real.pi * (s : ℝ))) : ℂ) + ((0 : I) : ℝ) • (1 : ℂ), hz (0, s)⟩ :
        Metric.closedBall (0 : ℂ) 1) = circlePoint (2 * Real.pi * (s : ℝ)) := by
      apply Subtype.ext
      simp
    rw [harg]
    exact hG _
  have htest2 : ∀ s : I, H (1, s) = γ₁ s := by
    intro s
    rw [H_apply, hγ₁_apply]
    have harg : (⟨(1 - ((1 : I) : ℝ)) •
        ((circlePoint (2 * Real.pi * (s : ℝ))) : ℂ) + ((1 : I) : ℝ) • (1 : ℂ), hz (1, s)⟩ :
        Metric.closedBall (0 : ℂ) 1) = circlePoint 0 := by
      apply Subtype.ext
      simp
    rw [harg, hG]
  have hprop : ∀ t : I, ∀ x ∈ ({0, 1} : Set I), H (t, x) = γ₀ x := by
    intro t x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hx | hx
    · subst hx
      rw [H_apply, hγ₀_apply]
      have harg : (⟨(1 - (t : ℝ)) •
          ((circlePoint (2 * Real.pi * ((0 : I) : ℝ))) : ℂ) + (t : ℝ) • (1 : ℂ), hz (t, 0)⟩ :
          Metric.closedBall (0 : ℂ) 1) = circlePoint (2 * Real.pi * ((0 : I) : ℝ)) := by
        apply Subtype.ext
        simp
      rw [harg, hG]
    · subst hx
      rw [H_apply, hγ₀_apply]
      have harg : (⟨(1 - (t : ℝ)) •
          ((circlePoint (2 * Real.pi * ((1 : I) : ℝ))) : ℂ) + (t : ℝ) • (1 : ℂ), hz (t, 1)⟩ :
          Metric.closedBall (0 : ℂ) 1) = circlePoint (2 * Real.pi * ((1 : I) : ℝ)) := by
        apply Subtype.ext
        simp [circlePoint_two_pi]
      rw [harg, hG]
  -- Package the homotopy.
  have hrel : γ₀.HomotopicRel γ₁ {0, 1} :=
    ⟨{ toContinuousMap := H
       map_zero_left := htest
       map_one_left := htest2
       prop' := hprop }⟩
  -- Both loops start at `Circle.exp (Λ 0)`.
  have hlift0 : γ₀ 0 = Circle.exp (Λ 0) := by
    rw [hγ₀_apply]; simpa using (hlift 0).symm
  have hlift1 : γ₁ 0 = Circle.exp (Λ 0) := by
    rw [hγ₁_apply]; exact (hlift 0).symm
  -- Monodromy: the lifts of two homotopic (rel. endpoints) paths starting at the
  -- same point end at the same point.
  have key := IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel
    Circle.isCoveringMap_exp hrel (Λ 0) hlift0 hlift1
  -- The lift of `γ₀` starting at `Λ 0` is `s ↦ Λ (2π s)`.
  have hA : (⟨fun s : I => Λ (2 * Real.pi * (s : ℝ)), hΛ.comp (by fun_prop)⟩ : C(I, ℝ)) =
      Circle.isCoveringMap_exp.liftPath γ₀ (Λ 0) hlift0 := by
    rw [IsCoveringMap.eq_liftPath_iff']
    refine ⟨?_, ?_⟩
    · ext s
      simp only [Function.comp_apply, hγ₀_apply]
      exact congrArg (fun z : Circle => (z : ℂ)) (hlift (2 * Real.pi * (s : ℝ)))
    · simp
  -- The lift of `γ₁` starting at `Λ 0` is the constant path at `Λ 0`.
  have hB : (ContinuousMap.const I (Λ 0) : C(I, ℝ)) =
      Circle.isCoveringMap_exp.liftPath γ₁ (Λ 0) hlift1 := by
    rw [IsCoveringMap.eq_liftPath_iff']
    refine ⟨?_, ?_⟩
    · ext s
      simp only [Function.comp_apply, hγ₁_apply]
      exact congrArg (fun z : Circle => (z : ℂ)) (hlift 0)
    · simp
  have hB1 := congrArg (fun F : C(I, ℝ) => F 1) hB
  simp only [ContinuousMap.const_apply] at hB1
  have h1 : Λ (2 * Real.pi) = (Circle.isCoveringMap_exp.liftPath γ₀ (Λ 0) hlift0) 1 := by
    rw [← congrArg (fun F : C(I, ℝ) => F 1) hA]
    norm_num
  exact h1.trans (key.trans hB1.symm)

end

end Work.CoreTopology
