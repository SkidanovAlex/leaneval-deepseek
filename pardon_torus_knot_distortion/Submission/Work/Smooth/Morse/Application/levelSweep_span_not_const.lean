import Mathlib
import Submission.Work.Smooth.Morse.Defs
import Submission.Work.SurgeryInvariance.API
import Submission.Work.Core.torusMap_eq_iff
import Submission.Work.Smooth.Morse.Critical.ae_regular_of_locallyFinite

namespace Work.Smooth.Morse.Application

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-!
# The winding span is not constant along a raw level family

For `ψ` the identity diffeomorphism of `ℝ³` and `g` the third coordinate function, the surface
`F = torus id` is the standard torus of revolution, whose third coordinate is `Real.sin φ` with
`φ` the meridian parameter.  Hence `F` is contained in the slab `-1 ≤ z ≤ 1`, so that

* `region id g (-2) = F ∩ {z < -2} = ∅`, whose winding span is `⊥`, while
* `region id g 2 = F ∩ {z < 2} = F`, whose winding span is `⊤`.

Since `⊥ ≠ ⊤`, the winding span of the sublevel regions of this (smooth, with locally finite
critical values) function is not constant, which is the content of
`Work.Smooth.Morse.Application.levelSweep_span_not_const`.

The critical values of the third coordinate on the torus are contained in `{-1, 1}`
(`criticalValues_subset`: a critical point of `(θ, φ) ↦ sin φ` has `cos φ = 0`, hence
`sin φ = ±1`), so they are locally finite.
-/

namespace LevelSweepWitness

/-! ## The witness: the identity diffeomorphism and the third coordinate -/

/-- The identity diffeomorphism of `ℝ³`. -/
def idDiffeo : Submission.Diffeo where
  toFun := id
  invFun := id
  smooth_toFun := contDiff_id
  smooth_invFun := contDiff_id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

@[simp] theorem idDiffeo_apply (x : R3) : idDiffeo x = x := rfl

@[simp] theorem idDiffeo_toFun : idDiffeo.toFun = id := rfl

/-- The third coordinate function on `ℝ³`. -/
def heightFn : R3 → ℝ := fun x => x (2 : Fin 3)

theorem contDiff_heightFn : ContDiff ℝ (⊤ : ℕ∞) heightFn := by
  unfold heightFn; fun_prop

/-- The parametrisation of the identity's torus is `Work.Core.torusMap`. -/
theorem param_idDiffeo (p : ℝ × ℝ) :
    param idDiffeo p = Work.Core.torusMap p.1 p.2 := rfl

/-- On the standard torus the third coordinate is `sin` of the meridian parameter. -/
theorem heightFn_torusMap (p : ℝ × ℝ) :
    heightFn (Work.Core.torusMap p.1 p.2) = Real.sin p.2 := by
  unfold heightFn; rw [Work.Core.torusMap_apply_two]

/-! ## The third coordinate of a point of the standard torus lies in `[-1, 1]` -/

theorem heightFn_bounds_of_mem_carrier {x : R3} (hx : x ∈ (torus idDiffeo).carrier) :
    -1 ≤ heightFn x ∧ heightFn x ≤ 1 := by
  rw [torus_carrier] at hx
  obtain ⟨p, hp⟩ := hx
  rw [← hp, param_idDiffeo, heightFn_torusMap]
  exact ⟨Real.neg_one_le_sin p.2, Real.sin_le_one p.2⟩

/-! ## The two regions -/

/-- The region below `-2` is empty: no point of the surface has third coordinate `< -2`. -/
theorem region_neg_two : region idDiffeo heightFn (-2) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  rw [mem_region] at hx
  obtain ⟨hxc, hxlt⟩ := hx
  have hb := heightFn_bounds_of_mem_carrier hxc
  linarith [hb.1]

/-- The region below `2` is the whole surface: every point of the surface has third
coordinate `< 2`. -/
theorem region_two : region idDiffeo heightFn 2 = (torus idDiffeo).carrier := by
  refine Set.inter_eq_left.mpr ?_
  intro x hx
  show heightFn x < 2
  have hb := heightFn_bounds_of_mem_carrier hx
  linarith [hb.2]

/-! ## The winding spans of the two regions -/

/-- The winding span of the empty region is `⊥`. -/
theorem windingSpan_empty (P : Work.CoreTopology.ParamTorus) :
    Work.SurgeryInvariance.WindingSpan P (∅ : Set R3) = ⊥ := by
  rw [Work.SurgeryInvariance.WindingSpan, Work.SurgeryInvariance.windingVectors]
  simp

theorem windingSpan_region_neg_two :
    Work.SurgeryInvariance.WindingSpan (torus idDiffeo) (region idDiffeo heightFn (-2)) = ⊥ := by
  rw [region_neg_two, windingSpan_empty]

theorem windingSpan_region_two :
    Work.SurgeryInvariance.WindingSpan (torus idDiffeo) (region idDiffeo heightFn 2) = ⊤ := by
  rw [region_two]
  exact Work.SurgeryInvariance.WindingSpan.carrier_eq_top _

/-! ## The critical values are contained in `{-1, 1}` -/

/-- A critical point of `(θ, φ) ↦ sin φ` in the parameter plane has `cos φ = 0`. -/
theorem cos_eq_zero_of_critical (p : ℝ × ℝ)
    (hp : fderiv ℝ (pullback idDiffeo heightFn) p = 0) : Real.cos p.2 = 0 := by
  have hfdG : fderiv ℝ (fun q : ℝ × ℝ => (Work.Core.torusMap q.1 q.2) (2 : Fin 3)) p = 0 := hp
  have h1 : (fderiv ℝ (fun q : ℝ × ℝ => (Work.Core.torusMap q.1 q.2) (2 : Fin 3)) p) (0, 1) = 0 := by
    rw [hfdG]; rfl
  have h2 : (fderiv ℝ (fun q : ℝ × ℝ => (Work.Core.torusMap q.1 q.2) (2 : Fin 3)) p) (0, 1) =
      Real.cos p.2 := by
    have heq : fderiv ℝ (fun q : ℝ × ℝ => (Work.Core.torusMap q.1 q.2) (2 : Fin 3)) p =
        fderiv ℝ (fun q : ℝ × ℝ => Real.sin q.2) p := by
      apply Filter.EventuallyEq.fderiv_eq
      filter_upwards with q
      exact Work.Core.torusMap_apply_two q.1 q.2
    rw [heq, fderiv_sin]
    · rw [fderiv_snd]; simp
    · fun_prop
  linarith

/-- The critical values of the third coordinate on the standard torus are among `±1`. -/
theorem criticalValues_subset :
    criticalValues idDiffeo heightFn ⊆ ({(-1 : ℝ), 1} : Set ℝ) := by
  rintro t ⟨p, hp, hpt⟩
  have hcos : Real.cos p.2 = 0 := cos_eq_zero_of_critical p hp
  have ht : t = Real.sin p.2 := by
    rw [← hpt]
    exact heightFn_torusMap p
  have hsin : Real.sin p.2 = 1 ∨ Real.sin p.2 = -1 := by
    have h1 : Real.sin p.2 ^ 2 = 1 := by
      have hs := Real.sin_sq_add_cos_sq p.2
      nlinarith [hs, hcos]
    exact sq_eq_one_iff.mp h1
  rw [ht]
  rcases hsin with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- Every bounded interval contains only finitely many critical values of the third coordinate. -/
theorem locallyFiniteCriticalValues : LocallyFiniteCriticalValues idDiffeo heightFn := by
  intro a b
  refine (Set.finite_singleton (1 : ℝ) |>.insert (-1 : ℝ)).subset ?_
  intro t ht
  exact criticalValues_subset (Set.mem_of_mem_inter_left ht)

end LevelSweepWitness

end

open LevelSweepWitness in
theorem levelSweep_span_not_const : ∃ (ψ : Submission.Diffeo) (g : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ) (a b : ℝ), ContDiff ℝ (⊤ : ℕ∞) g ∧ Work.Smooth.Morse.LocallyFiniteCriticalValues ψ g ∧ Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ) (Work.Smooth.Morse.region ψ g a) ≠ Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ) (Work.Smooth.Morse.region ψ g b) := by
  refine ⟨idDiffeo, heightFn, -2, 2, contDiff_heightFn, locallyFiniteCriticalValues, ?_⟩
  intro h
  rw [windingSpan_region_neg_two, windingSpan_region_two] at h
  exact absurd h (bot_ne_top (α := Submodule ℚ (ℚ × ℚ)))

end Work.Smooth.Morse.Application
