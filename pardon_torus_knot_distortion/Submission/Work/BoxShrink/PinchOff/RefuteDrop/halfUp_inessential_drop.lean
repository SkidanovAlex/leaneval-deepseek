import Mathlib
import Submission.Work.BoxShrink.PinchOff.RefuteDrop.Config
import Submission.Work.BoxShrink.PinchOff.RefuteDrop.omega_rank_two
import Submission.Work.BoxShrink.PinchOff.TangentData.Basic

/-!
# The upper half-region of the `RefuteDrop` configuration carries no essential loop

At the linear configuration of `Config.lean` — `ψ = dropDiffeo`, box centre `dropC = 0`, box size
`dropS = 7/5`, coordinate permutation `dropCyc = swap 0 2` and cutting plane `{x = 0}`
(`dropU = 0`) — the **upper half-region** `Ω₊ = Ω ∩ {x > 0}` carries no essential loop, so its
winding span vanishes (`Work.BoxShrink.PinchOff.RefuteDrop.halfUp_inessential_drop`).

The argument is the "confining grid line" one (`RefuteNC/halfUp_inessential.lean`,
`sphereTrace_inessential_drop.lean`).  A closed curve whose image lies in `Ω₊` lifts to a pair of
continuous parameter functions `(Θ, Φ)` with `dropVec (torusMap (Θ t) (Φ t))` in `Ω₊`; the
preimage of `Ω₊` in the parameter torus misses two whole grid circles, and each missed grid circle
kills the corresponding winding increment
(`Work.BoxShrink.PinchOff.int_eq_zero_of_notMem_lattice`):

* the **longitude** `{θ = dropD}`, `dropD = arcsin (4/5)`, i.e. `(cos θ, sin θ) = (3/5, 4/5)`.
  Writing `R = 2 + cos φ ∈ [1,3]`, a point of `Ω₊` with `θ = dropD` has
  `0 < w₀ = -(9/25)·R + (97/100)·sin φ`, whence `sin φ > (36/97)·R`, and then
  `w₂ = (643/500)·R + (59/100)·sin φ > (72991/48500)·R ≥ 72991/48500 > 7/5 = dropS`,
  contradicting the box bound `|w₂| < dropS`;
* the **meridian** `{φ = -π/2}` (equivalently `sin φ = -1`): with `cos φ = 0` the first coordinate
  is `w₀ = -(4/25)·cos θ - (39/50)·sin θ - 97/100`, whose amplitude
  `√((4/25)² + (39/50)²) = √(1585)/50 < 97/100` is strictly smaller than the constant term, so
  `w₀ < 0`, contradicting `w₀ > 0`.

Both are elementary estimates; the two grid lines are disjoint from the preimage, and the winding
vector of any loop of `Ω₊` is therefore `0`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff.RefuteDrop

noncomputable section

/-! ## The two forbidden parameter values -/

/-- **The excluded longitude parameter**: `(cos dropD, sin dropD) = (3/5, 4/5)`, an angle lying
inside the arc of longitudes the upper half-region misses. -/
def dropD : ℝ := Real.arcsin (4 / 5)

theorem dropD_cos : Real.cos dropD = 3 / 5 := by
  rw [dropD, Real.cos_arcsin]
  norm_num

theorem dropD_sin : Real.sin dropD = 4 / 5 := by
  rw [dropD, Real.sin_arcsin] <;> norm_num

/-- **The excluded meridian parameter**: `sin dropPhi = -1`. -/
def dropPhi : ℝ := -(Real.pi / 2)

theorem dropPhi_sin : Real.sin dropPhi = -1 := by
  rw [dropPhi, Real.sin_neg, Real.sin_pi_div_two]

/-! ## The shape of the upper region -/

/-- **The upper region misses the meridian `φ = -π/2`.**  A point
`dropVec (torusMap θ φ) ∈ ℝ³` of `Ω₊` has positive coordinate `0`; for `sin φ = -1` that
coordinate is `-(4/25)·cos θ - (39/50)·sin θ - 97/100`, of amplitude `√(1585)/50 < 97/100`, hence
strictly negative. -/
theorem drop_upperRegion_sin_ne_neg_one {θ φ : ℝ}
    (h : dropVec (Work.Core.torusMap θ φ) ∈
      Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus dropDiffeo)
        dropS dropC dropCyc dropU) :
    Real.sin φ ≠ -1 := by
  intro hsφ
  obtain ⟨-, -, hy0⟩ := (Work.BoxShrink.Core.mem_upperRegion).mp h
  simp only [dropCyc_two, dropC_zero, dropU, zero_add] at hy0
  have hcosφ : Real.cos φ = 0 := by
    have hc := Real.cos_sq_add_sin_sq φ
    rw [hsφ] at hc
    nlinarith [hc]
  have h0 : (dropVec (Work.Core.torusMap θ φ)).ofLp 0
      = (-(4 / 25)) * Real.cos θ + (-(39 / 50)) * Real.sin θ - 97 / 100 := by
    rw [dropVec_coord_zero, Work.CoreTopology.torusMap_apply_zero,
      Work.CoreTopology.torusMap_apply_one, Work.CoreTopology.torusMap_apply_two, hcosφ, hsφ]
    ring
  have habs := abs_cos_sin_lt (-(4 / 25)) (-(39 / 50)) (97 / 100) θ
    (by norm_num) (by norm_num)
  rw [h0] at hy0
  linarith [(abs_le.mp (le_of_lt habs)).2]

/-- **The upper region misses the longitude `θ = dropD`.**  Writing `R = 2 + cos φ`, a point of
`Ω₊` with `(cos θ, sin θ) = (3/5, 4/5)` has `w₀ = -(9/25)·R + (97/100)·sin φ > 0`, whence
`sin φ > (36/97)·R ≥ (36/97) > 0`; but then
`w₂ = (643/500)·R + (59/100)·sin φ > (72991/48500)·R ≥ 72991/48500 > 7/5 = dropS`, contradicting
the box bound `|w₂| < dropS`. -/
theorem drop_upperRegion_theta_ne {θ φ : ℝ}
    (h : dropVec (Work.Core.torusMap θ φ) ∈
      Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus dropDiffeo)
        dropS dropC dropCyc dropU) :
    ¬ (Real.cos θ = 3 / 5 ∧ Real.sin θ = 4 / 5) := by
  rintro ⟨hc, hs⟩
  obtain ⟨-, hbox, hy0⟩ := (Work.BoxShrink.Core.mem_upperRegion).mp h
  obtain ⟨hv2, -, -⟩ := (mem_PBox_drop _).mp hbox
  simp only [dropCyc_two, dropC_zero, dropU, zero_add] at hy0
  have h0 : (dropVec (Work.Core.torusMap θ φ)).ofLp 0
      = (-(9 / 25)) * (2 + Real.cos φ) + (97 / 100) * Real.sin φ := by
    rw [dropVec_coord_zero, Work.CoreTopology.torusMap_apply_zero,
      Work.CoreTopology.torusMap_apply_one, Work.CoreTopology.torusMap_apply_two, hc, hs]
    ring
  have h2 : (dropVec (Work.Core.torusMap θ φ)).ofLp 2
      = (643 / 500) * (2 + Real.cos φ) + (59 / 100) * Real.sin φ := by
    rw [dropVec_coord_two, Work.CoreTopology.torusMap_apply_zero,
      Work.CoreTopology.torusMap_apply_one, Work.CoreTopology.torusMap_apply_two, hc, hs]
    ring
  have hR : (1 : ℝ) ≤ 2 + Real.cos φ := by linarith [Real.neg_one_le_cos φ]
  rw [h0] at hy0
  have hsin : (36 / 97) * (2 + Real.cos φ) < Real.sin φ := by nlinarith [hy0]
  rw [h2] at hv2
  rw [abs_lt] at hv2
  rw [dropS] at hv2
  nlinarith [hv2.2, hsin, hR]

/-! ## The winding span vanishes -/

theorem halfUp_inessential_drop :
    Work.SurgeryInvariance.WindingSpan
      (Work.Smooth.Morse.torus Work.BoxShrink.PinchOff.RefuteDrop.dropDiffeo)
      (Work.BoxShrink.Core.upperRegion
        (Work.Smooth.Morse.torus Work.BoxShrink.PinchOff.RefuteDrop.dropDiffeo)
        Work.BoxShrink.PinchOff.RefuteDrop.dropS
        Work.BoxShrink.PinchOff.RefuteDrop.dropC
        Work.BoxShrink.PinchOff.RefuteDrop.dropCyc
        Work.BoxShrink.PinchOff.RefuteDrop.dropU) = ⊥ := by
  rw [Work.SurgeryInvariance.WindingSpan_eq_bot_iff]
  rintro ⟨γ, ⟨L, hL⟩, hmem⟩
  -- The image of a lift lies in the upper region.
  have hregion : ∀ t : ℝ, dropVec (Work.Core.torusMap (L.Θ t) (L.Φ t)) ∈
      Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus dropDiffeo)
        dropS dropC dropCyc dropU := by
    intro t
    have heq : dropVec (Work.Core.torusMap (L.Θ t) (L.Φ t)) = γ.γ t := by
      rw [← L.lifts t, Work.Smooth.Morse.torus_psi, param_dropDiffeo]
    have h := hmem t
    rwa [← heq] at h
  -- Hence neither parameter hits its forbidden grid circle.
  have hTheta : ∀ t : ℝ, ∀ k : ℤ, L.Θ t ≠ dropD + (k : ℝ) * (2 * Real.pi) := by
    intro t k hk
    have h1 : Real.cos (L.Θ t) = Real.cos dropD := by
      rw [hk, Real.cos_add_int_mul_two_pi]
    have h2 : Real.sin (L.Θ t) = Real.sin dropD := by
      rw [hk, Real.sin_add_int_mul_two_pi]
    exact drop_upperRegion_theta_ne (hregion t)
      ⟨by rw [h1, dropD_cos], by rw [h2, dropD_sin]⟩
  have hPhi : ∀ t : ℝ, ∀ k : ℤ, L.Φ t ≠ dropPhi + (k : ℝ) * (2 * Real.pi) := by
    intro t k hk
    have h2 : Real.sin (L.Φ t) = -1 := by
      rw [hk, Real.sin_add_int_mul_two_pi, dropPhi_sin]
    exact drop_upperRegion_sin_ne_neg_one (hregion t) h2
  -- So both winding increments vanish.
  have h1 : (L.winding).1 = 0 :=
    Work.BoxShrink.PinchOff.int_eq_zero_of_notMem_lattice L.contΘ hTheta
      (by linarith [(L.winding_spec).1])
  have h2 : (L.winding).2 = 0 :=
    Work.BoxShrink.PinchOff.int_eq_zero_of_notMem_lattice L.contΦ hPhi
      (by linarith [(L.winding_spec).2])
  exact hL (Prod.ext h1 h2)

end

end Work.BoxShrink.PinchOff.RefuteDrop
