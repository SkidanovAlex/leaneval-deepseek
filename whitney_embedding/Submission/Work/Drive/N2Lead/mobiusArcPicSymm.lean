import Mathlib
import Submission.Work.Drive.N2Lead.twistDefs
import Submission.Work.Drive.N2Lead.twistToolkit
import Submission.Work.Drive.N2Lead.mobius_bridgeStar

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

/-!
# The picture symmetry of the pushed Möbius arc

The Möbius arc of the saddle certificate is drawn as the planar arc `z ↦ cE3 z`
(`cE3 w = (re w, im w, 0)`, so `z` is the *planar* complex parameter of the arc), carried by the
vertical slab twist `twistX ε (-1)` — which rotates the vertical circle through `cE3 w` by the angle
`-π · τ ((re w + ε)/(2ε))`, `τ = smoothTransition` — and then pushed vertically by `pushY Dp εp 1`
(`y ↦ ψ y` with `ψ = pushProf Dp εp 1`, a strictly increasing *odd* function).

The two symmetries of the resulting picture `W z = pushY Dp εp 1 (twistX ε (-1) (cE3 z))` recorded
here are

* **the antipodal reflection** `proj2 (W z) ↦ -proj2 (W z)` under `z ↦ -star z` (the reflection in
  the origin of the *parameter* plane, `-star z = -conj z`), and
* **the conjugation symmetry** `proj2 (W z) ↦ star (proj2 (W z))` under `z ↦ star z`.

Both follow from the fact that the twist angle depends only on `re w`:

* `re (-star z) = - re z` and `im (-star z) = im z`, while
  `τ (((- re z) + ε)/(2ε)) = τ (1 - (re z + ε)/(2ε)) = 1 - τ ((re z + ε)/(2ε))`
  (`smoothTransition_one_sub`), so the twist angle changes from `θ` to `-π - θ`, and
  `cos (-π - θ) = - cos θ`.  Hence the *height* `im w · cos θ` is negated, and the oddness of `ψ`
  completes the reflection;
* `re (star z) = re z` and `im (star z) = - im z`, so the angle is *unchanged* and the height is
  negated, which the oddness of `ψ` turns into the conjugation of `proj2`.

No hypothesis on `Dp` is needed; `εp > 0` only serves to make `pushProf Dp εp 1` odd on the nose.
-/

/-- The angle by which `twistX ε (-1)` rotates the vertical circle through `cE3 w`. -/
def e3TwistAngle (ε : ℝ) (w : ℂ) : ℝ :=
  -1 * (Real.pi * Real.smoothTransition ((w.re + ε) / (2 * ε)))

/-- The trigonometric core of the antipodal reflection: passing from the argument `u` of
`smoothTransition` to `1 - u` sends the cosine of the twist angle to its negative. -/
theorem cos_neg_angle_one_sub (u : ℝ) :
    Real.cos (-1 * (Real.pi * (1 - u))) = -Real.cos (-1 * (Real.pi * u)) := by
  have h : -1 * (Real.pi * (1 - u)) = -((-1 * (Real.pi * u)) + Real.pi) := by ring
  rw [h, Real.cos_neg, Real.cos_add_pi]

/-- `star` on `ℂ`, in coordinates. -/
theorem complex_star_mk (a b : ℝ) : star (⟨a, b⟩ : ℂ) = ⟨a, -b⟩ := by
  apply Complex.ext <;> simp

/-- Negation of a complex number, in coordinates. -/
theorem complex_neg_mk (a b : ℝ) : -(⟨a, b⟩ : ℂ) = ⟨-a, -b⟩ := by
  apply Complex.ext <;> simp

/-- The twist angle only depends on the real part, so `star` does not move it. -/
theorem e3TwistAngle_star (ε : ℝ) (z : ℂ) : e3TwistAngle ε (star z) = e3TwistAngle ε z := by
  have hre : (star z : ℂ).re = z.re := by simp
  simp only [e3TwistAngle]
  rw [hre]

/-- The antipodal reflection of the parameter negates the cosine of the twist angle. -/
theorem cos_e3TwistAngle_neg_star {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    Real.cos (e3TwistAngle ε (-star z)) = -Real.cos (e3TwistAngle ε z) := by
  have harg : ((-star z : ℂ).re + ε) / (2 * ε) = 1 - (z.re + ε) / (2 * ε) := by
    have h2 : (2:ℝ) * ε ≠ 0 := by positivity
    have hre : (-star z : ℂ).re = -z.re := by simp
    rw [hre]
    field_simp
    ring
  have h1 : e3TwistAngle ε (-star z)
      = -1 * (Real.pi * Real.smoothTransition (1 - (z.re + ε) / (2 * ε))) := by
    simp only [e3TwistAngle, harg]
  have h2 : e3TwistAngle ε z
      = -1 * (Real.pi * Real.smoothTransition ((z.re + ε) / (2 * ε))) := rfl
  rw [h1, h2, smoothTransition_one_sub]
  exact cos_neg_angle_one_sub _

/-- **The projected pushed arc in coordinates.**  Writing `θ = e3TwistAngle ε w`, the twist rotates
the vertical circle through `cE3 w` to `(re w, im w · cos θ, im w · sin θ)` and the push only moves
the second coordinate by `pushProf`, so the planar projection is
`⟨re w, pushProf Dp εp 1 (im w · cos θ)⟩`. -/
theorem proj2_pushY_twistX_cE3 (Dp εp ε : ℝ) (w : ℂ) :
    proj2 (pushY Dp εp 1 (twistX ε (-1) (Work.Drive.N2.cE3 w)))
      = ⟨w.re, pushProf Dp εp 1 (w.im * Real.cos (e3TwistAngle ε w))⟩ := by
  have h1 : twistX ε (-1) (Work.Drive.N2.cE3 w)
      = rot12 (e3TwistAngle ε w) (Work.Drive.N2.cE3 w) := by
    rw [twistX_eq]
    simp only [twistAngleX, e3TwistAngle, Work.Drive.N2.cE3_apply_zero]
  rw [h1]
  have h0 : (rot12 (e3TwistAngle ε w) (Work.Drive.N2.cE3 w)) 0 = w.re := by
    simp [rot12, Work.Drive.N2.cE3_apply_zero, Work.Drive.N2.cE3_apply_two]
  have h2 : (rot12 (e3TwistAngle ε w) (Work.Drive.N2.cE3 w)) 1
      = w.im * Real.cos (e3TwistAngle ε w) := by
    simp [rot12, Work.Drive.N2.cE3_apply_zero, Work.Drive.N2.cE3_apply_one,
      Work.Drive.N2.cE3_apply_two]
  have hproj : proj2 (pushY Dp εp 1 (rot12 (e3TwistAngle ε w) (Work.Drive.N2.cE3 w)))
      = ⟨(rot12 (e3TwistAngle ε w) (Work.Drive.N2.cE3 w)) 0,
          pushProf Dp εp 1 ((rot12 (e3TwistAngle ε w) (Work.Drive.N2.cE3 w)) 1)⟩ := by
    simp [proj2, pushY_apply_zero, pushY_apply_one]
  rw [hproj, h0, h2]

theorem mobiusArcPicSymm {ε εp Dp : ℝ} (hε : 0 < ε) (hεp : 0 < εp) (z : ℂ) :
    Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.pushY Dp εp 1 (Work.Drive.N2Lead.twistX ε (-1)
        (Work.Drive.N2.cE3 (-star z))))
      = - Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.pushY Dp εp 1 (Work.Drive.N2Lead.twistX ε (-1)
        (Work.Drive.N2.cE3 z))) ∧
    Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.pushY Dp εp 1 (Work.Drive.N2Lead.twistX ε (-1)
        (Work.Drive.N2.cE3 (star z))))
      = star (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.pushY Dp εp 1 (Work.Drive.N2Lead.twistX ε (-1)
        (Work.Drive.N2.cE3 z)))) := by
  have hodd : ∀ y : ℝ, pushProf Dp εp 1 (-y) = -pushProf Dp εp 1 y :=
    fun y => pushProf_odd (D := Dp) (εp := εp) (s := 1) (y := y) (ne_of_gt hεp)
  have hz := proj2_pushY_twistX_cE3 Dp εp ε z
  refine ⟨?_, ?_⟩
  · rw [proj2_pushY_twistX_cE3 Dp εp ε (-star z), hz]
    have hre : (-star z : ℂ).re = -z.re := by simp
    have him : (-star z : ℂ).im = z.im := by simp
    rw [cos_e3TwistAngle_neg_star hε z, hre, him,
      show z.im * -Real.cos (e3TwistAngle ε z)
        = -(z.im * Real.cos (e3TwistAngle ε z)) by ring,
      hodd, complex_neg_mk]
  · rw [proj2_pushY_twistX_cE3 Dp εp ε (star z), hz]
    have hre : (star z : ℂ).re = z.re := by simp
    have him : (star z : ℂ).im = -z.im := by simp
    rw [e3TwistAngle_star, hre, him,
      show -z.im * Real.cos (e3TwistAngle ε z)
        = -(z.im * Real.cos (e3TwistAngle ε z)) by ring,
      hodd, complex_star_mk]

end

end Work.Drive.N2Lead
