import Mathlib
import Submission.Work.BoxShrink.PinchOff.RefuteDrop.Config

/-!
# Transversality of the cutting plane for the `DropCase` counterexample

This module proves the first of the five hypotheses of the refutation carried out in
`Work.BoxShrink.PinchOff.RefuteDrop` (see `Work.BoxShrink.PinchOff.RefuteDrop.Config` for the
configuration): the cutting plane `{x = 0}` is **transverse** to the surface
`dropDiffeo(F_standard)` inside the box, i.e.

`Work.BoxShrink.Pinch.TransverseSlice dropDiffeo dropS dropC dropCyc dropU`.

Expanding the definition (`Work.BoxShrink.Pinch.TransverseSlice`), the claim is that for every
parameter `p = (θ, φ) ∈ ℝ²` with `boxB dropDiffeo dropC dropCyc p < dropS = 7/5` and
`planeG dropDiffeo dropC dropCyc dropU p = 0`, the derivative `fderiv ℝ (planeG …) p` is nonzero.

The computation is completely explicit.  With `σ = dropCyc = swap 0 2` one has `σ 2 = 0`, hence the
plane coordinate is the first coordinate of `ℝ³`, and since `dropDiffeo = dropVec` is the linear
map of `dropA` the pull-back is the trigonometric function

`G(θ, φ) = (2 + cos φ) · ((-2/25)·cos θ - (39/100)·sin θ) + (97/100)·sin φ`

(here `-2/25`, `-39/100`, `97/100` are the entries of the first row of `dropA`, because
`σ 2 = 0`; see `Work.Core.torusMap` for the parametrisation of the standard torus).

Writing `P = (-2/25)·cos θ - (39/100)·sin θ`, `Q = (2/25)·sin θ - (39/100)·cos θ`, `s = sin φ`,
`k = cos φ`, the two partial derivatives at a point with `G = 0` are `(2 + k)·Q` and `-P·s +
(97/100)·k`.  The point of the proof is the algebraic identity

`P² + Q² = ((-2/25)² + (39/100)²) = 317/2000`,

which is nothing but `cos²θ + sin²θ = 1`.  So if `G`, `G_θ` and `G_φ` all vanished, then
`Q = 0`, `P² = 317/2000`, `(2 + k)·P + (97/100)·s = 0` and `P·s = (97/100)·k`; multiplying the
third relation by `s` and using `s² + k² = 1` gives `(97/100)·(1 + 2k) = 0`, so `k = -1/2`, and
multiplying it by `P` gives `(3/2)·(317/2000) = (97/100)²`, i.e. `4755/10000 = 9409/10000`, a
contradiction.  (`drop_alg` below isolates this arithmetic.)

An important feature: **the box hypothesis is never used**.  The plane `{x = 0}` meets the surface
`dropDiffeo(F_standard)` transversally at every point of the surface, not merely inside the box; the
`TransverseSlice` hypothesis is therefore satisfied a fortiori.  This is consistent with the role of
`transverseSlice_drop` in the refutation: `TransverseSlice` is the general-position hypothesis which
the counterexample *does* satisfy, so that the residual `DropCase` cannot be dismissed by
degeneracy of the cutting plane.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff.RefuteDrop

noncomputable section

/-! ## The first row of the distortion matrix -/

/-- The `(0,0)`-entry of `dropA`. -/
theorem dropA_zero_zero : dropA 0 0 = (-2/25 : ℝ) := rfl

/-- The `(0,1)`-entry of `dropA`. -/
theorem dropA_zero_one : dropA 0 1 = (-39/100 : ℝ) := rfl

/-- The `(0,2)`-entry of `dropA`. -/
theorem dropA_zero_two : dropA 0 2 = (97/100 : ℝ) := rfl

/-- The permutation `dropCyc = swap 0 2` sends the plane direction `2` to the coordinate `0`. -/
theorem dropCyc_two : dropCyc 2 = (0 : Fin 3) := by decide

/-! ## The explicit form of the plane coordinate -/

/-- The pull-back of the cutting plane coordinate at the counterexample's configuration, in
closed form: `G(θ, φ) = (2 + cos φ)·((-2/25)·cos θ - (39/100)·sin θ) + (97/100)·sin φ`. -/
def dropGform (p : ℝ × ℝ) : ℝ :=
  (2 + Real.cos p.2) * ((-2/25) * Real.cos p.1 + (-39/100) * Real.sin p.1)
    + (97/100) * Real.sin p.2

@[simp] theorem dropGform_apply (p : ℝ × ℝ) : dropGform p =
    (2 + Real.cos p.2) * ((-2/25) * Real.cos p.1 + (-39/100) * Real.sin p.1)
      + (97/100) * Real.sin p.2 := rfl

/-- **The plane coordinate of the counterexample is `dropGform`.** -/
theorem planeG_drop :
    Work.BoxShrink.Pinch.planeG dropDiffeo dropC dropCyc dropU = dropGform := by
  funext p
  rw [Work.BoxShrink.Pinch.planeG_apply, Work.BoxShrink.Bubble.planeCoord_apply,
    Work.BoxShrink.Pinch.par_apply]
  simp only [dropDiffeo_apply, dropC, dropU, dropCyc]
  have hσ : (Equiv.swap 0 2 : Equiv.Perm (Fin 3)) 2 = 0 := by decide
  rw [hσ]
  simp only [WithLp.ofLp_zero, Pi.zero_apply, zero_add, sub_zero, dropVec_apply,
    Fin.sum_univ_three]
  rw [dropA_zero_zero, dropA_zero_one, dropA_zero_two,
    Work.CoreTopology.torusMap_apply_zero, Work.CoreTopology.torusMap_apply_one,
    Work.CoreTopology.torusMap_apply_two, dropGform_apply]
  ring

/-! ## The derivative of the plane coordinate -/

/-- **The Fréchet derivative of `dropGform`**, in row-vector form: its value on `(1,0)` is
`(2 + cos φ)·Q` and its value on `(0,1)` is `-P·sin φ + (97/100)·cos φ`. -/
theorem fderiv_dropG (p : ℝ × ℝ) :
    fderiv ℝ dropGform p
      = (2 + Real.cos p.2) •
          (((2/25) * Real.sin p.1 + (-39/100) * Real.cos p.1) •
            (ContinuousLinearMap.fst ℝ ℝ ℝ))
        + ((-2/25) * Real.cos p.1 + (-39/100) * Real.sin p.1) •
          ((-Real.sin p.2) • (ContinuousLinearMap.snd ℝ ℝ ℝ))
        + ((97/100) * Real.cos p.2) • (ContinuousLinearMap.snd ℝ ℝ ℝ) := by
  have hA : HasFDerivAt (fun q : ℝ × ℝ => 2 + Real.cos q.2)
      ((-Real.sin p.2) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) p :=
    ((ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.snd ℝ ℝ ℝ) (x := p)).cos).const_add 2
  have hB1 : HasFDerivAt (fun q : ℝ × ℝ => Real.cos q.1)
      ((-Real.sin p.1) • (ContinuousLinearMap.fst ℝ ℝ ℝ)) p :=
    (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.fst ℝ ℝ ℝ) (x := p)).cos
  have hB2 : HasFDerivAt (fun q : ℝ × ℝ => Real.sin q.1)
      (Real.cos p.1 • (ContinuousLinearMap.fst ℝ ℝ ℝ)) p :=
    (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.fst ℝ ℝ ℝ) (x := p)).sin
  have hB : HasFDerivAt
      (fun q : ℝ × ℝ => (-2/25) * Real.cos q.1 + (-39/100) * Real.sin q.1)
      (((2/25) * Real.sin p.1 + (-39/100) * Real.cos p.1) •
        (ContinuousLinearMap.fst ℝ ℝ ℝ)) p := by
    have h := (hB1.const_mul (-2/25)).add (hB2.const_mul (-39/100))
    have hprod : ((-2/25 : ℝ) • ((-Real.sin p.1) • (ContinuousLinearMap.fst ℝ ℝ ℝ))
      + (-39/100 : ℝ) • (Real.cos p.1 • (ContinuousLinearMap.fst ℝ ℝ ℝ)))
        = (((2/25) * Real.sin p.1 + (-39/100) * Real.cos p.1) •
            (ContinuousLinearMap.fst ℝ ℝ ℝ)) := by
      apply ContinuousLinearMap.ext
      intro v
      simp only [add_apply, smul_apply]
      ring
    rwa [hprod] at h
  have hC : HasFDerivAt (fun q : ℝ × ℝ => (97/100) * Real.sin q.2)
      (((97/100) * Real.cos p.2) • (ContinuousLinearMap.snd ℝ ℝ ℝ)) p := by
    have h := ((ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.snd ℝ ℝ ℝ)
      (x := p)).sin).const_mul (97/100)
    have hprod : ((97/100 : ℝ) •
        (Real.cos ((ContinuousLinearMap.snd ℝ ℝ ℝ) p) • (ContinuousLinearMap.snd ℝ ℝ ℝ)))
        = (((97/100) * Real.cos ((ContinuousLinearMap.snd ℝ ℝ ℝ) p)) •
            (ContinuousLinearMap.snd ℝ ℝ ℝ)) := by
      apply ContinuousLinearMap.ext
      intro v
      simp only [smul_apply]
      ring
    rwa [hprod] at h
  exact (hA.mul hB).add hC |>.fderiv

/-- The derivative of `dropGform` in the `θ`-direction: `(2 + cos φ)·Q`. -/
theorem fderiv_dropG_fst (p : ℝ × ℝ) : fderiv ℝ dropGform p (1, 0)
    = (2 + Real.cos p.2) * ((2/25) * Real.sin p.1 + (-39/100) * Real.cos p.1) := by
  rw [fderiv_dropG]
  simp only [add_apply, smul_apply]
  norm_num

/-- The derivative of `dropGform` in the `φ`-direction: `-P·sin φ + (97/100)·cos φ`. -/
theorem fderiv_dropG_snd (p : ℝ × ℝ) : fderiv ℝ dropGform p (0, 1)
    = -((-2/25) * Real.cos p.1 + (-39/100) * Real.sin p.1) * Real.sin p.2
        + (97/100) * Real.cos p.2 := by
  rw [fderiv_dropG]
  simp only [add_apply, smul_apply]
  norm_num
  ring

/-! ## The arithmetic of the counterexample -/

/-- **`G`, `G_θ` and `G_φ` cannot vanish simultaneously.**  Here `P = -2/25·cos θ - 39/100·sin θ`,
`s = sin φ` and `k = cos φ`: the four hypotheses are `P² = 317/2000` (which is `P² + Q²` with
`Q = G_θ/(2 + cos φ) = 0`), the vanishing of `G`, the vanishing of `G_φ` and `s² + k² = 1`. -/
theorem drop_alg (P s k : ℝ) (hP2 : P^2 = (317/2000 : ℝ))
    (h3 : (2 + k) * P + (97/100) * s = 0)
    (h4 : P * s = (97/100) * k)
    (h5 : s^2 + k^2 = 1) : False := by
  -- multiplying `G = 0` by `s` and using `P·s = (97/100)·k` gives `(97/100)·(2k + 1) = 0`
  have hk : k = -(1/2) := by
    have e1 : s * ((2 + k) * P + (97/100) * s) = 0 := by rw [h3, mul_zero]
    have e2 : (2 + k) * ((97/100) * k) + (97/100) * s^2 = 0 := by
      linear_combination e1 - (2 + k) * h4
    nlinarith [e2, h5]
  -- multiplying `G = 0` by `P` and using `P·s = (97/100)·k` and `P² = 317/2000`
  have e3 : P * ((2 + k) * P + (97/100) * s) = 0 := by rw [h3, mul_zero]
  have e4 : (2 + k) * (317/2000) + (97/100)^2 * k = 0 := by
    linear_combination e3 - (2 + k) * hP2 - (97/100) * h4
  rw [hk] at e4
  norm_num at e4

/-- **Nonvanishing of the plane-coordinate form.**  For every parameter `p`, `dropGform p = 0`
implies `fderiv ℝ dropGform p ≠ 0`.  The box hypothesis of `TransverseSlice` is not needed. -/
theorem fderiv_dropG_ne_zero (p : ℝ × ℝ) (hG : dropGform p = 0) :
    fderiv ℝ dropGform p ≠ 0 := by
  intro hD
  -- the two partial derivatives of `G` vanish
  have hQ0 : (2 + Real.cos p.2)
      * ((2/25) * Real.sin p.1 + (-39/100) * Real.cos p.1) = 0 := by
    have h := fderiv_dropG_fst p
    rw [hD] at h
    simpa using h.symm
  have hQ : (2/25) * Real.sin p.1 + (-39/100) * Real.cos p.1 = 0 := by
    have hpos : 0 < 2 + Real.cos p.2 := by nlinarith [Real.neg_one_le_cos p.2]
    rcases mul_eq_zero.mp hQ0 with h | h
    · exact absurd h (ne_of_gt hpos)
    · exact h
  -- hence `P² = P² + Q² = 317/2000`
  have hP2 : ((-2/25) * Real.cos p.1 + (-39/100) * Real.sin p.1)^2 = 317/2000 := by
    have hsum : ((-2/25) * Real.cos p.1 + (-39/100) * Real.sin p.1)^2
        + ((2/25) * Real.sin p.1 + (-39/100) * Real.cos p.1)^2 = 317/2000 := by
      nlinarith [Real.cos_sq_add_sin_sq p.1]
    simp [hQ] at hsum
    exact hsum
  -- the `φ`-derivative gives `P·sin φ = (97/100)·cos φ`
  have h4 : ((-2/25) * Real.cos p.1 + (-39/100) * Real.sin p.1) * Real.sin p.2
      = (97/100) * Real.cos p.2 := by
    have h := fderiv_dropG_snd p
    rw [hD] at h
    simp only [zero_apply] at h
    linarith [h]
  exact drop_alg ((-2/25) * Real.cos p.1 + (-39/100) * Real.sin p.1) (Real.sin p.2)
    (Real.cos p.2) hP2 hG h4 (Real.sin_sq_add_cos_sq p.2)

/-! ## The deliverable -/

theorem transverseSlice_drop :
    Work.BoxShrink.Pinch.TransverseSlice
      Work.BoxShrink.PinchOff.RefuteDrop.dropDiffeo
      Work.BoxShrink.PinchOff.RefuteDrop.dropS
      Work.BoxShrink.PinchOff.RefuteDrop.dropC
      Work.BoxShrink.PinchOff.RefuteDrop.dropCyc
      Work.BoxShrink.PinchOff.RefuteDrop.dropU := by
  intro p _ hG hD
  rw [planeG_drop] at hG hD
  exact fderiv_dropG_ne_zero p hG hD

end

end Work.BoxShrink.PinchOff.RefuteDrop
