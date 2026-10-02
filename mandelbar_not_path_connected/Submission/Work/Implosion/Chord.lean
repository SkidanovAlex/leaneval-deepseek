/-
Copyright: subproject `Submission/Work/Implosion/` of `mandelbar_not_path_connected`.

# The chord foliation of the fundamental domain, and the cylinder chart

`Geometry.fundamentalDomain` is the union of the straight chords from `t·a ∈ ℓ` to
`f(t·a) ∈ f(ℓ)`.  This file makes that parametrisation explicit and shows that — in the
geometrically natural case that occurs for the set `Nm = {a_c² < 0}` of the lead's (I1),
namely

  `a = i·λ` with `λ > 0`   and   `h` **real-valued on the cut** `ℓ`

(cf. `normalForm_cutPt_re`, `imageCut_disjoint_cut` and `ecalleHeight_eq_zero`) — the
chords are exactly the **horizontal** segments

  `chordPt a h t s = s·λ²(1−t²)·h(t·a) + i·t·λ`,

so that `(t,s) ↦ chordPt a h t s` is a *homeomorphism* from `(−1,1) × [0,1]` onto the
fundamental domain, the two boundary edges `s = 0` (on `ℓ`) and `s = 1` (on `f(ℓ)`) are
identified **at constant height**, and the resulting cylinder is explicitly

  `(phase, height) ∈ (ℝ/ℤ) × ℝ  ≅  ℂ/ℤ ≅ ℂ^*`,

with `phase = s` and `height = log((1+t)/(1−t))/(2λ).  The latter is exactly minus the
Écalle height of the cut point (`Ecalle.ecalCoord_cutPt_im`), which is why the paper can
call the `Im`-coordinate of the cylinder the Écalle height.

This is the straightening that HS Prop. 4.2 / Lemma 4.3 assert; the identification map
`f : ℓ → f(ℓ)` is height-preserving in the ideal case, so the quotient is the cylinder
*by construction*.  The general case (h not real on the cut) is the same statement up to
a horizontal perturbation of the chords; see `NOTES.md` §3.
-/
import Submission.Work.Implosion.Geometry
import Submission.Work.Implosion.Disp

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion

open Complex

/-! ## The chords -/

/-- The chord of the fundamental domain from `t·a ∈ ℓ` to `f(t·a) ∈ f(ℓ)`, linearly
parametrised by `s ∈ [0,1]`. -/
noncomputable def chordPt (a : ℂ) (h : ℂ → ℂ) (t s : ℝ) : ℂ :=
  ((1 - s : ℝ) : ℂ) * cutPt a t + (s : ℂ) * normalForm a h (cutPt a t)

@[simp] theorem chordPt_apply (a : ℂ) (h : ℂ → ℂ) (t s : ℝ) :
    chordPt a h t s
      = ((1 - s : ℝ) : ℂ) * cutPt a t + (s : ℂ) * normalForm a h (cutPt a t) := rfl

/-- The chord starts on the cut `ℓ`. -/
theorem chordPt_zero (a : ℂ) (h : ℂ → ℂ) (t : ℝ) : chordPt a h t 0 = cutPt a t := by
  simp [chordPt]

/-- The chord ends on the image arc `f(ℓ)`. -/
theorem chordPt_one (a : ℂ) (h : ℂ → ℂ) (t : ℝ) :
    chordPt a h t 1 = normalForm a h (cutPt a t) := by
  simp [chordPt]

/-- The fundamental domain is exactly the image of the chord map. -/
theorem mem_fundamentalDomain_iff_chordPt (a : ℂ) (h : ℂ → ℂ) (ζ : ℂ) :
    ζ ∈ fundamentalDomain a h ↔
      ∃ t : ℝ, t ∈ Set.Ioo (-1 : ℝ) 1 ∧ ∃ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 ∧
        ζ = chordPt a h t s := by
  exact Iff.rfl

/-! ## The height coordinate of the cut -/

/-- The **height** coordinate along the cut: `log((1+t)/(1−t))/(2λ)`.  By
`Ecalle.ecalCoord_cutPt_im` this is `−Im (ecalCoord a (t·a))` for `a = iλ`, i.e. minus
the Écalle height of the cut point; it runs over all of `ℝ` as `t` runs over `(−1,1)`. -/
noncomputable def chordHeight (lam t : ℝ) : ℝ := Real.log ((1 + t) / (1 - t)) / (2 * lam)

/-! ## The cylinder coordinate on the fundamental domain -/

/-- The **cylinder coordinate** of the ideal case: a point of the fundamental domain
sits on the chord at height `chordHeight t` and at chord parameter `s ∈ [0,1)`; the map
`(phase, height) ↦ exp (2πi (phase + i·height))` sends the cylinder `(ℝ/ℤ) × ℝ` onto
`ℂ*`, and the identification `s = 0 ↔ s = 1` is exactly the period. -/
noncomputable def chordCylCoord (lam : ℝ) (t s : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * I * ((s : ℂ) + (chordHeight lam t : ℂ) * I))


/-! ## The tilted case: the twist, and the chart of the general perturbed cylinder

When `h` is *not* real on the cut the straight chords of §`chordPt` are no longer
horizontal.  One then changes the transversal: in the Écalle coordinate `u` take the
**horizontal** segments from the line `L = {Re u = x}` (the image of the cut under
`ecalCoord`, which does not depend on `h`) to the image curve `transitMap '' L`.  These
segments never cross (distinct level `Im u`), and the only data needed is

* the **twist** `twist a h x y = Im (transitMap a h (x + y·I))`, i.e. the level at which
  the image of the base point of level `y` sits; the curve `transitMap '' L` is a graph
  over the level precisely when `twist` is a strictly monotone surjection `ℝ → ℝ`
  (`Chord.levelMap_strictMono);
* the gluing `(y, 0) ~ (twist y, 1)` of the two boundary curves of the slab; an
  increasing homeomorphism of `ℝ` with `twist y > y` is conjugate to `y ↦ y+1`
  (`Chord.exists_conj_translation`), which straightens the twist.

The chart is then explicit: with `F(y,s) = Ψ y − s` the gluing invariant,

  `tiltedCylCoord Ψ y s = exp (−2π F(y,s)) · exp (2πi s)`,

which is periodic with period `2` in `F` and therefore constant on the gluing; on the
fundamental domain `s ∈ [0,1)` it is **injective**, and since `F` runs over `ℝ` its
range is all of `ℂ*`.  Hence the perturbed cylinder is `(ℝ/ℤ) × ℝ ≅ ℂ/ℤ ≅ ℂ*` also in
the tilted case, with `phase = s` and `height = Ψ y`.
-/

/-- The **twist** of the tilted cylinder: the level of the image of the base point of
level `y` under one iterate of the dynamics. -/
noncomputable def twist (a : ℂ) (h : ℂ → ℂ) (x y : ℝ) : ℝ :=
  (transitMap a h (x + (y : ℂ) * I)).im

/-- The **chart of the tilted cylinder**: `(y, s)` parametrises the horizontal segment of
the slab at level `y` (parameter `s ∈ [0,1]` from the line `L` to the image curve), and
`tiltedCylCoord Ψ y s = exp (−2π (Ψ y − s)) · exp (2π i s)` is the resulting coordinate
on the cylinder.  It is invariant under the gluing `(y,0) ~ (twist y,1)` whenever
`Ψ (twist y) = Ψ y + 1`. -/
noncomputable def tiltedCylCoord (Psi : ℝ → ℝ) (y s : ℝ) : ℂ :=
  Complex.exp (-(2 * Real.pi) * ((Psi y - s : ℝ) : ℂ)) * Complex.exp (2 * Real.pi * I * (s : ℂ))

theorem tiltedCylCoord_apply (Psi : ℝ → ℝ) (y s : ℝ) :
    tiltedCylCoord Psi y s
      = Complex.exp (-(2 * Real.pi) * ((Psi y - s : ℝ) : ℂ))
        * Complex.exp (2 * Real.pi * I * (s : ℂ)) := rfl

end Work.Implosion