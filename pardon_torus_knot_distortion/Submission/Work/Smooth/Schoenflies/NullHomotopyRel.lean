import Submission.Work.Smooth.Plane.Jordan
import Submission.Work.Smooth.SphereJordan.Defs

/-!
# The corrected null-homotopy predicate

`Work.Smooth.Plane.NullHomotopicAvoiding` (the "the loop does not wind around `x`" hypothesis of the
planar innermost-disc chapter) is missing the condition that the homotopy go through *loops based at
`c 0`*; as recorded in `Submission/Work/Smooth/Schoenflies/NullHomotopy.lean` it is therefore
satisfied by the cone homotopy for **every** point off the trace, and the classical input
`Work.Smooth.Plane.PlaneJordanInput` built on it is false (`not_planeJordanInput`).

This file introduces the corrected predicate `NullHomotopicRel`: the same homotopy, but required to
be constant on the endpoints of the interval, i.e. a homotopy of loops relative to the base point.
With this correction the predicate has the intended meaning:

* a continuous extension `F : 𝔻 → ℂ` of `c` avoiding `x`, **with `F 0 = c 0`**, gives a
  `NullHomotopicRel c x` (`NullHomotopicRel.of_discExtension`, proved here — the easy direction,
  via the *cone map* `conePoint (s, t) = (1 - s) e^{2π i t}`);
* conversely a `NullHomotopicRel c x` gives such an extension
  (`Work.Smooth.Schoenflies.exists_discExtension_of_nullHomotopicRel`, in `RelExtension.lean`) —
  the classical "a null-homotopic loop extends over the disc", obtained by descending the homotopy
  through the quotient map `conePoint`;
* and then the hard direction of the Jordan curve theorem holds in the corrected form: for `x` on
  the bounded side of a Schoenflies curve `c`, `¬ NullHomotopicRel c x`
  (`Work.Smooth.Schoenflies.not_nullHomotopicRel_of_mem_V`), so the corrected datum
  `Work.Smooth.Schoenflies.PlaneJordanDataRel` is inhabited for every `C¹` simple closed curve
  (`Work.Smooth.Schoenflies.nonempty_planeJordanDataRel_of_smooth`).

## Main definitions

* `conePoint` — the map `[0,1]² → 𝔻`, `(s, t) ↦ (1 - s) e^{2π i t}` (a closed quotient map);
* `NullHomotopicRel c x` — the loop `θ ↦ c (2π θ)` is null-homotopic to the constant loop at `c 0`
  through loops based at `c 0`, in the complement of `x`.

## Main results

* `NullHomotopicRel.of_discExtension` — an avoiding disc extension fixing `c 0` at the centre gives
  a null-homotopy;
* `NullHomotopicRel.const_of_ne` — a constant loop is null-homotopic;
* `NullHomotopicRel.mono` — the predicate only depends on the values of `c` on one period.

## The cone map

`conePoint` is the quotient map through which the converse direction descends the homotopy; its
surjectivity and the description of its fibres (needed for
`Work.Smooth.Schoenflies.exists_discExtension_of_nullHomotopicRel`, see `RelExtension.lean`) are
elementary:
`conePoint (s, t) = conePoint (s', t')` iff `s = s' = 1`, or `s = s' < 1` and `t = t'` or
`{t, t'} = {0, 1}` (using `Complex.exp_eq_exp_iff_exists_int`), and every `z` of the closed disc is
`conePoint (1 - ‖z‖, t)` for a suitable `t` (using `Complex.norm_mul_exp_arg_mul_I`).
-/

open Set

namespace Work.Smooth.Schoenflies

noncomputable section

/-! ## The cone map `[0,1]² → 𝔻` -/

/-- **The cone map** `(s, t) ↦ (1 - s) e^{2π i t}` from the square onto the closed unit disc.  It is
a closed (hence quotient) surjection: it identifies the right edge `{1} × [0,1]` with the centre
`0`, and the two horizontal edges `[0,1] × {0}`, `[0,1] × {1}` with the same radii, so that
`(s, 0)` and `(s, 1)` have the same image. -/
def conePoint (p : Work.Smooth.Plane.ArcInterval × Work.Smooth.Plane.ArcInterval) :
    Work.Smooth.Jordan.Disc :=
  ⟨(((1 - (p.1 : ℝ)) : ℝ) : ℂ)
      * Complex.exp (((((2 * Real.pi * (p.2 : ℝ)) : ℝ)) : ℂ) * Complex.I),
    by
      have hnorm1 : ‖(((1 - (p.1 : ℝ)) : ℝ) : ℂ)‖ = |(1 - (p.1 : ℝ))| := by
        rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]
      rw [Metric.mem_closedBall, dist_zero_right, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
        hnorm1, abs_le]
      exact ⟨by linarith [p.1.2.2], by linarith [p.1.2.1]⟩⟩

/-- The underlying point of `conePoint p`. -/
theorem conePoint_coe (p : Work.Smooth.Plane.ArcInterval × Work.Smooth.Plane.ArcInterval) :
    (conePoint p : ℂ) = (((1 - (p.1 : ℝ)) : ℝ) : ℂ)
      * Complex.exp (((((2 * Real.pi * (p.2 : ℝ)) : ℝ)) : ℂ) * Complex.I) :=
  rfl

/-- The cone map is continuous. -/
theorem continuous_conePoint : Continuous conePoint := by
  refine Continuous.subtype_mk ?_ _
  exact (Complex.continuous_ofReal.comp
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst))).mul
    (Complex.continuous_exp.comp (by fun_prop))

/-- The left edge of the square maps to the boundary circle. -/
theorem conePoint_zero (t : Work.Smooth.Plane.ArcInterval) :
    conePoint (0, t) = Work.Smooth.Jordan.circlePoint (2 * Real.pi * (t : ℝ)) := by
  apply Subtype.ext
  simp only [conePoint]
  rw [Work.Smooth.Jordan.circlePoint_coe]
  simp

/-- The right edge of the square maps to the centre of the disc. -/
theorem conePoint_one (t : Work.Smooth.Plane.ArcInterval) :
    conePoint (1, t) = (0 : Work.Smooth.Jordan.Disc) := by
  apply Subtype.ext
  simp only [conePoint]
  push_cast
  ring_nf

/-- The two horizontal edges of the square map to the same radii. -/
theorem conePoint_snd (s : Work.Smooth.Plane.ArcInterval) :
    conePoint (s, 0) = conePoint (s, 1) := by
  apply Subtype.ext
  simp only [conePoint]
  rw [show (↑(2 * Real.pi * ((0 : Work.Smooth.Plane.ArcInterval) : ℝ)) : ℂ) * Complex.I = 0
        from by rw [show ((0 : Work.Smooth.Plane.ArcInterval) : ℝ) = 0 from rfl]; norm_num,
      Complex.exp_zero,
      show (↑(2 * Real.pi * ((1 : Work.Smooth.Plane.ArcInterval) : ℝ)) : ℂ) * Complex.I
        = 2 * (Real.pi : ℂ) * Complex.I
        from by rw [show ((1 : Work.Smooth.Plane.ArcInterval) : ℝ) = 1 from rfl]; push_cast; ring,
      Complex.exp_two_pi_mul_I]

/-! ## The corrected predicate -/

/-- **The corrected null-homotopy predicate.**  `NullHomotopicRel c x` says: there is a homotopy of
loops, based at `c 0`, from `θ ↦ c (2π θ)` to the constant loop at `c 0`, all of whose values avoid
`x`.

The homotopy is a continuous map `H` on the square `[0,1] × [0,1]`, with

* `H (0, t) = c (2π t)` — the loop,
* `H (1, t) = c 0` — the constant loop,
* `H (s, 0) = H (s, 1)` — the base point of the interval is fixed (this is the condition missing
  from `Work.Smooth.Plane.NullHomotopicAvoiding`; without it the cone homotopy
  `Work.Smooth.Schoenflies.nullHomotopicAvoiding_of_notMem_range` makes the predicate trivial), and
* `H p ≠ x` for all `p`.

So `NullHomotopicRel c x` is the statement that the loop `c` represents the trivial element of
`π₁ (ℂ ∖ {x}, c 0)`, which for `ℂ ∖ {x} ≃ S¹` is exactly "the loop winds zero times around `x`". -/
def NullHomotopicRel (c : ℝ → ℂ) (x : ℂ) : Prop :=
  ∃ H : C(Work.Smooth.Plane.ArcInterval × Work.Smooth.Plane.ArcInterval, ℂ),
    (∀ p, H p ≠ x) ∧
    (∀ t, H (0, t) = c (2 * Real.pi * t)) ∧
    (∀ t, H (1, t) = c 0) ∧
    (∀ s, H (s, 0) = H (s, 1))

namespace NullHomotopicRel

/-- **A disc extension avoiding `x` and fixing `c 0` at the centre gives a null-homotopy relative to
the base point.**  If `F : 𝔻 → ℂ` avoids `x`, restricts to `c` on the boundary circle and satisfies
`F 0 = c 0`, then `H (s, t) = F (conePoint (s, t)) = F ((1 - s) e^{2π i t})` is a homotopy of loops
based at `c 0`, through values avoiding `x`, from the loop `c` to the constant loop.

(The condition `F 0 = c 0` cannot be dropped: an extension over the disc always makes the loop
null-homotopic *freely*, but a homotopy of loops based at `c 0` needs the centre to move to `c 0`.)

This is the easy direction of the equivalence between `NullHomotopicRel` and the existence of an
avoiding disc extension (the other direction is
`Work.Smooth.Schoenflies.exists_discExtension_of_nullHomotopicRel`), and it shows that the corrected
predicate is *not* vacuous. -/
theorem of_discExtension {c : ℝ → ℂ} {x : ℂ} (F : C(Work.Smooth.Jordan.Disc, ℂ))
    (hF : ∀ z, F z ≠ x) (hbd : ∀ θ : ℝ, F (Work.Smooth.Jordan.circlePoint θ) = c θ)
    (h0 : F 0 = c 0) :
    NullHomotopicRel c x :=
  ⟨F.comp ⟨conePoint, continuous_conePoint⟩, fun p => hF _,
    fun t => by
      change F (conePoint (0, t)) = c (2 * Real.pi * (t : ℝ))
      rw [conePoint_zero, hbd],
    fun t => by
      change F (conePoint (1, t)) = c 0
      rw [conePoint_one, h0],
    fun s => by
      change F (conePoint (s, 0)) = F (conePoint (s, 1))
      rw [conePoint_snd]⟩

/-- A constant loop at a point `y ≠ x` is null-homotopic in the complement of `x`. -/
theorem const_of_ne {x y : ℂ} (hxy : y ≠ x) : NullHomotopicRel (fun _ => y) x :=
  of_discExtension (ContinuousMap.const Work.Smooth.Jordan.Disc y) (fun _ => hxy)
    (fun _ => rfl) rfl

/-- The predicate only depends on the values of the loop on one period. -/
theorem mono {c c' : ℝ → ℂ} {x : ℂ} (h : ∀ t : ℝ, c t = c' t) (hc : NullHomotopicRel c x) :
    NullHomotopicRel c' x := by
  obtain ⟨H, hne, h0, h1, hrel⟩ := hc
  exact ⟨H, hne, fun t => by rw [h0 t, h (2 * Real.pi * t)],
    fun t => by rw [h1 t, h 0], hrel⟩

end NullHomotopicRel

end

end Work.Smooth.Schoenflies
