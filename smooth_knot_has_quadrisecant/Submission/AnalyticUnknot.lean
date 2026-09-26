import Mathlib
import ChallengeDeps
import Submission.Helpers

open LeanEval.KnotTheory.Quadrisecant
open scoped Real Topology

/-!
# Layer B, explicit-formula case — vertical graphs over the round circle are
unknotted (VERIFIED, sorry-free)
(Submission/AnalyticUnknot.lean)

**Why an explicit formula is needed.**  `IsUnknotted r` demands a *single*
two-parameter map `R : ℝ → ℝ → Space` with `ContDiff ℝ ⊤ (fun p => R p.1 p.2)`
whose slices `R · s` are smooth knots for `s ∈ [0,1]`, joining `r` to
`standardCircle`.  Because `ContDiff ℝ ⊤` is **analyticity** (`ω`, see ROADMAP
S283b), there is no room for gluing with cutoffs: a family that is constant on
an interval of `s` is constant there, so the classical "pause and concatenate"
construction of an isotopy is *not* available at the analytic order.  Any
Layer-B route must therefore produce the isotopy as **one formula** — which is
exactly what Kuperberg's chord-family disk is built from.

This module carries out the one explicit case that the trisecant geometry
naturally produces, in complete generality at the level of the *formula*:

* a **vertical graph over the round circle** is a curve
  `t ↦ standardCircle t + γ t • e₃` with `γ : ℝ → ℝ` (here `e₃ = !₂[0,0,1]`),
  i.e. a knot lying over the unit circle in the `xy`-plane, at height `γ t`;
* such a curve, when `γ` is analytic and `period`-periodic, is a smooth knot
  (`isSmoothKnot_verticalGraph`), and it is **unknotted**
  (`isUnknotted_of_verticalGraph`), with the completely explicit isotopy
  ```
  R t s = standardCircle t + ((1 - s) * γ t) • e₃      (linear interpolation of the height)
  ```
  which is analytic in `(t,s)` whenever `γ` is, and whose every slice is again
  a vertical graph over the round circle, hence a smooth knot.

The ingredient that makes the slices smooth knots is that *nothing can go
wrong*: the `xy`-projection of every slice is the (injective, regular) round
circle, so the slice is injective on one period and has nonzero velocity
(`velocity_verticalGraph_ne_zero`, from the explicit derivative
`deriv_verticalGraph`).

This is the formalized shape of Kuperberg's §1 "trivial case": as soon as the
trisecant-free geometry produces a spanning disk that is a *vertical graph*
over the round circle, the whole Layer-B bridge `SpanningDisk_implies_IsUnknotted`
becomes the single displayed formula above, with no Dehn/Schoenflies input.

Everything here is elementary and verified (no axioms, no `sorry`).
-/

noncomputable section
namespace LeanEval.KnotTheory.Quadrisecant

/-- The unit vertical vector `!₂[0, 0, 1]`. -/
def e3 : Space := !₂[(0 : ℝ), 0, 1]

/-! ## 1. The explicit family and its analyticity -/

/-- **The vertical-graph isotopy is jointly analytic (VERIFIED)**: for analytic
`γ`, the two-parameter family `(t, s) ↦ standardCircle t + ((1 - s) * γ t) • e₃`
is analytic in `(t, s)`. -/
theorem contDiff_verticalGraphFamily {γ : ℝ → ℝ} (hγ : ContDiff ℝ ⊤ γ) :
    ContDiff ℝ ⊤
      (fun p : ℝ × ℝ => standardCircle p.1 + ((1 - p.2) * γ p.1) • e3) := by
  have h1 : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => standardCircle p.1) :=
    standardCircle_contDiff.comp contDiff_fst
  have h2 : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => (1 - p.2) * γ p.1) :=
    (contDiff_const.sub contDiff_snd).mul (hγ.comp contDiff_fst)
  exact h1.add (h2.smul contDiff_const)

/-- **The derivative of a vertical graph (VERIFIED)**: for `γ` differentiable at
`t`, the derivative of `u ↦ standardCircle u + γ u • e₃` at `t` is
`!₂[-sin t, cos t, γ' t]` — the `xy`-part is exactly the unit tangent of the
round circle, and the height simply contributes `γ' t`. -/
theorem deriv_verticalGraph {γ : ℝ → ℝ} {t : ℝ} (hγ : DifferentiableAt ℝ γ t) :
    deriv (fun u : ℝ => standardCircle u + (γ u) • e3) t =
      !₂[-Real.sin t, Real.cos t, deriv γ t] := by
  have hA : HasDerivAt (fun u : ℝ => standardCircle u) (velocity standardCircle t) t :=
    ((standardCircle_contDiff.differentiable (by simp)).differentiableAt).hasDerivAt
  have hB : HasDerivAt (fun u : ℝ => (γ u) • e3) ((deriv γ t) • e3) t :=
    hγ.hasDerivAt.smul_const e3
  have hsum : HasDerivAt (fun u : ℝ => standardCircle u + (γ u) • e3)
      (velocity standardCircle t + (deriv γ t) • e3) t := hA.add hB
  rw [hsum.deriv, standardCircle_velocity]
  ext i
  fin_cases i <;> simp [e3]

/-- **Vertical graphs are everywhere regular (VERIFIED)**: for `γ`
differentiable at `t`, the velocity of `u ↦ standardCircle u + γ u • e₃` at `t`
is nonzero — its `xy`-part is the unit tangent vector of the round circle. -/
theorem velocity_verticalGraph_ne_zero {γ : ℝ → ℝ} {t : ℝ}
    (hγ : DifferentiableAt ℝ γ t) :
    velocity (fun u : ℝ => standardCircle u + (γ u) • e3) t ≠ 0 := by
  rw [velocity, deriv_verticalGraph hγ]
  intro h
  have hnorm : ‖(!₂[-Real.sin t, Real.cos t, deriv γ t] : Space)‖ ^ 2
      = 1 + (deriv γ t) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_three, Real.sin_sq_add_cos_sq]
  have h0 : ‖(!₂[-Real.sin t, Real.cos t, deriv γ t] : Space)‖ ^ 2 = 0 := by
    rw [h]; simp
  nlinarith [sq_nonneg (deriv γ t)]

/-! ## 2. Slices are smooth knots -/

/-- **`period`-periodicity of a vertical graph (VERIFIED)**: the vertical graph
of a `period`-periodic height function is `period`-periodic. -/
theorem periodic_verticalGraph {γ : ℝ → ℝ} (hγ : Function.Periodic γ period) :
    Function.Periodic (fun t : ℝ => standardCircle t + (γ t) • e3) period := by
  intro t
  change standardCircle (t + period) + (γ (t + period)) • e3
    = standardCircle t + (γ t) • e3
  rw [standardCircle_periodic t, hγ t]

/-- **The vertical graph is injective on one period (VERIFIED)**: two points of
the vertical graph of `γ` coincide only if their `xy`-projections — round circle
points — coincide, i.e. only if the parameters agree modulo the period. -/
theorem injOn_verticalGraph (γ : ℝ → ℝ) :
    Set.InjOn (fun t : ℝ => standardCircle t + (γ t) • e3) (Set.Ico (0 : ℝ) period) := by
  intro t ht t' ht' heq
  have hsc : standardCircle t = standardCircle t' := by
    ext i
    fin_cases i
    · have h := congrArg (fun z : Space => z.ofLp 0) heq
      simpa [e3] using h
    · have h := congrArg (fun z : Space => z.ofLp 1) heq
      simpa [e3] using h
    · simp [standardCircle]
  exact standardCircle_injective ht ht' hsc

/-- **A vertical graph over the round circle with analytic periodic height is a
smooth knot (VERIFIED)**: it is analytic, `period`-periodic, injective on one
period, and everywhere regular. -/
theorem isSmoothKnot_verticalGraph {γ : ℝ → ℝ} (hγ : ContDiff ℝ ⊤ γ)
    (hper : Function.Periodic γ period) :
    IsSmoothKnot (fun t : ℝ => standardCircle t + (γ t) • e3) where
  smooth := standardCircle_contDiff.add (hγ.smul contDiff_const)
  periodic := periodic_verticalGraph hper
  injective_on_period := injOn_verticalGraph γ
  regular := fun t => velocity_verticalGraph_ne_zero
    (hγ.differentiable (by simp)).differentiableAt

/-- **Every slice of the vertical-graph isotopy is a smooth knot (VERIFIED)**:
the slice `t ↦ standardCircle t + ((1 - s) ⋅ γ t) • e₃` is the vertical graph of
the (analytic, `period`-periodic) height `(1 - s) ⋅ γ`. -/
theorem isSmoothKnot_verticalGraph_slice {γ : ℝ → ℝ} (hγ : ContDiff ℝ ⊤ γ)
    (hper : Function.Periodic γ period) (s : ℝ) :
    IsSmoothKnot (fun t : ℝ => standardCircle t + ((1 - s) * γ t) • e3) := by
  refine isSmoothKnot_verticalGraph (contDiff_const.mul hγ) ?_
  intro t
  change (1 - s) * γ (t + period) = (1 - s) * γ t
  rw [hper t]

/-! ## 3. The unknotting theorem -/

/-- **A vertical graph over the round circle is unknotted (VERIFIED)**: the
height is linearly interpolated to `0`, giving the single analytic formula
`R t s = standardCircle t + ((1 - s) ⋅ γ t) • e₃`; at `s = 0` it is the given
curve, at `s = 1` the round circle, and every slice is a smooth knot
(`isSmoothKnot_verticalGraph_slice`). -/
theorem isUnknotted_of_verticalGraph {r : ℝ → Space} {γ : ℝ → ℝ}
    (hγ : ContDiff ℝ ⊤ γ) (hper : Function.Periodic γ period)
    (hr : ∀ t : ℝ, r t = standardCircle t + (γ t) • e3) : IsUnknotted r := by
  refine ⟨fun t s => standardCircle t + ((1 - s) * γ t) • e3,
    contDiff_verticalGraphFamily hγ, ?_, ?_, ?_⟩
  · intro t
    rw [hr t]
    simp
  · intro t
    simp [standardCircle, e3]
  · intro s _
    exact isSmoothKnot_verticalGraph_slice hγ hper s

/-- **Version consuming `IsSmoothKnot r` (VERIFIED)**: if the smooth knot `r` is
a vertical graph over the round circle at analytic height `γ`, then `r` is
unknotted.  The `period`-periodicity of `γ` is *derived* from that of `r` (the
height is the third coordinate of `r`), so this is the form in which the
trisecant geometry would feed the Layer-B bridge. -/
theorem isUnknotted_of_verticalGraph_of_isSmoothKnot {r : ℝ → Space}
    (h : IsSmoothKnot r) {γ : ℝ → ℝ} (hγ : ContDiff ℝ ⊤ γ)
    (hr : ∀ t : ℝ, r t = standardCircle t + (γ t) • e3) : IsUnknotted r := by
  have hper : Function.Periodic γ period := by
    intro t
    have hh : r (t + period) = r t := h.periodic t
    have h3 : (r (t + period)).ofLp 2 = (r t).ofLp 2 := by rw [hh]
    rw [hr (t + period), hr t] at h3
    simpa [e3, standardCircle] using h3
  exact isUnknotted_of_verticalGraph hγ hper hr

/-! ## 4. Cylindrical graphs: the radius and the height both vary

The vertical-graph case (`a ≡ 1` below) is the special case of a **cylindrical
graph**: a curve of the form
`t ↦ (a t · cos t, a t · sin t, b t)`, i.e. a knot lying over the unit circle
in the `xy`-plane with radius `a t > 0` and height `b t`.  Every such curve
with analytic `period`-periodic `a`, `b` and `a > 0` is unknotted, by the
single formula
`R t s = ((1−s)·a t + s)·(cos t, sin t) + (1−s)·b t · e₃`
(interpolating the radius to `1` and the height to `0`).  This is the shape a
*star-shaped* spanning disk produces (the cone from a point of the axis). -/

/-- The first coordinate vector of `Space`. -/
def e1 : Space := !₂[(1 : ℝ), 0, 0]

/-- The second coordinate vector of `Space`. -/
def e2 : Space := !₂[(0 : ℝ), 1, 0]

/-- **Coordinate decomposition of `!₂[·,·,·]` (VERIFIED)**: any vector of
`Space` written as a triple is the corresponding combination of the three
coordinate vectors. -/
lemma vec3_decomp (X Y Z : ℝ) :
    (!₂[X, Y, Z] : Space) = X • e1 + Y • e2 + Z • e3 := by
  ext i
  fin_cases i <;> simp [e1, e2, e3]

/-- **Analyticity of a vector-valued triple (VERIFIED)**: joint analyticity of
the three coordinates gives joint analyticity of the `!₂`-valued map. -/
lemma contDiff_vec3 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f g h : X → ℝ} (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g)
    (hh : ContDiff ℝ ⊤ h) :
    ContDiff ℝ ⊤ (fun p : X => !₂[f p, g p, h p]) := by
  rw [show (fun p : X => (!₂[f p, g p, h p] : Space)) =
      fun p => (f p) • e1 + (g p) • e2 + (h p) • e3 from
    funext fun p => vec3_decomp (f p) (g p) (h p)]
  exact ((hf.smul contDiff_const).add (hg.smul contDiff_const)).add (hh.smul contDiff_const)

/-- **The cylindrical family is jointly analytic (VERIFIED)**: for analytic
`a`, `b`, the two-parameter family
`(t, s) ↦ ((1−s)·a t + s)·(cos t, sin t) + (1−s)·b t · e₃` is analytic. -/
theorem contDiff_cylGraphFamily {a b : ℝ → ℝ} (ha : ContDiff ℝ ⊤ a) (hb : ContDiff ℝ ⊤ b) :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ =>
      !₂[((1 - p.2) * a p.1 + p.2) * Real.cos p.1,
         ((1 - p.2) * a p.1 + p.2) * Real.sin p.1,
         (1 - p.2) * b p.1]) := by
  apply contDiff_vec3
  · exact (((contDiff_const.sub contDiff_snd).mul (ha.comp contDiff_fst)).add contDiff_snd).mul
      (Real.contDiff_cos.comp contDiff_fst)
  · exact (((contDiff_const.sub contDiff_snd).mul (ha.comp contDiff_fst)).add contDiff_snd).mul
      (Real.contDiff_sin.comp contDiff_fst)
  · exact (contDiff_const.sub contDiff_snd).mul (hb.comp contDiff_fst)

/-- **The cylindrical slice is everywhere regular (VERIFIED)**: for
`0 ≤ s ≤ 1`, `a t > 0` and `a` differentiable at `t`, the velocity of the
slice `u ↦ ((1−s)·a u + s)·(cos u, sin u) + z u · e₃` at `t` is nonzero — its
`xy`-part is `c'·(cos t, sin t) + c·(−sin t, cos t)` with `c = (1−s)·a t + s > 0`,
of squared norm `c'² + c² ≥ c² > 0`. -/
theorem velocity_cylGraphSlice_ne_zero {a z : ℝ → ℝ} {s t : ℝ}
    (ha : DifferentiableAt ℝ a t) (hz : DifferentiableAt ℝ z t)
    (hapos : 0 < a t) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    velocity (fun u : ℝ => !₂[((1 - s) * a u + s) * Real.cos u,
      ((1 - s) * a u + s) * Real.sin u, z u]) t ≠ 0 := by
  have hc : HasDerivAt (fun u : ℝ => (1 - s) * a u + s) ((1 - s) * deriv a t) t :=
    ((ha.hasDerivAt).const_mul (1 - s)).add_const s
  have hsc : HasDerivAt standardCircle (velocity standardCircle t) t :=
    ((standardCircle_contDiff.differentiable (by simp)).differentiableAt).hasDerivAt
  have hsmul : HasDerivAt (fun u : ℝ => ((1 - s) * a u + s) • standardCircle u)
      (((1 - s) * a t + s) • velocity standardCircle t + ((1 - s) * deriv a t) •
        standardCircle t) t := hc.smul hsc
  have hz' : HasDerivAt (fun u : ℝ => z u • e3) ((deriv z t) • e3) t :=
    (hz.hasDerivAt).smul_const e3
  have hsum : HasDerivAt
      (fun u : ℝ => ((1 - s) * a u + s) • standardCircle u + z u • e3)
      ((((1 - s) * a t + s) • velocity standardCircle t + ((1 - s) * deriv a t) •
        standardCircle t) + (deriv z t) • e3) t := hsmul.add hz'
  have hfun : (fun u : ℝ => !₂[((1 - s) * a u + s) * Real.cos u,
        ((1 - s) * a u + s) * Real.sin u, z u])
      = (fun u : ℝ => ((1 - s) * a u + s) • standardCircle u + z u • e3) := by
    funext u
    ext i
    fin_cases i <;> simp [standardCircle, e3]
  rw [velocity, hfun, hsum.deriv]
  intro hcon
  have h0 := congrArg (fun v : Space => v.ofLp 0) hcon
  have h1 := congrArg (fun v : Space => v.ofLp 1) hcon
  simp [standardCircle, e3, standardCircle_velocity] at h0 h1
  have hcpos : 0 < (1 - s) * a t + s := by
    rcases eq_or_lt_of_le hs0 with h | h
    · rw [← h]; simp; exact hapos
    · have : 0 ≤ (1 - s) * a t := mul_nonneg (by linarith) (le_of_lt hapos)
      linarith
  have key : ((1 - s) * a t + s) ^ 2 + ((1 - s) * deriv a t) ^ 2 = 0 := by
    nlinarith [h0, h1, Real.sin_sq_add_cos_sq t,
      sq_nonneg (((1 - s) * a t + s) * Real.cos t + ((1 - s) * deriv a t) * Real.sin t),
      sq_nonneg (((1 - s) * a t + s) * Real.sin t - ((1 - s) * deriv a t) * Real.cos t)]
  nlinarith [sq_nonneg ((1 - s) * deriv a t), key, hcpos]

/-- **The cylindrical slice is injective on one period (VERIFIED)**: the
`xy`-projection of the slice is the radial graph `t ↦ ((1−s)·a t + s)·(cos t, sin t)`
with positive radius, and the squared radius is the norm of the `xy`-part, so
two coincident slice points have equal radii and equal arguments modulo the
period. -/
theorem injOn_cylGraphSlice {a b : ℝ → ℝ} {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hapos : ∀ t : ℝ, 0 < a t) :
    Set.InjOn (fun t : ℝ => !₂[((1 - s) * a t + s) * Real.cos t,
      ((1 - s) * a t + s) * Real.sin t, (1 - s) * b t]) (Set.Ico (0 : ℝ) period) := by
  intro t ht t' ht' heq
  have h1 : ((1 - s) * a t + s) * Real.cos t = ((1 - s) * a t' + s) * Real.cos t' := by
    have := congrArg (fun v : Space => v.ofLp 0) heq
    simpa using this
  have h2 : ((1 - s) * a t + s) * Real.sin t = ((1 - s) * a t' + s) * Real.sin t' := by
    have := congrArg (fun v : Space => v.ofLp 1) heq
    simpa using this
  have hpos : ∀ u : ℝ, 0 < (1 - s) * a u + s := by
    intro u
    rcases eq_or_lt_of_le hs0 with h | h
    · rw [← h]; simp; exact hapos u
    · have : 0 ≤ (1 - s) * a u := mul_nonneg (by linarith) (le_of_lt (hapos u))
      linarith
  have hs1' : (((1 - s) * a t + s) * Real.cos t) ^ 2
      = (((1 - s) * a t' + s) * Real.cos t') ^ 2 := by rw [h1]
  have hs2' : (((1 - s) * a t + s) * Real.sin t) ^ 2
      = (((1 - s) * a t' + s) * Real.sin t') ^ 2 := by rw [h2]
  have hsq : ((1 - s) * a t + s) ^ 2 = ((1 - s) * a t' + s) ^ 2 := by
    nlinarith [hs1', hs2', Real.sin_sq_add_cos_sq t, Real.sin_sq_add_cos_sq t']
  have hcc : (1 - s) * a t + s = (1 - s) * a t' + s := by
    nlinarith [hpos t, hpos t', hsq]
  have hcos : Real.cos t = Real.cos t' := by
    rw [hcc] at h1
    exact mul_left_cancel₀ (ne_of_gt (hpos t')) h1
  have hsin : Real.sin t = Real.sin t' := by
    rw [hcc] at h2
    exact mul_left_cancel₀ (ne_of_gt (hpos t')) h2
  exact standardCircle_injective ht ht' (by
    ext i
    fin_cases i <;> simp [standardCircle, hcos, hsin])

/-- **Every cylindrical slice is a smooth knot (VERIFIED)**: for analytic
`period`-periodic `a`, `b` with `a > 0` and `0 ≤ s ≤ 1`, the slice
`t ↦ ((1−s)·a t + s)·(cos t, sin t) + (1−s)·b t · e₃` is a smooth knot. -/
theorem isSmoothKnot_cylGraphSlice {a b : ℝ → ℝ} (ha : ContDiff ℝ ⊤ a) (hb : ContDiff ℝ ⊤ b)
    (hapos : ∀ t : ℝ, 0 < a t) (haper : Function.Periodic a period)
    (hbper : Function.Periodic b period) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    IsSmoothKnot (fun t : ℝ => !₂[((1 - s) * a t + s) * Real.cos t,
      ((1 - s) * a t + s) * Real.sin t, (1 - s) * b t]) where
  smooth := by
    apply contDiff_vec3
    · exact ((contDiff_const.mul ha).add contDiff_const).mul Real.contDiff_cos
    · exact ((contDiff_const.mul ha).add contDiff_const).mul Real.contDiff_sin
    · exact contDiff_const.mul hb
  periodic := by
    intro t
    show (!₂[((1 - s) * a (t + period) + s) * Real.cos (t + period),
        ((1 - s) * a (t + period) + s) * Real.sin (t + period),
        (1 - s) * b (t + period)] : Space)
      = !₂[((1 - s) * a t + s) * Real.cos t, ((1 - s) * a t + s) * Real.sin t,
        (1 - s) * b t]
    rw [vec3_decomp (((1 - s) * a (t + period) + s) * Real.cos (t + period))
        (((1 - s) * a (t + period) + s) * Real.sin (t + period)) ((1 - s) * b (t + period)),
      vec3_decomp (((1 - s) * a t + s) * Real.cos t) (((1 - s) * a t + s) * Real.sin t)
        ((1 - s) * b t)]
    rw [haper t, hbper t]
    simp only [period, Real.cos_add_two_pi, Real.sin_add_two_pi]
  injective_on_period := injOn_cylGraphSlice hs0 hs1 hapos
  regular := fun t => velocity_cylGraphSlice_ne_zero
    (ha.differentiable (by simp)).differentiableAt
    ((contDiff_const.mul hb).differentiable (by simp)).differentiableAt
    (hapos t) hs0 hs1

/-- **A cylindrical graph over the round circle is unknotted (VERIFIED)**: the
single analytic formula `R t s = ((1−s)·a t + s)·(cos t, sin t) + (1−s)·b t · e₃`
interpolates the radius `a` to `1` and the height `b` to `0`; at `s = 0` it is
the given curve, at `s = 1` the round circle, and every slice is a smooth knot
(`isSmoothKnot_cylGraphSlice`). -/
theorem isUnknotted_of_cylindricalGraph {r : ℝ → Space} {a b : ℝ → ℝ}
    (ha : ContDiff ℝ ⊤ a) (hb : ContDiff ℝ ⊤ b) (hapos : ∀ t : ℝ, 0 < a t)
    (haper : Function.Periodic a period) (hbper : Function.Periodic b period)
    (hr : ∀ t : ℝ, r t = !₂[a t * Real.cos t, a t * Real.sin t, b t]) : IsUnknotted r := by
  refine ⟨fun t s => !₂[((1 - s) * a t + s) * Real.cos t,
      ((1 - s) * a t + s) * Real.sin t, (1 - s) * b t],
    contDiff_cylGraphFamily ha hb, ?_, ?_, ?_⟩
  · intro t
    show (!₂[((1 - (0 : ℝ)) * a t + 0) * Real.cos t,
      ((1 - (0 : ℝ)) * a t + 0) * Real.sin t, (1 - (0 : ℝ)) * b t] : Space) = r t
    rw [hr t]
    norm_num
  · intro t
    show (!₂[((1 - (1 : ℝ)) * a t + 1) * Real.cos t,
      ((1 - (1 : ℝ)) * a t + 1) * Real.sin t, (1 - (1 : ℝ)) * b t] : Space) = standardCircle t
    norm_num
    simp [standardCircle]
  · intro s hs
    exact isSmoothKnot_cylGraphSlice ha hb hapos haper hbper hs.1 hs.2

end LeanEval.KnotTheory.Quadrisecant
