import Mathlib
import ChallengeDeps

/-!
# The vocabulary of the smooth Jordan–Schoenflies chapter

This file fixes the objects in which the smooth separation theory of simple closed curves is
stated.  Throughout, a *closed curve in the plane* is a continuous, `2π`-periodic map
`γ : ℝ → ℂ` (equivalently a continuous map `ℝ/2πℤ → ℂ`), and a *smooth* closed curve is a `C¹`
one.  This is the same convention as the sibling chapters `Work.CoreTopology` (whose
`ClosedCurve P` is a `2π`-periodic curve on a parametrised torus) and
`Work.Topology.Classical` (whose `IsJordanCurveOn A c` is a `2π`-periodic injection into a subset
`A ⊆ ℝ³`); the bridges to those chapters are in `Work.Smooth.Jordan.Bridge`.

## Main definitions

* `Disc` — the model closed 2-disc `𝔻 = Metric.closedBall (0 : ℂ) 1`;
* `circlePoint θ = e^{iθ}` — the standard parametrisation of its boundary;
* `PlaneCurve` — a continuous `2π`-periodic `γ : ℝ → ℂ`, with image `PlaneCurve.trace`;
* `PlaneCurve.IsSimple` — injectivity on one period `[0, 2π)`;
* `SmoothPlaneCurve` — a `C¹` `PlaneCurve`;
* `SmoothPlaneCurve.IsImmersion` — non-vanishing derivative (`γ` is an immersed curve);
* `IsSimpleClosedCurveOn A c` — a simple closed curve in a subset `A ⊆ ℝ³` (this is exactly the
  `IsJordanCurveOn` of `Work.Topology.Classical`);
* `IsEmbeddedCircle A K` — a compact 1-dimensional submanifold of `A ⊆ ℝ³` presented as the image
  of a simple closed curve: **this is how the compact 1-manifolds of the application (the
  components of `∂PBox ∩ F`) enter the chapter**;
* `IsSpanningDisc`, `IsSpanningDiscOn A` — `e : 𝔻 → ℂ` (resp. `𝔻 → ℝ³` with image in `A`) is an
  embedding whose boundary circle maps to the curve.
-/

open Set
open LeanEval.KnotTheory.PardonDistortion

namespace Work.Smooth.Jordan

noncomputable section

/-! ## The model disc and its boundary circle -/

/-- The model closed `2`-disc `𝔻 = {z : ℂ | ‖z‖ ≤ 1}`. -/
abbrev Disc : Type := Metric.closedBall (0 : ℂ) 1

/-- The unit circle `S¹ = {z : ℂ | ‖z‖ = 1}`, as a type. -/
abbrev Circ : Type := Metric.sphere (0 : ℂ) 1

/-- The boundary point `e^{iθ}`, as an element of the disc `𝔻`. -/
def circlePoint (θ : ℝ) : Disc :=
  ⟨Complex.exp (θ * Complex.I), by
    rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_exp_ofReal_mul_I]⟩

@[simp] theorem circlePoint_coe (θ : ℝ) :
    ((circlePoint θ : Disc) : ℂ) = Complex.exp (θ * Complex.I) := rfl

theorem two_pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity

theorem two_pi_ne_zero : (2 * Real.pi : ℝ) ≠ 0 := by positivity

theorem two_pi_I_ne_zero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  simp [Complex.I_ne_zero, Real.pi_ne_zero]

/-- **Polar coordinates on the boundary circle**: every point of the unit sphere of `ℂ` is
`circlePoint θ` for some `θ`. -/
theorem exists_circlePoint_eq (z : Disc) (hz : ‖(z : ℂ)‖ = 1) : ∃ θ : ℝ, circlePoint θ = z := by
  refine ⟨Complex.arg (z : ℂ), Subtype.ext ?_⟩
  have hz' : ((‖(z : ℂ)‖ : ℝ) : ℂ) = 1 := by rw [hz]; norm_num
  have h := Complex.norm_mul_exp_arg_mul_I (z : ℂ)
  rw [hz', one_mul] at h
  rw [circlePoint_coe]
  exact h

/-! ## Closed curves and smooth closed curves in the plane -/

/-- A **closed curve in the plane**: a continuous `2π`-periodic map `ℝ → ℂ`. -/
structure PlaneCurve where
  /-- the parametrisation -/
  γ : ℝ → ℂ
  /-- it is continuous -/
  cont : Continuous γ
  /-- it is `2π`-periodic -/
  periodic : Function.Periodic γ (2 * Real.pi)

/-- A **`C¹` closed curve in the plane**. -/
structure SmoothPlaneCurve extends PlaneCurve where
  /-- it is continuously differentiable -/
  contDiff : ContDiff ℝ 1 γ

namespace PlaneCurve

instance : CoeFun PlaneCurve (fun _ => ℝ → ℂ) := ⟨fun c => c.γ⟩

variable (c : PlaneCurve)

theorem periodic_apply (t : ℝ) : c (t + 2 * Real.pi) = c t := c.periodic t

/-- The image (trace) of the curve. -/
def trace : Set ℂ := Set.range c.γ

theorem mem_trace_iff (x : ℂ) : x ∈ c.trace ↔ ∃ t : ℝ, c t = x := Iff.rfl

theorem mem_trace (t : ℝ) : c t ∈ c.trace := ⟨t, rfl⟩

theorem trace_eq_image_Icc : c.trace = c.γ '' Set.Icc (0 : ℝ) (2 * Real.pi) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨t, rfl⟩
    set n : ℤ := ⌊t / (2 * Real.pi)⌋ with hn
    refine ⟨t - (n : ℝ) * (2 * Real.pi), ⟨?_, ?_⟩, ?_⟩
    · have hpos : (0 : ℝ) < 2 * Real.pi := two_pi_pos
      have := (le_div_iff₀ hpos).mp (Int.floor_le (t / (2 * Real.pi)))
      linarith
    · have hpos : (0 : ℝ) < 2 * Real.pi := two_pi_pos
      have := (div_lt_iff₀ hpos).mp (Int.lt_floor_add_one (t / (2 * Real.pi)))
      linarith
    · have hper : Function.Periodic c.γ (2 * Real.pi) := c.periodic
      have := hper.int_mul n (t - (n : ℝ) * (2 * Real.pi))
      rw [show t - (n : ℝ) * (2 * Real.pi) + (n : ℝ) * (2 * Real.pi) = t from by ring] at this
      exact this.symm
  · rintro _ ⟨t, _, rfl⟩
    exact ⟨t, rfl⟩

theorem trace_eq_image_Ico : c.trace = c.γ '' Set.Ico (0 : ℝ) (2 * Real.pi) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨t, rfl⟩
    set n : ℤ := ⌊t / (2 * Real.pi)⌋ with hn
    refine ⟨t - (n : ℝ) * (2 * Real.pi), ⟨?_, ?_⟩, ?_⟩
    · have hpos : (0 : ℝ) < 2 * Real.pi := two_pi_pos
      have := (le_div_iff₀ hpos).mp (Int.floor_le (t / (2 * Real.pi)))
      linarith
    · have hpos : (0 : ℝ) < 2 * Real.pi := two_pi_pos
      have := (div_lt_iff₀ hpos).mp (Int.lt_floor_add_one (t / (2 * Real.pi)))
      linarith
    · have hper : Function.Periodic c.γ (2 * Real.pi) := c.periodic
      have := hper.int_mul n (t - (n : ℝ) * (2 * Real.pi))
      rw [show t - (n : ℝ) * (2 * Real.pi) + (n : ℝ) * (2 * Real.pi) = t from by ring] at this
      exact this.symm
  · rintro _ ⟨t, _, rfl⟩
    exact ⟨t, rfl⟩

theorem isCompact_trace : IsCompact c.trace := by
  rw [trace_eq_image_Icc]
  exact isCompact_Icc.image c.cont

theorem isClosed_trace : IsClosed c.trace := c.isCompact_trace.isClosed

theorem isOpen_compl_trace : IsOpen c.traceᶜ := c.isClosed_trace.isOpen_compl

/-- A closed curve is **simple** if it is injective on one period `[0, 2π)`. -/
def IsSimple : Prop := Set.InjOn c.γ (Set.Ico 0 (2 * Real.pi))

/-- The image of the `2π`-periodic curve is invariant under integer shifts of the parameter. -/
theorem apply_add_int_mul (t : ℝ) (k : ℤ) : c (t + (k : ℝ) * (2 * Real.pi)) = c t :=
  c.periodic.int_mul k t

end PlaneCurve

namespace SmoothPlaneCurve

instance : CoeFun SmoothPlaneCurve (fun _ => ℝ → ℂ) := ⟨fun c => c.γ⟩

variable (c : SmoothPlaneCurve)

theorem differentiable : Differentiable ℝ c.γ := c.contDiff.differentiable (by norm_num)

theorem continuous_deriv : Continuous (deriv c.γ) :=
  c.contDiff.continuous_deriv le_rfl

/-- `γ` is an **immersion**: its derivative never vanishes. -/
def IsImmersion : Prop := ∀ t : ℝ, deriv c.γ t ≠ 0

end SmoothPlaneCurve

/-! ## Curves in `ℝ³` and compact `1`-manifolds -/

/-- A **simple closed curve in a subset `A ⊆ ℝ³`**: a continuous `2π`-periodic injection into `A`.
This is definitionally the `IsJordanCurveOn A c` of `Work.Topology.Classical`, and is the shape of
curve for which the separation theorems are stated. -/
def IsSimpleClosedCurveOn (A : Set R3) (c : ℝ → R3) : Prop :=
  (∀ t : ℝ, c t ∈ A) ∧ Continuous c ∧ Function.Periodic c (2 * Real.pi) ∧
    Set.InjOn c (Set.Ico 0 (2 * Real.pi))

/-- A **compact `1`-dimensional submanifold of `A ⊆ ℝ³`**, presented as the trace of a simple
closed curve.  The curves of Pardon's application — the components of `S ∩ F`, where `S` is the
boundary of a convex body and `F` a smoothly embedded torus — are of this shape: a compact
`1`-manifold is a finite disjoint union of circles, so its components are the traces of simple
closed curves. -/
def IsEmbeddedCircle (A : Set R3) (K : Set R3) : Prop :=
  K ⊆ A ∧ ∃ c : ℝ → R3, IsSimpleClosedCurveOn A c ∧ Set.range c = K

/-! ## Spanning discs -/

/-- `e : 𝔻 → ℂ` presents the plane curve `c` as the **boundary of an embedded disc**: `e` is
injective and its boundary circle maps to `c`. -/
def IsSpanningDisc (c : PlaneCurve) (e : C(Disc, ℂ)) : Prop :=
  Function.Injective e ∧ ∀ θ : ℝ, e (circlePoint θ) = c.γ θ

/-- The plane curve `c` bounds an embedded disc. -/
def BoundsDisc (c : PlaneCurve) : Prop := ∃ e : C(Disc, ℂ), IsSpanningDisc c e

/-- `e : 𝔻 → ℝ³` presents the curve `c` as the **boundary of an embedded disc contained in
`A`**. -/
def IsSpanningDiscOn (A : Set R3) (c : ℝ → R3) (e : C(Disc, R3)) : Prop :=
  Function.Injective e ∧ (∀ θ : ℝ, e (circlePoint θ) = c θ) ∧ (∀ z : Disc, e z ∈ A)

/-- The **interior** of the image of a spanning disc: the image of the open disc. -/
def openDisc (e : C(Disc, R3)) : Set R3 := e '' {z : Disc | ‖(z : ℂ)‖ < 1}

theorem openDisc_def (e : C(Disc, R3)) :
    openDisc e = e '' {z : Disc | ‖(z : ℂ)‖ < 1} := rfl

end

end Work.Smooth.Jordan
