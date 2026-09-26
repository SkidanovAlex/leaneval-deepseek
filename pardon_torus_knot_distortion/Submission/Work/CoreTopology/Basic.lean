import Mathlib
import ChallengeDeps
import Submission.Work.Core.Torus
import Submission.Work.Core.torusMap_eq_iff

/-!
# The vocabulary of a parametrised torus (Pardon's topological core)

This file sets up the objects in which the purely topological part of Pardon's
proof of the torus-knot distortion bound is stated.

* `ParamTorus` is a parametrisation `psi : ℝ → ℝ → ℝ³` of an embedded torus which
  is `2π`-periodic in each variable and injective modulo `2π`; `P.carrier` is its
  image `F ⊆ ℝ³`.
* `ParamTorus.standard` is the standard torus of revolution with major radius `2`
  and minor radius `1`, whose parametrisation is `Work.Core.torusMap`.
* `ParamTorus.meridianLoop θ` is the "small" circle `{θ = const}` (the boundary of a
  meridian disk of the solid torus bounded by `F`), and `ParamTorus.longitudeLoop φ`
  is the "big" circle `{φ = const}` around the axis.
* `ClosedCurve P` bundles a continuous `2π`-periodic curve lying in `F`.

The topological content of Pardon's proof is phrased in terms of these.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.CoreTopology

noncomputable section

/-- A parametrised embedded torus in `ℝ³`.

`psi x y` is the point of the torus with longitude parameter `x` and meridian
parameter `y`.  The parametrisation is continuous, `2π`-periodic in each variable`,
and injective modulo `2π` in each variable (this is the faithful encoding of
"embedded, with the two families of circles"). -/
structure ParamTorus where
  /-- The parametrising map. -/
  psi : ℝ → ℝ → R3
  /-- The parametrisation is continuous. -/
  cont : Continuous (Function.uncurry psi)
  /-- `2π`-periodicity in the longitude variable. -/
  per_left : ∀ x y : ℝ, psi (x + 2 * Real.pi) y = psi x y
  /-- `2π`-periodicity in the meridian variable. -/
  per_right : ∀ x y : ℝ, psi x (y + 2 * Real.pi) = psi x y
  /-- Injectivity modulo `2π` in each variable. -/
  inj_mod : ∀ x y x' y' : ℝ, psi x y = psi x' y' ↔
    (∃ k : ℤ, x = x' + k * (2 * Real.pi)) ∧ (∃ k : ℤ, y = y' + k * (2 * Real.pi))

namespace ParamTorus

variable (P : ParamTorus)

/-- The surface `F` underlying a parametrised torus: the image of the
parametrisation. -/
def carrier : Set R3 := Set.range fun p : ℝ × ℝ => P.psi p.1 p.2

theorem mem_carrier_iff (X : R3) : X ∈ P.carrier ↔ ∃ x y : ℝ, P.psi x y = X := by
  rw [carrier, Set.mem_range]
  constructor
  · rintro ⟨p, hp⟩; exact ⟨p.1, p.2, hp⟩
  · rintro ⟨x, y, hxy⟩; exact ⟨(x, y), hxy⟩

theorem psi_mem_carrier (x y : ℝ) : P.psi x y ∈ P.carrier := ⟨(x, y), rfl⟩

/-- The **meridian circle** at longitude parameter `θ`: the level set `{θ = const}`.
It is a small circle around the tube of the torus, i.e. the boundary of a meridian
disk of the solid torus that the torus bounds. -/
def meridianLoop (θ : ℝ) : ℝ → R3 := fun φ => P.psi θ φ

/-- The **longitude circle** at meridian parameter `φ`: the level set `{φ = const}`.
It is a circle going around the axis of the torus. -/
def longitudeLoop (φ : ℝ) : ℝ → R3 := fun θ => P.psi θ φ

theorem meridianLoop_apply (θ φ : ℝ) : P.meridianLoop θ φ = P.psi θ φ := rfl

theorem longitudeLoop_apply (θ φ : ℝ) : P.longitudeLoop φ θ = P.psi θ φ := rfl

theorem meridianLoop_periodic (θ φ : ℝ) :
    P.meridianLoop θ (φ + 2 * Real.pi) = P.meridianLoop θ φ :=
  P.per_right θ φ

theorem longitudeLoop_periodic (φ θ : ℝ) :
    P.longitudeLoop φ (θ + 2 * Real.pi) = P.longitudeLoop φ θ :=
  P.per_left θ φ

theorem meridianLoop_cont (θ : ℝ) : Continuous (P.meridianLoop θ) :=
  P.cont.comp (continuous_const.prodMk continuous_id)

theorem longitudeLoop_cont (φ : ℝ) : Continuous (P.longitudeLoop φ) :=
  P.cont.comp (continuous_id.prodMk continuous_const)

theorem meridianLoop_mem_carrier (θ φ : ℝ) : P.meridianLoop θ φ ∈ P.carrier :=
  P.psi_mem_carrier θ φ

theorem longitudeLoop_mem_carrier (φ θ : ℝ) : P.longitudeLoop φ θ ∈ P.carrier :=
  P.psi_mem_carrier θ φ

/-- Two parameters give the same point of the torus exactly when they agree
modulo `2π` in each coordinate. -/
theorem psi_eq_iff (x y x' y' : ℝ) : P.psi x y = P.psi x' y' ↔
    (∃ k : ℤ, x = x' + k * (2 * Real.pi)) ∧ (∃ k : ℤ, y = y' + k * (2 * Real.pi)) :=
  P.inj_mod x y x' y'

theorem psi_congr_left {x x' y y' : ℝ} (h : ∃ k : ℤ, x = x' + k * (2 * Real.pi))
    (hy : y = y') : P.psi x y = P.psi x' y' :=
  (P.psi_eq_iff x y x' y').mpr ⟨h, ⟨0, by simp [hy]⟩⟩

theorem psi_congr_right {x x' y y' : ℝ} (hx : x = x')
    (h : ∃ k : ℤ, y = y' + k * (2 * Real.pi)) : P.psi x y = P.psi x' y' :=
  (P.psi_eq_iff x y x' y').mpr ⟨⟨0, by simp [hx]⟩, h⟩

end ParamTorus

/-- `Work.Core.torusMap`, as a function of the two parameters, is continuous. -/
theorem torusMap_continuous : Continuous (fun p : ℝ × ℝ => Work.Core.torusMap p.1 p.2) := by
  have h : Continuous (fun p : ℝ × ℝ => fun i : Fin 3 =>
      (if i.val = 0 then (2 + Real.cos p.2) * Real.cos p.1
       else if i.val = 1 then (2 + Real.cos p.2) * Real.sin p.1
       else Real.sin p.2 : ℝ)) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp h

/-- The standard parametrisation restricted to a straight line of parameters is
continuous (used for the standard `(p,q)` curve). -/
theorem torusMap_continuous_linear (a b : ℝ) :
    Continuous (fun t : ℝ => Work.Core.torusMap (a * t) (b * t)) := by
  have h : Continuous (fun t : ℝ => fun i : Fin 3 =>
      (if i.val = 0 then (2 + Real.cos (b * t)) * Real.cos (a * t)
       else if i.val = 1 then (2 + Real.cos (b * t)) * Real.sin (a * t)
       else Real.sin (b * t) : ℝ)) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp h

/-- The standard torus of revolution with major radius `2` and minor radius `1`. -/
def standard : ParamTorus where
  psi := Work.Core.torusMap
  cont := torusMap_continuous
  per_left := Work.Core.torusMap_add_two_pi_left
  per_right := Work.Core.torusMap_add_two_pi_right
  inj_mod := Work.Core.torusMap_eq_iff

@[simp] theorem standard_psi (x y : ℝ) :
    standard.psi x y = Work.Core.torusMap x y := rfl

theorem standard_carrier :
    standard.carrier = Set.range (fun p : ℝ × ℝ => Work.Core.torusMap p.1 p.2) := rfl

theorem standard_meridianLoop (θ : ℝ) :
    standard.meridianLoop θ = Work.Core.meridianCircle θ := rfl

theorem standard_longitudeLoop (φ : ℝ) :
    standard.longitudeLoop φ = Work.Core.longitudeCircle φ := rfl

/-- A continuous `2π`-periodic curve lying in the torus surface `F = P.carrier`. -/
structure ClosedCurve (P : ParamTorus) where
  /-- The parametrising map of the curve. -/
  γ : ℝ → R3
  /-- The curve is continuous. -/
  cont : Continuous γ
  /-- The curve is `2π`-periodic. -/
  periodic : ∀ t : ℝ, γ (t + 2 * Real.pi) = γ t
  /-- The curve lies in the torus surface. -/
  mem : ∀ t : ℝ, γ t ∈ P.carrier

namespace ClosedCurve

variable {P : ParamTorus}

instance : CoeFun (ClosedCurve P) (fun _ => ℝ → R3) := ⟨ClosedCurve.γ⟩

theorem range_subset_carrier (γ : ClosedCurve P) : Set.range γ ⊆ P.carrier :=
  fun _ ⟨t, ht⟩ => ht ▸ γ.mem t

theorem mapsTo (γ : ClosedCurve P) : Set.MapsTo γ Set.univ P.carrier :=
  fun t _ => γ.mem t

/-- A closed curve is determined by its underlying function. -/
@[ext] theorem ext {γ₁ γ₂ : ClosedCurve P} (h : γ₁.γ = γ₂.γ) : γ₁ = γ₂ := by
  cases γ₁; cases γ₂; simp_all

end ClosedCurve

/-- The meridian circle as a `ClosedCurve`. -/
def meridianCurve (P : ParamTorus) (θ : ℝ) : ClosedCurve P where
  γ := P.meridianLoop θ
  cont := P.meridianLoop_cont θ
  periodic := P.meridianLoop_periodic θ
  mem := fun φ => P.meridianLoop_mem_carrier θ φ

/-- The longitude circle as a `ClosedCurve`. -/
def longitudeCurve (P : ParamTorus) (φ : ℝ) : ClosedCurve P where
  γ := P.longitudeLoop φ
  cont := P.longitudeLoop_cont φ
  periodic := P.longitudeLoop_periodic φ
  mem := fun θ => P.longitudeLoop_mem_carrier φ θ

@[simp] theorem meridianCurve_apply (P : ParamTorus) (θ φ : ℝ) :
    meridianCurve P θ φ = P.psi θ φ := rfl

@[simp] theorem longitudeCurve_apply (P : ParamTorus) (φ θ : ℝ) :
    longitudeCurve P φ θ = P.psi θ φ := rfl

end

end Work.CoreTopology
