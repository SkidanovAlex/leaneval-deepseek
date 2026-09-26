import Mathlib
import Submission.Work.Core.Torus

/-!
# The covering-space / winding-number machinery of a parametrised torus

A *parametrised torus* is a map `psi : ℝ → ℝ → R3` (equivalently `ℝ × ℝ → R3`) which

(i)   is `2π`-periodic in each variable,
(ii)  is injective modulo `2π`: `psi x y = psi x' y'` iff `x - x'` and `y - y'` are integer
      multiples of `2π`,
(iii) is an immersion with a uniform positive lower bound `c > 0` for its derivative
      (`c * ‖u‖ ≤ ‖fderiv ℝ (psiMap psi) p u‖` for all `p` and `u`).

The intended instances are `psi = torusMap` (the standard torus of revolution) and
`psi = fun x y => Φ.Hinv 1 (torusMap x y)` for an ambient isotopy `Φ`.

This file sets up the vocabulary:

* `psiMap psi : ℝ × ℝ → R3` and `psiMapToRange psi`, the same map viewed as a map onto
  its range (the base of the covering `ℝ² → range psi`);
* `lattice`, the period lattice `2πℤ² ⊂ ℝ × ℝ`, with `periodShift v` its element attached to
  `v : ℤ × ℤ`, together with the basic metric facts (`lattice_norm_ge`, `isDiscrete_lattice`);
* `IsLift`, `IsPeriodicLift`, `HasWinding`: a lift of a closed curve in the parameter plane,
  a lift whose period shift is a given winding vector, and the winding vector itself;
* `TorusParam`, the bundled hypotheses (i)-(iii) together with `C¹` regularity (which is
  what turns the pointwise bound (iii) into a *uniform* two-point bound, see
  `Work.TorusCover.Cometric`);
* `curveLength`, the total variation of a curve over an interval.

The winding vector of a closed curve in the range of `psi` is defined in
`Work.TorusCover.Lift`; the extrinsic systole bound in `Work.TorusCover.Systole`.

## Conventions

* The parameter plane `ℝ × ℝ` carries the product norm `‖(x,y)‖ = max ‖x‖ ‖y‖`, so the
  period displacement `periodShift v` has norm `2π * max |v.1| |v.2|`, which is `≥ 2π`
  for `v ≠ 0` (`two_pi_le_norm_periodShift`).
* Curves are functions `ℝ → R3`; they are *closed* when `γ (t + 2π) = γ t`.
-/

open LeanEval.KnotTheory.PardonDistortion Set
open scoped ENNReal

namespace Work.TorusCover

noncomputable section

/-! ### The parametrisation and its period lattice -/

/-- The map `ℝ × ℝ → R3` underlying a parametrised torus `psi : ℝ → ℝ → R3`. -/
def psiMap (psi : ℝ → ℝ → R3) : ℝ × ℝ → R3 := fun p => psi p.1 p.2

@[simp] lemma psiMap_apply (psi : ℝ → ℝ → R3) (p : ℝ × ℝ) :
    psiMap psi p = psi p.1 p.2 := rfl

/-- The parametrised torus, viewed as a map onto its range (the base of the covering
`ℝ² → range psi`). -/
def psiMapToRange (psi : ℝ → ℝ → R3) : ℝ × ℝ → Set.range (psiMap psi) :=
  Set.rangeFactorization (psiMap psi)

@[simp] lemma psiMapToRange_coe (psi : ℝ → ℝ → R3) (p : ℝ × ℝ) :
    ((psiMapToRange psi p : Set.range (psiMap psi)) : R3) = psi p.1 p.2 := rfl

@[simp] lemma psiMapToRange_apply (psi : ℝ → ℝ → R3) (p : ℝ × ℝ) :
    psiMapToRange psi p = ⟨psiMap psi p, Set.mem_range_self p⟩ := rfl

/-- The period shift attached to a winding vector `v : ℤ × ℤ`. -/
def periodShift (v : ℤ × ℤ) : ℝ × ℝ :=
  ((v.1 : ℝ) * (2 * Real.pi), (v.2 : ℝ) * (2 * Real.pi))

/-- The period shift as an additive homomorphism `ℤ × ℤ → ℝ × ℝ`. -/
def latticeHom : ℤ × ℤ →+ ℝ × ℝ where
  toFun := periodShift
  map_zero' := by simp [periodShift]
  map_add' := by intro a b; ext <;> simp [periodShift] <;> ring

/-- The period lattice `2πℤ²` of the parameter plane, as an additive subgroup of `ℝ × ℝ`. -/
def lattice : AddSubgroup (ℝ × ℝ) := latticeHom.range

/-- Membership in the period lattice. -/
lemma mem_lattice_iff (p : ℝ × ℝ) :
    p ∈ lattice ↔ ∃ v : ℤ × ℤ, periodShift v = p := by
  rw [lattice, AddMonoidHom.mem_range]
  exact ⟨fun ⟨v, h⟩ => ⟨v, by simpa [latticeHom] using h⟩,
    fun ⟨v, h⟩ => ⟨v, by simpa [latticeHom] using h⟩⟩

/-- Membership in the period lattice, in coordinates. -/
lemma mem_lattice_iff' (p : ℝ × ℝ) :
    p ∈ lattice ↔ ∃ k l : ℤ, p = ((k : ℝ) * (2 * Real.pi), (l : ℝ) * (2 * Real.pi)) := by
  rw [mem_lattice_iff]
  constructor
  · rintro ⟨v, hv⟩; exact ⟨v.1, v.2, hv.symm⟩
  · rintro ⟨k, l, h⟩; exact ⟨(k, l), h.symm⟩

@[simp] lemma periodShift_mem_lattice (v : ℤ × ℤ) : periodShift v ∈ lattice :=
  (mem_lattice_iff _).mpr ⟨v, rfl⟩

lemma exists_periodShift_eq_iff (p : ℝ × ℝ) :
    (∃ v : ℤ × ℤ, periodShift v = p) ↔ p ∈ lattice :=
  (mem_lattice_iff p).symm

@[simp] lemma periodShift_zero : periodShift 0 = 0 := by
  simp [periodShift]

lemma periodShift_injective : Function.Injective periodShift := by
  intro v w h
  have h1 : (v.1 : ℝ) * (2 * Real.pi) = (w.1 : ℝ) * (2 * Real.pi) := by
    simpa [periodShift] using congrArg Prod.fst h
  have h2 : (v.2 : ℝ) * (2 * Real.pi) = (w.2 : ℝ) * (2 * Real.pi) := by
    simpa [periodShift] using congrArg Prod.snd h
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  refine Prod.ext ?_ ?_
  · exact Int.cast_injective (mul_right_cancel₀ hp h1)
  · exact Int.cast_injective (mul_right_cancel₀ hp h2)

lemma periodShift_eq_zero_iff {v : ℤ × ℤ} : periodShift v = 0 ↔ v = 0 := by
  rw [← periodShift_zero]
  exact ⟨fun h => periodShift_injective h, fun h => by rw [h]⟩

/-- The norm of a period shift is `2π` times the sup-norm of the integer vector. -/
lemma norm_periodShift (v : ℤ × ℤ) :
    ‖periodShift v‖ = 2 * Real.pi * max |(v.1 : ℝ)| |(v.2 : ℝ)| := by
  have h2 : (0 : ℝ) < 2 * Real.pi := by positivity
  have key : ‖periodShift v‖ =
      max (|(v.1 : ℝ)| * (2 * Real.pi)) (|(v.2 : ℝ)| * (2 * Real.pi)) := by
    simp only [periodShift, Prod.norm_def, Real.norm_eq_abs, abs_mul, abs_of_pos h2]
  rw [key, ← max_mul_of_nonneg _ _ (le_of_lt h2)]
  ring

/-- A nonzero winding vector gives a period displacement of norm at least `2π`. -/
lemma two_pi_le_norm_periodShift {v : ℤ × ℤ} (hv : v ≠ 0) :
    2 * Real.pi ≤ ‖periodShift v‖ := by
  rw [norm_periodShift]
  have hmax : (1 : ℝ) ≤ max |(v.1 : ℝ)| |(v.2 : ℝ)| := by
    rcases eq_or_ne v.1 0 with h1 | h1
    · have h2 : v.2 ≠ 0 := fun h2 => hv (Prod.ext h1 h2)
      have h3 : (1 : ℤ) ≤ |v.2| := by
        have : (0 : ℤ) < |v.2| := abs_pos.mpr h2
        omega
      have h3' : (1 : ℝ) ≤ |((v.2 : ℤ) : ℝ)| := by exact_mod_cast h3
      exact le_trans h3' (le_max_right _ _)
    · have h3 : (1 : ℤ) ≤ |v.1| := by
        have : (0 : ℤ) < |v.1| := abs_pos.mpr h1
        omega
      have h3' : (1 : ℝ) ≤ |((v.1 : ℤ) : ℝ)| := by exact_mod_cast h3
      exact le_trans h3' (le_max_left _ _)
  nlinarith [Real.pi_pos, hmax]

/-- A nonzero element of the period lattice has norm at least `2π`. -/
lemma lattice_norm_ge {p : ℝ × ℝ} (hp : p ∈ lattice) (h0 : p ≠ 0) :
    2 * Real.pi ≤ ‖p‖ := by
  obtain ⟨v, rfl⟩ := (mem_lattice_iff p).mp hp
  have hv : v ≠ 0 := by
    rintro rfl
    exact h0 (by simp)
  exact two_pi_le_norm_periodShift hv

/-- The period lattice is discrete (its points are `2π` apart). -/
lemma isDiscrete_lattice : IsDiscrete (lattice : Set (ℝ × ℝ)) := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  intro p hp
  refine ⟨Metric.ball p Real.pi, Metric.isOpen_ball, ?_⟩
  ext q
  rw [Set.mem_inter_iff, Set.mem_singleton_iff, Metric.mem_ball, dist_eq_norm]
  constructor
  · rintro ⟨hdist, hq⟩
    by_contra hne
    have hdiff : q - p ∈ lattice := lattice.sub_mem hq hp
    have hne0 : q - p ≠ 0 := sub_ne_zero.mpr hne
    have hge := lattice_norm_ge hdiff hne0
    linarith [Real.pi_pos]
  · rintro rfl
    exact ⟨by simpa using Real.pi_pos, hp⟩

/-! ### Lifts and winding vectors -/

/-- `Λ` is a lift of the curve `γ` through the parametrised torus `psi`. -/
def IsLift (psi : ℝ → ℝ → R3) (γ : ℝ → R3) (Λ : ℝ → ℝ × ℝ) : Prop :=
  Continuous Λ ∧ ∀ t, psi (Λ t).1 (Λ t).2 = γ t

/-- A lift which is shifted by `periodShift v` when the parameter advances by one period;
`v` is then the winding vector of `γ`. -/
def IsPeriodicLift (psi : ℝ → ℝ → R3) (γ : ℝ → R3) (v : ℤ × ℤ) (Λ : ℝ → ℝ × ℝ) : Prop :=
  IsLift psi γ Λ ∧ ∀ t, Λ (t + 2 * Real.pi) = Λ t + periodShift v

/-- The curve `γ` has winding vector `v` with respect to the parametrised torus `psi`:
it admits a lift which advances by `periodShift v` over one period. -/
def HasWinding (psi : ℝ → ℝ → R3) (γ : ℝ → R3) (v : ℤ × ℤ) : Prop :=
  ∃ Λ, IsPeriodicLift psi γ v Λ

/-- A curve which is continuous and closed (periodic with period `2π`). -/
def IsClosedCurve (γ : ℝ → R3) : Prop :=
  Continuous γ ∧ ∀ t, γ (t + 2 * Real.pi) = γ t

/-- A curve has nonzero winding vector with respect to `psi`: it is *essential*
(it represents a nonzero class in `π₁` of the range of `psi`). -/
def IsEssential (psi : ℝ → ℝ → R3) (γ : ℝ → R3) : Prop :=
  ∃ v : ℤ × ℤ, v ≠ 0 ∧ HasWinding psi γ v

/-- Two closed curves with values in the range of `psi` are *homotopic through closed curves in
the range of `psi`*: there is a continuous homotopy `H` between them, all of whose level curves
`H s` are `2π`-periodic and take values in the range of `psi`. -/
def HomotopicClosed (psi : ℝ → ℝ → R3) (γ₀ γ₁ : ℝ → R3) : Prop :=
  ∃ H : ℝ × ℝ → R3, Continuous H ∧ (∀ t, H (0, t) = γ₀ t) ∧ (∀ t, H (1, t) = γ₁ t) ∧
    (∀ s t, H (s, t + 2 * Real.pi) = H (s, t)) ∧
    (∀ s t, H (s, t) ∈ Set.range (psiMap psi))

lemma IsPeriodicLift.isLift {psi : ℝ → ℝ → R3} {γ : ℝ → R3} {v : ℤ × ℤ} {Λ : ℝ → ℝ × ℝ}
    (h : IsPeriodicLift psi γ v Λ) : IsLift psi γ Λ := h.1

lemma IsPeriodicLift.continuous {psi : ℝ → ℝ → R3} {γ : ℝ → R3} {v : ℤ × ℤ} {Λ : ℝ → ℝ × ℝ}
    (h : IsPeriodicLift psi γ v Λ) : Continuous Λ := h.1.1

lemma IsPeriodicLift.map_eq {psi : ℝ → ℝ → R3} {γ : ℝ → R3} {v : ℤ × ℤ} {Λ : ℝ → ℝ × ℝ}
    (h : IsPeriodicLift psi γ v Λ) (t : ℝ) : psi (Λ t).1 (Λ t).2 = γ t := h.1.2 t

lemma IsPeriodicLift.shift {psi : ℝ → ℝ → R3} {γ : ℝ → R3} {v : ℤ × ℤ} {Λ : ℝ → ℝ × ℝ}
    (h : IsPeriodicLift psi γ v Λ) (t : ℝ) :
    Λ (t + 2 * Real.pi) = Λ t + periodShift v := h.2 t

/-- The displacement of a periodic lift over one period. -/
lemma IsPeriodicLift.displacement {psi : ℝ → ℝ → R3} {γ : ℝ → R3} {v : ℤ × ℤ}
    {Λ : ℝ → ℝ × ℝ} (h : IsPeriodicLift psi γ v Λ) :
    Λ (2 * Real.pi) = Λ 0 + periodShift v := by
  simpa using h.shift 0

/-- The displacement of a periodic lift over one period has norm at least `2π` when the
winding vector is nonzero. -/
lemma IsPeriodicLift.two_pi_le_norm_displacement {psi : ℝ → ℝ → R3} {γ : ℝ → R3}
    {v : ℤ × ℤ} {Λ : ℝ → ℝ × ℝ} (h : IsPeriodicLift psi γ v Λ) (hv : v ≠ 0) :
    2 * Real.pi ≤ ‖Λ (2 * Real.pi) - Λ 0‖ := by
  rw [h.displacement, add_sub_cancel_left]
  exact two_pi_le_norm_periodShift hv

/-! ### The bundled hypotheses -/

/-- The bundled hypotheses on a parametrised torus.  Besides periodicity (i), injectivity
modulo `2π` (ii) and the uniform lower bound for the derivative (iii), we record `C¹`
regularity of `psiMap psi`: it is what makes the *pointwise* bound (iii) uniform
(see `Work.TorusCover.Cometric`), which the extrinsic systole bound needs.
All intended instances (the standard torus, and the image of the standard torus under a
diffeomorphism of `ℝ³`) are smooth. -/
structure TorusParam where
  /-- the parametrisation -/
  psi : ℝ → ℝ → R3
  /-- (i) periodicity in the first variable -/
  periodic_fst : ∀ x y, psi (x + 2 * Real.pi) y = psi x y
  /-- (i) periodicity in the second variable -/
  periodic_snd : ∀ x y, psi x (y + 2 * Real.pi) = psi x y
  /-- (ii) injectivity modulo `2π` -/
  inj_mod : ∀ x y x' y', psi x y = psi x' y' ↔
    (∃ k : ℤ, x = x' + k * (2 * Real.pi)) ∧ (∃ k : ℤ, y = y' + k * (2 * Real.pi))
  /-- the constant of (iii) -/
  c : ℝ
  c_pos : 0 < c
  /-- (iii) uniform lower bound for the derivative of `psiMap` -/
  deriv_lower : ∀ x y (u : ℝ × ℝ), c * ‖u‖ ≤ ‖fderiv ℝ (psiMap psi) (x, y) u‖
  /-- `C¹` regularity -/
  contDiff : ContDiff ℝ (1 : ℕ∞) (psiMap psi)

namespace TorusParam

variable (P : TorusParam)

/-- Periodicity in the first variable, for integer multiples. -/
lemma psi_periodic_int_fst (x y : ℝ) (k : ℤ) :
    P.psi (x + k * (2 * Real.pi)) y = P.psi x y := by
  have hper : Function.Periodic (fun x => P.psi x y) (2 * Real.pi) :=
    fun x => P.periodic_fst x y
  simpa using hper.int_mul k x

/-- Periodicity in the second variable, for integer multiples. -/
lemma psi_periodic_int_snd (x y : ℝ) (k : ℤ) :
    P.psi x (y + k * (2 * Real.pi)) = P.psi x y := by
  have hper : Function.Periodic (fun y => P.psi x y) (2 * Real.pi) :=
    fun y => P.periodic_snd x y
  simpa using hper.int_mul k y

/-- The parametrisation is invariant under the period lattice. -/
lemma psiMap_add_lattice (p q : ℝ × ℝ) (hq : q ∈ lattice) :
    psiMap P.psi (p + q) = psiMap P.psi p := by
  obtain ⟨k, l, rfl⟩ := (mem_lattice_iff' q).mp hq
  simp only [psiMap_apply, Prod.fst_add, Prod.snd_add]
  rw [P.psi_periodic_int_snd (p.1 + (k : ℝ) * (2 * Real.pi)) p.2 l,
    P.psi_periodic_int_fst p.1 p.2 k]

/-- The parametrisation is invariant under a period shift. -/
@[simp] lemma psiMap_add_periodShift (p : ℝ × ℝ) (v : ℤ × ℤ) :
    psiMap P.psi (p + periodShift v) = psiMap P.psi p :=
  P.psiMap_add_lattice p (periodShift v) (periodShift_mem_lattice v)

/-- Two parameter points have the same image under `psi` exactly when they differ by a
period-lattice element: hypothesis (ii) in the form used throughout. -/
lemma psiMap_eq_iff {p q : ℝ × ℝ} : psiMap P.psi p = psiMap P.psi q ↔ p - q ∈ lattice := by
  rw [psiMap_apply, psiMap_apply, P.inj_mod p.1 p.2 q.1 q.2, mem_lattice_iff']
  constructor
  · rintro ⟨⟨k, hk⟩, ⟨l, hl⟩⟩
    refine ⟨k, l, ?_⟩
    have h1 : p.1 - q.1 = (k : ℝ) * (2 * Real.pi) := by linarith
    have h2 : p.2 - q.2 = (l : ℝ) * (2 * Real.pi) := by linarith
    exact Prod.ext h1 h2
  · rintro ⟨k, l, h⟩
    refine ⟨⟨k, ?_⟩, ⟨l, ?_⟩⟩
    · have := congrArg Prod.fst h
      simp only [Prod.fst_sub] at this
      linarith
    · have := congrArg Prod.snd h
      simp only [Prod.snd_sub] at this
      linarith

/-- Points of the period lattice have the same image under `psi`. -/
lemma psiMap_eq_of_sub_mem_lattice {p q : ℝ × ℝ} (h : p - q ∈ lattice) :
    psiMap P.psi p = psiMap P.psi q :=
  P.psiMap_eq_iff.mpr h

/-- The fibre of `psi` over the image of `p` is exactly `p + 2πℤ²`. -/
lemma psiMap_eq_iff_mem_add {p q : ℝ × ℝ} :
    psiMap P.psi q = psiMap P.psi p ↔ ∃ v : ℤ × ℤ, q = p + periodShift v := by
  rw [psiMap_eq_iff, mem_lattice_iff]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_⟩
    rw [hv]
    ext <;> simp
  · rintro ⟨v, rfl⟩
    refine ⟨v, ?_⟩
    ext <;> simp [periodShift]

end TorusParam

/-! ### Length of a curve

We use the total variation `eVariationOn` of the curve over `[a,b]`, i.e. the supremum of the
lengths of inscribed polygonal lines; for a `C¹` curve this coincides with the classical
arclength `∫ ‖γ'‖`. -/

/-- The extrinsic length (total variation) of a curve `γ` over `[a,b]`. -/
def curveLength (γ : ℝ → R3) (a b : ℝ) : ℝ≥0∞ :=
  eVariationOn γ (Set.Icc a b)

@[simp] lemma curveLength_def (γ : ℝ → R3) (a b : ℝ) :
    curveLength γ a b = eVariationOn γ (Set.Icc a b) := rfl

end

end Work.TorusCover
