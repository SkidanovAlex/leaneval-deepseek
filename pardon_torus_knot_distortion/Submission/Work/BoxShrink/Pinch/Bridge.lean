import Submission.Work.BoxShrink.Pinch.Plane

/-!
# The exact dictionary: loops of the torus versus periodic paths of the plane

`Plane.lean` established the two halves of the dictionary between loops of a parametrised torus
`F = P.carrier` and paths of its parameter plane `ℝ × ℝ`:

* `containsEssentialLoop_of_periodicPath` — a path `q` with `q (t+1) = q t + (2πk, 2πl)`,
  `(k,l) ≠ 0`, whose image lies in the preimage of `X`, gives an essential loop of `F` in `X`;
* the window criterion — if every connected subset of the preimage is confined to a *window*
  (a set contained in an open rectangle of side lengths `< 2π`), then `X` carries no essential
  loop.

This module closes the dictionary: the *converse* of the second statement, hence the exact
criterion

  `X` carries an essential loop  ⟺  some nonzero period `(k,l) ≠ 0` is realised by a path of the
  preimage `Φ⁻¹ X`,

and the sharper statement that the whole `ℚ`-submodule `Work.SurgeryInvariance.WindingSpan P X`
is the span of the realised periods (`periodSpan_eq_windingSpan`).  The proof of the converse is
short because a lift `L` of a loop `γ : ℝ → F` is a *global* continuous map `ℝ → ℝ²` whose shift
over one period is the winding vector *for every* base point
(`Work.CoreTopology.LiftOf.period_shift_winding`): so `s ↦ (L.Θ (2π s), L.Φ (2π s))` is already a
periodic path with shift exactly `2π·(L.winding)` — no gluing or reparametrisation is needed.

Consequently the whole of the winding-span bookkeeping of the pinch can be read in the parameter
plane, where the only notion involved is that of a *path* realising a lattice shift; this is the
language in which the two-dimensional arguments about the slice and the box region are run.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Pinch

noncomputable section

variable {P : Work.CoreTopology.ParamTorus}

/-! ## Realised periods -/

/-- **A lattice period realised by the region's preimage.**  A continuous path `q : ℝ → ℝ²` which
is periodic up to the shift `2π(k,l)` and whose image lies in the preimage of `X` under the
parametrisation.  By `containsEssentialLoop_of_periodicPath` a *nonzero* realised period is exactly
an essential loop of `F` inside `X`. -/
def PeriodRealised (P : Work.CoreTopology.ParamTorus) (X : Set R3) (k l : ℤ) : Prop :=
  ∃ q : ℝ → ℝ × ℝ, Continuous q ∧
    (∀ t : ℝ, q (t + 1) = q t + Work.TorusCover.periodShift (k, l)) ∧
    ∀ t : ℝ, Phi P (q t) ∈ X

theorem periodRealised_mono {X Y : Set R3} (h : X ⊆ Y) {k l : ℤ}
    (hX : PeriodRealised P X k l) : PeriodRealised P Y k l := by
  obtain ⟨q, hq, hper, hmem⟩ := hX
  exact ⟨q, hq, hper, fun t => h (hmem t)⟩

/-- The period `(0,0)` is realised by the constant path through any point of the region. -/
theorem periodRealised_zero_of_mem {X : Set R3} {x : R3} (hx : x ∈ X) (hxF : x ∈ P.carrier) :
    PeriodRealised P X 0 0 := by
  obtain ⟨p, hp⟩ := hxF
  refine ⟨fun _ => p, continuous_const, fun t => ?_, fun t => ?_⟩
  · simp [Work.TorusCover.periodShift]
  · rw [show Phi P p = x from hp]; exact hx

/-! ## The path associated to a lift -/

/-- **The periodic path of the plane associated to a lift.**  If `L` lifts the loop `γ`, then
`s ↦ (L.Θ (2π s), L.Φ (2π s))` is continuous, its shift over one period is the winding vector of
`L`, and it lies over `γ`. -/
theorem lift_periodicPath {γ : Work.CoreTopology.ClosedCurve P} (L : Work.CoreTopology.LiftOf P γ) :
    Continuous (fun s : ℝ => (L.Θ (2 * Real.pi * s), L.Φ (2 * Real.pi * s))) ∧
    (∀ s : ℝ, (fun s : ℝ => (L.Θ (2 * Real.pi * s), L.Φ (2 * Real.pi * s))) (s + 1) =
      (fun s : ℝ => (L.Θ (2 * Real.pi * s), L.Φ (2 * Real.pi * s))) s +
        Work.TorusCover.periodShift L.winding) ∧
    (∀ s : ℝ, Phi P ((L.Θ (2 * Real.pi * s), L.Φ (2 * Real.pi * s))) = γ (2 * Real.pi * s)) := by
  refine ⟨(L.contΘ.comp (continuous_const.mul continuous_id)).prodMk
    (L.contΦ.comp (continuous_const.mul continuous_id)), ?_, ?_⟩
  · intro s
    have hspec := L.period_shift_winding (2 * Real.pi * s)
    have harg : 2 * Real.pi * s + 2 * Real.pi = 2 * Real.pi * (s + 1) := by ring
    rw [harg] at hspec
    change (L.Θ (2 * Real.pi * (s + 1)), L.Φ (2 * Real.pi * (s + 1))) =
      (L.Θ (2 * Real.pi * s), L.Φ (2 * Real.pi * s)) + Work.TorusCover.periodShift L.winding
    rw [hspec.1, hspec.2, Work.TorusCover.periodShift]
    rfl
  · intro s
    rw [Phi, L.lifts (2 * Real.pi * s)]

/-! ## The two directions of the dictionary -/

/-- **A nonzero realised period gives an essential loop** (`Plane.lean`, restated in the period
vocabulary). -/
theorem containsEssentialLoop_of_periodRealised {X : Set R3} {k l : ℤ}
    (h : PeriodRealised P X k l) (hne : (k, l) ≠ 0) : P.ContainsEssentialLoop X := by
  obtain ⟨q, hq, hper, hmem⟩ := h
  refine containsEssentialLoop_of_periodicPath (P := P) hq (k := k) (l := l) ?_ hne hmem
  intro t
  simpa [Work.TorusCover.periodShift] using hper t

/-- **Every realised period is the winding vector of a loop inside the region.**  This is the
sharp form of the converse of `containsEssentialLoop_of_periodicPath`: not only is the loop
essential, its winding vector is the realised period. -/
theorem exists_windingOf_eq_of_periodRealised {X : Set R3} {k l : ℤ}
    (h : PeriodRealised P X k l) :
    ∃ γ : Work.CoreTopology.ClosedCurve P, (∀ t : ℝ, γ t ∈ X) ∧
      Work.SurgeryInvariance.windingOf P γ = (k, l) := by
  obtain ⟨q, hq, hper, hmem⟩ := h
  have htwopi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  set L : ℝ → ℝ × ℝ := fun t => q (t / (2 * Real.pi)) with hL
  have hLcont : Continuous L := hq.comp (continuous_id.div_const _)
  have hperL : ∀ t : ℝ, L (t + 2 * Real.pi) = L t + Work.TorusCover.periodShift (k, l) := by
    intro t
    have harg : (t + 2 * Real.pi) / (2 * Real.pi) = t / (2 * Real.pi) + 1 := by field_simp
    simp only [hL, harg]
    exact hper _
  have hperγ : ∀ t : ℝ, Phi P (L (t + 2 * Real.pi)) = Phi P (L t) := by
    intro t
    rw [hperL t]
    exact Phi_add_lattice (P := P) (L t)
  let γ : Work.CoreTopology.ClosedCurve P :=
    { γ := fun t => Phi P (L t), cont := (Phi_continuous (P := P)).comp hLcont, periodic := hperγ,
      mem := fun t => Phi_mem_carrier (P := P) (L t) }
  let Λ : Work.CoreTopology.LiftOf P γ :=
    { Θ := fun t => (L t).1, Φ := fun t => (L t).2, contΘ := continuous_fst.comp hLcont,
      contΦ := continuous_snd.comp hLcont, lifts := fun _ => rfl }
  have hΘ : Λ.Θ (2 * Real.pi) = Λ.Θ 0 + (k : ℝ) * (2 * Real.pi) := by
    have h' := congrArg Prod.fst (hperL 0)
    simpa [Λ, hL, Work.TorusCover.periodShift] using h'
  have hΦ : Λ.Φ (2 * Real.pi) = Λ.Φ 0 + (l : ℝ) * (2 * Real.pi) := by
    have h' := congrArg Prod.snd (hperL 0)
    simpa [Λ, hL, Work.TorusCover.periodShift] using h'
  have hw1 : (Λ.winding).1 = k := by
    have hh := Λ.winding_spec.1
    rw [hΘ] at hh
    have hh' : (((Λ.winding).1 : ℤ) : ℝ) * (2 * Real.pi) = (k : ℝ) * (2 * Real.pi) := by linarith
    exact_mod_cast mul_right_cancel₀ htwopi hh'
  have hw2 : (Λ.winding).2 = l := by
    have hh := Λ.winding_spec.2
    rw [hΦ] at hh
    have hh' : (((Λ.winding).2 : ℤ) : ℝ) * (2 * Real.pi) = (l : ℝ) * (2 * Real.pi) := by linarith
    exact_mod_cast mul_right_cancel₀ htwopi hh'
  refine ⟨γ, fun t => ?_, ?_⟩
  · show Phi P (q (t / (2 * Real.pi))) ∈ X
    exact hmem _
  · rw [Work.SurgeryInvariance.windingOf_eq P γ Λ]
    rw [Prod.ext_iff]
    exact ⟨hw1, hw2⟩

/-- **An essential loop gives a nonzero realised period.** -/
theorem periodRealised_of_containsEssentialLoop {X : Set R3} (h : P.ContainsEssentialLoop X) :
    ∃ k l : ℤ, (k, l) ≠ 0 ∧ PeriodRealised P X k l := by
  obtain ⟨γ, hess, hmem⟩ := h
  obtain ⟨L⟩ := Work.TorusCover.ParamTorus_exists_liftOf P γ
  refine ⟨(L.winding).1, (L.winding).2, fun hzero => hess.winding_ne L hzero, ?_⟩
  refine ⟨fun s => (L.Θ (2 * Real.pi * s), L.Φ (2 * Real.pi * s)),
    (lift_periodicPath L).1, ?_, ?_⟩
  · intro s
    have h' := (lift_periodicPath L).2.1 s
    simpa [Work.TorusCover.periodShift] using h'
  · intro s
    rw [(lift_periodicPath L).2.2 s]
    exact hmem (2 * Real.pi * s)

/-- **The exact criterion.**  A region of the surface carries an essential loop of the torus if and
only if its preimage in the parameter plane contains a path realising a nonzero lattice period. -/
theorem containsEssentialLoop_iff_exists_periodRealised (X : Set R3) :
    P.ContainsEssentialLoop X ↔ ∃ k l : ℤ, (k, l) ≠ 0 ∧ PeriodRealised P X k l :=
  ⟨periodRealised_of_containsEssentialLoop, fun ⟨_, _, hne, h⟩ =>
    containsEssentialLoop_of_periodRealised h hne⟩

/-- **Inessentiality in the period language**: `X` carries no essential loop exactly when no path
of its preimage realises a nonzero period.  This is the form in which the hypotheses on the sphere
trace and on the slice are consumed by the two-dimensional arguments. -/
theorem not_containsEssentialLoop_iff_forall_periodRealised (X : Set R3) :
    ¬ P.ContainsEssentialLoop X ↔ ∀ k l : ℤ, PeriodRealised P X k l → (k, l) = 0 := by
  constructor
  · intro h k l hk
    by_contra hne
    exact h (containsEssentialLoop_of_periodRealised hk hne)
  · rintro h hcon
    obtain ⟨k, l, hne, hk⟩ := (containsEssentialLoop_iff_exists_periodRealised X).mp hcon
    exact hne (h k l hk)

/-! ## The `ℚ`-span of the realised periods is the winding span -/

/-- The `ℚ`-submodule spanned by the realised periods: the plane-side counterpart of
`Work.SurgeryInvariance.WindingSpan`, obtained by pushing the integer periods into `ℚ × ℚ`. -/
def periodSpan (P : Work.CoreTopology.ParamTorus) (X : Set R3) : Submodule ℚ (ℚ × ℚ) :=
  Submodule.span ℚ {v : ℚ × ℚ | ∃ k l : ℤ, PeriodRealised P X k l ∧ (((k : ℚ), (l : ℚ)) = v)}

theorem windingVectors_subset_periodSpan (X : Set R3) :
    Work.SurgeryInvariance.windingVectors P X ⊆ (periodSpan P X : Set (ℚ × ℚ)) := by
  rintro v ⟨γ, hγ, rfl⟩
  obtain ⟨L⟩ := Work.TorusCover.ParamTorus_exists_liftOf P γ
  have hw : Work.SurgeryInvariance.windingOf P γ = L.winding :=
    Work.SurgeryInvariance.windingOf_eq P γ L
  have hper : PeriodRealised P X (L.winding).1 (L.winding).2 := by
    refine ⟨fun s => (L.Θ (2 * Real.pi * s), L.Φ (2 * Real.pi * s)),
      (lift_periodicPath L).1, ?_, ?_⟩
    · intro s
      have h' := (lift_periodicPath L).2.1 s
      simpa [Work.TorusCover.periodShift] using h'
    · intro s
      rw [(lift_periodicPath L).2.2 s]
      exact hγ (2 * Real.pi * s)
  refine Submodule.subset_span ⟨(L.winding).1, (L.winding).2, hper, ?_⟩
  rw [← hw]

theorem periodSpan_le_windingSpan (X : Set R3) :
    periodSpan P X ≤ Work.SurgeryInvariance.WindingSpan P X := by
  refine Submodule.span_le.mpr ?_
  rintro v ⟨k, l, hper, rfl⟩
  obtain ⟨γ, hγ, hw⟩ := exists_windingOf_eq_of_periodRealised hper
  rw [Work.SurgeryInvariance.WindingSpan]
  refine Submodule.subset_span ⟨γ, hγ, ?_⟩
  rw [hw]

/-- **The plane-side span is the winding span**: the finrank bookkeeping of the pinch can be read
entirely in the parameter plane, where `periodSpan` is the span of the periods realised by paths
of the preimage. -/
theorem periodSpan_eq_windingSpan (X : Set R3) :
    periodSpan P X = Work.SurgeryInvariance.WindingSpan P X :=
  le_antisymm (periodSpan_le_windingSpan X) (by
    rw [Work.SurgeryInvariance.WindingSpan]
    exact Submodule.span_le.mpr (fun v hv => windingVectors_subset_periodSpan X hv))

end

end Work.BoxShrink.Pinch
