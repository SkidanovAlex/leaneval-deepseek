import Submission.Work.TorusCover.Basic
import Submission.Work.TorusCover.Covering
import Submission.Work.TorusCover.isLift_unique
import Submission.Work.TorusCover.hasWinding_unique
import Submission.Work.TorusCover.exists_isLift_of_isCoveringMap
import Submission.Work.TorusCover.exists_hasWinding_of_isCoveringMap

/-!
# Lifts and winding vectors of closed curves on a parametrised torus

Here we assemble the main API of deliverable 1 of the torus-covering subproject:

* `Work.TorusCover.TorusParam.exists_isLift`: every continuous curve in the range of `psi`
  lifts through the covering `ℝ² → range psi`, with prescribed value at `0`
  (path lifting for the covering map `Work.TorusCover.TorusParam.isCoveringMap_psiMapToRange`);
* `Work.TorusCover.TorusParam.exists_hasWinding`: every closed curve in the range of `psi` has a
  winding vector;
* `Work.TorusCover.windingVector`, `Work.TorusCover.windingVector_spec`,
  `Work.TorusCover.windingVector_eq`: the winding vector of a closed curve, its defining property
  (a periodic lift advancing by `periodShift v`), and its uniqueness — the winding vector is
  independent of the chosen lift;
* `Work.TorusCover.isEssential_iff_windingVector_ne_zero`: a curve is essential exactly when its
  winding vector is nonzero;
* `Work.TorusCover.hasWinding_zero_of_isLift_periodic`: a curve with a `2π`-periodic lift (a
  constant curve, or one lying in a simply connected piece covered by a single chart) has
  winding vector `(0,0)`.
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.TorusCover

noncomputable section

variable {P : TorusParam}

/-! ### Existence of lifts and of winding vectors -/

/-- **Path lifting.**  A continuous curve `γ` with values in the range of `psi` lifts through
the covering `psiMapToRange psi` to a continuous `Λ : ℝ → ℝ × ℝ` with `psi ∘ Λ = γ`; the value
at `0` can be prescribed to be any preimage of `γ 0`. -/
theorem TorusParam.exists_isLift (P : TorusParam) {γ : ℝ → R3} (hγ : Continuous γ)
    (himg : ∀ t, γ t ∈ Set.range (psiMap P.psi)) (p₀ : ℝ × ℝ)
    (hp₀ : psiMap P.psi p₀ = γ 0) :
    ∃ Λ : ℝ → ℝ × ℝ, IsLift P.psi γ Λ ∧ Λ 0 = p₀ :=
  _root_.Work.TorusCover.exists_isLift_of_isCoveringMap P P.isCoveringMap_psiMapToRange
    hγ himg p₀ hp₀

/-- **Existence of the winding vector.**  Every continuous closed curve in the range of `psi`
admits a lift which advances by a period shift over one period. -/
theorem TorusParam.exists_hasWinding (P : TorusParam) {γ : ℝ → R3} (hγ : Continuous γ)
    (hper : ∀ t, γ (t + 2 * Real.pi) = γ t)
    (himg : ∀ t, γ t ∈ Set.range (psiMap P.psi)) : ∃ v : ℤ × ℤ, HasWinding P.psi γ v :=
  _root_.Work.TorusCover.exists_hasWinding_of_isCoveringMap P P.isCoveringMap_psiMapToRange
    hγ hper himg

/-! ### The winding vector -/

/-- The **winding vector** of a continuous closed curve in the range of `psi`: the pair
`(a, b)` such that some lift `Λ` satisfies `Λ (t + 2π) = Λ t + (2π a, 2π b)`.  By
`Work.TorusCover.windingVector_eq` this is independent of the lift. -/
noncomputable def windingVector (P : TorusParam) (γ : ℝ → R3) (hγ : Continuous γ)
    (hper : ∀ t, γ (t + 2 * Real.pi) = γ t) (himg : ∀ t, γ t ∈ Set.range (psiMap P.psi)) :
    ℤ × ℤ :=
  Classical.choose (P.exists_hasWinding hγ hper himg)

/-- Characterising property of `Work.TorusCover.windingVector`. -/
theorem windingVector_spec (P : TorusParam) {γ : ℝ → R3} (hγ : Continuous γ)
    (hper : ∀ t, γ (t + 2 * Real.pi) = γ t)
    (himg : ∀ t, γ t ∈ Set.range (psiMap P.psi)) :
    HasWinding P.psi γ (windingVector P γ hγ hper himg) :=
  Classical.choose_spec (P.exists_hasWinding hγ hper himg)

/-- **The winding vector is well defined**: any lift-based witness of the winding vector of `γ`
is equal to `windingVector P γ`. -/
theorem windingVector_eq (P : TorusParam) {γ : ℝ → R3} (hγ : Continuous γ)
    (hper : ∀ t, γ (t + 2 * Real.pi) = γ t)
    (himg : ∀ t, γ t ∈ Set.range (psiMap P.psi)) {v : ℤ × ℤ}
    (hv : HasWinding P.psi γ v) : v = windingVector P γ hγ hper himg :=
  _root_.Work.TorusCover.hasWinding_unique P hv (windingVector_spec P hγ hper himg)

/-- The winding vector of `γ` determines the period displacement of *any* periodic lift of
`γ`. -/
theorem windingVector_eq_of_isPeriodicLift (P : TorusParam) {γ : ℝ → R3} (hγ : Continuous γ)
    (hper : ∀ t, γ (t + 2 * Real.pi) = γ t)
    (himg : ∀ t, γ t ∈ Set.range (psiMap P.psi)) {v : ℤ × ℤ} {Λ : ℝ → ℝ × ℝ}
    (hΛ : IsPeriodicLift P.psi γ v Λ) : v = windingVector P γ hγ hper himg :=
  windingVector_eq P hγ hper himg ⟨Λ, hΛ⟩

/-- **Essential curves are exactly those with nonzero winding vector.** -/
theorem isEssential_iff_windingVector_ne_zero (P : TorusParam) {γ : ℝ → R3}
    (hγ : Continuous γ) (hper : ∀ t, γ (t + 2 * Real.pi) = γ t)
    (himg : ∀ t, γ t ∈ Set.range (psiMap P.psi)) :
    IsEssential P.psi γ ↔ windingVector P γ hγ hper himg ≠ 0 := by
  constructor
  · rintro ⟨v, hv, hw⟩ hzero
    rw [← windingVector_eq P hγ hper himg hw] at hzero
    exact hv hzero
  · intro h
    exact ⟨windingVector P γ hγ hper himg, h, windingVector_spec P hγ hper himg⟩

/-! ### Inessential curves -/

/-- A curve admitting a `2π`-periodic lift has winding vector `(0,0)`.  This covers constant
curves and curves whose image lies in a simply connected piece of the torus (an open set on
which `psi` has a continuous section). -/
theorem hasWinding_zero_of_isLift_periodic {psi : ℝ → ℝ → R3} {γ : ℝ → R3} {Λ : ℝ → ℝ × ℝ}
    (h : IsLift psi γ Λ) (hper : ∀ t, Λ (t + 2 * Real.pi) = Λ t) : HasWinding psi γ 0 :=
  ⟨Λ, h, by intro t; rw [hper t]; simp⟩

/-- A curve whose image lies in a piece of the torus on which the parametrisation has a
continuous section has winding vector `(0,0)`: composing the section with the curve gives a
`2π`-periodic lift.  This is the precise form of "the winding vector of a curve lying in a simply
connected piece of the torus is zero". -/
theorem hasWinding_zero_of_section {psi : ℝ → ℝ → R3} {γ : ℝ → R3} {s : Set R3}
    {σ : R3 → ℝ × ℝ} (hσ : ContinuousOn σ s)
    (hsec : ∀ x ∈ s, psi (σ x).1 (σ x).2 = x) (hγ : Continuous γ)
    (hper : ∀ t, γ (t + 2 * Real.pi) = γ t) (himg : ∀ t, γ t ∈ s) : HasWinding psi γ 0 :=
  hasWinding_zero_of_isLift_periodic
    ⟨hσ.comp_continuous hγ himg, fun t => hsec (γ t) (himg t)⟩
    (fun t => by simp [hper t])

/-- A constant curve with value in the range of `psi` has winding vector `(0,0)`. -/
theorem hasWinding_zero_of_const {psi : ℝ → ℝ → R3} {x : R3}
    (hx : x ∈ Set.range (psiMap psi)) : HasWinding psi (fun _ => x) 0 := by
  obtain ⟨p₀, hp₀⟩ := hx
  refine hasWinding_zero_of_isLift_periodic (Λ := fun _ => p₀) ⟨continuous_const, ?_⟩
    (fun _ => rfl)
  intro t
  simpa using hp₀

end

end Work.TorusCover
