import Mathlib
import Submission.Diff.Interfaces
import Submission.Work.Diff.GE.kato_deps
import Submission.Work.Diff.GE.kato_bump_pos

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Gram–Schmidt construction of a geodesic orthonormal frame at a point

This module sets up the definitions used in the proof of `Work.Diff.GE.kato_geodesic_frame`.

Starting from a smooth family `V` of vector fields (a `g`-orthonormal frame at `x` in the intended
application), we run Gram–Schmidt with respect to the metric `g`, but with the normalisation
`s ↦ (√s)⁻¹` replaced by a *globally smooth* device: for the Gram function `f = |u|²` of the
pre-normalisation vector `u`, and a smooth bump `ψ` which is `1` near `x` and whose support is
contained in `{f > 0}`, one uses the normalisation

`F = f x + (f - f x) * ψ`,   `c = (√F)⁻¹`,

which is smooth and positive everywhere, agrees with `f` near `x` (so `c` is the honest
normalisation `|u|⁻¹` near `x`), and has vanishing derivative at `x` because the derivative of `f`
does and because `F =ᶠ f`.

The definitions:

* `katoU g V W i` — the pre-normalisation vector of the Gram–Schmidt step, using the previously
  produced fields `W j` for `j < i`;
* `katoGram g V W i` — the `g`-Gram function `|katoU|²`;
* `katoBump f x` — the smooth bump of the normalisation;
* `katoNorm g x V W i` — the smoothed Gram function `F`;
* `katoC g x V W i` — the normalising scalar `(√F)⁻¹`;
* `katoStep g x V W i = katoC · • katoU ·` — one Gram–Schmidt step;
* `katoFrame g x V` — the resulting family, by well-founded recursion on the index.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The index type of the frame: `Fin (finrank ℝ E)`. -/
abbrev katoIdx (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :=
  Fin (Module.finrank ℝ E)

/-- The indices strictly below `i`. -/
noncomputable def katoPre (i : katoIdx E) : Finset (katoIdx E) := Finset.univ.filter (fun j => j.val < i.val)

@[simp] theorem katoPre_mem {i j : katoIdx E} : j ∈ katoPre (E := E) i ↔ j.val < i.val := by
  simp [katoPre]

/-- A smooth bump which is `1` near `x` and which vanishes off the set where `f > 0`. -/
noncomputable def katoBump (f : M → ℝ) (x : M) : M → ℝ := by
  classical
  exact if h : ∃ ψ : M → ℝ, CMDiff ∞ ψ ∧ (∀ y, 0 ≤ ψ y) ∧ (∀ y, ψ y ≤ 1) ∧
      (∀ y, 0 < ψ y → 0 < f y) ∧ (ψ =ᶠ[𝓝 x] 1) then h.choose else fun _ => 1

/-- The bump `katoBump` has all the properties for which it is chosen. -/
theorem katoBump_spec' {f : M → ℝ} {x : M}
    (hP : ∃ ψ : M → ℝ, CMDiff ∞ ψ ∧ (∀ y, 0 ≤ ψ y) ∧ (∀ y, ψ y ≤ 1) ∧
      (∀ y, 0 < ψ y → 0 < f y) ∧ (ψ =ᶠ[𝓝 x] 1)) :
    CMDiff ∞ (katoBump (I := I) f x) ∧ (∀ y, 0 ≤ katoBump (I := I) f x y) ∧
      (∀ y, katoBump (I := I) f x y ≤ 1) ∧
      (∀ y, 0 < katoBump (I := I) f x y → 0 < f y) ∧ (katoBump (I := I) f x =ᶠ[𝓝 x] 1) := by
  classical
  rw [katoBump, dite_eq_left hP]
  exact ⟨hP.choose_spec.1, hP.choose_spec.2.1, hP.choose_spec.2.2.1,
    hP.choose_spec.2.2.2.1, hP.choose_spec.2.2.2.2⟩

/-- The bump `katoBump` has all the properties for which it is chosen. -/
theorem katoBump_spec {f : M → ℝ} {x : M} (hf : CMDiff ∞ f) (hpos : 0 < f x) :
    CMDiff ∞ (katoBump (I := I) f x) ∧ (∀ y, 0 ≤ katoBump (I := I) f x y) ∧
      (∀ y, katoBump (I := I) f x y ≤ 1) ∧
      (∀ y, 0 < katoBump (I := I) f x y → 0 < f y) ∧ (katoBump (I := I) f x =ᶠ[𝓝 x] 1) :=
  katoBump_spec' (kato_bump_pos f x hf hpos)

/-- The pre-normalisation vector of the `i`-th Gram–Schmidt step, using the fields `W j` for
`j < i`. -/
noncomputable def katoU (g : SMet I M) (V W : katoIdx E → Π y : M, TangentSpace I y)
    (i : katoIdx E) : Π y : M, TangentSpace I y :=
  fun y => V i y - ∑ j ∈ katoPre (E := E) i, g.inner y (V i y) (W j y) • W j y

/-- The `g`-Gram function of the pre-normalisation vector. -/
noncomputable def katoGram (g : SMet I M) (V W : katoIdx E → Π y : M, TangentSpace I y)
    (i : katoIdx E) : M → ℝ :=
  fun y => g.inner y (katoU g V W i y) (katoU g V W i y)

/-- The smoothed Gram function of the Gram–Schmidt step. -/
noncomputable def katoNorm (g : SMet I M) (x : M) (V W : katoIdx E → Π y : M, TangentSpace I y)
    (i : katoIdx E) : M → ℝ :=
  fun y => katoGram g V W i x
    + (katoGram g V W i y - katoGram g V W i x) * katoBump (I := I) (katoGram g V W i) x y

/-- The normalising scalar `(√F)⁻¹` of the Gram–Schmidt step. -/
noncomputable def katoC (g : SMet I M) (x : M) (V W : katoIdx E → Π y : M, TangentSpace I y)
    (i : katoIdx E) : M → ℝ :=
  fun y => (Real.sqrt (katoNorm g x V W i y))⁻¹

/-- One Gram–Schmidt step: normalise the pre-normalisation vector. -/
noncomputable def katoStep (g : SMet I M) (x : M) (V W : katoIdx E → Π y : M, TangentSpace I y)
    (i : katoIdx E) : Π y : M, TangentSpace I y :=
  fun y => katoC g x V W i y • katoU g V W i y

/-- The Gram–Schmidt family obtained from the family `V`, by well-founded recursion on the index. -/
noncomputable def katoFrame (g : SMet I M) (x : M) (V : katoIdx E → Π y : M, TangentSpace I y) :
    katoIdx E → Π y : M, TangentSpace I y :=
  WellFounded.fix (InvImage.wf (fun i : katoIdx E => i.val) wellFounded_lt)
    (fun i ih => katoStep g x V (fun j => if h : j.val < i.val then ih j h else 0) i)

theorem katoU_congr (g : SMet I M) (V : katoIdx E → Π y : M, TangentSpace I y)
    {W₁ W₂ : katoIdx E → Π y : M, TangentSpace I y} {i : katoIdx E}
    (h : ∀ j, j.val < i.val → W₁ j = W₂ j) : katoU g V W₁ i = katoU g V W₂ i := by
  funext y
  simp only [katoU]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [katoPre_mem] at hj
  rw [h j hj]

theorem katoGram_congr (g : SMet I M) (V : katoIdx E → Π y : M, TangentSpace I y)
    {W₁ W₂ : katoIdx E → Π y : M, TangentSpace I y} {i : katoIdx E}
    (h : ∀ j, j.val < i.val → W₁ j = W₂ j) : katoGram g V W₁ i = katoGram g V W₂ i := by
  funext y
  simp only [katoGram, katoU_congr g V h]

theorem katoNorm_congr (g : SMet I M) (x : M) (V : katoIdx E → Π y : M, TangentSpace I y)
    {W₁ W₂ : katoIdx E → Π y : M, TangentSpace I y} {i : katoIdx E}
    (h : ∀ j, j.val < i.val → W₁ j = W₂ j) : katoNorm g x V W₁ i = katoNorm g x V W₂ i := by
  funext y
  simp only [katoNorm, katoGram_congr g V h]

theorem katoC_congr (g : SMet I M) (x : M) (V : katoIdx E → Π y : M, TangentSpace I y)
    {W₁ W₂ : katoIdx E → Π y : M, TangentSpace I y} {i : katoIdx E}
    (h : ∀ j, j.val < i.val → W₁ j = W₂ j) : katoC g x V W₁ i = katoC g x V W₂ i := by
  funext y
  simp only [katoC, katoNorm_congr g x V h]

theorem katoStep_congr (g : SMet I M) (x : M) (V : katoIdx E → Π y : M, TangentSpace I y)
    {W₁ W₂ : katoIdx E → Π y : M, TangentSpace I y} {i : katoIdx E}
    (h : ∀ j, j.val < i.val → W₁ j = W₂ j) : katoStep g x V W₁ i = katoStep g x V W₂ i := by
  funext y
  simp only [katoStep, katoC_congr g x V h, katoU_congr g V h]

/-- The recursion equation for the Gram–Schmidt family. -/
theorem katoFrame_eq (g : SMet I M) (x : M) (V : katoIdx E → Π y : M, TangentSpace I y)
    (i : katoIdx E) : katoFrame g x V i = katoStep g x V (katoFrame g x V) i := by
  have h : katoFrame g x V i
      = katoStep g x V (fun j => if h : j.val < i.val then katoFrame g x V j else 0) i :=
    WellFounded.fix_eq (InvImage.wf (fun i : katoIdx E => i.val) wellFounded_lt) _ i
  rw [h]
  exact katoStep_congr g x V (fun j hj => dite_eq_left hj)

@[simp] theorem katoU_apply (g : SMet I M) (V W : katoIdx E → Π y : M, TangentSpace I y)
    (i : katoIdx E) (y : M) :
    katoU g V W i y = V i y - ∑ j ∈ katoPre (E := E) i, g.inner y (V i y) (W j y) • W j y :=
  rfl

@[simp] theorem katoGram_apply (g : SMet I M) (V W : katoIdx E → Π y : M, TangentSpace I y)
    (i : katoIdx E) (y : M) :
    katoGram g V W i y = g.inner y (katoU g V W i y) (katoU g V W i y) := rfl

@[simp] theorem katoNorm_apply (g : SMet I M) (x : M)
    (V W : katoIdx E → Π y : M, TangentSpace I y) (i : katoIdx E) (y : M) :
    katoNorm g x V W i y = katoGram g V W i x
      + (katoGram g V W i y - katoGram g V W i x) * katoBump (I := I) (katoGram g V W i) x y :=
  rfl

@[simp] theorem katoC_apply (g : SMet I M) (x : M)
    (V W : katoIdx E → Π y : M, TangentSpace I y) (i : katoIdx E) (y : M) :
    katoC g x V W i y = (Real.sqrt (katoNorm g x V W i y))⁻¹ := rfl

@[simp] theorem katoStep_apply (g : SMet I M) (x : M)
    (V W : katoIdx E → Π y : M, TangentSpace I y) (i : katoIdx E) (y : M) :
    katoStep g x V W i y = katoC g x V W i y • katoU g V W i y := rfl

end Work.Diff.GE
