import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set

namespace Work.EXT

/-- Componentwise criterion for smoothness of a continuous-linear-map-valued function: if `Φ : M → E →L[ℝ] E` is such that `y ↦ Φ y (b j)` is `C^∞` at `x` for every element `b j` of a basis `b` of the finite-dimensional real space `E`, then `Φ` itself is `C^∞` at `x` (both sides read in the model `E →L[ℝ] E` resp. `E`).

A possible proof: `fun c : Fin n → E => ∑ i, (((b.coord i).toContinuousLinearMap).smulRight (c i))` is the inverse of `Φ ↦ fun i => Φ (b i)`; use `Basis.sum_repr` to see that `Φ y = ∑ i, ((b.coord i).toContinuousLinearMap).smulRight (Φ y (b i))` for every `y`, then close under finite sums. -/
theorem contMDiffAt_of_apply_basis
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {Φ : M → E →L[ℝ] E} {x : M}
    (h : ∀ j, ContMDiffAt I (modelWithCornersSelf ℝ E) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : M => Φ y (b j)) x) :
    ContMDiffAt I (modelWithCornersSelf ℝ (E →L[ℝ] E)) ((⊤ : ℕ∞) : WithTop ℕ∞) Φ x := by
  -- The "reconstruction" continuous linear map `(Fin n → E) →L (E →L E)`.
  let T : (Fin (Module.finrank ℝ E) → E) →L[ℝ] (E →L[ℝ] E) :=
    ∑ i, (ContinuousLinearMap.smulRightL ℝ E E ((b.coord i).toContinuousLinearMap)).comp
      (ContinuousLinearMap.proj i)
  -- `T` inverts `Φ ↦ fun i => Φ (b i)`.
  have hkey : ∀ y : M, T (fun i => Φ y (b i)) = Φ y := by
    intro y
    change (∑ i, (ContinuousLinearMap.smulRightL ℝ E E ((b.coord i).toContinuousLinearMap)).comp
      (ContinuousLinearMap.proj i)) (fun i => Φ y (b i)) = Φ y
    ext z
    simp only [sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      ContinuousLinearMap.smulRightL_apply_apply, ContinuousLinearMap.smulRight_apply]
    rw [← Module.Basis.sum_repr b z, map_sum]
    simp [map_smul]
  have hP : ContMDiffAt I (modelWithCornersSelf ℝ (Fin (Module.finrank ℝ E) → E))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : M => fun i => Φ y (b i)) x :=
    contMDiffAt_pi_space.2 (fun i => h i)
  have hmain : ContMDiffAt I (modelWithCornersSelf ℝ (E →L[ℝ] E)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : M => T (fun i => Φ y (b i))) x :=
    T.contMDiff.contMDiffAt.comp x hP
  rwa [show (fun y : M => T (fun i => Φ y (b i))) = Φ from funext hkey] at hmain

end Work.EXT
