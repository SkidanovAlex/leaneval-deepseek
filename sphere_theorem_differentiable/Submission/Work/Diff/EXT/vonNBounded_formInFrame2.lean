import Mathlib
import Submission.Work.Diff.EXT.glueDefs
import Submission.Work.Diff.EXT.isVonNBounded_quadForm_lt2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Sublevel sets of `formInFrame` are von Neumann bounded

`formInFrame (I := I) x₀ x A` is the bilinear form on the tangent space `TangentSpace I x` whose
matrix in the coordinate frame of the chart at `x₀` is the prescribed matrix `A` (see
`Work.Diff.EXT.glueDefs`).  This file proves

`Work.Diff.EXT.vonNBounded_formInFrame2`:

if the quadratic form of `A` is strictly positive away from the origin, then for every `r > 0` the
sublevel set `{u | formInFrame x₀ x A u u < r}` is von Neumann bounded.

The proof is a transport along the *coordinate equivalence* of the frame of the chart at `x₀`:

`Ψ : TangentSpace I x ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ)`,

`Ψ u i = coordᵢ (frameCoords x₀ x u)` (the `i`-th coordinate of `u` in the frame of the chart at
`x₀`).  It is the composition of the continuous linear equivalence of the tangent-bundle
trivialisation at `x₀` (`Trivialization.continuousLinearEquivAt`, available on the base set of the
trivialisation, which is exactly the hypothesis `hx`) with the linear equivalence `Basis.equivFunL`
of the basis `bB`.  By `formInFrame_apply`, `formInFrame x₀ x A u u` is precisely the coordinate
quadratic form `∑ i, ∑ j, (Ψ u) i * (Ψ u) j * A i j` of `A`, so the sublevel set in question is the
`Ψ`-preimage of the sublevel set of the coordinate quadratic form on `Fin n → ℝ`, equivalently the
image of that set under `Ψ.symm` (a continuous linear map).  The latter is von Neumann bounded by
`Work.Diff.EXT.isVonNBounded_quadForm_lt2`, and von Neumann boundedness is preserved by continuous
linear images (`Bornology.IsVonNBounded.image`).

Decomposition of the argument (the two helper lemmas are `private`, since they are not needed
elsewhere): `frameCoordsEquiv_aux` builds `Ψ`, and `formInFrame_self_eq_quadForm_aux` identifies
the diagonal values of `formInFrame` with the coordinate quadratic form of `A`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set

namespace Work.Diff.EXT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]

/-- **The coordinate equivalence of the frame of the chart at `x₀`.**  For `x` in the base set of
the tangent-bundle trivialisation at `x₀`, the coordinates of a tangent vector in the frame of the
chart at `x₀` are the components of a continuous linear equivalence
`TangentSpace I x ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ)`. -/
private lemma frameCoordsEquiv_aux (x₀ x : M)
    (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    ∃ Ψ : TangentSpace I x ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ),
      ∀ (u : TangentSpace I x) (i : Fin (Module.finrank ℝ E)),
        Ψ u i = ((bB (E := E)).coord i) (frameCoords (I := I) x₀ x u) := by
  refine ⟨((trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt ℝ x hx).trans
    (bB (E := E)).equivFunL, fun u i => ?_⟩
  have hΦ : (((trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt ℝ x hx :
      TangentSpace I x →L[ℝ] E)) = frameCoords (I := I) x₀ x :=
    Trivialization.coe_continuousLinearEquivAt_eq' _ hx
  rw [ContinuousLinearEquiv.trans_apply, ← hΦ, Module.Basis.equivFunL_apply,
    Module.Basis.coord_apply]
  rfl

/-- The diagonal values of `formInFrame` are the coordinate quadratic form of `A` in the frame of
the chart at `x₀`. -/
private lemma formInFrame_self_eq_quadForm_aux (x₀ x : M) (A : MatE (E := E))
    (u : TangentSpace I x) :
    formInFrame (I := I) x₀ x A u u
      = ∑ i, ∑ j, ((bB (E := E)).coord i) (frameCoords (I := I) x₀ x u)
          * ((bB (E := E)).coord j) (frameCoords (I := I) x₀ x u) * A i j := by
  rw [formInFrame_apply]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

theorem vonNBounded_formInFrame2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
    {x₀ x : M} (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    {A : Work.Diff.EXT.MatE (E := E)}
    (h : ∀ v : Fin (Module.finrank ℝ E) → ℝ, v ≠ 0 → 0 < ∑ i, ∑ j, v i * v j * A i j)
    {r : ℝ} (hr : 0 < r) :
    Bornology.IsVonNBounded ℝ
      {u : TangentSpace I x | Work.Diff.EXT.formInFrame (I := I) x₀ x A u u < r} := by
  classical
  obtain ⟨Ψ, hΨ⟩ := frameCoordsEquiv_aux (I := I) x₀ x hx
  -- The diagonal values of `formInFrame` are the coordinate quadratic form of `A` in the frame.
  have hquad : ∀ u : TangentSpace I x, formInFrame (I := I) x₀ x A u u
      = ∑ i, ∑ j, Ψ u i * Ψ u j * A i j := by
    intro u
    rw [formInFrame_self_eq_quadForm_aux (I := I) x₀ x A u]
    exact Finset.sum_congr rfl
      (fun i _ => Finset.sum_congr rfl (fun j _ => by rw [hΨ u i, hΨ u j]))
  -- The sublevel set of `formInFrame` is the `Ψ`-preimage of the sublevel set of the coordinate
  -- quadratic form of `A`.
  have hset : {u : TangentSpace I x | formInFrame (I := I) x₀ x A u u < r}
      = Ψ ⁻¹' {v : Fin (Module.finrank ℝ E) → ℝ | ∑ i, ∑ j, v i * v j * A i j < r} := by
    ext u
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, hquad]
  -- ... equivalently the image of that set under the continuous linear map `Ψ.symm`.
  have hpre : Ψ ⁻¹' {v : Fin (Module.finrank ℝ E) → ℝ | ∑ i, ∑ j, v i * v j * A i j < r}
      = Ψ.symm '' {v : Fin (Module.finrank ℝ E) → ℝ | ∑ i, ∑ j, v i * v j * A i j < r} := by
    ext u
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · intro hhu
      exact ⟨Ψ u, hhu, ContinuousLinearEquiv.symm_apply_apply Ψ u⟩
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
  rw [hset, hpre]
  exact Bornology.IsVonNBounded.image (σ := RingHom.id ℝ)
    (isVonNBounded_quadForm_lt2 (Module.finrank ℝ E) A h hr)
    (Ψ.symm : (Fin (Module.finrank ℝ E) → ℝ) →L[ℝ] TangentSpace I x)

end Work.Diff.EXT
