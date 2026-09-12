import Mathlib
import Submission.Commons.Lattice.SuccessiveMinima.Basic

/-!
# Successive minima are unchanged when a lattice in a subspace is pushed into the ambient space

If `V ≤ E` is a real subspace, `W ≤ V` a `ℤ`-submodule and `W' = W.map (V.subtype)` its image
in `E`, then the defining sets of the successive minima of `W` (as a lattice in the normed
space `V`) and of `W'` (as a lattice in `E`) coincide; hence `λᵢ(W) = λᵢ(W')`.

The norm on the subspace `V` is the restriction of the norm on `E`
(`Submodule.norm_coe` is `rfl`), so the inclusion `V ↪ E` is an isometry onto its image.  The
inclusion restricts to a `ℤ`-linear equivalence
`carrierEquiv : W ≃ₗ[ℤ] W'` (via `Submodule.equivMapOfInjective` and `LinearEquiv.ofEq`);
sending a realising family through it (resp. through its inverse) transports witnesses of a
radius `r` from one lattice to the other, since `ℤ`-linear independence is preserved by
`LinearIndependent.map'` / `LinearIndependent.of_comp` and norms are preserved because
`(carrierEquiv x : E) = (x : V)`.
-/

noncomputable section

open Set
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Commons.Lattice.SuccessiveMinima

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {V : Submodule ℝ E}

/-- The inclusion `V ↪ E`, viewed as a `ℤ`-linear map, is injective. -/
private lemma subtype_restrictScalars_injective :
    Function.Injective (V.subtype.restrictScalars ℤ : V →ₗ[ℤ] E) :=
  fun _ _ hxy => V.injective_subtype hxy

/-- The `ℤ`-linear equivalence `W ≃ₗ[ℤ] W'` induced by the inclusion `V ↪ E`, when
`W' = W.map (V.subtype.restrictScalars ℤ)`. -/
private def carrierEquiv (W : Submodule ℤ V) (W' : Submodule ℤ E)
    (h : W' = W.map (V.subtype.restrictScalars ℤ)) : W ≃ₗ[ℤ] W' :=
  (Submodule.equivMapOfInjective (V.subtype.restrictScalars ℤ)
    subtype_restrictScalars_injective W).trans
    (LinearEquiv.ofEq _ _ h.symm)

/-- The `carrierEquiv` equivalence acts on the ambient space simply by the inclusion. -/
private lemma carrierEquiv_coe (W : Submodule ℤ V) (W' : Submodule ℤ E)
    (h : W' = W.map (V.subtype.restrictScalars ℤ)) (x : W) :
    ((carrierEquiv W W' h x : W') : E) = ((x : V) : E) := by
  show ((Submodule.equivMapOfInjective (V.subtype.restrictScalars ℤ)
      subtype_restrictScalars_injective W x : W.map (V.subtype.restrictScalars ℤ)) : E)
    = ((x : V) : E)
  rw [Submodule.coe_equivMapOfInjective_apply]
  exact (rfl : (V.subtype.restrictScalars ℤ) (x : V) = ((x : V) : E))

/-- The inverse of `carrierEquiv` also acts on the ambient space by the inclusion. -/
private lemma carrierEquiv_symm_coe (W : Submodule ℤ V) (W' : Submodule ℤ E)
    (h : W' = W.map (V.subtype.restrictScalars ℤ)) (y : W') :
    (V.subtype.restrictScalars ℤ) (((carrierEquiv W W' h).symm y : W) : V) = (y : E) := by
  have h1 : (V.subtype.restrictScalars ℤ) (((carrierEquiv W W' h).symm y : W) : V)
      = ((carrierEquiv W W' h ((carrierEquiv W W' h).symm y) : W') : E) :=
    (carrierEquiv_coe W W' h _).symm
  rw [h1, LinearEquiv.apply_symm_apply]

/-- One inclusion of the defining sets of the successive minima: a radius realising `i`
independent points of `W ≤ V` also realises `i` independent points of its image `W' ≤ E`. -/
lemma smSet_subset_of_carrier_eq (W : Submodule ℤ V) (W' : Submodule ℤ E)
    (h : W' = W.map (V.subtype.restrictScalars ℤ)) (i : ℕ) :
    successiveMinimumSet W i ⊆ successiveMinimumSet W' i := by
  intro r hr
  rcases hr with ⟨hr0, g, hlin, hnorm⟩
  refine ⟨hr0, fun j => carrierEquiv W W' h (g j), ?_, ?_⟩
  · have hmap : LinearIndependent ℤ
        ((V.subtype.restrictScalars ℤ) ∘ fun j : Fin i => (g j : V)) :=
      hlin.map' _ (LinearMap.ker_eq_bot.mpr subtype_restrictScalars_injective)
    convert hmap using 1
    funext j
    exact carrierEquiv_coe W W' h (g j)
  · intro j
    rw [carrierEquiv_coe W W' h (g j)]
    exact hnorm j

/-- The converse inclusion of the defining sets: a radius realising `i` independent points of
`W' ≤ E` also realises `i` independent points of the lattice `W ≤ V` it comes from. -/
lemma smSet_carrier_subset_of_eq (W : Submodule ℤ V) (W' : Submodule ℤ E)
    (h : W' = W.map (V.subtype.restrictScalars ℤ)) (i : ℕ) :
    successiveMinimumSet W' i ⊆ successiveMinimumSet W i := by
  intro r hr
  rcases hr with ⟨hr0, g, hlin, hnorm⟩
  refine ⟨hr0, fun j => (carrierEquiv W W' h).symm (g j), ?_, ?_⟩
  · have hmap : LinearIndependent ℤ
        ((V.subtype.restrictScalars ℤ) ∘
          fun j : Fin i => (((carrierEquiv W W' h).symm (g j) : W) : V)) := by
      convert hlin using 1
      funext j
      exact carrierEquiv_symm_coe W W' h (g j)
    exact LinearIndependent.of_comp _ hmap
  · intro j
    have hcoe := carrierEquiv_symm_coe W W' h (g j)
    calc ‖(((carrierEquiv W W' h).symm (g j) : W) : V)‖
        = ‖(V.subtype.restrictScalars ℤ)
            (((carrierEquiv W W' h).symm (g j) : W) : V)‖ := rfl
      _ = ‖(g j : E)‖ := by rw [hcoe]
      _ ≤ r := hnorm j

/-- Successive minima are unchanged when a `ℤ`-lattice in a subspace `V ≤ E` is transported to
the ambient space along the inclusion `V ↪ E`: if `W'` is the image of `W ≤ V` under
`V.subtype`, the defining sets of `λᵢ` (hence the successive minima themselves) coincide. -/
lemma successiveMinimum_eq_of_carrier_eq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {V : Submodule ℝ E} (W : Submodule ℤ V)
    (W' : Submodule ℤ E) (h : W' = W.map (V.subtype.restrictScalars ℤ)) (i : ℕ) :
    Commons.Lattice.SuccessiveMinima.successiveMinimum (E := V) W i =
      Commons.Lattice.SuccessiveMinima.successiveMinimum (E := E) W' i := by
  rw [successiveMinimum, successiveMinimum, Set.Subset.antisymm_iff.mpr
    ⟨smSet_subset_of_carrier_eq W W' h i, smSet_carrier_subset_of_eq W W' h i⟩]

end Commons.Lattice.SuccessiveMinima
