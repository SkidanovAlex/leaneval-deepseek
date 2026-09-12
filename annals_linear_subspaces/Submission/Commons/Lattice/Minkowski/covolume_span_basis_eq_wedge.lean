import Mathlib
import Submission.Commons.Analysis.InnerProductSpace.covol_span_wedge_gen

namespace Commons.Lattice.Minkowski

/-- An `ℝ`-linear map preserving inner products preserves the norms of decomposable exterior
powers (an isometric embedding does not change the Gram matrix of a family, hence not the norm
of its wedge product). -/
private lemma norm_iMulti_eq_of_inner_preserving {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    (f : F →ₗ[ℝ] G) (hf : ∀ x y : F, inner ℝ (f x) (f y) = inner ℝ x y) (n : ℕ)
    (v : Fin n → F) :
    ‖exteriorPower.ιMulti ℝ n (fun i => f (v i))‖ = ‖exteriorPower.ιMulti ℝ n v‖ := by
  have hgram : Matrix.gram ℝ (fun i => f (v i)) = Matrix.gram ℝ v := by
    ext i j
    rw [Matrix.gram_apply, Matrix.gram_apply, hf]
  have hsq : ‖exteriorPower.ιMulti ℝ n (fun i => f (v i))‖ ^ 2
      = ‖exteriorPower.ιMulti ℝ n v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      exteriorPower.inner_ιMulti_self, exteriorPower.inner_ιMulti_self, hgram]
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with h | h
  · exact h
  · have h1 : 0 ≤ ‖exteriorPower.ιMulti ℝ n (fun i => f (v i))‖ := norm_nonneg _
    have h2 : 0 ≤ ‖exteriorPower.ιMulti ℝ n v‖ := norm_nonneg _
    nlinarith

/-- **Covolume of the `ℤ`-span of a basis of a subspace, transported to the ambient space.**
Let `E` be a finite-dimensional real inner product space, `V ≤ E` a submodule and
`b : Basis (Fin r) ℝ V` an `ℝ`-basis of `V`. Then the covolume (computed inside `V`, i.e. with
respect to the volume of the inner product space `V`) of the `ℤ`-lattice `span ℤ (range b)`
equals the **ambient** norm of the top exterior power of the basis vectors. -/
theorem covolume_span_basis_eq_wedge {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {r : ℕ} (V : Submodule ℝ E)
    [MeasurableSpace V] [BorelSpace V] (b : Module.Basis (Fin r) ℝ V) :
    ZLattice.covolume (Submodule.span ℤ (Set.range b)) =
      ‖exteriorPower.ιMulti ℝ r (fun i => (b i : E))‖ := by
  have hV : ZLattice.covolume (Submodule.span ℤ (Set.range b)) =
      ‖exteriorPower.ιMulti ℝ r ⇑b‖ :=
    Commons.Analysis.InnerProductSpace.covol_span_wedge_gen (E := V) (k := r) b
  have hsub : ‖exteriorPower.ιMulti ℝ r (fun i => V.subtype (b i))‖ =
      ‖exteriorPower.ιMulti ℝ r ⇑b‖ :=
    norm_iMulti_eq_of_inner_preserving (F := V) (G := E) (f := V.subtype)
      (fun x y => (Submodule.coe_inner V x y).symm) r ⇑b
  have hfe : (fun i : Fin r => V.subtype (b i)) = (fun i : Fin r => (b i : E)) := by
    funext i
    rfl
  rw [hV, ← hfe]
  exact hsub.symm

end Commons.Lattice.Minkowski
