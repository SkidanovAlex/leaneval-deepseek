import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
namespace Commons.Analysis.InnerProductSpace

/-- Every finite-dimensional real subspace `W` of a real inner product space `E` admits an
orthonormal family of `k = finrank ℝ W` vectors of `E` that all lie in `W` and span `W`. -/
lemma orthonormalBasis_self_of_finrank {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (W : Submodule ℝ E) {k : ℕ} (hk : Module.finrank ℝ W = k) :
    ∃ b : Fin k → E, Orthonormal ℝ b ∧ (∀ j : Fin k, b j ∈ W) ∧
      Submodule.span ℝ (Set.range b) = W := by
  classical
  -- `W` carries an orthonormal basis indexed by `Fin (finrank ℝ W)`; reindex it to `Fin k`.
  let e : Fin (Module.finrank ℝ W) ≃ Fin k :=
    (Fintype.equivFinOfCardEq (by rw [Fintype.card_fin, hk])).symm
  let bW : OrthonormalBasis (Fin k) ℝ W := (stdOrthonormalBasis ℝ W).reindex e
  -- push the basis vectors of `W` into `E` through the inclusion.
  let b : Fin k → E := fun j => (bW j : E)
  have hb : b = W.subtypeₗᵢ ∘ (fun j => bW j) := by
    ext j
    simp [b]
  refine ⟨b, ?_, ?_, ?_⟩
  · -- the inclusion `W →ₗᵢ E` preserves orthonormality
    rw [hb]
    exact bW.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  · intro j
    rw [hb]
    exact (bW j).2
  · -- the basis `bW` spans `W` inside `W`; push that through the inclusion
    have hspanW : Submodule.span ℝ (Set.range bW) = ⊤ := by
      simpa using (bW.toBasis.span_eq)
    calc
      Submodule.span ℝ (Set.range b) = Submodule.map W.subtype (Submodule.span ℝ (Set.range bW)) := by
        rw [Submodule.map_span]
        congr 1
        ext x
        constructor
        · rintro ⟨j, rfl⟩
          refine ⟨bW j, ⟨j, rfl⟩, ?_⟩
          simp [b]
        · rintro ⟨y, ⟨j, rfl⟩, rfl⟩
          refine ⟨j, ?_⟩
          simp [b]
      _ = Submodule.map W.subtype ⊤ := by rw [hspanW]
      _ = W := by simp

end Commons.Analysis.InnerProductSpace
