import Mathlib
import Submission.Commons.Analysis.InnerProductSpace.orthonormalBasis_self_of_finrank

/-!
# An orthonormal family of a subspace adapted to a second subspace

Let `E` be a finite-dimensional real inner product space and `P, L ⊆ E` two
subspaces.  This file produces an orthonormal family `v` of `E` indexed by
`Fin (finrank P)` whose span is `P`, and whose *first* `finrank (P ⊓ L)`
elements already lie in `L`.

Concretely, we start from an orthonormal family of the intersection `W = P ⊓ L`
(provided by `Commons.Analysis.InnerProductSpace.orthonormalBasis_self_of_finrank`),
viewed inside `P`.  We use the extension theorem for orthonormal families,
`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`, in the inner product
space `P`: it extends an orthonormal family supported on a subset `s` of the
index set to an orthonormal basis of `P` (of matching cardinality) without
moving the vectors of `s`.  Taking `s = {i | (i : ℕ) < finrank W}` places the
intersection's frame first.

The result is the standard "Gram–Schmidt adapted to a subspace" statement used
to split a subspace into its part inside `L` and a complementary part.
-/

noncomputable section

namespace Commons.Analysis.InnerProductSpace

theorem orthonormal_family_adapted_to_inf {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (P L : Submodule ℝ E) : ∃ v : Fin (Module.finrank ℝ P) → E, Orthonormal ℝ v ∧ (∀ i, v i ∈ P) ∧ Submodule.span ℝ (Set.range v) = P ∧ (∀ i : Fin (Module.finrank ℝ P), (i : ℕ) < Module.finrank ℝ (P ⊓ L : Submodule ℝ E) → v i ∈ L) := by
  classical
  -- Work with the intersection `W = P ⊓ L`, so that membership in `L` becomes membership in `W`.
  set W : Submodule ℝ E := P ⊓ L with hWdef
  have hWP : W ≤ P := by rw [hWdef]; exact inf_le_left
  have hWL : W ≤ L := by rw [hWdef]; exact inf_le_right
  -- An orthonormal family of `W`, spanning it.
  obtain ⟨w, hw_orth, hw_mem, _hw_span⟩ :=
    orthonormalBasis_self_of_finrank W (k := Module.finrank ℝ W) rfl
  -- The same vectors, regarded as elements of the subspace `P`.
  let wP : Fin (Module.finrank ℝ W) → P := fun j => ⟨w j, hWP (hw_mem j)⟩
  have hwP : Orthonormal ℝ wP := by
    rw [orthonormal_iff_ite] at hw_orth ⊢
    intro i j
    simpa [wP] using hw_orth i j
  -- The distinguished set of indices that will carry the intersection's frame.
  let s : Set (Fin (Module.finrank ℝ P)) := {i | (i : ℕ) < Module.finrank ℝ W}
  let φ : s → Fin (Module.finrank ℝ W) := fun x => ⟨(x : Fin (Module.finrank ℝ P)).val, x.2⟩
  -- A family on `Fin (finrank P)` whose restriction to `s` is the orthonormal frame of `W`.
  let v : Fin (Module.finrank ℝ P) → P := fun i =>
    if h : (i : ℕ) < Module.finrank ℝ W then wP ⟨(i : ℕ), h⟩ else 0
  have hφ : Function.Injective φ := by
    intro x y h
    have hval : (x : Fin (Module.finrank ℝ P)).val = (y : Fin (Module.finrank ℝ P)).val := by
      have := congrArg Fin.val h
      simpa [φ] using this
    exact Subtype.ext (Fin.ext hval)
  have hsd : s.domRestrict v = wP ∘ φ := by
    funext x
    simp only [Set.domRestrict, Function.comp_apply, v, φ]
    rw [dif_pos (show ((x : Fin (Module.finrank ℝ P)) : ℕ) < Module.finrank ℝ W from x.2)]
  have hv_orth : Orthonormal ℝ (s.domRestrict v) := by
    rw [hsd]
    exact hwP.comp φ hφ
  -- Extend this partial frame to an orthonormal basis of `P` indexed by `Fin (finrank P)`.
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ) (E := P)
      (v := v) (s := s) (by simp) hv_orth
  refine ⟨fun i => (b i : E), ?_, ?_, ?_, ?_⟩
  · -- the inclusion `P →ₗᵢ E` preserves orthonormality
    exact b.orthonormal.comp_linearIsometry P.subtypeₗᵢ
  · intro i
    exact (b i).2
  · -- the basis spans `P`, pushed forward through the inclusion
    have hspanP : Submodule.span ℝ (Set.range b) = ⊤ := by
      simpa using b.toBasis.span_eq
    calc
      Submodule.span ℝ (Set.range (fun i => (b i : E)))
          = Submodule.map P.subtype (Submodule.span ℝ (Set.range b)) := by
            rw [Submodule.map_span]
            congr 1
            ext x
            constructor
            · rintro ⟨j, rfl⟩
              exact ⟨b j, ⟨j, rfl⟩, rfl⟩
            · rintro ⟨y, ⟨j, rfl⟩, rfl⟩
              exact ⟨j, rfl⟩
      _ = Submodule.map P.subtype ⊤ := by rw [hspanP]
      _ = P := by simp
  · -- the leading vectors were chosen inside `W ≤ L`
    intro i hi
    change (b i : E) ∈ L
    have hbi : b i = v i := hb i hi
    have hvE : (v i : E) = w ⟨(i : ℕ), hi⟩ := by
      simp only [v, dif_pos hi, wP]
    rw [show (b i : E) = v i from congrArg Subtype.val hbi, hvE]
    exact hWL (hw_mem ⟨(i : ℕ), hi⟩)

end Commons.Analysis.InnerProductSpace
