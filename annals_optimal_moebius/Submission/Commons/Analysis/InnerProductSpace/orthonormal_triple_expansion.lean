import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Expansion of a vector in an orthonormal triple of `ℝ³`

Let `t₀, t₁, N` be a unit, pairwise orthogonal triple of vectors of
`EuclideanSpace ℝ (Fin 3)`.  Then every vector `v` expands in this frame:

`v = ⟪v, t₀⟫ • t₀ + ⟪v, t₁⟫ • t₁ + ⟪v, N⟫ • N`.

Consequences used elsewhere: if `⟪v, t₀⟫ = ⟪v, t₁⟫ = ⟪v, N⟫ = 0` then
`v = 0`.  This complements
`Commons.Analysis.InnerProductSpace.orthonormal_frame_decomp` and
`Commons.Analysis.InnerProductSpace.span_of_orth_normal`; together the three
give the full frame decomposition of `ℝ³`.  Proof: an orthonormal triple in
dimension three is an orthonormal basis; use Mathlib's `OrthonormalBasis`
API (`orthonormalBasis` from an orthonormal linearly independent family of
correct cardinality, or the direct statement that the map
`v ↦ (⟪v,t₀⟫, ⟪v,t₁⟫, ⟪v,N⟫)` is an equivalence).
-/

noncomputable section
open scoped BigOperators
namespace Commons.Analysis.InnerProductSpace

/-- Expansion in an orthonormal triple of `EuclideanSpace ℝ (Fin 3)`. -/
theorem orthonormal_triple_expansion {t₀ t₁ Nx v : EuclideanSpace ℝ (Fin 3)}
    (ht₀ : ‖t₀‖ = 1) (ht₁ : ‖t₁‖ = 1) (hN : ‖Nx‖ = 1)
    (h₀₁ : inner ℝ t₀ t₁ = 0) (h₀N : inner ℝ t₀ Nx = 0) (h₁N : inner ℝ t₁ Nx = 0) :
    v = inner ℝ v t₀ • t₀ + inner ℝ v t₁ • t₁ + inner ℝ v Nx • Nx := by
  classical
  -- inner products of ℝ³ are symmetric, so record the mirrored hypotheses
  have h₁₀ : inner ℝ t₁ t₀ = 0 := by simpa [real_inner_comm] using h₀₁
  have hN₀ : inner ℝ Nx t₀ = 0 := by simpa [real_inner_comm] using h₀N
  have hN₁ : inner ℝ Nx t₁ = 0 := by simpa [real_inner_comm] using h₁N
  -- e is the orthonormal frame (t₀, t₁, Nx), indexed by Fin 3
  let e : Fin 3 → EuclideanSpace ℝ (Fin 3) := ![t₀, t₁, Nx]
  have he : Orthonormal ℝ e := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [e, ht₀, ht₁, hN, h₀₁, h₁₀, h₀N, hN₀, h₁N, hN₁]
  -- an orthonormal family of the right cardinality is a basis
  have hcard : Fintype.card (Fin 3) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by simp
  let B := basisOfOrthonormalOfCardEqFinrank he hcard
  have heB : Orthonormal ℝ (B : Fin 3 → EuclideanSpace ℝ (Fin 3)) := by
    simpa [B, basisOfOrthonormalOfCardEqFinrank] using he
  let b : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)) := B.toOrthonormalBasis heB
  have hb0 : b 0 = t₀ := by
    simp [b, B, basisOfOrthonormalOfCardEqFinrank, Module.Basis.coe_toOrthonormalBasis, e]
  have hb1 : b 1 = t₁ := by
    simp [b, B, basisOfOrthonormalOfCardEqFinrank, Module.Basis.coe_toOrthonormalBasis, e]
  have hb2 : b 2 = Nx := by
    simp [b, B, basisOfOrthonormalOfCardEqFinrank, Module.Basis.coe_toOrthonormalBasis, e]
  -- expand v in the frame
  calc
    v = ∑ i : Fin 3, inner ℝ (b i) v • b i := by
      simpa using (b.sum_repr' v).symm
    _ = inner ℝ (b 0) v • b 0 + inner ℝ (b 1) v • b 1 + inner ℝ (b 2) v • b 2 := by
      rw [Fin.sum_univ_three]
    _ = inner ℝ t₀ v • t₀ + inner ℝ t₁ v • t₁ + inner ℝ Nx v • Nx := by
      rw [hb0, hb1, hb2]
    _ = inner ℝ v t₀ • t₀ + inner ℝ v t₁ • t₁ + inner ℝ v Nx • Nx := by
      simp [real_inner_comm]

end Commons.Analysis.InnerProductSpace
